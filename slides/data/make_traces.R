# Fit traces for the RIPr search widget.
#
# Run from the repository root, bypassing the project .Rprofile:
#
#   Rscript --vanilla slides/data/make_traces.R
#
# Scenario: multinomial, K = 3, n = 10 trials, point alternative
# mu = (0.45, 0.35, 0.20); plurality null H0 = union_{j in 2,3} {theta_1 <= theta_j},
# each piece a simplex with the tie point replacing e_1 (as in
# ripr-vis/search-slides.qmd).
#
# Every method gets the same compute budget, BUDGET seconds of step-rule time:
# the cumulative `elapsed` column of ripr's trace, which is what
# riprvis::ripr_compare_data() uses as its clock. It excludes the diagnostic
# `record_gap` sweeps and snapshots, so the wall clock is roughly double.
# `t` in the output is that same cumulative step time (init row included).
#
# Per iterate:
#   kl   = KL(Q || P_W) in nats (trace column `kl`).
#   logL = log1p(gap), where ripr's gap is sup_theta G(theta) - 1 with
#          G(theta) = E_theta[Q / P_W], the sup being found by a multi-start
#          local search (so it is a lower bound on the true sup): logL is the
#          log of a lower bound on G_W = sup_{H0} E_theta[Q / P_W].
# final.logU = log of certify()'s branch-and-bound upper bound on G_W for the
#          final iterate's mixture (as fitted, no reweighting or pruning).

suppressPackageStartupMessages({
  library(ripr)
  library(jsonlite)
})

args <- commandArgs(trailingOnly = FALSE)
script <- sub("^--file=", "", grep("^--file=", args, value = TRUE))
out_dir <- if (length(script)) dirname(normalizePath(script)) else "slides/data"

BUDGET <- 2 # seconds of step time per method
MAX_BYTES <- 2e6
TOL <- 1e-9

K <- 3L
N_TRIALS <- 10L
MU <- c(0.45, 0.35, 0.20)

family <- multinomial_family(n_trials = N_TRIALS, k = K)
plurality <- null_model(
  family,
  lapply(2:K, function(j) {
    vertices <- diag(K)
    vertices[, 1L] <- replace(numeric(K), c(1L, j), 0.5)
    simplex_region(vertices = vertices)
  })
)
Q <- family(MU)

# --- Running a method to budget -----------------------------------------------

step_time <- function(state) sum(state@trace$elapsed)

init <- function(atoms = NULL) {
  ripr_init(
    Q,
    plurality,
    atoms = atoms,
    record_gap = TRUE,
    control = ripr_control(snapshot = "all")
  )
}

# `step` advances the state by one round (one or more trace rows).
run_to_budget <- function(state, step) {
  while (step_time(state) < BUDGET) state <- step(state)
  state
}

em_only <- function(state) em_step(state, record_gap = TRUE)
fw_only <- function(state) fw_step(state, record_gap = TRUE)
hybrid <- function(state) {
  state |> fw_step(record_gap = TRUE) |> em_step(record_gap = TRUE)
}

# --- Output -------------------------------------------------------------------

flatten <- function(atoms, weights) {
  list(
    atoms = unname(t(do.call(cbind, atoms))),
    weights = unname(unlist(weights))
  )
}

certify_log_ub <- function(P) {
  X <- likelihood(Q, label = "Q") / likelihood(P, label = "P")
  cert <- certify(X, plurality, tol = TOL)
  if (any(cert$budget_hit)) warning("certify hit its node budget")
  log(cert$sup_ub)
}

# Keep the first and last rows and roughly log-spaced times in between.
thin <- function(iters, n_keep) {
  n <- length(iters)
  if (n <= n_keep) return(iters)
  t <- vapply(iters, `[[`, numeric(1L), "t")
  t0 <- max(min(t[t > 0]), 1e-4)
  targets <- exp(seq(log(t0), log(max(t)), length.out = n_keep))
  keep <- unique(c(1L, vapply(targets, function(x) which.min(abs(t - x)), 1L), n))
  iters[sort(keep)]
}

write_trace <- function(state, method) {
  tr <- state@trace
  snaps <- state@snapshots
  stopifnot(length(snaps) == nrow(tr))
  t <- cumsum(tr$elapsed)
  iters <- lapply(seq_len(nrow(tr)), function(i) {
    flat <- flatten(snaps[[i]]$atoms, snaps[[i]]$weights)
    list(
      t = t[i],
      phase = tr$phase[i],
      atoms = flat$atoms,
      weights = flat$weights,
      kl = tr$kl[i],
      logL = log1p(tr$gap_after[i])
    )
  })
  fit <- ripr_finish(state)
  out <- list(
    method = method,
    scenario = list(n = N_TRIALS, mu = MU),
    budget_seconds = BUDGET,
    n_iters_run = nrow(tr),
    iters = iters,
    final = list(logU = certify_log_ub(fit$P_star))
  )
  path <- file.path(out_dir, paste0("trace_", method, ".json"))
  json <- function(o) toJSON(o, auto_unbox = TRUE, digits = NA, matrix = "rowmajor")
  txt <- json(out)
  n_keep <- length(iters)
  while (nchar(txt, type = "bytes") > MAX_BYTES) {
    n_keep <- floor(n_keep * 0.8)
    out$iters <- thin(iters, n_keep)
    txt <- json(out)
  }
  writeLines(txt, path)
  last <- iters[[length(iters)]]
  message(sprintf(
    "%-9s rows=%4d kept=%4d t=%.2fs kl=%.6f logL=%.3g logU=%.3g atoms=%d  (%s, %.0f kB)",
    method, nrow(tr), length(out$iters), last$t, last$kl, last$logL,
    out$final$logU, length(last$weights), basename(path),
    file.size(path) / 1e3
  ))
  invisible(out)
}

# --- Default scenario ---------------------------------------------------------

# ripr's default init: one atom per piece, the projection of the family's
# reference point: (0.4, 0.4, 0.2) and (0.325, 0.35, 0.325).
set.seed(1L)
st_em <- run_to_budget(init(), em_only)
set.seed(1L)
st_fw <- run_to_budget(init(), fw_only)
set.seed(1L)
st_hy <- run_to_budget(init(), hybrid)

write_trace(st_em, "EM")
write_trace(st_fw, "FW")
write_trace(st_hy, "hybrid")

# --- The fitted RIPr ----------------------------------------------------------

# The hybrid ends with many near-coincident atoms around one point per tie
# edge. Collapse each piece to its weighted mean, then polish that two-atom
# mixture with EM until KL stops moving; keep whichever of the two certifies
# the smaller upper bound.
collapse <- lapply(seq_along(st_hy@atoms), function(p) {
  a <- st_hy@atoms[[p]]
  w <- st_hy@weights[[p]]
  if (!length(w)) return(matrix(numeric(0), nrow = K, ncol = 0L))
  matrix(a %*% w / sum(w), ncol = 1L)
})
set.seed(1L)
st_two <- ripr_init(Q, plurality, atoms = collapse) |>
  em_step(times = 5000L, until = kl_flat(1e-14))

candidate <- function(state) {
  fit <- ripr_finish(state, reoptimise = TRUE, identify = TRUE)
  list(
    atoms = unname(t(fit$W0@components)),
    weights = fit$W0@weights,
    kl = fit$kl,
    logU = certify_log_ub(fit$P_star)
  )
}
cands <- list(hybrid = candidate(st_hy), two_atom = candidate(st_two))
best <- cands[[which.min(vapply(cands, `[[`, 0, "logU"))]]
for (nm in names(cands)) {
  message(sprintf(
    "RIPr candidate %-8s atoms=%d kl=%.8f logU=%.3g",
    nm, length(cands[[nm]]$weights), cands[[nm]]$kl, cands[[nm]]$logU
  ))
}
writeLines(
  toJSON(best, auto_unbox = TRUE, digits = NA, matrix = "rowmajor"),
  file.path(out_dir, "ripr_default.json")
)
