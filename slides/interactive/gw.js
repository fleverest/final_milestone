/* Interactive widgets for the final milestone deck.
 *
 * Loaded as a classic script after d3 (not an ES module, so the deck still
 * works when presentation.html is opened straight from disk), and everything
 * hangs off window.GW. Each widget is mounted by a short inline script on its
 * slide.
 *
 * Maths (K = 3, fixed n, sampling with replacement). For every tally c with
 * c1 + c2 + c3 = n,
 *   r(c) = q(c) / p_W(c)                      (sequence probabilities)
 *   g_W(theta) = sum_c B_c(theta) r(c)        (a Bernstein polynomial)
 *   KL(Q || P_W) = sum_c qtilde(c) log r(c),  qtilde(c) = n!/(c!) q(c).
 * The field-on-a-padded-grid idea is borrowed from riprvis: g_W is a
 * polynomial, so it is evaluated past the triangle and only the drawing is
 * clipped, which keeps false contours off the edges. */
window.GW = (function () {
  "use strict";
  var d3 = window.d3;

  // --- palette --------------------------------------------------------------
  var W1 = "#0072B2";   // alternative, as in the thesis TikZ
  var W0 = "#D55E00";   // null
  var INK = "#222";
  var MUTED = "#666";
  var LIM = Math.log10(20);
  // log10 g on a red-blue scale centred at g = 1, red above 1. Atoms get a
  // dark outline so the blue and vermillion markers stay visible on it.
  function fieldColour(v) {
    var t = Math.max(-1, Math.min(1, v / LIM));
    return d3.interpolateRdBu(0.5 - 0.5 * t);
  }
  var EDGE = 1e-3;      // atoms stay this far from every edge

  var uid = 0;
  function nextId(p) { uid += 1; return "gw-" + p + "-" + uid; }

  // --- ternary geometry -----------------------------------------------------
  // theta1 at the top, theta2 bottom left, theta3 bottom right; a fixed
  // viewBox, so the SVG scales with its container.
  var CORNERS = [[250, 36], [22, 430], [478, 430]];
  function toXY(b) {
    return [
      b[0] * CORNERS[0][0] + b[1] * CORNERS[1][0] + b[2] * CORNERS[2][0],
      b[0] * CORNERS[0][1] + b[1] * CORNERS[1][1] + b[2] * CORNERS[2][1]
    ];
  }
  function toBary(x, y) {
    var A = CORNERS[0], B = CORNERS[1], C = CORNERS[2];
    var det = (B[1] - C[1]) * (A[0] - C[0]) + (C[0] - B[0]) * (A[1] - C[1]);
    var b0 = ((B[1] - C[1]) * (x - C[0]) + (C[0] - B[0]) * (y - C[1])) / det;
    var b1 = ((C[1] - A[1]) * (x - C[0]) + (A[0] - C[0]) * (y - C[1])) / det;
    return [b0, b1, 1 - b0 - b1];
  }
  function poly(V) {
    return "M" + V.map(function (v) { return toXY(v).join(","); }).join("L") + "Z";
  }
  var T1 = [1, 0, 0], T2 = [0, 1, 0], T3 = [0, 0, 1];
  var M12 = [0.5, 0.5, 0], M13 = [0.5, 0, 0.5], G = [1 / 3, 1 / 3, 1 / 3];
  var SIMPLEX = poly([T1, T2, T3]);
  var NULL_POLY = poly([T2, M12, G, M13, T3]);
  var PIECES = [poly([T2, T3, M12]), poly([T3, T2, M13])];

  function inNull(b) { return b[0] <= Math.max(b[1], b[2]); }

  function intoSimplex(b) {
    var c = b.map(function (v) { return Math.max(v, 0); });
    var s = c[0] + c[1] + c[2];
    return c.map(function (v) { return v / s; });
  }
  function awayFromEdges(b) {
    var c = b.map(function (v) { return Math.max(v, EDGE); });
    var s = c[0] + c[1] + c[2];
    return c.map(function (v) { return v / s; });
  }
  // A null atom dropped in Theta1 goes to the nearer of the planes
  // theta1 = theta2 and theta1 = theta3 (the Euclidean projection onto either
  // plane averages the two coordinates).
  function clampNull(b) {
    b = awayFromEdges(intoSimplex(b));
    if (inNull(b)) return b;
    var j = b[0] - b[1] <= b[0] - b[2] ? 1 : 2;
    var m = (b[0] + b[j]) / 2;
    var c = b.slice(); c[0] = m; c[j] = m;
    return c;
  }
  // An alternative atom dropped in Theta0 is pushed just into Theta1.
  function clampAlt(b) {
    b = awayFromEdges(intoSimplex(b));
    var d = 0.004;
    for (var pass = 0; pass < 3; pass++) {
      for (var j = 1; j <= 2; j++) {
        if (b[0] < b[j] + d) {
          var m = (b[0] + b[j]) / 2;
          b[0] = m + d / 2; b[j] = m - d / 2;
        }
      }
    }
    return b;
  }

  // --- the model ------------------------------------------------------------
  function lgamma(k) { var s = 0; for (var i = 2; i <= k; i++) s += Math.log(i); return s; }

  function logSumExp(a) {
    var m = -Infinity;
    for (var i = 0; i < a.length; i++) if (a[i] > m) m = a[i];
    if (m === -Infinity) return m;
    var s = 0;
    for (var j = 0; j < a.length; j++) s += Math.exp(a[j] - m);
    return m + Math.log(s);
  }

  // Tallies, multinomial coefficients and the Bernstein basis on the drawing
  // grid and on the null search lattice, all rebuilt only when n changes.
  function Lattice(n) {
    var Y = [];
    for (var a = 0; a <= n; a++) for (var b = 0; b <= n - a; b++) Y.push([a, b, n - a - b]);
    var lf = lgamma(n);
    var logMult = Y.map(function (c) { return lf - lgamma(c[0]) - lgamma(c[1]) - lgamma(c[2]); });
    var mult = logMult.map(Math.exp);
    var m = Y.length;

    function basisFor(pts) {
      var npts = pts.length / 3;
      var B = new Float64Array(npts * m);
      var p0 = new Float64Array(n + 1), p1 = new Float64Array(n + 1), p2 = new Float64Array(n + 1);
      for (var k = 0; k < npts; k++) {
        p0[0] = p1[0] = p2[0] = 1;
        for (var e = 1; e <= n; e++) {
          p0[e] = p0[e - 1] * pts[3 * k];
          p1[e] = p1[e - 1] * pts[3 * k + 1];
          p2[e] = p2[e - 1] * pts[3 * k + 2];
        }
        for (var c = 0; c < m; c++) B[k * m + c] = mult[c] * p0[Y[c][0]] * p1[Y[c][1]] * p2[Y[c][2]];
      }
      return B;
    }

    // Drawing grid, padded past the triangle.
    var nx = 112, ny = 98, pad = 0.06;
    var w = CORNERS[2][0] - CORNERS[1][0], h = CORNERS[1][1] - CORNERS[0][1];
    var x0 = CORNERS[1][0] - pad * w, x1 = CORNERS[2][0] + pad * w;
    var y0 = CORNERS[0][1] - pad * h, y1 = CORNERS[1][1] + pad * h;
    var dx = (x1 - x0) / (nx - 1), dy = (y1 - y0) / (ny - 1);
    var gpts = new Float64Array(nx * ny * 3);
    for (var j = 0; j < ny; j++) for (var i = 0; i < nx; i++) {
      var bb = toBary(x0 + i * dx, y0 + j * dy), k = j * nx + i;
      gpts[3 * k] = bb[0]; gpts[3 * k + 1] = bb[1]; gpts[3 * k + 2] = bb[2];
    }
    var grid = { nx: nx, ny: ny, basis: basisFor(gpts) };
    grid.path = d3.geoPath(d3.geoTransform({
      point: function (x, y) { this.stream.point(x0 + x * dx, y0 + y * dy); }
    }));

    // Null search lattice: step 1/120, which contains both boundary planes.
    var N = 120, npts = [];
    for (var i1 = 0; i1 <= N; i1++) for (var i2 = 0; i2 <= N - i1; i2++) {
      var i3 = N - i1 - i2;
      if (i1 <= Math.max(i2, i3)) npts.push(i1 / N, i2 / N, i3 / N);
    }
    var search = { pts: npts, basis: basisFor(npts), count: npts.length / 3 };

    return { n: n, Y: Y, m: m, logMult: logMult, grid: grid, search: search };
  }

  var latticeCache = {};
  function lattice(n) {
    if (!latticeCache[n]) latticeCache[n] = Lattice(n);
    return latticeCache[n];
  }

  // Log sequence probabilities of one mixture at every tally, plus each
  // atom's own (for the weight update).
  function logMixture(L, mix) {
    var J = mix.atoms.length;
    var logAtoms = mix.atoms.map(function (a) { return a.map(Math.log); });
    var per = [];
    for (var j = 0; j < J; j++) per.push(new Float64Array(L.m));
    var out = new Float64Array(L.m), tmp = new Array(J);
    for (var c = 0; c < L.m; c++) {
      var y = L.Y[c];
      for (var jj = 0; jj < J; jj++) {
        var la = logAtoms[jj];
        per[jj][c] = y[0] * la[0] + y[1] * la[1] + y[2] * la[2];
        tmp[jj] = Math.log(mix.weights[jj]) + per[jj][c];
      }
      out[c] = logSumExp(tmp);
    }
    return { total: out, per: per };
  }

  // Everything the views need, from one alternative and one null mixture.
  function evaluate(n, alt, nul, opts) {
    var L = lattice(n);
    var lq = logMixture(L, alt).total, lpW = logMixture(L, nul);
    var lp = lpW.total;
    var r = new Float64Array(L.m), kl = 0, maxr = 0;
    for (var c = 0; c < L.m; c++) {
      r[c] = Math.exp(lq[c] - lp[c]);
      if (r[c] > maxr) maxr = r[c];
      kl += Math.exp(L.logMult[c] + lq[c]) * (lq[c] - lp[c]);
    }
    var res = { n: n, L: L, r: r, kl: kl, maxr: maxr, lq: lq, lp: lpW };
    if (opts && opts.klOnly) return res;
    // Grid maximum over the null: a search, so a lower bound on G_W.
    var S = L.search, gmax = -Infinity, arg = 0, m = L.m;
    for (var k = 0; k < S.count; k++) {
      var g = 0;
      for (var cc = 0; cc < m; cc++) g += S.basis[k * m + cc] * r[cc];
      if (g > gmax) { gmax = g; arg = k; }
    }
    res.gmax = gmax;
    res.argmax = [S.pts[3 * arg], S.pts[3 * arg + 1], S.pts[3 * arg + 2]];
    if (!(opts && opts.noField)) {
      var Gd = L.grid, np = Gd.nx * Gd.ny, z = new Float64Array(np);
      for (var kk = 0; kk < np; kk++) {
        var gg = 0;
        for (var c2 = 0; c2 < m; c2++) gg += Gd.basis[kk * m + c2] * r[c2];
        z[kk] = gg > 0 ? Math.log10(gg) : -99;
      }
      res.z = z;
    }
    return res;
  }

  // One Csiszar-Tusnady (EM) weight update with the atoms held fixed.
  function reweight(res, nul) {
    var L = res.L, lq = res.lq, lp = res.lp.total;
    var w = nul.weights.map(function (wj, j) {
      var s = 0, per = res.lp.per[j];
      for (var c = 0; c < L.m; c++) s += Math.exp(L.logMult[c] + lq[c]) * Math.exp(per[c] - lp[c]);
      return wj * s;
    });
    var tot = d3.sum(w);
    return w.map(function (v) { return v / tot; });
  }

  // --- small DOM helpers ----------------------------------------------------
  function el(tag, cls, text) {
    var e = document.createElement(tag);
    if (cls) e.className = cls;
    if (text !== undefined) e.textContent = text;
    return e;
  }
  function button(label, onClick, cls) {
    var b = el("button", "gw-btn" + (cls ? " " + cls : ""), label);
    b.type = "button";
    b.addEventListener("click", function (e) { e.stopPropagation(); onClick(b); });
    return b;
  }
  function slider(label, min, max, value, onInput, fmt) {
    var wrap = el("label", "gw-ctl");
    var input = el("input"); input.type = "range";
    input.min = min; input.max = max; input.step = 1; input.value = value;
    var out = el("span", "gw-val");
    fmt = fmt || String;
    out.textContent = fmt(value);
    input.addEventListener("input", function () { out.textContent = fmt(+input.value); onInput(+input.value); });
    wrap.append(el("span", null, label), input, out);
    return {
      el: wrap,
      get value() { return +input.value; },
      set value(v) { input.value = v; out.textContent = fmt(+v); },
      setMax: function (v) { input.max = v; }
    };
  }
  function toggle(label, onChange) {
    var wrap = el("label", "gw-ctl");
    var input = el("input"); input.type = "checkbox";
    input.addEventListener("change", function () { onChange(input.checked); });
    wrap.append(input, el("span", null, label));
    return { el: wrap, input: input, get value() { return input.checked; }, set value(v) { input.checked = v; } };
  }
  function tabs(labels, onChange) {
    var wrap = el("div", "gw-tabs"), value = 0;
    var bs = labels.map(function (t, i) {
      var b = button(t, function () {
        bs.forEach(function (o) { o.classList.remove("on"); });
        b.classList.add("on"); value = i; onChange(i);
      }, "gw-tab" + (i === 0 ? " on" : ""));
      wrap.append(b);
      return b;
    });
    return { el: wrap, get value() { return value; } };
  }
  function row(cls) { return el("div", "gw-row" + (cls ? " " + cls : "")); }
  function sub(s) { return "<sub>" + s + "</sub>"; }
  function fg(v) { return v >= 1000 ? d3.format(".3~s")(v) : d3.format(".4~r")(v); }

  // Save an SVG as a PNG, for the fallback snapshots.
  function snapshot(svgNode, name) {
    var clone = svgNode.cloneNode(true);
    var vb = svgNode.viewBox.baseVal, scale = 2;
    clone.setAttribute("width", vb.width * scale);
    clone.setAttribute("height", vb.height * scale);
    clone.setAttribute("font-family", getComputedStyle(svgNode).fontFamily);
    var xml = new XMLSerializer().serializeToString(clone);
    var img = new Image();
    img.onload = function () {
      var cv = document.createElement("canvas");
      cv.width = vb.width * scale; cv.height = vb.height * scale;
      var ctx = cv.getContext("2d");
      ctx.fillStyle = "#fff"; ctx.fillRect(0, 0, cv.width, cv.height);
      ctx.drawImage(img, 0, 0, cv.width, cv.height);
      var a = document.createElement("a");
      a.download = (name || "widget") + ".png";
      a.href = cv.toDataURL("image/png");
      a.click();
    };
    img.src = "data:image/svg+xml;charset=utf-8," + encodeURIComponent(xml);
  }

  function hatch(defs, id, colour) {
    var p = defs.append("pattern").attr("id", id).attr("patternUnits", "userSpaceOnUse")
      .attr("width", 8).attr("height", 8).attr("patternTransform", "rotate(45)");
    p.append("line").attr("x1", 0).attr("y1", 0).attr("x2", 0).attr("y2", 8)
      .attr("stroke", colour || "#777").attr("stroke-width", 2.2);
  }

  // Vertical colour bar for log10 of the plotted quantity.
  function colourBar(g, x, y0, y1, label) {
    var id = nextId("bar");
    var grad = g.append("defs").append("linearGradient").attr("id", id)
      .attr("x1", 0).attr("x2", 0).attr("y1", 1).attr("y2", 0);
    d3.range(0, 1.0001, 0.05).forEach(function (t) {
      grad.append("stop").attr("offset", t).attr("stop-color", fieldColour(-LIM + 2 * LIM * t));
    });
    g.append("rect").attr("x", x).attr("y", y0).attr("width", 16).attr("height", y1 - y0)
      .attr("fill", "url(#" + id + ")").attr("stroke", "#999").attr("stroke-width", 0.6);
    var s = d3.scaleLinear([-LIM, LIM], [y1, y0]);
    [[0.1, "1/10"], [0.5, "1/2"], [1, "1"], [2, "2"], [10, "10"]].forEach(function (t) {
      var yy = s(Math.log10(t[0]));
      g.append("line").attr("x1", x + 16).attr("x2", x + 21).attr("y1", yy).attr("y2", yy).attr("stroke", "#555");
      g.append("text").attr("x", x + 24).attr("y", yy + 4).attr("font-size", 13).attr("fill", INK).text(t[1]);
    });
    g.append("text").attr("x", x + 8).attr("y", y0 - 12).attr("text-anchor", "middle")
      .attr("font-size", 14).attr("font-style", "italic").attr("fill", INK).html(label);
  }

  function vertexLabels(g) {
    var at = [{ p: T1, dx: 0, dy: -12 }, { p: T2, dx: -8, dy: 22 }, { p: T3, dx: 8, dy: 22 }];
    g.selectAll("text.vl").data(at).join("text").attr("class", "vl")
      .attr("x", function (d) { return toXY(d.p)[0] + d.dx; })
      .attr("y", function (d) { return toXY(d.p)[1] + d.dy; })
      .attr("text-anchor", "middle").attr("font-size", 18).attr("font-style", "italic").attr("fill", INK)
      .html(function (d, i) { return "θ<tspan font-size=\"13\" dy=\"4\">" + (i + 1) + "</tspan>"; });
  }

  function atomRadius(w) { return Math.max(3.5, 12 * Math.sqrt(w)); }

  // --- ternary view ---------------------------------------------------------
  // A static drawing surface: field bands, the contour, the null hatch and
  // outlines, and layers for atoms. Used by widgets 2 to 6.
  function TernaryView(parent, opts) {
    opts = opts || {};
    var W = opts.colourBar === false ? 500 : 600;
    var svg = d3.select(parent).append("svg").attr("class", "gw-ternary")
      .attr("viewBox", "0 0 " + W + " 462").attr("width", "100%");
    var defs = svg.append("defs");
    var clip = nextId("clip"), hat = nextId("hatch");
    defs.append("clipPath").attr("id", clip).append("path").attr("d", SIMPLEX);
    hatch(defs, hat);
    var field = svg.append("g").attr("clip-path", "url(#" + clip + ")");
    var bands = field.append("g");
    var contour = field.append("g");
    var hatchLayer = svg.append("path").attr("d", NULL_POLY).attr("fill", "url(#" + hat + ")")
      .attr("opacity", 0.35).attr("pointer-events", "none");
    svg.append("g").selectAll("path").data(PIECES).join("path").attr("d", String)
      .attr("fill", "none").attr("stroke", "#777").attr("stroke-width", 1)
      .attr("stroke-dasharray", "1.5 3").attr("pointer-events", "none");
    svg.append("path").attr("d", SIMPLEX).attr("fill", "none").attr("stroke", "#555")
      .attr("stroke-width", 1.4).attr("pointer-events", "none");
    var marks = svg.append("g");      // overlays: fitted rings, search argmax
    var atoms = svg.append("g");
    vertexLabels(svg.append("g"));
    if (opts.colourBar !== false) colourBar(svg.append("g"), 528, 90, 400, opts.barLabel || "g" + "<tspan font-size=\"10\" dy=\"3\">W</tspan>");
    if (opts.title) {
      svg.append("text").attr("x", 10).attr("y", 30).attr("font-size", 32).attr("font-weight", 600)
        .attr("fill", INK).text(opts.title);
    }
    var thresholds = d3.range(0, 25).map(function (i) { return -LIM + (2 * LIM * i) / 24; });

    return {
      svg: svg, node: svg.node(), atoms: atoms, marks: marks, hatch: hatchLayer,
      // z is log10 g on the grid; shift is log10 C (the plotted field is g / C).
      drawField: function (res, shift) {
        shift = shift || 0;
        var Gd = res.L.grid, z = res.z;
        var zz = shift ? z.map(function (v) { return v - shift; }) : z;
        var cs = d3.contours().size([Gd.nx, Gd.ny]).thresholds(thresholds)(zz);
        bands.selectAll("path.base").data([0]).join("path").attr("class", "base")
          .attr("d", SIMPLEX).attr("fill", fieldColour(-LIM));
        bands.selectAll("path.band").data(cs).join("path").attr("class", "band")
          .attr("d", Gd.path).attr("fill", function (d) { return fieldColour(d.value); });
        var line = d3.contours().size([Gd.nx, Gd.ny]).thresholds([0])(zz);
        contour.selectAll("path").data(line).join("path").attr("d", Gd.path)
          .attr("fill", "none").attr("stroke", "#555").attr("stroke-width", 2.2)
          .attr("stroke-dasharray", "6 4");
      }
    };
  }

  // Readout rows: [label html, value html].
  function readout(node, rows) {
    node.innerHTML = rows.map(function (r) {
      return "<div class=\"gw-r\"><span class=\"gw-rl\">" + r[0] + "</span><span class=\"gw-rv\">" + r[1] + "</span></div>";
    }).join("");
  }

  // --- widgets 2 to 5 -------------------------------------------------------
  /* cfg: {
   *   fig, panel         elements (or ids) for the drawing and the controls
   *   n, nMax            sample size and slider maximum
   *   alt, nul           {atoms: [[...]], weights: [...]}
   *   editNull           click/wheel/double-click editing of the null mixture
   *   editAlt            a toggle to edit the alternative instead (widget 5)
   *   buttons            ["fw", "reweight"]
   *   fitted             URL-free data object {atoms, weights} for the overlay
   *   cSlider            widget 4's rescaling constant
   *   presets            [{label, alt, nul}]
   *   name               file-name stem for snapshots
   * } */
  function ternary(cfg) {
    var fig = typeof cfg.fig === "string" ? document.getElementById(cfg.fig) : cfg.fig;
    var panel = typeof cfg.panel === "string" ? document.getElementById(cfg.panel) : cfg.panel;
    fig.classList.add("gw"); panel.classList.add("gw", "gw-panel");

    function copyMix(m) { return { atoms: m.atoms.map(function (a) { return a.slice(); }), weights: m.weights.slice() }; }
    var init = { n: cfg.n || 10, alt: copyMix(cfg.alt), nul: copyMix(cfg.nul) };
    var state, res, logC = 0, showFitted = false, editing = "nul";
    function reset(from) {
      from = from || init;
      state = { n: state ? state.n : init.n, alt: copyMix(from.alt), nul: copyMix(from.nul) };
      if (from === init) state.n = init.n;
      // Frank-Wolfe open-loop step 2/(k+2), k counting the atoms added so far
      // (the starting atoms included, so the first click does not wipe them).
      state.added = { alt: state.alt.atoms.length, nul: state.nul.atoms.length };
    }
    reset();

    var view = TernaryView(fig, { barLabel: cfg.cSlider ? "g<tspan font-size=\"10\" dy=\"3\">W</tspan><tspan dy=\"-3\"> / C</tspan>" : undefined });
    var svg = view.svg;

    // Controls.
    var controls = row("gw-controls");
    var nSlider = slider("n", 1, cfg.nMax || 12, state.n, function (v) { state.n = v; schedule(); });
    controls.append(nSlider.el);
    var btnRow = row();
    btnRow.append(button("reset", function () { reset(); nSlider.value = state.n; schedule(); }));
    btnRow.append(button("snapshot", function () { snapshot(view.node, cfg.name || "ternary"); }));
    var editTabs = null;
    if (cfg.editAlt) {
      editTabs = tabs(["edit null", "edit alternative"], function (i) { editing = i === 0 ? "nul" : "alt"; });
    }
    var actRow = row();
    (cfg.buttons || []).forEach(function (b) {
      if (b === "fw") actRow.append(button("Frank–Wolfe step", function () { fwStep(); }));
      if (b === "reweight") actRow.append(button("reweight", function () {
        state.nul.weights = reweight(res, state.nul); schedule();
      }));
    });
    var fittedToggle = null;
    if (cfg.fitted) {
      fittedToggle = toggle("show fitted RIPr", function (v) { showFitted = v; schedule(); });
      actRow.append(fittedToggle.el);
    }
    var presetRow = null;
    if (cfg.presets) {
      presetRow = row();
      cfg.presets.forEach(function (p) {
        presetRow.append(button(p.label, function () { reset(p); if (p.n) { state.n = p.n; nSlider.value = p.n; } schedule(); }));
      });
    }
    var cBox = null, cUpdate = null;
    if (cfg.cSlider) { cBox = el("div", "gw-cslider"); cUpdate = cSliderView(cBox, function (v) { logC = v; schedule(); }); }
    var out = el("div", "gw-readout");

    panel.append(controls);
    if (editTabs) panel.append(editTabs.el);
    if (presetRow) panel.append(presetRow);
    if ((cfg.buttons || []).length || cfg.fitted) panel.append(actRow);
    if (cBox) panel.append(cBox);
    panel.append(btnRow, out);

    // The button uses an exact line search for the new atom's weight: KL is
    // convex along the segment, but so curved near the edges that the
    // open-loop step 2/(k+2) badly overshoots on a live demo.
    function fwStep() {
      var atom = clampNull(res.argmax);
      var atoms = state.nul.atoms.concat([atom]);
      function klAt(gam) {
        var w = state.nul.weights.map(function (v) { return v * (1 - gam); }).concat([gam]);
        return evaluate(state.n, state.alt, { atoms: atoms, weights: w }, { klOnly: true }).kl;
      }
      var lo = 0, hi = 1, phi = (Math.sqrt(5) - 1) / 2;
      var a = hi - phi * (hi - lo), b = lo + phi * (hi - lo), fa = klAt(a), fb = klAt(b);
      for (var it = 0; it < 40; it++) {
        if (fa < fb) { hi = b; b = a; fb = fa; a = hi - phi * (hi - lo); fa = klAt(a); }
        else { lo = a; a = b; fa = fb; b = lo + phi * (hi - lo); fb = klAt(b); }
      }
      var gam = (lo + hi) / 2;
      if (klAt(gam) >= res.kl) return;
      state.nul.weights = state.nul.weights.map(function (w) { return w * (1 - gam); });
      state.nul.atoms.push(atom);
      state.nul.weights.push(gam);
      state.added.nul += 1;
      schedule();
    }

    // Interaction: drag, wheel, click to add, double-click to remove.
    function pointerBary(ev) { var p = d3.pointer(ev, view.node); return toBary(p[0], p[1]); }
    var drag = d3.drag()
      .on("start", function (ev) { ev.sourceEvent.stopPropagation(); })
      .on("drag", function (ev, d) {
        var b = intoSimplex(pointerBary(ev.sourceEvent));
        state[d.mix].atoms[d.i] = d.mix === "nul" ? clampNull(b) : clampAlt(b);
        schedule();
      });

    function canEdit(mix) { return mix === "nul" ? cfg.editNull : (cfg.editAlt && editing === "alt"); }

    view.node.addEventListener("wheel", function (ev) {
      var d = ev.target.__data__;
      if (!d || !d.mix || !canEdit(d.mix)) return;
      ev.preventDefault();
      var mix = state[d.mix];
      if (mix.weights.length < 2) return;
      var w = mix.weights[d.i], nw = Math.min(0.995, Math.max(0.005, w * Math.exp(ev.deltaY < 0 ? 0.1 : -0.1)));
      var s = (1 - nw) / (1 - w);
      mix.weights = mix.weights.map(function (v, j) { return j === d.i ? nw : v * s; });
      schedule();
    }, { passive: false });

    svg.on("click", function (ev) {
      if (ev.defaultPrevented) return;
      var mix = editing;
      if (!canEdit(mix)) return;
      var b = pointerBary(ev);
      if (b[0] < 0 || b[1] < 0 || b[2] < 0) return;
      if (mix === "nul" && !inNull(b)) return;
      if (mix === "alt" && inNull(b)) return;
      var M = state[mix], k = state.added[mix], gam = 2 / (k + 2);
      M.weights = M.weights.map(function (w) { return w * (1 - gam); });
      M.atoms.push(mix === "nul" ? clampNull(b) : clampAlt(b));
      M.weights.push(gam);
      state.added[mix] += 1;
      schedule();
    });

    function removeAtom(d) {
      var M = state[d.mix];
      if (!canEdit(d.mix) || M.atoms.length < 2) return;
      M.atoms.splice(d.i, 1);
      var w = M.weights.splice(d.i, 1)[0];
      M.weights = M.weights.map(function (v) { return v / (1 - w); });
      schedule();
    }

    function drawAtoms() {
      var altMany = state.alt.atoms.length > 10;
      var data = [];
      state.alt.atoms.forEach(function (a, i) { data.push({ mix: "alt", i: i, a: a, w: state.alt.weights[i] }); });
      state.nul.atoms.forEach(function (a, i) { data.push({ mix: "nul", i: i, a: a, w: state.nul.weights[i] }); });
      view.atoms.selectAll("circle.atom").data(data, function (d) { return d.mix + d.i; }).join("circle")
        .attr("class", function (d) { return "atom " + d.mix; })
        .attr("cx", function (d) { return toXY(d.a)[0]; })
        .attr("cy", function (d) { return toXY(d.a)[1]; })
        .attr("r", function (d) { return d.mix === "alt" && altMany ? 3 : atomRadius(d.w); })
        .attr("fill", function (d) { return d.mix === "alt" ? W1 : W0; })
        .attr("fill-opacity", function (d) { return d.mix === "alt" && altMany ? 0.35 : 1; })
        .attr("stroke", function (d) { return d.mix === "alt" && altMany ? "none" : INK; })
        .attr("stroke-width", 1.5)
        .style("cursor", "grab")
        .call(drag)
        .on("click", function (ev) { ev.stopPropagation(); })
        .on("dblclick", function (ev, d) { ev.stopPropagation(); ev.preventDefault(); removeAtom(d); });
      var rings = showFitted && cfg.fitted ? cfg.fitted.atoms.map(function (a, i) { return { a: a, w: cfg.fitted.weights[i] }; }) : [];
      view.marks.selectAll("circle.fit").data(rings).join("circle").attr("class", "fit")
        .attr("cx", function (d) { return toXY(d.a)[0]; }).attr("cy", function (d) { return toXY(d.a)[1]; })
        .attr("r", function (d) { return atomRadius(d.w) + 5; })
        .attr("fill", "none").attr("stroke", W0).attr("stroke-width", 2).attr("stroke-dasharray", "3 2")
        .attr("pointer-events", "none");
    }

    function update() {
      res = evaluate(state.n, state.alt, state.nul);
      view.drawField(res, logC / Math.LN10);
      drawAtoms();
      if (cfg.cSlider) cUpdate(logC, res.gmax, res.maxr);
      readout(out, [["max of g" + sub("W") + " over the null", fg(res.gmax)]]);
    }
    var pending = false;
    function schedule() {
      if (pending) return;
      pending = true;
      requestAnimationFrame(function () { pending = false; update(); });
    }
    update();

    // Widget 4's constant: a log-scale track with ticks at the grid max and
    // at max r(c), where dividing always gives a valid but useless e-variable.
    function cSliderView(box, onInput) {
      var Wd = 420, H = 74, x0 = 16, x1 = Wd - 16, ly = 30;
      var s = d3.select(box).append("svg").attr("viewBox", "0 0 " + Wd + " " + H).attr("width", "100%");
      var track = s.append("g");
      var scale = d3.scaleLog([1, 10], [x0, x1]).clamp(true);
      var knob = s.append("circle").attr("r", 9).attr("cy", ly).attr("fill", INK).style("cursor", "ew-resize");
      var ticks = s.append("g");
      var grab = s.append("g");
      s.append("text").attr("x", x0).attr("y", 12).attr("font-size", 13).attr("fill", MUTED).text("C (log scale)");
      var btn = button("C = grid max", function () { onInput(Math.log(Math.max(1, last.gmax))); });
      var btnOne = button("C = 1", function () { onInput(0); });
      var r2 = row(); r2.append(btn, btnOne); box.append(r2);
      var last = { gmax: 1, maxr: 1 };
      function set(ev) {
        var p = d3.pointer(ev, s.node());
        onInput(Math.log(scale.invert(Math.max(x0, Math.min(x1, p[0])))));
      }
      s.call(d3.drag().on("start drag", function (ev) { set(ev.sourceEvent); }));
      return function (lc, gmax, maxr) {
        last = { gmax: gmax, maxr: maxr };
        var top = Math.max(10, maxr * 1.3, Math.exp(lc) * 1.05);
        scale.domain([1, top]);
        track.selectAll("line").data([0]).join("line").attr("x1", x0).attr("x2", x1).attr("y1", ly).attr("y2", ly)
          .attr("stroke", "#bbb").attr("stroke-width", 4).attr("stroke-linecap", "round");
        var tk = [{ v: Math.max(gmax, 1), t: "grid max", c: "#555", dy: 22 }, { v: maxr, t: "max r(c)", c: W0, dy: 38 }];
        ticks.selectAll("g").data(tk).join(function (e) {
          var g = e.append("g"); g.append("line"); g.append("text"); return g;
        }).each(function (d) {
          var g = d3.select(this), x = scale(d.v);
          g.select("line").attr("x1", x).attr("x2", x).attr("y1", ly - 10).attr("y2", ly + d.dy - 12).attr("stroke", d.c).attr("stroke-width", 2);
          g.select("text").attr("x", x).attr("y", ly + d.dy).attr("text-anchor", "middle").attr("font-size", 12).attr("fill", d.c).text(d.t);
        });
        knob.attr("cx", scale(Math.exp(lc)));
      };
    }

    return { update: schedule, state: function () { return state; } };
  }

  // --- widget 1: the one-dimensional likelihood ratio -----------------------
  function line(cfg) {
    var fig = typeof cfg.fig === "string" ? document.getElementById(cfg.fig) : cfg.fig;
    fig.classList.add("gw");
    var st = { mu: cfg.mu || 0.6, nu: cfg.nu || 0.5, n: cfg.n || 10 };
    var init = { mu: st.mu, nu: st.nu, n: st.n };
    var Wd = 1100, H = 330, m = { l: 70, r: 30, t: 12, b: 76 };
    var svg = d3.select(fig).append("svg").attr("class", "gw-line")
      .attr("viewBox", "0 0 " + Wd + " " + H).attr("width", "100%");
    var x = d3.scaleLinear([0, 1], [m.l, Wd - m.r]);
    var y = d3.scaleLog([0.01, 100], [H - m.b, m.t]);
    var defs = svg.append("defs"), clip = nextId("clip"), hat = nextId("hatch");
    defs.append("clipPath").attr("id", clip).append("rect").attr("x", m.l).attr("y", m.t)
      .attr("width", Wd - m.l - m.r).attr("height", H - m.t - m.b);
    hatch(defs, hat);
    svg.append("rect").attr("x", x(0)).attr("y", m.t).attr("width", x(0.5) - x(0)).attr("height", H - m.t - m.b)
      .attr("fill", "url(#" + hat + ")").attr("opacity", 0.35);
    svg.append("text").attr("x", x(0.25)).attr("y", m.t + 26).attr("text-anchor", "middle").attr("font-size", 22)
      .attr("fill", INK).html("H<tspan font-size=\"15\" dy=\"5\">0</tspan>");
    svg.append("text").attr("x", x(0.75)).attr("y", m.t + 26).attr("text-anchor", "middle").attr("font-size", 22)
      .attr("fill", INK).html("H<tspan font-size=\"15\" dy=\"5\">1</tspan>");
    svg.append("line").attr("x1", x(0)).attr("x2", x(1)).attr("y1", y(1)).attr("y2", y(1))
      .attr("stroke", "#555").attr("stroke-dasharray", "2 4").attr("stroke-width", 1.5);
    var axX = svg.append("g").attr("transform", "translate(0," + (H - m.b) + ")")
      .call(d3.axisBottom(x).tickValues([0, 0.25, 0.5, 0.75, 1]).tickFormat(function (v) { return v === 0.5 ? "1/2" : String(v); }));
    svg.append("g").attr("transform", "translate(" + m.l + ",0)")
      .call(d3.axisLeft(y).tickValues([0.01, 0.1, 1, 10, 100]).tickFormat(function (v) { return v < 1 ? "1/" + Math.round(1 / v) : String(v); }));
    svg.selectAll(".tick text").attr("font-size", 16);
    svg.append("text").attr("x", Wd - m.r).attr("y", H - m.b + 26).attr("text-anchor", "end")
      .attr("font-size", 20).attr("font-style", "italic").text("θ");
    svg.append("text").attr("x", m.l + 10).attr("y", m.t + 26).attr("font-size", 20).attr("font-style", "italic").text("g(θ)");
    var curve = svg.append("g").attr("clip-path", "url(#" + clip + ")");
    var handles = svg.append("g");

    var controls = row("gw-controls");
    var nS = slider("n", 1, 50, st.n, function (v) { st.n = v; draw(); });
    controls.append(nS.el,
      button("reset", function () { st.mu = init.mu; st.nu = init.nu; st.n = init.n; nS.value = st.n; draw(); }),
      button("snapshot", function () { snapshot(svg.node(), cfg.name || "likelihood-ratio"); }));
    var out = el("div", "gw-readout gw-inline");
    controls.append(out);
    fig.append(controls);

    function g(t) { return Math.pow(t * st.mu / st.nu + (1 - t) * (1 - st.mu) / (1 - st.nu), st.n); }

    var hy = H - m.b;
    var hd = [{ key: "mu", colour: W1, label: "μ" }, { key: "nu", colour: W0, label: "ν" }];
    var drag = d3.drag().on("drag", function (ev, d) {
      var v = x.invert(d3.pointer(ev.sourceEvent, svg.node())[0]);
      v = Math.max(0.01, Math.min(0.99, v));
      if (d.key === "nu" && Math.abs(v - 0.5) < 0.01) v = 0.5;
      st[d.key] = v; draw();
    });

    function draw() {
      var N = 400, pts = d3.range(N + 1).map(function (i) { var t = i / N; return [t, g(t)]; });
      var segs = [];
      for (var i = 0; i < N; i++) segs.push([pts[i], pts[i + 1]]);
      curve.selectAll("line").data(segs).join("line")
        .attr("x1", function (s) { return x(s[0][0]); }).attr("x2", function (s) { return x(s[1][0]); })
        .attr("y1", function (s) { return y(Math.max(1e-9, s[0][1])); }).attr("y2", function (s) { return y(Math.max(1e-9, s[1][1])); })
        .attr("stroke", function (s) { return fieldColour(Math.log10((s[0][1] + s[1][1]) / 2)); })
        .attr("stroke-width", function (s) { return s[1][0] <= 0.5 && s[0][1] > 1 && s[1][1] > 1 ? 7 : 3.5; })
        .attr("stroke-linecap", "round");
      handles.selectAll("g.h").data(hd).join(function (e) {
        var gg = e.append("g").attr("class", "h").style("cursor", "ew-resize").call(drag);
        gg.append("path"); gg.append("text"); return gg;
      }).each(function (d) {
        var gg = d3.select(this), xv = x(st[d.key]);
        gg.select("path").attr("d", d.key === "mu"
          ? "M" + xv + "," + (hy - 12) + "l10,18h-20z"
          : d3.symbol(d3.symbolCircle, 260)())
          .attr("transform", d.key === "nu" ? "translate(" + xv + "," + hy + ")" : null)
          .attr("fill", d.colour).attr("stroke", INK).attr("stroke-width", 1.5);
        gg.select("text").attr("x", xv).attr("y", hy + 50).attr("text-anchor", "middle")
          .attr("font-size", 20).attr("font-style", "italic").attr("fill", d.colour)
          .text(d.label + " = " + d3.format(".2f")(st[d.key]));
      });
      axX.raise(); handles.raise();
      var mx = d3.max(d3.range(0, 201).map(function (i) { return g(0.5 * i / 200); }));
      readout(out, [
        ["e-variable", mx <= 1 + 1e-12 ? "<span class=\"gw-good\">yes</span>" : "<span class=\"gw-bad\">no</span>"]
      ]);
    }
    draw();
  }

  // --- reading a ternary diagram ------------------------------------------
  // The probability vector under the cursor, with a pointer. When the cursor
  // leaves the triangle the pointer returns to the example election.
  function reader(cfg) {
    var fig = typeof cfg.fig === "string" ? document.getElementById(cfg.fig) : cfg.fig;
    fig.classList.add("gw", "gw-reader");
    var home = cfg.point || [0.45, 0.35, 0.20];
    var svg = d3.select(fig).append("svg").attr("viewBox", "0 0 500 462").attr("width", "100%");
    var clip = nextId("clip");
    svg.append("defs").append("clipPath").attr("id", clip).append("path").attr("d", SIMPLEX);
    var grid = svg.append("g").attr("clip-path", "url(#" + clip + ")");
    d3.range(1, 10).forEach(function (k) {
      var t = k / 10;
      [[[t, 1 - t, 0], [t, 0, 1 - t]], [[1 - t, t, 0], [0, t, 1 - t]], [[1 - t, 0, t], [0, 1 - t, t]]].forEach(function (seg) {
        var a = toXY(seg[0]), b = toXY(seg[1]);
        grid.append("line").attr("x1", a[0]).attr("y1", a[1]).attr("x2", b[0]).attr("y2", b[1])
          .attr("stroke", "#e4e4e4").attr("stroke-width", 1);
      });
    });
    svg.append("path").attr("d", SIMPLEX).attr("fill", "none").attr("stroke", "#555").attr("stroke-width", 1.6);
    vertexLabels(svg.append("g"));
    var ptr = svg.append("g").attr("pointer-events", "none");
    var dot = ptr.append("circle").attr("r", 9).attr("fill", W1).attr("stroke", INK).attr("stroke-width", 1.5);
    var label = ptr.append("text").attr("font-size", 28).attr("fill", INK)
      .attr("paint-order", "stroke").attr("stroke", "#fff").attr("stroke-width", 5).attr("stroke-linejoin", "round");
    var f = d3.format(".2f");

    function show(b) {
      var p = toXY(b), right = p[0] > 290;
      dot.attr("cx", p[0]).attr("cy", p[1]);
      label.attr("x", p[0] + (right ? -16 : 16)).attr("y", p[1] - 14)
        .attr("text-anchor", right ? "end" : "start")
        .text("(" + b.map(f).join(", ") + ")");
    }
    // A transparent hit area slightly larger than the triangle, so the
    // pointer can reach the edges and vertices.
    svg.append("rect").attr("width", 500).attr("height", 462).attr("fill", "transparent")
      .on("pointermove", function (ev) {
        var p = d3.pointer(ev, svg.node()), b = toBary(p[0], p[1]);
        if (Math.min(b[0], b[1], b[2]) < -0.02) { show(home); return; }
        show(intoSimplex(b));
      })
      .on("pointerleave", function () { show(home); });
    show(home);
  }

  // --- widget 6: playback of ripr fits -------------------------------------
  /* cfg: { fig, panel, scenarios: [{label, runs: [{title, trace}]}] }, each
   * trace in the slides/data/trace_<method>.json format. */
  var RUN_COLOURS = ["#6a3d9a", "#1b9e77", "#222"];
  function playback(cfg) {
    var fig = typeof cfg.fig === "string" ? document.getElementById(cfg.fig) : cfg.fig;
    fig.classList.add("gw", "gw-playback");
    var panelsRow = el("div", "gw-panels"), chartBox = el("div", "gw-chart"), controls = row("gw-controls");
    fig.append(panelsRow, chartBox, controls);

    var SPEEDS = [0.05, 0.1, 0.15, 0.2, 0.25];
    var sc, views, pos = 0, playing = false, speed = SPEEDS[1], sync = "time", timer = null;
    var cache = new Map();
    function resFor(trace, i) {
      var key = trace.method + ":" + i;
      if (!cache.has(key)) {
        var it = trace.iters[i];
        cache.set(key, evaluate(trace.scenario.n, { atoms: [trace.scenario.mu], weights: [1] },
          { atoms: it.atoms.map(awayFromEdges), weights: it.weights }));
        if (cache.size > 600) cache.delete(cache.keys().next().value);
      }
      return cache.get(key);
    }

    var chart = d3.select(chartBox).append("svg").attr("viewBox", "0 0 1100 200").attr("width", "100%");
    var cm = { l: 70, r: 150, t: 28, b: 40 };

    function growth(it) { return it.kl - (it.logL == null ? 0 : it.logL); }
    function tRange() {
      var hi = 0;
      sc.runs.forEach(function (r) { r.trace.iters.forEach(function (it) { hi = Math.max(hi, it.t); }); });
      return [0, hi];
    }
    function iMax() { return d3.max(sc.runs, function (r) { return r.trace.iters.length; }); }
    function indexAt(trace) {
      var its = trace.iters;
      if (sync === "iter") return Math.min(its.length - 1, Math.round(pos * (iMax() - 1)));
      var T = pos * tRange()[1];
      var k = d3.bisector(function (it) { return it.t; }).right(its, T) - 1;
      return Math.max(0, k);
    }

    function setScenario(i) {
      sc = cfg.scenarios[i];
      panelsRow.replaceChildren();
      views = sc.runs.map(function (r) {
        var box = el("div", "gw-panel-cell");
        panelsRow.append(box);
        return TernaryView(box, { colourBar: false, title: r.title });
      });
      pos = 0; draw();
    }

    function drawChart() {
      var tr = tRange();
      var x = sync === "iter"
        ? d3.scaleLinear([1, iMax()], [cm.l, 1100 - cm.r])
        : d3.scaleLinear(tr, [cm.l, 1100 - cm.r]);
      var all = [];
      sc.runs.forEach(function (r) { r.trace.iters.forEach(function (it) { all.push(growth(it)); }); if (r.trace.final && r.trace.final.logU != null) all.push(r.trace.iters[r.trace.iters.length - 1].kl - r.trace.final.logU); });
      var ext = d3.extent(all);
      var y = d3.scaleLinear([Math.min(0, ext[0]), ext[1]], [200 - cm.b, cm.t]).nice();
      chart.selectAll("*").remove();
      chart.append("g").attr("transform", "translate(0," + (200 - cm.b) + ")").call(d3.axisBottom(x).ticks(8, sync === "iter" ? "~d" : "~g"));
      chart.append("g").attr("transform", "translate(" + cm.l + ",0)").call(d3.axisLeft(y).ticks(4));
      chart.selectAll(".tick text").attr("font-size", 13);
      chart.append("text").attr("x", 1100 - cm.r).attr("y", 200 - 4).attr("text-anchor", "end").attr("font-size", 14).attr("fill", MUTED)
        .text(sync === "iter" ? "iteration" : "wall-clock seconds");
      chart.append("text").attr("x", cm.l + 6).attr("y", cm.t - 12).attr("font-size", 14).attr("fill", MUTED)
        .text("estimated growth KL − log L (nats)");
      function xv(it, j) { return sync === "iter" ? x(j + 1) : x(it.t); }
      sc.runs.forEach(function (r, k) {
        var col = RUN_COLOURS[k % RUN_COLOURS.length], its = r.trace.iters;
        chart.append("path").datum(its).attr("fill", "none").attr("stroke", col).attr("stroke-width", 2)
          .attr("d", d3.line().x(function (it, j) { return xv(it, j); }).y(function (it) { return y(growth(it)); }));
        var last = its[its.length - 1];
        if (r.trace.final && r.trace.final.logU != null) {
          chart.append("path").attr("d", d3.symbol(d3.symbolDiamond, 90)())
            .attr("transform", "translate(" + xv(last, its.length - 1) + "," + y(last.kl - r.trace.final.logU) + ")").attr("fill", col);
        }
        var i = indexAt(r.trace), cur = its[i];
        chart.append("circle").attr("r", 5).attr("fill", col).attr("stroke", "#fff")
          .attr("cx", xv(cur, i)).attr("cy", y(growth(cur)));
        chart.append("text").attr("x", 1100 - cm.r + 10).attr("y", cm.t + 18 + 20 * k).attr("font-size", 14).attr("fill", col).text(r.title);
      });
      chart.append("text").attr("x", 1100 - cm.r + 10).attr("y", cm.t + 18 + 20 * sc.runs.length + 6).attr("font-size", 12).attr("fill", MUTED)
        .text("◆ bounded: KL − log U");
      var cx = sync === "iter" ? x(1 + pos * (iMax() - 1)) : x(pos * tr[1]);
      chart.append("line").attr("x1", cx).attr("x2", cx).attr("y1", cm.t).attr("y2", 200 - cm.b)
        .attr("stroke", "#888").attr("stroke-dasharray", "3 3");
    }

    function draw() {
      sc.runs.forEach(function (r, k) {
        var i = indexAt(r.trace), it = r.trace.iters[i], res = resFor(r.trace, i), v = views[k];
        v.drawField(res, 0);
        var data = it.atoms.map(function (a, j) { return { a: awayFromEdges(a), w: it.weights[j], mix: "nul" }; });
        data.push({ a: r.trace.scenario.mu, w: 0.5, mix: "alt" });
        v.atoms.selectAll("circle").data(data).join("circle")
          .attr("cx", function (d) { return toXY(d.a)[0]; }).attr("cy", function (d) { return toXY(d.a)[1]; })
          .attr("r", function (d) { return d.mix === "alt" ? 7 : atomRadius(d.w); })
          .attr("fill", function (d) { return d.mix === "alt" ? W1 : W0; }).attr("stroke", INK).attr("stroke-width", 1.5);
        v.marks.selectAll("text").data([0]).join("text").attr("x", 490).attr("y", 28).attr("text-anchor", "end")
          .attr("font-size", 22).attr("fill", MUTED)
          .text(it.atoms.length + (it.atoms.length === 1 ? " atom" : " atoms"));
      });
      drawChart();
      scrub.value = Math.round(pos * 1000);
    }

    var scrub = slider("", 0, 1000, 0, function (v) { pos = v / 1000; draw(); }, function () { return ""; });
    var playBtn = button("play", function () { playing = !playing; playBtn.textContent = playing ? "pause" : "play"; tick(); });
    var speedS = slider("speed", 0, SPEEDS.length - 1, 1, function (v) { speed = SPEEDS[v]; }, function (v) { return SPEEDS[v] + "×"; });
    var syncTabs = tabs(["wall-clock sync", "iteration sync"], function (i) { sync = i === 0 ? "time" : "iter"; draw(); });
    controls.append(playBtn, scrub.el, speedS.el, syncTabs.el);
    if (cfg.scenarios.length > 1) {
      controls.append(tabs(cfg.scenarios.map(function (s) { return s.label; }), function (i) { setScenario(i); }).el);
    }

    // Speed is a multiple of real time: at 0.1x a 2 s fit plays in 20 s.
    // Iteration sync moves at the same overall rate.
    var lastT = null;
    function tick() {
      if (timer) cancelAnimationFrame(timer);
      lastT = null;
      function frame(now) {
        if (!playing) return;
        if (lastT !== null) {
          pos += (now - lastT) / 1000 * speed / tRange()[1];
          if (pos >= 1) { pos = 1; playing = false; playBtn.textContent = "play"; }
          draw();
        }
        lastT = now;
        if (playing) timer = requestAnimationFrame(frame);
      }
      if (playing) { if (pos >= 1) pos = 0; timer = requestAnimationFrame(frame); }
    }

    setScenario(0);
  }

  // k draws from Dirichlet(1, 1, 1) truncated to Theta1 (rejection
  // sampling), equal weights, reproducible from the seed.
  function priorSample(k, seed) {
    var rnd = d3.randomLcg(seed || 1), atoms = [];
    while (atoms.length < k) {
      var u = [rnd(), rnd()].sort(d3.ascending);
      var b = [u[0], u[1] - u[0], 1 - u[1]];
      if (!inNull(b)) atoms.push(awayFromEdges(b));
    }
    return { atoms: atoms, weights: atoms.map(function () { return 1 / k; }) };
  }

  return {
    priorSample: priorSample,
    W0: W0, W1: W1, fieldColour: fieldColour, evaluate: evaluate, reweight: reweight,
    ternary: ternary, line: line, playback: playback, reader: reader, snapshot: snapshot
  };
})();
