"""Bundle the ripr traces into gw_data.js, loaded by the deck as a plain
script (fetch() and ES modules do not work when the slides are opened from
disk). Run after make_traces.R: python3 slides/data/bundle.py"""
import json
from pathlib import Path

here = Path(__file__).parent


def rounded(x):
    if isinstance(x, float):
        return float(f"{x:.6g}")
    if isinstance(x, list):
        return [rounded(v) for v in x]
    if isinstance(x, dict):
        return {k: rounded(v) for k, v in x.items()}
    return x


data = {
    "fitted": rounded(json.loads((here / "ripr_default.json").read_text())),
    "traces": {
        m: rounded(json.loads((here / f"trace_{m}.json").read_text()))
        for m in ["EM", "FW", "hybrid"]
    },
}
out = "window.GW_DATA = " + json.dumps(data, separators=(",", ":")) + ";\n"
(here / "gw_data.js").write_text(out)
print(f"wrote gw_data.js ({len(out) / 1e6:.2f} MB)")
