# Scripts

| Script | Purpose |
|---|---|
| `check_all.sh` | The full check: the zero-warning `lake build`, the source sweep and the axiom report of the six main results |
| `check_sources.py` | Fails on `sorry`, `admit`, `axiom` or `opaque` declarations, `native_decide`, `implemented_by`, `extern`, kernel type-check bypasses, and heartbeat or recursion-depth overrides anywhere in the Lean sources (comments and strings are ignored). Each comparator challenge must contain exactly one `sorry`, the proof of its final theorem |
| `check_axioms.py` | Checks the output of `lake env lean Riesz2/Meta/AxiomsAudit.lean`: each main result must depend on exactly `propext`, `Classical.choice` and `Quot.sound` |
| `run_comparators.sh` | Runs `lake comparator` on the pairs under `Riesz2Audit/`, with the Lean, NanoDa and con-ron kernels bundled with the toolchain |

`check_axioms.py` and `run_comparators.sh` are adapted from the scripts of the same names in
[subdiffusive-process](https://github.com/nitromannitol/subdiffusive-process) (Apache License
2.0). All scripts are released under the Apache License 2.0.
