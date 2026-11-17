# Handoff archive — Eulerian cross-vendor review audit

Start with `AUDIT.md`. It holds the verdicts, the reconstruction of each decisive step, every issue found, the comparison of the two submissions, the theorem supported, the computations performed and their limits.

## Contents

| Path | What it is |
|---|---|
| `AUDIT.md` | the audit |
| `checks/eul.py` | exact toolkit written for the audit (Sturm, Sturm–Tarski, isolation) |
| `checks/00_selftest.py` … `08_large_degree.py` | the audit's own checks; each file's docstring states what it certifies |
| `outputs/0*.txt` | actual output of each check as run for the audit |
| `outputs/supplied_*.txt` | actual stdout of the seven scripts supplied in the packet |
| `outputs/supplied_generated/` | JSON files those supplied scripts wrote when re-run |
| `run_all.sh` | re-runs checks 00–08 (the two slow `08` runs are listed as comments) |
| `requirements-audit.txt` | pinned dependencies |
| `SHA256SUMS` | hashes of every file in this archive |

The packet itself is not copied here. It is identified by
SHA-256 `546fb0ce23613ee2a02ac87a56d74400e6ea91aecdd93094d005d846d5897a2e` (`eulerian-cross-vendor-review.zip`).

## Reproduce

```
python3 -m venv venv
./venv/bin/python -m pip install -r requirements-audit.txt
./run_all.sh /path/to/extracted/eulerian-cross-vendor-review     # packet path optional
./venv/bin/python -I checks/08_large_degree.py 130 160            # about 4 minutes
./venv/bin/python -I checks/08_large_degree.py 200                # about 9 minutes
```

`run_all.sh` takes about 9 minutes on two cores; checks `05` and `06` account for nearly all of it. Each check prints a JSON summary ending in `"status": "PASS"` and exits non-zero on the first failed assertion. Random tests use fixed seeds, so outputs are reproducible apart from timings.

The packet path given to `run_all.sh` is used by `06_candidate_B.py` only, to compare B's stored certificate JSON with the recomputed values. Without it that comparison is skipped and everything else runs.

Environment used for the audit: Python 3.13.18, sympy 1.14.0, python-flint 0.9.0, mpmath 1.3.0, Linux, 2 cores.
