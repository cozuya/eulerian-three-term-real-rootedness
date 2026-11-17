#!/usr/bin/env bash
# Re-run every audit check.  Usage:  ./run_all.sh [path-to-extracted-packet]
# The packet path is optional; it only enables the cross-check of B's supplied certificate JSON.
set -u
cd "$(dirname "$0")"
PY=${PY:-./venv/bin/python}
PACKET=${1:-}
mkdir -p outputs
for s in 00_selftest 01_eulerian_basics 02_residue_lemma 03_logderiv_lemma 04_central_identity 05_root_count 07_cross_checks; do
  echo "== $s"; "$PY" -I checks/$s.py > outputs/$s.txt 2>&1; echo "exit=$?"
done
echo "== 06_candidate_B"; "$PY" -I checks/06_candidate_B.py $PACKET > outputs/06_candidate_B.txt 2>&1; echo "exit=$?"
echo "== 08_large_degree (60 80 100)"; "$PY" -I checks/08_large_degree.py 60 80 100 > outputs/08_large_degree_part1.txt 2>&1; echo "exit=$?"
# slower spot checks (about 4 and 9 minutes on the audit machine):
#   "$PY" -I checks/08_large_degree.py 130 160 > outputs/08_large_degree_part2.txt
#   "$PY" -I checks/08_large_degree.py 200     > outputs/08_large_degree_part3.txt
grep -l '"status": "PASS"' outputs/0*.txt | wc -l
