#!/usr/bin/env bash
# Rebuild the whole Lean project from source and audit the exact statements and axioms.
# Requires the pinned Lean on PATH (or LEAN_BIN_DIR) and fetched dependencies; see REPRODUCE.md.
# Optional: VERIFY_LEANCHECKER=1 also replays the proofs with the toolchain's leanchecker.
set -uo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
if [[ -n ${LEAN_BIN_DIR:-} ]]; then export PATH="$LEAN_BIN_DIR:$PATH"; fi
for program in lean lake python3 sha256sum git; do
  command -v "$program" >/dev/null || { printf 'Missing prerequisite: %s\n' "$program" >&2; exit 2; }
done
leanchecker=${VERIFY_LEANCHECKER:-0}
[[ $leanchecker == 0 || $leanchecker == 1 ]] || { printf 'VERIFY_LEANCHECKER must be 0 or 1\n' >&2; exit 2; }
mkdir -p .build
log=.build/verification.log
started=$(date -u '+%Y-%m-%dT%H:%M:%SZ')
run() {
  printf '\n$'
  printf ' %q' "$@"
  printf '\n'
  local start=$SECONDS
  "$@"
  local code=$?
  printf 'EXIT_CODE=%s WALL_SECONDS=%s\n' "$code" "$((SECONDS - start))"
  return "$code"
}
run_capture() {
  local capture=$1
  shift
  printf '\n$'
  printf ' %q' "$@"
  printf '  # output also saved to %s\n' "$capture"
  local start=$SECONDS
  "$@" 2>&1 | tee "$capture"
  local codes=("${PIPESTATUS[@]}")
  local code=${codes[0]}
  if (( codes[1] != 0 )); then code=${codes[1]}; fi
  printf 'EXIT_CODE=%s WALL_SECONDS=%s\n' "$code" "$((SECONDS - start))"
  return "$code"
}
verify_main() {
  run date -u '+%Y-%m-%dT%H:%M:%SZ' || return $?
  run lean --version || return $?
  run lean --githash || return $?
  run lake --version || return $?
  run cat lean-toolchain || return $?
  run git -C .lake/packages/mathlib rev-parse HEAD || return $?
  run python3 scripts/audit.py pins || return $?
  run python3 scripts/audit.py sources || return $?
  run python3 scripts/check-package.py --sources-only || return $?
  run sha256sum --check SOURCE_SHA256SUMS || return $?
  run python3 scripts/audit.py hashes || return $?
  # Remove this project's build outputs only; dependency caches stay in .lake/packages.
  run rm -rf .lake/build || return $?
  run_capture .build/build.log lake build EulerianRegion || return $?
  run python3 scripts/audit.py build .build/build.log || return $?
  run_capture .build/kernel-check.log lake env lean --trust=0 Verification.lean || return $?
  run python3 scripts/audit.py axioms .build/kernel-check.log || return $?
  if [[ $leanchecker == 1 ]]; then
    # One runtime worker keeps the checker's memory use down.
    run env LEAN_NUM_THREADS=1 lake env leanchecker --verbose EulerianRegion || return $?
    run env LEAN_NUM_THREADS=1 lake env leanchecker --verbose --fresh EulerianRegion.MainTheorem \
      || return $?
  fi
  run date -u '+%Y-%m-%dT%H:%M:%SZ' || return $?
  printf '\nFULL_REBUILD=PASS\nWARNING_FREE_BUILD=PASS\nREAL_ROOTED_IFF=PASS\nSTRONG_FORM=PASS\n'
  printf 'NECESSITY_AT_DEGREE_THREE=PASS\nNON_VACUOUS_HYPOTHESIS=PASS\nAXIOM_AUDIT=PASS\n'
  if [[ $leanchecker == 1 ]]; then printf 'LEANCHECKER_REPLAY=PASS\n'; fi
  printf 'TRUST_MODEL=kernel-only (propext, Classical.choice, Quot.sound)\n'
}
verify_main 2>&1 | tee "$log"
codes=("${PIPESTATUS[@]}")
code=${codes[0]}
if (( codes[1] != 0 )); then code=${codes[1]}; fi
finished=$(date -u '+%Y-%m-%dT%H:%M:%SZ')
run python3 scripts/audit.py record "$code" "$started" "$finished" "$leanchecker" 2>&1 | tee -a "$log"
record_codes=("${PIPESTATUS[@]}")
if (( record_codes[0] != 0 )); then code=${record_codes[0]}; fi
if (( record_codes[1] != 0 )); then code=${record_codes[1]}; fi
printf '\nVERIFY_EXIT_CODE=%s\n' "$code" | tee -a "$log"
exit "$code"
