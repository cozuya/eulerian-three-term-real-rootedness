# Reproducing the verification

Everything needed is in this repository and its pinned dependencies (Mathlib and its locked
transitive packages). No files from any other repository are used.

## Requirements

- Linux x86_64, with Bash, Git, Python 3, curl, tar, zstd and coreutils. Without zstd,
  Python 3.14 or later can unpack the Lean archive instead.
- About 10 GB of free disk: about 2.5 GB for Lean, and the rest for the dependency
  checkouts and prebuilt Mathlib.
- About 4 GB of RAM for the build and the axiom audit; about 8 GB for the optional
  `leanchecker` replay.

Other platforms can install Lean 4.35.0 from [lean-toolchain](lean-toolchain), put it on
`PATH`, and run the same fetch and verification commands in Bash.

## Commands

```sh
git clone https://github.com/cozuya/eulerian-three-term-real-rootedness.git
cd eulerian-three-term-real-rootedness
bash scripts/install-lean.sh                  # checksum-pinned Lean 4.35.0 into .tools/
export PATH="$PWD/.tools/lean-4.35.0-linux/bin:$PATH"
bash scripts/fetch-deps.sh                    # locked Mathlib, prebuilt Mathlib
./verify.sh                                   # rebuild and statement/axiom audit
python3 scripts/check-package.py              # inventory, hashes, links, evidence
```

To add the standalone kernel replay:

```sh
VERIFY_LEANCHECKER=1 ./verify.sh
```

If Lean 4.35.0 is already installed elsewhere, skip the installer. Put its `bin` directory on
`PATH`, or set `LEAN_BIN_DIR` for `fetch-deps.sh` and `verify.sh`.

`fetch-deps.sh` runs `lake exe cache get` and then checks that `lake-manifest.json` is
unchanged and that every dependency is checked out, unmodified, at its pinned revision. No
`lake update` is needed. Mathlib and its dependencies come from the prebuilt cache; every
module of this project is compiled from source by `verify.sh`.

## What `verify.sh` does

1. It prints the Lean, Lake and Mathlib versions and checks them, and every locked
   dependency, against [TOOLCHAIN.json](TOOLCHAIN.json) and the lockfile.
2. It scans the 14 Lean files with [scripts/audit.py](scripts/audit.py) `sources`. Outside
   comments, the scan rejects `sorry`, `admit`, axiom declarations, `native_decide`,
   `unsafe`, `implemented_by`, `extern`, `csimp`, `opaque`, kernel-check options, instances,
   notation, macros and attributes other than `@[simp]` and `@[expose]`.
3. It checks [SOURCE_SHA256SUMS](SOURCE_SHA256SUMS) and the package inventory, including the
   preserved material in [original/](original/README.md).
4. It deletes this project's `.lake/build` and runs `lake build EulerianRegion`. The build
   must finish with no warnings or errors.
5. It runs `lake env lean --trust=0 Verification.lean`, which prints the types of the
   restated theorems, the definitions, and the axioms of 23 declarations.
6. It checks with `audit.py axioms` that each declaration depends on exactly `propext`,
   `Classical.choice` and `Quot.sound`. Any warning, error, `sorryAx` or other axiom fails
   the run.
7. With `VERIFY_LEANCHECKER=1`, it runs the toolchain's `leanchecker` on all project modules,
   and with `--fresh` on the full import closure of `EulerianRegion.MainTheorem`, including
   Mathlib, each with one worker thread.
8. It writes `.build/verification.log`, `.build/build.log`, `.build/kernel-check.log` and
   `.build/verification.json`, with the commit, source hashes, exit codes and timings.

The final lines of a successful transcript include `AXIOM_AUDIT=PASS` and
`VERIFY_EXIT_CODE=0`.

## Re-running the informal checks

The exact-arithmetic scripts of the informal proof and of the audit are described in
[original/README.md](original/README.md). They are corroboration only and are not part of
`verify.sh`.
