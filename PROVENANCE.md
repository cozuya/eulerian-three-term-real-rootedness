# Provenance

**Chris Ozols, with AI-assisted proof development and formalization.** Chris directed the
work and its verification.

- **Informal proof, computations and literature check:** AI assistants produced these
  ([original/coefficient-region/](original/coefficient-region/REPORT.md)), together with a
  second, partial argument ([original/review-packet/](original/review-packet/candidate_B/ARGUMENT.md)).
  No exact model identity is asserted for that work.
- **Independent audit:** Anthropic's Claude audited both arguments and reconstructed every
  decisive step before the formalization ([original/audit/](original/audit/README.md)).
- **Lean formalization:** Anthropic's Claude (Claude Opus 5.5, in Claude Code) wrote the Lean
  proof in [EulerianRegion/](EulerianRegion). OpenAI's Codex completed the final step:
  it narrowed two imports so that the standalone kernel replay fits in memory, ran the
  clean rebuild and replays, and wrote the development repository's verification report.
- **This package:** Claude (Claude Opus 5.5, in Claude Code) wrote
  [Verification.lean](Verification.lean), the scripts and the documentation.

Nobody wrote the Lean proofs by hand. Chris Ozols is listed as author in
[CITATION.cff](CITATION.cff) as the person responsible for the work and the repository.

## Timeline

| Date (UTC) | Event | Record and its limits |
| --- | --- | --- |
| 2026-11-14 | Informal proof and exact computations ([REPORT.md](original/coefficient-region/REPORT.md)) | Date written in the record ("Research attempt dated November 14, 2026"); not an authenticated timestamp |
| 2026-11-14 | Independent audit of the informal proof and of the partial argument ([AUDIT.md](original/audit/AUDIT.md)) | Date written in the audit; not an authenticated timestamp |
| 2026-11-16, 02:37–07:43 | Lean formalization in a private local development repository: ten batches, each checked by a full Lean build and an automated four-model code review | Private local Git history; commit dates are editable metadata |
| 2026-11-16, until 23:51 | Final batch (import narrowing, clean rebuild, `leanchecker` replays, report), commit `9381cdc`, reviewed by the same panel; exact-commit rerun of the full suite | Private local Git history and run records |
| 2026-11-17 | This package assembled from development commit `9381cdc`; fresh verification run | [evidence/](evidence/verification.json) in this repository |
| Not yet | First public availability | — |

Git commit dates are editable metadata, and hashes identify bytes. Neither proves
mathematical truth, an authenticated creation date, or discovery priority.

## The Lean sources

The files in [EulerianRegion/](EulerianRegion), `EulerianRegion.lean`, `lakefile.toml`,
`lake-manifest.json` and `lean-toolchain` are byte-identical to development commit
`9381cdc8ec64363d16b312573fea7ee8f677cde1`. [Verification.lean](Verification.lean) and the
[scripts](scripts) were written for this package. The development repository's
`Verify/Audit.lean` and `Verify/Consumer.lean` are superseded by `Verification.lean`, which
restates the same results for any sequence satisfying the recurrence, includes the same
boundary and outside examples, and prints the same axiom reports. (The old audit file used a
custom command, which this package's source scan does not allow.)

The formalization followed the informal proof and the audit's reconstruction, with one
recorded departure: the case $b=0$, $n$ even uses a factor-$z$ sign count instead of a limit
([PROOF.md](PROOF.md), §6).

During development every batch was reviewed by an automated panel of four language models
(two Claude and two OpenAI models) in addition to the Lean build. The reports found no
defects in the proofs; their documentation notes were fixed. These reviews are process
records, not evidence of correctness: correctness rests on the Lean kernel check.

## The informal proof material

[original/](original/README.md) preserves, byte-for-byte, three groups of files from the
input bundle of the formalization:

- the informal proof and its research record, from the archive
  `eulerian-with-solver-seed.zip`
  (SHA-256 `3ed30906cc5268f470a927fac19231e8f0755192fb0f3e3a4bfc4591af395bb2`);
- the independent audit, the whole of `eulerian-audit-handoff.zip`
  (`e51ec1ecbef37f2332f1f8d87e7b0cc50b913f61b9b3d76347728db9295d5690`);
- the partial argument, from the review packet `eulerian-cross-vendor-review.zip`
  (`546fb0ce23613ee2a02ac87a56d74400e6ea91aecdd93094d005d846d5897a2e`).

[original/MANIFEST.sha256](original/MANIFEST.sha256) lists every preserved file. Each value
agrees with the manifest inside its source archive (the audit's `SHA256SUMS` is itself one
of those manifests). Withheld are the task statements and
instructions given to the AI assistants (the solver seed, the problem statement, the
review packet's reviewer instructions and problem file, and the formalization assignment).
The review packet's copy of the main argument is also omitted, because it repeats
§§1–6 of the included report with the same check scripts. None of the withheld files is needed
to read or check anything here.

The informal material claims more than is formalized: simple roots and negative roots.
Those claims are not checked by Lean. Its check scripts are finite-range corroboration, not
proofs.

## Verification evidence

The package uses Lean **4.35.0** at `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` and Mathlib
**v4.35.0** at `56a005855ea17e0b0958f73ec801ae140b0a1679`. [TOOLCHAIN.json](TOOLCHAIN.json)
and [lake-manifest.json](lake-manifest.json) record every pin.
[SOURCE_SHA256SUMS](SOURCE_SHA256SUMS) identifies every file that can affect verification,
plus the preserved material.

Evidence files:

- [verification report](evidence/verification.json)
- [transcript](evidence/verification.log)
- [build log](evidence/build.log)
- [theorem types and axioms](evidence/kernel-check.log)

These are fresh checks of the sources in this package. They can be repeated with
`./verify.sh`.
