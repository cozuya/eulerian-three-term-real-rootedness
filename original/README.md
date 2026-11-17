# Informal proof material

This directory preserves, byte-for-byte, the informal proof, its independent audit and a
second, partial argument, all of which preceded the Lean formalization.
[MANIFEST.sha256](MANIFEST.sha256) gives each file's SHA-256 value; every value agrees with
the manifest inside the archive the file came from (the audit's own `SHA256SUMS` is such a
manifest) ([PROVENANCE.md](../PROVENANCE.md)). The
material is historical; it is not needed to rebuild or check the Lean theorems.

**Start with [coefficient-region/REPORT.md](coefficient-region/REPORT.md).** It states the
theorem, gives the complete argument, and records the exact computations. Its mathematics
uses LaTeX delimiters that GitHub may not render.

| Path | Contents |
| --- | --- |
| [coefficient-region/REPORT.md](coefficient-region/REPORT.md) | The theorem and its proof (§§1–6), relation to Athanasiadis's Example 3.3, verification record |
| [coefficient-region/research/transform/](coefficient-region/research/transform) | The full hybrid proof, a two-step interlacing proof, notes, identity and reduction checks |
| [coefficient-region/research/sturm/](coefficient-region/research/sturm) | Two adversarial reviews of the proof and their identity checks |
| [coefficient-region/research/search/](coefficient-region/research/search) | Exact sign certificates for the hybrid test points (`verify_hybrid_proof`), an adversarial review, and earlier screens and failed routes |
| [coefficient-region/FAILED_APPROACHES.md](coefficient-region/FAILED_APPROACHES.md) | Approaches that failed, with exact obstructions |
| [coefficient-region/SOURCES.md](coefficient-region/SOURCES.md) | Sources inspected and the scope of the novelty check |
| [audit/AUDIT.md](audit/AUDIT.md) | Independent audit: reconstruction of every decisive step, issues, comparison of the two arguments, computations performed |
| [audit/checks/](audit/checks) | The audit's own exact toolkit and checks, with recorded output in [audit/outputs/](audit/outputs) |
| [review-packet/candidate_B/](review-packet/candidate_B) | A second, partial argument: $n-1$ distinct negative roots for every $n\ge3$ when $c\le1+(b+1)^2/4$, a reduction of the full criterion to an unproved inequality, and finite certificates |

## What is and is not checked

Only the statements listed in the [README](../README.md) as *Formalized* are checked by Lean.
The informal claims beyond them (simple roots and negative roots) are not. The scripts check
exact identities, signs and root counts for bounded degrees and sampled parameters; they are
corroboration, not proofs.

The informal proof treats the case $b=0$, $n$ even by a limit $b\to0^+$; the Lean proof uses
a factor-$z$ sign count instead ([PROOF.md](../PROOF.md), §6). The audit's verdict on the
partial argument is that its stated theorem is valid and that its route to the full
criterion is incomplete, as that argument itself says.

Withheld from the source archives are the task statements and instructions given to the AI
assistants, and the review packet's duplicate copy of the main argument
([PROVENANCE.md](../PROVENANCE.md)). Some preserved files mention them; nothing preserved
depends on them.

## Reproducing the checks

Informal proof. Original environment: Python 3.12.14, SymPy 1.14.0. From
`coefficient-region/`:

```sh
python -m pip install -r requirements.txt
python verify_conventions.py
python research/transform/check_proof_identities.py
python research/sturm/verify_full_proof_identities.py
python research/search/verify_hybrid_proof.py
```

Audit. Original environment: Python 3.13.18, SymPy 1.14.0, python-flint 0.9.0, mpmath 1.3.0.
From `audit/`:

```sh
python3 -m venv venv
./venv/bin/python -m pip install -r requirements-audit.txt
./run_all.sh            # checks 00-08, about 9 minutes on two cores; rewrites outputs/
```

Partial argument. From `review-packet/`:

```sh
python -m pip install -r requirements.txt
python candidate_B/proof_route/check_identities.py
python candidate_B/eulerian_attempt/exact_reduction_checks.py
python candidate_B/counterexample_search/review_exact_reduction.py
python candidate_B/counterexample_search/one_step_counterexample.py
```

Several scripts write their output next to themselves or into `outputs/`, which changes the
preserved files; run them on a copy to keep the manifest valid. Runtime fields can differ.
