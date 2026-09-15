# Production provenance

## System and workflow

The official leaderboard credits **Forall (Astrio)**. This repository releases the accepted proofs produced with Forall-Lean-Agent using GPT-6 Astra at max reasoning effort for proof actors and fresh reviewers.

Proof development was iterative and used compiler feedback, persistent actor sessions, and fresh review sessions. Operator and assistant support included infrastructure recovery, checkpoint management, and strategic guidance. These results are not presented as a one-shot or fully unassisted evaluation.

The CoC development continued through multiple checkpoints and proves all six original obligations, including strong normalization and consistency. The final result is not restricted to a fixed number of universes. Historical milestone-audit comments in some supporting modules describe earlier checkpoints.

The Astra RCF attempt began from the pristine benchmark starter without seeding the earlier Sol proof. Two actor rounds were followed by a verification-only recovery with no proof changes. It proves all four original obligations without fixed degree or formula-depth restrictions. An optional reviewer safety-metadata diagnostic remained unfinished and is not counted as a passing check.

## Accepted source

Both official results identify the same original source commit.

```text
c1a049be4d9d780b73b1a2552ebb764e67497f49
```

The release copies all 233 CoC solver files and the single RCF solver file byte for byte from that commit. Publication changed documentation and package metadata without modifying those proofs.

| Problem | Submission ID | Accepted at UTC |
| --- | --- | --- |
| CoC strong normalization | `01a07975-2721-731f-bf03-3e8a0696bcc4` | 2026-09-07 02:14:38 |
| RCF quantifier elimination | `01a07976-d8b9-70af-9778-20e51195cca0` | 2026-09-07 02:09:39 |

[accepted-results.json](accepted-results.json) preserves the official records retrieved on September 15, 2026 from [leanprover/lean-eval-submissions](https://github.com/leanprover/lean-eval-submissions/blob/main/results/nolanlwin.json).

## Verification records

Local fresh review, Docker comparator, Nanoda, and Lean kernel checks passed before submission. The local checks used benchmark commit `242d5b0232f40bda70c54c6648fec64348c62c8b` and Lean 4.33.0. The official acceptance records identify benchmark commit `6b4b87b672f5301f24983a12fda65dac608453ce`.

The support files and dependency lockfiles in these two packaged workspaces were compared with the official benchmark commit and are identical. [verification.json](verification.json) retains the local proof digests and verification results alongside the official acceptance identifiers.

The package-integrity check does not rerun Lean or certify arbitrary later modifications. The public acceptance claims refer to the exact original submission recorded by LeanEval.
