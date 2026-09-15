# Forall LeanEval

Accepted Lean proofs for the [LeanEval software-verification benchmark](https://lean-lang.org/eval/software-verification/), produced with Forall-Lean-Agent from [Astrio Labs](https://github.com/astrio-labs).

Both problems were accepted on September 7, 2026 under the leaderboard name **Forall (Astrio)**, using GPT-6 Astra. The proof files in this repository match the exact accepted submission commit.

| Problem | Obligations | Official result | Proof source |
| --- | --- | --- | --- |
| CoC strong normalization | 6 | Accepted | [Submission.lean](proofs/coc_strong_normalization/Submission.lean) and [supporting modules](proofs/coc_strong_normalization/Submission) |
| Real-closed-field quantifier elimination | 4 | Accepted | [Submission.lean](proofs/rcf_quantifier_elimination/Submission.lean) |

See the [official result record](https://github.com/leanprover/lean-eval-submissions/blob/main/results/nolanlwin.json), its saved [snapshot](accepted-results.json), and [production provenance](PROVENANCE.md).

## Get the proofs

```sh
git clone https://github.com/astrio-labs/forall-lean-eval.git
cd forall-lean-eval
```

The two workspaces are under `proofs/`. Each includes its benchmark statement, submitted proof, dependency lockfile, and Lean toolchain pin.

## Verify package integrity

Python 3.11 or newer is required for the package check.

```sh
python3 scripts/verify_package.py
```

This checks the proof and support-file digests, accepted-result identifiers, and package layout. It runs locally without downloading dependencies. The check verifies the released snapshot against the recorded digests and does not run the Lean kernel.

## Build and check a proof

Install [elan](https://github.com/leanprover/elan) and use the committed Lean 4.33.0 toolchain and dependency lockfiles. From either workspace, build the submitted proof and solution.

```sh
cd proofs/coc_strong_normalization
lake exe cache get
lake build Submission Solution
```

For the RCF proof, use `proofs/rcf_quantifier_elimination` instead.

To run the benchmark verification, install the pinned Linux verification tools following the [upstream setup instructions](https://github.com/leanprover/lean-eval/blob/6b4b87b672f5301f24983a12fda65dac608453ce/README.md#5-run-comparator-locally), then run this command in the workspace.

```sh
lake test
```

The benchmark check requires `comparator`, `landrun`, `lean4export`, and `nanoda_bin` on `PATH`. It checks the submitted declarations against the benchmark and replays them through Nanoda. Linux is required for the sandboxed verification. Dependency caches and proof builds can require substantial disk space and time.

The original placeholders in `Challenge.lean` define benchmark obligations. Completed proofs are in `Submission.lean` and `Submission/`.

## Accepted source and verification

The original accepted source commit is `c1a049be4d9d780b73b1a2552ebb764e67497f49`. Both official results use statement revision 1 and benchmark commit `6b4b87b672f5301f24983a12fda65dac608453ce`.

The packaged benchmark support files and dependency lockfiles match those at the official benchmark commit. [verification.json](verification.json) records the proof digests, original local checks, and official acceptance identifiers. The saved result snapshot retains the original submission metadata, including its private visibility at submission time.

## License and attribution

Released under the [Apache License 2.0](LICENSE). Benchmark files retain their original Lean FRO attribution. See [NOTICE](NOTICE) and the [upstream material record](third-party/README.md).
