# Upstream material

The fixed workspace files under `generated/` are copied without modification
from `leanprover/lean-eval` commit
`242d5b0232f40bda70c54c6648fec64348c62c8b`:

- `Challenge.lean`, `ChallengeDeps.lean`, `Solution.lean`, `WorkspaceTest.lean`;
- `README.md`, `config.json`, `holes.json`, `lakefile.toml`, `lean-toolchain`.

Each workspace's `lake-manifest.json` is copied without modification from that
commit's root dependency lockfile. `lean-eval-SECURITY.md` is copied from the
same commit's `SECURITY.md` for reference.

The upstream license text is preserved as [lean-eval-LICENSE](lean-eval-LICENSE).
Upstream copyright: 2026 Lean FRO, LLC. Existing references and attribution
remain in the benchmark files. The `Submission.lean` files replace the upstream
starter placeholders with the accepted Forall (Astrio) proof candidates;
`Submission/` contains the accepted solver helper files.

The packaged workspace support files and dependency lockfiles also match the
corresponding files at official acceptance benchmark commit
`6b4b87b672f5301f24983a12fda65dac608453ce`.

The upstream workspaces' `Submitter: Kim Morrison` field identifies the benchmark
problem contributor. The accepted proof submission is credited to Forall (Astrio),
submitted by `nolanlwin`.
