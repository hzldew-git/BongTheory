# Reproducing the formalization

## Frozen inputs

- Lean toolchain: `v4.32.1`, pinned by `lean-toolchain`.
- mathlib and transitive packages: pinned by `lake-manifest.json`.
- Formal proof-and-test baseline: commit
  `10e8c666bfda81dcac44332cd38f481d8d02e31a`.
- Audited release-candidate code and CI commit:
  `5befe079dbf3569d1760b8e66bc52aef0de21745`.
- Current release-candidate target: `v0.2.0-rc.1`.
- Supported build entry points: `Bong` and `BongTest`.

No paper PDF, generated proof file, environment variable, Mathematica
notebook, Sage session, or external solver is required for the Lean build.

## Clean-clone protocol

Run the following in a new directory, not in an existing development checkout:

```text
git clone <repository-url> BongTheory-clean
cd BongTheory-clean
git checkout <release-tag-or-full-commit>
lake exe cache get
lake build
lake env lean BongTest/FinalPublicTheoremAudit.lean
lake env lean BongTest/Beli2006Audit.lean
lake env lean BongTest/Beli2009Audit.lean
lake env lean BongTest/Beli2019Audit.lean
lake env lean BongTest/BeliUniversalAudit.lean
git status --porcelain
```

`lake exe cache get` is an optimization, not a trust assumption.  If the
binary cache is unavailable, let Lake build the pinned dependencies from
source.  On memory-constrained Windows hosts, use a process-local setting
before the build:

```powershell
$env:LEAN_NUM_THREADS = '4'
lake --log-level=error build
```

The audited `v0.2.0-rc.1` candidate run used that setting.  A separate clone
with no pre-existing `.lake` directory completed from source with 5,597 jobs
and did not copy any project build artifact from the development checkout.

Success requires all commands to exit with status zero and the last command to
produce no output.  The cold clean-clone graph contained 5,597 Lake jobs; the
already-populated development worktree's default graph contained 5,589.  The
eight additional cold-start tool/dependency jobs are not source changes.  Lint
warnings do not invalidate a successful kernel build; build errors do.

`FinalPublicTheoremAudit.lean` prints the elaborated public signatures and
their transitive axiom sets. The expected project-independent axiom set is:

```text
propext
Classical.choice
Quot.sound
```

The GitHub workflows repeat this protocol from a fresh runner. The local
clean-clone receipt records the exact operating system, tool versions, commit,
commands, exit codes, and final worktree status.

The current local receipt is
[`docs/reproducibility/clean-clone-5befe079.md`](docs/reproducibility/clean-clone-5befe079.md).

## Hosted exact-revision run

To repeat the protocol on GitHub-hosted infrastructure, open **Actions →
Release reproducibility → Run workflow**.  Select the workflow from `main`,
enter the release tag or full commit in `checkout_ref`, and choose `both`,
`ubuntu-latest`, or `windows-latest` as the runner selection.  The workflow
definition is read from `main`, but its checkout step builds the exact value of
`checkout_ref`.  Tag pushes continue to run both supported hosted operating
systems automatically.

Each hosted job has a 360-minute limit, uploads the five theorem-audit logs,
and rejects a build that leaves the checked worktree dirty.  Ubuntu builds the
complete default target.  To stay within the hosted Windows six-hour hard
limit, Windows builds the complete dependency closure of the five public
audit modules (4,970 Lake jobs) and then executes those modules.  This is not
substituted for the separate full local Windows source rebuild; both hosted
jobs continue to disable the GitHub project cache.

The exact-tag `v0.2.0-rc.1` run history, log hashes, and artifact hashes will be
recorded after its Ubuntu and Windows jobs finish.  The prior four-paper
release's historical record is
[`docs/reproducibility/github-actions-v0.1.0-rc.1.md`](docs/reproducibility/github-actions-v0.1.0-rc.1.md).

## Failure reporting

Open an issue containing the full commit, operating system, `lean --version`,
`lake --version`, the failing command, and the first complete error block.
Do not report only a screenshot or a truncated final line.
