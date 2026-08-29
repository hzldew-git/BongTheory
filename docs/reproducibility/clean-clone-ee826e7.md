# Clean-clone source-rebuild receipt

## Result

Local classification:
`REPRODUCIBLE_WITH_DOCUMENTED_EXTERNAL_DEPENDENCIES`.

The complete `Bong` and `BongTest` default target built successfully from a
separate clone of committed revision
`ee826e7a8e67dda053563c01e027b2379bd68e6f`.  All four focused audit commands
then exited zero, and the final Git worktree was clean.

This receipt establishes local committed-source reproducibility.  Subsequent
public hosted-run evidence is recorded separately in
`github-actions-v0.1.0-rc.1.md`.  Neither receipt records an independent human
semantic sign-off.

## Host and pinned inputs

- Audit date: 29 August 2026.
- Host: Microsoft Windows 11 Home, version `10.0.26200`, build `26200`, x86-64.
- Lean: 4.32.1, commit
  `f054605aea4b840552cca2e725580bffd1e1b704`.
- Lake: `5.0.0-src+f054605`.
- Toolchain file: `leanprover/lean4:v4.32.1`.
- Git commit:
  `ee826e7a8e67dda053563c01e027b2379bd68e6f`.
- Branch at clone time: `main`.

The manifest revisions were:

| Package | Revision |
|---|---|
| mathlib | `520045ab14e26149ee970e2e617ca04b09bde5d6` |
| plausible | `e12c1910fe855cbfc38803cd4e55543906d5fa62` |
| LeanSearchClient | `c5d5b8fe6e5158def25cd28eb94e4141ad97c843` |
| importGraph | `7e9612bf0b9ee66db3cb5b9988a35afc706f5a12` |
| proofwidgets | `6e311e2a844da9b2cc3971187df2fe0066947b93` |
| aesop | `a7dbf0c63b694e47f425f3dcddbc0e178bb432d3` |
| Qq | `38d591e778f100aec9762bb582f9c7f55f50e9dc` |
| batteries | `023ce7d62a0531e22a5331e20b587817a80d49ff` |
| Cli | `88679d088c9720c27ebdf2ba4dafe17341747f94` |

No paper PDF or TeX source was needed to compile the project.

## Clone and cache boundary

The audit clone was created with `git clone --no-local --branch main` in
`D:\AI-Workspace\Builds\BongTheory-clean-ee826e7`.  Its checked `HEAD` exactly
matched the full commit above, and no `.lake` directory existed before the
dependency step.

The first package-fetch attempt was interrupted by a GitHub connection reset.
A retry cloned every package at its manifest revision.  The official mathlib
binary cache returned HTTP 404 responses for the requested artifacts, so it
was not usable for this toolchain snapshot.  No `.olean` or other project
artifact was copied from the development checkout.

## Source build and Windows concurrency

An initial source-build attempt allowed too many simultaneous Lean processes.
It progressed through thousands of jobs but eventually produced a Windows
access violation, a missing-read error for a concurrently generated mathlib
`.olean`, and `std::bad_alloc`.  These were platform resource failures, not
Lean theorem errors.

The same clean clone was then retried with:

```powershell
$env:LEAN_NUM_THREADS = '4'
lake --log-level=error build
```

The retry retained only artifacts already generated from source in this clean
clone.  It introduced no external project cache and made no source change.
It ran from 02:39:58 to 05:06:01 Asia/Shanghai, approximately 2 hours 26
minutes, and ended with:

```text
Build completed successfully (5555 jobs).
```

The modules that failed in the high-concurrency attempt all have successful
records in the retry log, including:

- `Bong.Lattice.OrthogonalDecompositionPrefixCarrier`;
- `Bong.Lattice.OmearaOddQuaternaryModels`;
- `Bong.Lattice.JordanAmalgamation`.

## Focused audit results

| Command | Exit | Time | Axiom reports |
|---|---:|---:|---:|
| `lake env lean BongTest/FinalPublicTheoremAudit.lean` | 0 | 16.13 s | 18 |
| `lake env lean BongTest/Beli2006Audit.lean` | 0 | 15.13 s | 2 |
| `lake env lean BongTest/Beli2009Audit.lean` | 0 | 15.42 s | 65 |
| `lake env lean BongTest/Beli2019Audit.lean` | 0 | 15.25 s | 555 |

Every final public theorem report used only `propext`, `Classical.choice`, and
`Quot.sound`.  The four audit logs contained no `sorryAx`, unknown declaration,
Lean error, or placeholder marker.

## Log identities

The audit-host logs were stored outside the Git repository.  Their SHA-256
values are:

| Log | Bytes | Lines | SHA-256 |
|---|---:|---:|---|
| `clean-build-retry.log` | 121,387 | 1,886 | `B4E03267EBEE275F9401EDE8FF863E58E43DBC69F26048A71927787FF76077CB` |
| `FinalPublicTheoremAudit.log` | 10,300 | 117 | `7D4B4EE1117AC9E2BEBC1D42BCF4F0033859B1F471DA45B64769B627B536734B` |
| `Beli2006Audit.log` | 1,442 | 16 | `D57054DF3E470E22FCEFF60BCF7C0D536B1A11085151BE5F001C27403EA34D45` |
| `Beli2009Audit.log` | 8,563 | 104 | `D54F688AAB9E1B9361C7DAF1FD2D5A91C9DC7FE9A61A6435962A1528290512D3` |
| `Beli2019Audit.log` | 66,020 | 909 | `8508BFF962B91E2E8D66B7A19087D62881C5105313AAAB942E879298C9FE7E42` |

## Clean-state check and remaining boundary

After all audit commands:

```text
git rev-parse HEAD
ee826e7a8e67dda053563c01e027b2379bd68e6f

git status --porcelain
<no output>
```

The subsequent exact-tag Ubuntu full build and Windows build/audit evidence,
including downloaded log and artifact hashes, is recorded in
`github-actions-v0.1.0-rc.1.md`.  Independent mathematical and Lean review
signatures remain intentionally blank in
`docs/audit/IndependentReviewSignoff.md`.
