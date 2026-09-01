# Clean-clone source-rebuild receipt for Beli 2020

This historical `v0.2.0-rc.1` receipt retains the then-current
`BeliUniversalAudit` command and log names. Current paper metadata and review
entry points use the canonical year-based name `Beli2020`.

## Result

Local classification:
`REPRODUCIBLE_WITH_DOCUMENTED_EXTERNAL_DEPENDENCIES`.

The complete `Bong` and `BongTest` default target built successfully from a
separate GitHub clone of committed revision
`5befe079dbf3569d1760b8e66bc52aef0de21745`.  All five focused audit commands
then exited zero, the paper-specific trust-boundary scan returned no matches,
and the final Git worktree was clean.

This receipt establishes local committed-source reproducibility for the code
included in release candidate `v0.2.0-rc.1`.  It is project-author/AI-run
evidence, not an independent human semantic or reproducibility sign-off.

## Host and pinned inputs

- Audit date: 1 September 2026.
- Host: Microsoft Windows 11 Home Chinese edition, version `10.0.26200`,
  build `26200`, x86-64.
- CPU: Intel Core Ultra 9 285H, 16 logical processors.
- Physical memory: 31.43 GiB.
- Lean: 4.32.1, commit
  `f054605aea4b840552cca2e725580bffd1e1b704`.
- Lake: `5.0.0-src+f054605`.
- Git: `2.53.0.windows.3`.
- Toolchain file: `leanprover/lean4:v4.32.1`.
- Audited code commit:
  `5befe079dbf3569d1760b8e66bc52aef0de21745`.
- Branch at clone time: `release/beli-universal-v0.2.0-rc.1`.

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

No paper PDF, TeX source, Mathematica notebook, Sage session, or external
solver was needed to compile the project.

## Clone and cache boundary

The audit clone was created with:

```powershell
git clone --no-local --single-branch `
  --branch release/beli-universal-v0.2.0-rc.1 `
  https://github.com/hzldew-git/BongTheory.git `
  D:\AI-Workspace\Builds\BongTheory-clean-5befe079
```

Its checked `HEAD` exactly matched the audited code commit, `git status
--porcelain` produced no output, and no `.lake` directory existed before the
build.  The command `lake exe cache get` was not invoked.  Lake resolved the
manifest-pinned packages and compiled the required dependency and project
targets from source.  No `.olean`, project `.lake`, or other build artifact
was copied or linked from the development checkout.

## Complete source build

The build used a process-local Windows concurrency bound:

```powershell
$env:LEAN_NUM_THREADS = '4'
lake --log-level=error build
```

It exited zero after `17,213.742` seconds, approximately 4 hours 46 minutes
54 seconds, and ended with:

```text
Build completed successfully (5597 jobs).
```

The cold-start graph included eight more tool/dependency jobs than the
already-populated development worktree's 5,589-job default graph.  Both counts
come directly from Lake.  The difference is not a source or theorem change.

Previously resource-sensitive modules all have successful records in this
run, including:

- `Bong.Lattice.OrthogonalDecompositionPrefixCarrier`;
- `Bong.Lattice.OmearaOddQuaternaryModels`;
- `Bong.Lattice.JordanAmalgamation`;
- `Bong.Lattice.Omeara9328GapTwoNontrigger`;
- `Bong.Lattice.Omeara9328EqualOrderTwistAbsorption`.

The Universal-paper chain itself built through
`Bong.Bong.BeliUniversalComplete`, followed by the public `Bong` entry point,
`BongTest.FinalPublicTheoremAudit`, and `BongTest.BeliUniversalAudit`.

## Focused audit results

| Command | Exit | Time | Axiom reports |
|---|---:|---:|---:|
| `lake env lean BongTest/FinalPublicTheoremAudit.lean` | 0 | 13.521 s | 23 |
| `lake env lean BongTest/Beli2006Audit.lean` | 0 | 13.099 s | 2 |
| `lake env lean BongTest/Beli2009Audit.lean` | 0 | 13.362 s | 65 |
| `lake env lean BongTest/Beli2019Audit.lean` | 0 | 12.817 s | 555 |
| `lake env lean BongTest/BeliUniversalAudit.lean` | 0 | 13.499 s | 30 |

Every reported theorem depended only on `propext`, `Classical.choice`, and
`Quot.sound`.  The audit logs contained no `sorryAx`, unknown declaration, or
Lean error.

The Universal-source trust scan used:

```powershell
rg -n `
  -g 'BeliUniversal*.lean' `
  -g 'GoodBONGScalarAgreementClassification.lean' `
  -g 'OMaximal*.lean' `
  -g 'Universality.lean' `
  -g 'BeliUniversalAudit.lean' `
  '\bsorry\b|\badmit\b|\bsorryAx\b|^\s*axiom\b|^\s*opaque\b|^\s*unsafe\b|^\s*extern\b|implemented_by|native_decide|run_tac' `
  Bong BongTest
```

It returned no matches and the expected `rg` exit code `1`.

## Log identities

The logs are retained outside the Git repository.  Their SHA-256 values are:

| Log | Bytes | Lines | SHA-256 |
|---|---:|---:|---|
| `lake-build.log` | 351,966 | 5,573 | `C9122C20CCCA5DA61DD38754523F0A992F4D3FD779BBCEBE73912D4592E97198` |
| `FinalPublicTheoremAudit.log` | 13,942 | 164 | `CC00D61462D2508DCA0537CB4C591282EECC41DB5587320BB0106F78A8900358` |
| `Beli2006Audit.log` | 1,442 | 16 | `D57054DF3E470E22FCEFF60BCF7C0D536B1A11085151BE5F001C27403EA34D45` |
| `Beli2009Audit.log` | 8,563 | 104 | `D54F688AAB9E1B9361C7DAF1FD2D5A91C9DC7FE9A61A6435962A1528290512D3` |
| `Beli2019Audit.log` | 66,020 | 909 | `8508BFF962B91E2E8D66B7A19087D62881C5105313AAAB942E879298C9FE7E42` |
| `BeliUniversalAudit.log` | 19,785 | 238 | `F0095F8598C91F9671C088A3C828E36B922835D47D0439973866E28C0CF33EBD` |

## Clean state and remaining boundary

After all audit commands:

```text
git rev-parse HEAD
5befe079dbf3569d1760b8e66bc52aef0de21745

git status --porcelain
<no output>
```

This technical receipt does not resolve the documented `r_1` versus `2r_1`
coefficient discrepancy in the frozen paper's Theorem 3.1, and it does not
replace independent source-to-Lean comparison.  Exact-tag Ubuntu and Windows
evidence is recorded separately in
[`github-actions-v0.2.0-rc.1.md`](github-actions-v0.2.0-rc.1.md).
