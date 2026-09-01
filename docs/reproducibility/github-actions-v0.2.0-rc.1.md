# GitHub Actions reproducibility receipt for v0.2.0-rc.1

The historical artifact names `BeliUniversalAudit.log` below are preserved
verbatim. Current paper metadata identifies the paper as Beli 2020 and uses
`Beli2020` for canonical review entry points.

## Scope and exact revisions

Receipt finalized: 1 September 2026 (Asia/Shanghai).

This receipt records the public hosted-run evidence for release candidate
`v0.2.0-rc.1`.  The annotated tag object
`c061d8ac068a5437ac887848f4e8c5af6c7ea182` resolves to merge commit
`90511e852471ba68bbb375290668c456522b0f9c`.
The published prerelease is available at
<https://github.com/hzldew-git/BongTheory/releases/tag/v0.2.0-rc.1>.

The separate local Windows no-cache source rebuild was performed at code-and-
CI commit `5befe079dbf3569d1760b8e66bc52aef0de21745`.  Between that revision and
the tag, only six README, audit, and reproducibility documents changed.  All
Lean files, `lean-toolchain`, `lake-manifest.json`, `lakefile.toml`, and
workflow definitions are identical.  The local result is recorded in
[`clean-clone-5befe079.md`](clean-clone-5befe079.md).

Every hosted build below disabled the GitHub project cache and permitted the
official mathlib cache.  Ubuntu built the complete default target.  Windows
built the complete dependency closure of the five public audit modules so
that it remained within the hosted six-hour limit.  Both runner paths use
`LEAN_NUM_THREADS=4`.

## Pull-request and merge CI

The following **Lean CI** jobs completed successfully.  Each includes the
complete default build, namespace axiom audit, unfinished-proof scan,
final-public signature audit, and clean-generated-state check.

| Revision | Run | Job | UTC interval | Jobs | Job-log SHA-256 |
|---|---:|---:|---|---:|---|
| PR head `723e3ed108bf24b987cb6f668219d35029a9d517` | [`33460193962`](https://github.com/hzldew-git/BongTheory/actions/runs/33460193962) | `99708542221` | 2026-09-01 01:49:12--01:52:29 | 5,589 | `76E68180EF1C9B33EBC4AD77E82ACBACB18F4BC445917257487BED0745659DF4` |
| Tag target `90511e852471ba68bbb375290668c456522b0f9c` | [`33460465143`](https://github.com/hzldew-git/BongTheory/actions/runs/33460465143) | `99709328771` | 2026-09-01 01:53:34--02:00:35 | 5,589 | `3C3ACF8DF9E5952E47D273C578919992497F3D5291661DF5771441E322D58D0B` |
| Cross-platform workflow fix `d746c373d9f4f6e94e8591baaaa5c3753ecfcad1` | [`33470880164`](https://github.com/hzldew-git/BongTheory/actions/runs/33470880164) | `99740220035` | 2026-09-01 04:43:04--04:45:56 | 5,589 | `2794F9AC70AA65BFCA7BE75532D68242522B81B5BCB835599B8AEFFB9FB7BC31` |

## Initial tag run and transparent Ubuntu plumbing failure

The tag-triggered **Release reproducibility** run
[`33461392000`](https://github.com/hzldew-git/BongTheory/actions/runs/33461392000)
checked out tag target `90511e852471ba68bbb375290668c456522b0f9c`.
Its overall conclusion is `failure`, and that conclusion is retained rather
than hidden.

Ubuntu job `99712057136` ran from 2026-09-01 02:08:11 UTC to 04:40:48 UTC.
The complete default build succeeded with 5,589 jobs:

```text
Build completed successfully (5589 jobs).
```

The following PowerShell audit step then attempted to construct the Windows-
specific path `$env:USERPROFILE/.elan/bin/lake.exe`.  On the Ubuntu runner,
`USERPROFILE` was null, so `Join-Path` failed before any audit log was
created.  Artifact upload consequently failed for lack of files, and the
clean-worktree step was skipped.  This is classified as workflow plumbing
failure after a successful Lean build, not as a theorem or compilation
failure.  The complete failed job log has SHA-256
`384DAACD8B3274D29DDF2149A3C0675B8CC22338942D459C447B613ECFE74DFE`.

Commit `d746c373d9f4f6e94e8591baaaa5c3753ecfcad1` repaired the audit step by
resolving `lake` from `PATH` first and otherwise using `HOME`/`USERPROFILE`
with the platform-appropriate executable name.  Its ordinary CI passed as
recorded above.  The corrected manual Ubuntu run reads that workflow revision
from `main` but checks out the exact release tag.

## Successful Windows exact-tag result

The Windows half of initial run `33461392000`, job `99712056926`, ran from
2026-09-01 02:08:11 UTC to 07:21:42 UTC.  It built the complete dependency
closure of the five public audit modules, 4,970 Lake jobs, without a GitHub
project cache.  The build, all five audits, artifact upload, and exact-clean-
worktree check completed successfully.

The complete Windows job log has SHA-256
`AC8AAF0EF7796B9CFF2D61519DA15F30E10921F471EA35D4E37101811A6675CF`.
Artifact `audit-logs-windows-latest`, ID `9790181472`, has 12,732 bytes and
downloaded SHA-256
`FA07D68E8E82A274E09BFB18E21BA700F8DF7BDCAFE95A1430E3EC67CB61F9AF`.

| Audit log | Reports | Bytes | Lines | SHA-256 |
|---|---:|---:|---:|---|
| `FinalPublicTheoremAudit.log` | 23 | 13,942 | 164 | `CC00D61462D2508DCA0537CB4C591282EECC41DB5587320BB0106F78A8900358` |
| `Beli2006Audit.log` | 2 | 1,442 | 16 | `D57054DF3E470E22FCEFF60BCF7C0D536B1A11085151BE5F001C27403EA34D45` |
| `Beli2009Audit.log` | 65 | 8,563 | 104 | `D54F688AAB9E1B9361C7DAF1FD2D5A91C9DC7FE9A61A6435962A1528290512D3` |
| `Beli2019Audit.log` | 555 | 66,020 | 909 | `8508BFF962B91E2E8D66B7A19087D62881C5105313AAAB942E879298C9FE7E42` |
| `BeliUniversalAudit.log` | 30 | 19,785 | 238 | `F0095F8598C91F9671C088A3C828E36B922835D47D0439973866E28C0CF33EBD` |

These five logs are byte-for-byte identical to the corresponding logs from
the separate local Windows clean-clone source rebuild.

## Corrected Ubuntu exact-tag result

Manual **Release reproducibility** run
[`33470916396`](https://github.com/hzldew-git/BongTheory/actions/runs/33470916396),
job `99740328147`, used workflow revision
`d746c373d9f4f6e94e8591baaaa5c3753ecfcad1` and checked out
`v0.2.0-rc.1`.  It ran from 2026-09-01 04:43:40 UTC to 06:53:04 UTC.
The complete 5,589-job default build, all five audits, artifact upload, and
exact-clean-worktree check completed successfully.

The complete corrected Ubuntu job log has SHA-256
`F28BADB2DD67815D1B314D04D1C84F7B9B11D5AE7DB37AFBA2774E2DDDA2FF90`.
Artifact `audit-logs-ubuntu-latest`, ID `9789383630`, has 12,688 bytes and
downloaded SHA-256
`CA4DAE917F9667D803C7BEB6D9092621732F57F2BCA38F5429CB410A74D884E2`.

| Audit log | Reports | Bytes | Lines | SHA-256 |
|---|---:|---:|---:|---|
| `FinalPublicTheoremAudit.log` | 23 | 13,778 | 164 | `492093CCB6B01263DFE0C3C71BBB578D1DAA1AEF9A3FCC39F939A7D40BCFF9F2` |
| `Beli2006Audit.log` | 2 | 1,426 | 16 | `76DC4C59E0B297539EAC634BF3DC694C0227968E2C6B4F38AD066288617BBCA3` |
| `Beli2009Audit.log` | 65 | 8,459 | 104 | `5D01C84BECA74E47C91370D8E2A10967F94932CB3AD04E54C3365B2DA84BA7A4` |
| `Beli2019Audit.log` | 555 | 65,111 | 909 | `F0C6CA3711831C8D8F9E0A0BE82C07797F19C7A66C671EB1AE8966FDC164B410` |
| `BeliUniversalAudit.log` | 30 | 19,547 | 238 | `C161A472335CCED3FFE59DD413228D4DDDB2D47AE1B8F4388121A14C6BC98C68` |

For both successful platforms, every parsed report uses only `propext`,
`Classical.choice`, and `Quot.sound`.  The artifact logs contain no Lean
error, unknown declaration, or `sorryAx`.

## Uploaded release artifacts

After publication, the three prerelease assets were downloaded anonymously
from their public GitHub release URLs.  Public API sizes and downloaded sizes
agreed.

| Asset | Bytes | Downloaded SHA-256 |
|---|---:|---|
| `BongTheory-v0.2.0-rc.1-SHA256SUMS.txt` | 189 | `42F344849414195C7D7BC67656A5A4450C6BC762FCCAF49233BB1D7F61098EBC` |
| `BongTheory-v0.2.0-rc.1.bundle` | 5,898,139 | `1B54F6CDE242FFDC220B9EAF7F6CD006107299D9E05B9F7EC0669425A1C8755E` |
| `BongTheory-v0.2.0-rc.1.zip` | 6,604,518 | `71780B1AF750DED8E69B67208006CC5F3CBBC48AFC524BE67E7B147E04D3507D` |

`git bundle verify` reports a complete history containing only `HEAD`,
`refs/heads/main`, and annotated tag `refs/tags/v0.2.0-rc.1`; `HEAD` and
`main` resolve to the tag target, and the tag ref resolves to tag object
`c061d8ac068a5437ac887848f4e8c5af6c7ea182`.  The source ZIP contains 2,663
entries and no `.lake`, `.olean`, or Beli Relative-paper path.

## Interpretation and limit

These local and hosted runs establish technical reproducibility of the pinned
Lean artifacts within the recorded dependency and runner boundaries.  They do
not certify that the definitions, assumptions, quantifiers, normalizations,
index conventions, or boundary cases exactly match the paper.

In particular, the frozen paper's Theorem 3.1 prints coefficient `r_1`, while
direct substitution into Theorem 2.1 gives `2r_1`.  The formalization keeps
that discrepancy explicit.  The release therefore remains
`FORMALIZATION_COMPLETE_WITH_SOURCE_DISCREPANCY`, with semantic verdict
`PROVISIONAL_MATCH`, Grade B, pending independent human review.
