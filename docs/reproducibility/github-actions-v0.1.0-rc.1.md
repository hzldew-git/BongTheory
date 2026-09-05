# GitHub Actions reproducibility receipt for v0.1.0-rc.1

## Scope and exact revisions

Receipt finalized: 30 August 2026 (Asia/Shanghai).

This receipt records the public hosted-run evidence for release candidate
`v0.1.0-rc.1`.  The annotated tag resolves to
`3840b0fabc1142cd55c7b132a62174e732759692`.  The tag changes documentation
only after the locally audited code-and-CI commit
`ee826e7a8e67dda053563c01e027b2379bd68e6f`; the Lean sources,
`lean-toolchain`, `lake-manifest.json`, and workflow files are identical at
those two revisions.

Later commits adjusted only the hosted workflow and reproducibility
documentation:

- `5f7a95d3fe8d4c5f76f49e5992d497a8ecfa055a` increased the ordinary CI
  timeout from 120 to 180 minutes;
- `0c3cd2d73dc25c396e997412b282afe2f4f6a460` added exact-ref manual release
  reruns and a 300-minute release-job limit;
- `4fc27c49f85ee54202f3da1799da3fc67d45d5f4` set process-local
  `LEAN_NUM_THREADS=4` and raised the release-job limit to GitHub's
  360-minute hosted maximum;
- `2eedad46979a9a8c7d6e33db64098eb6ca693ee7` fixed the Windows Elan/Lake
  path and limited the hosted Windows build to the complete dependency
  closure of the four public audit modules.

The workflow definition is read from `main`, but every manual release job
checks out the supplied `checkout_ref`.  The successful/retried jobs below
therefore distinguish the workflow revision from the exact Lean revision
being reproduced.

## Ubuntu exact-tag result

The tag-triggered **Release reproducibility** run
[`33212303098`](https://github.com/hzldew-git/BongTheory/actions/runs/33212303098)
checked out `3840b0fabc1142cd55c7b132a62174e732759692`.  Its Ubuntu job
`98988114873` ran from 28 August 2026 21:22:58 UTC to 23:13:10 UTC and
completed successfully.  The API records success for checkout, the complete
build without a GitHub project cache, all four paper-specific audits, artifact
upload, and the exact-clean-worktree check.

The complete Ubuntu job log has SHA-256
`4A8456547A35E2B2E5E7EF783026B1CF3BE3B3DD9B4555E1BAD4E412AA5051E4`.
The downloaded `audit-logs-ubuntu-latest.zip` artifact has SHA-256
`C41F845BA7BBD0087B7AADB1BA8828072A1D71A3B166791277B6FFF15B0E0712`.

| Audit log | Axiom reports | SHA-256 |
|---|---:|---|
| `FinalPublicTheoremAudit.log` | 18 | `E0015BCC90A5884026D7FA9728AE67685ADF2EB3775A208FB9DDA6F427C0B176` |
| `Beli2006Audit.log` | 2 | `76DC4C59E0B297539EAC634BF3DC694C0227968E2C6B4F38AD066288617BBCA3` |
| `Beli2009Audit.log` | 65 | `5D01C84BECA74E47C91370D8E2A10967F94932CB3AD04E54C3365B2DA84BA7A4` |
| `Beli2019Audit.log` | 555 | `F0C6CA3711831C8D8F9E0A0BE82C07797F19C7A66C671EB1AE8966FDC164B410` |

The artifact logs contain no Lean error, unknown declaration, `sorryAx`, or
project axiom.  The final-public reports depend only on `propext`,
`Classical.choice`, and `Quot.sound`.

## Windows exact-tag result

Exact-tag run
[`33240324779`](https://github.com/hzldew-git/BongTheory/actions/runs/33240324779)
provides public evidence that a hosted Windows runner completed the entire
5,555-job default source build without a GitHub project cache.  The build ran
from 29 August 2026 07:13:22 UTC to 13:00:24 UTC and ended with
`Build completed successfully (5555 jobs).`

The run's overall conclusion is nevertheless `failure`: the following
PowerShell audit step could not find `lake.exe` on `PATH`, although
`lean-action` had installed it under the runner user's `.elan/bin` directory.
No audit log was produced, the artifact upload consequently found no file,
and the clean-worktree step was skipped.  The complete job-log SHA-256 is
`BE05D619FE251CE7BAB96F1A888094B09312DA3689946010438729330C63ABD4`.
This is classified as workflow plumbing failure after a successful Lean
build, not as a successful audit job and not as a theorem failure.

Corrected exact-tag run
[`33254045519`](https://github.com/hzldew-git/BongTheory/actions/runs/33254045519),
job `99104572266`, used workflow revision
`2eedad46979a9a8c7d6e33db64098eb6ca693ee7` and checked out tag target
`3840b0fabc1142cd55c7b132a62174e732759692`.  It retained
`LEAN_NUM_THREADS=4`, disabled the GitHub project cache, and built the complete
dependency closure of the four public audit modules: 4,935 Lake jobs.  The
build ran from 29 August 2026 13:03:46 UTC to 18:05:23 UTC and completed
successfully.  The four audits, artifact upload, and exact-clean-worktree
check then all completed successfully; the job ended at 18:06:40 UTC.

The corrected job log has SHA-256
`68918256451912DF0732A0DADE3F4E3762E234F51CD803AC1E5DDB3EA3A46420`.
The downloaded `audit-logs-windows-latest.zip` artifact has SHA-256
`5BFACBD59572210BA380090E9E03A4570B89B905CEE6C9A9791553CEDAD268B3`.

| Audit log | Axiom reports | SHA-256 |
|---|---:|---|
| `FinalPublicTheoremAudit.log` | 18 | `7D4B4EE1117AC9E2BEBC1D42BCF4F0033859B1F471DA45B64769B627B536734B` |
| `Beli2006Audit.log` | 2 | `D57054DF3E470E22FCEFF60BCF7C0D536B1A11085151BE5F001C27403EA34D45` |
| `Beli2009Audit.log` | 65 | `D54F688AAB9E1B9361C7DAF1FD2D5A91C9DC7FE9A61A6435962A1528290512D3` |
| `Beli2019Audit.log` | 555 | `8508BFF962B91E2E8D66B7A19087D62881C5105313AAAB942E879298C9FE7E42` |

Every parsed axiom report uses only `propext`, `Classical.choice`, and
`Quot.sound`; no Lean error, nonzero command exit, `sorryAx`, or unknown
declaration occurs.  These four Windows artifact hashes are byte-for-byte
identical to the corresponding logs from the earlier separate local
clean-clone execution recorded in `clean-clone-ee826e7.md`.

The separate local Windows no-project-cache source rebuild remains
recorded in `clean-clone-ee826e7.md`.  Hosted evidence is reported separately
because GitHub-hosted Windows runners have a hard six-hour job limit.

## Main-branch CI results

Correction recorded on 5 September 2026: the pinned Lean action does not
implement the configured `axiom-audit` inputs. These historical jobs do not
certify an enforcing namespace-wide axiom gate. Their build results and
individually recorded axiom reports remain distinct evidence. See the
[deployment correction](../audit/HePaperDeploymentCheckpoint-20260905.md).

The following public **Lean CI** jobs completed successfully, including the
complete build, unfinished-proof scan, final-public signature reports and
clean-generated-state check:

| Revision | Run | Job | UTC interval | Job-log SHA-256 |
|---|---:|---:|---|---|
| `5f7a95d` | [`33220368631`](https://github.com/hzldew-git/BongTheory/actions/runs/33220368631) | `99012939158` | 2026-08-28 23:25:16--2026-08-29 02:09:12 | `57194E058EDB36F096526F21FB52FB14FDF1B6A8B73C1AC1DC35C1760CDDC6BA` |
| `0c3cd2d` | [`33228264447`](https://github.com/hzldew-git/BongTheory/actions/runs/33228264447) | `99036124774` | 2026-08-29 02:10:07--02:12:43 | `116377C4EC5BA14A65A3DD3E75DA8CABA116E3F8CC35A2D732A3A2A5297C6A3E` |
| `4fc27c4` | [`33240312339`](https://github.com/hzldew-git/BongTheory/actions/runs/33240312339) | `99068410870` | 2026-08-29 07:12:58--07:16:29 | `48A3E69BFB44E7D40610D6AE78207C99809BA1B761063244D6FD75A3CEDEAB04` |
| `2eedad4` | [`33254026013`](https://github.com/hzldew-git/BongTheory/actions/runs/33254026013) | `99104519641` | 2026-08-29 13:03:12--13:06:29 | `B766241C1F0E6F521F95C3F631F978E68CAC15F1F0F0BBBB60F709AF30A2FFC5` |

The short later runs legitimately reused dependency/project caches populated
under the workflow's pinned cache keys.  They complement rather than replace
the exact-tag no-project-cache release job and the documented local Windows
source rebuild.

## Transparent timeout history

Timeouts are retained as public evidence rather than hidden:

- tag-era Lean CI run
  [`33212301971`](https://github.com/hzldew-git/BongTheory/actions/runs/33212301971)
  was cancelled at its original 120-minute limit after reaching job 5,381 of
  5,555; its log contains no Lean error;
- the initial Windows half of release run `33212303098` was cancelled at its
  original 180-minute limit after reaching job 5,204 of 5,555; its log
  contains no Lean error;
- exact-tag Windows rerun
  [`33228280171`](https://github.com/hzldew-git/BongTheory/actions/runs/33228280171)
  was cancelled at its then-current 300-minute limit after reaching job 5,391
  of 5,555; the API conclusion is `cancelled`, not `failure`, and the only
  terminal diagnostic is the cancellation.

The corresponding downloaded job-log SHA-256 values are, respectively,
`3193A7A68A48FFB248F0EC7A48D1062AA98A8C4BF9936D7E7D93B8AB1DFD6DFA`,
`7573C0D737DCAAEDD3154ED651A41F3D50EC16E5F95A61163E88060C16AE03B1`,
and `54C3568D40091C063D97F35B9FE1C3A099ED7741277CF7EC66EFC6BD0A752A1D`.

## Published release artifacts

The three assets were downloaded again from the public
[`v0.1.0-rc.1`](https://github.com/hzldew-git/BongTheory/releases/tag/v0.1.0-rc.1)
release, rather than checked only before upload.  The API sizes and downloaded
sizes agreed exactly.

| Published asset | Bytes | Downloaded SHA-256 |
|---|---:|---|
| `BongTheory-v0.1.0-rc.1-SHA256SUMS.txt` | 189 | `23282B089B1CF9F2E4BA91B54F3690050C25288532FAFE796A446CEA5F3E3F6B` |
| `BongTheory-v0.1.0-rc.1.bundle` | 5,716,001 | `DDC71237044283F6874720AAF4B5031E9D3EA8053A69366A8BCD00C86ECF361C` |
| `BongTheory-v0.1.0-rc.1.zip` | 6,304,923 | `CF536B4818A339235E9715EEAAB387833D761A387A60019695E6782BADA8356F` |

`git bundle verify` reports a complete history containing `main`, the
annotated tag object `e01ec6914c6f488617609899656c4aa51dfe8638`, and tag
target `3840b0fabc1142cd55c7b132a62174e732759692`.  The zip contains the
pinned toolchain, manifest, sources, audit modules, and review documents.

## Interpretation and limit

These runs establish public technical reproducibility of the pinned Lean
artifacts within the explicitly recorded dependency and runner boundary.
They do not certify that the Lean definitions, quantifiers, normalizations,
or theorem endpoints exactly match the four papers.  That distinct semantic
question remains `PROVISIONAL_MATCH`, Grade B, until the independent human
sign-off requirements in `REVIEWING.md` and
`docs/audit/IndependentReviewSignoff.md` are met.
