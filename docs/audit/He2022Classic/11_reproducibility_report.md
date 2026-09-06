# Reproducibility report

Run `lake build Bong.Papers.He2022Classic` and then
`lake env lean BongTest/He2022ClassicAudit.lean`. The independent Review Kit is
generated from `papers/he2022classic/paper.json`. The publisher PDF is excluded;
its manifest hash identifies the version reviewers must obtain independently.
The audit output must distinguish the proposition-valued definition from the
proof `he2022ClassicTheorem11`, and print the latter's transitive axioms.
The unary and all-ranks local Theorem 1.5 endpoints, the Lemma 7.10(iii)
`C`-row witness endpoints, and the source refutation are audited too.

Code checkpoint: `cf2f474d7bb82ad076ba39b92bcba9f7a2de082a`.
Lean: 4.32.1; dependency versions: the committed `lake-manifest.json`.
Reproducibility status for this checkpoint: `PARTIALLY_REPRODUCIBLE` until its
own generated kit has passed clean extraction, compilation, and all audits.
Successful CI for an older commit is not evidence for a newer release commit.

## Subsequent clean-kit CI checkpoint

[Paper Review Kits run 33929872783](https://github.com/hzldew-git/BongTheory/actions/runs/33929872783),
Classic job `101206371200`, completed successfully at 03:05:13 UTC on
5 September 2026. Its actual packaged source is merge-test commit
`6bf3bdf8bd272109e898335683f05bb76664330c`, whose tree was independently
checked equal to branch commit `db0398506b2e242288bc979217972c6a1d175674`.
The inspected log records a successful 5010-job build and the expanded Classic
audit, including the full local Theorem 1.1, the then-restricted Theorem 1.5,
literal Lemma 7.1(ii) refutation, conditional odd testing and full even testing.

The separate source-only artifact is
[`paper-review-he2022classic-6bf3bdf8bd272109e898335683f05bb76664330c`](https://github.com/hzldew-git/BongTheory/actions/runs/33929872783/artifacts/9961760603),
ID `9961760603`, 5800025 bytes. It is a 30-day workflow artifact, not a
permanent tagged release. Its green build does not complete the remaining
odd testing/counting, source-resolution or global obligations.

This checkpoint predates the new enforcing transitive-axiom gate. Its
individually inspected axiom reports are not a successful run of that later
gate, nor a certificate for a newer source revision. See the deployment
correction in `../HePaperDeploymentCheckpoint-20260905.md`.

The current checkpoint includes the published unary branch, a complete local
n >= 1 dispatcher, and the Lemma 7.10(iii) `C`-row deletion-witness core.
Local cached compilation with warnings treated as errors, the Classic audit,
the 2,743-source proof-token scan, all 24 CI helper tests, and a focused
transitive gate over 58,173 declarations pass. A new
clean-kit run for this exact checkpoint is still required; the historical
artifacts below do not certify it.

## First clean-kit checkpoint with enforced dependencies

[Run 33942437722, Classic job 101242489505](https://github.com/hzldew-git/BongTheory/actions/runs/33942437722/job/101242489505)
completed successfully on actual merge-test source
`c82668b97ed80f0cead4493206cb6483c4e8d77d`. Its tree
`821e857945c1f9a3b556d877075e67c28524866a` was checked equal to head
`f6f7485b6a3acabedbec5a7facce46f8ee7365ab`. The inspected log verifies
1967 payload hashes, a 5004-job build and the real `PaperAxiomGate`
success marker on 61,515 declarations. Its nonfatal generated-driver lint
warnings are not proof or gate failures.

[Independent Classic download](https://github.com/hzldew-git/BongTheory/actions/runs/33942437722/artifacts/9962386381),
artifact `9962386381`, 5802993 outer ZIP bytes. The inner source ZIP
SHA-256 is `079D6DFCFB9982415F0D3271C29C6AF0E2C560111B79FB08828D6131C4F97987`.
This certifies the new gate for this fixed kit, not complete paper coverage,
human semantic approval, the separate whole-production CI or a permanent
release. The source discrepancy and odd/global obligations are unchanged.
