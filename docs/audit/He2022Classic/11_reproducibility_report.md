# Reproducibility report

Run `lake build Bong.Papers.He2022Classic` and then
`lake env lean BongTest/He2022ClassicAudit.lean`. The independent Review Kit is
generated from `papers/he2022classic/paper.json`. The publisher PDF is excluded;
its manifest hash identifies the version reviewers must obtain independently.
The audit output must distinguish the proposition-valued definition from the
proof `he2022ClassicTheorem11`, and print the latter's transitive axioms.
The restricted local Theorem 1.5 and the source refutation are audited too.

Code checkpoint: `31873263c5390f1df802cf9b25d125ee65f79d07`.
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
audit, including the full local Theorem 1.1, restricted Theorem 1.5, literal
Lemma 7.1(ii) refutation, conditional odd testing and full even testing.

The separate source-only artifact is
[`paper-review-he2022classic-6bf3bdf8bd272109e898335683f05bb76664330c`](https://github.com/hzldew-git/BongTheory/actions/runs/33929872783/artifacts/9961760603),
ID `9961760603`, 5800025 bytes. It is a 30-day workflow artifact, not a
permanent tagged release. Its green build does not complete the remaining
odd testing/counting, source-resolution or global obligations.

This checkpoint predates the new enforcing transitive-axiom gate. Its
individually inspected axiom reports are not a successful run of that later
gate, nor a certificate for a newer source revision. See the deployment
correction in `../HePaperDeploymentCheckpoint-20260905.md`.
