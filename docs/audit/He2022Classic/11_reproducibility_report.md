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
