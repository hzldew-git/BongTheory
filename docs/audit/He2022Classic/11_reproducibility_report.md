# Reproducibility report

Run `lake build Bong.Papers.He2022Classic` and then
`lake env lean BongTest/He2022ClassicAudit.lean`. The independent Review Kit is
generated from `papers/he2022classic/paper.json`. The publisher PDF is excluded;
its manifest hash identifies the version reviewers must obtain independently.
The audit output must show the statement definition separately from the axiom
reports for the two proved foundational theorems.
