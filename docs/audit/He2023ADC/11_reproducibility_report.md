# Reproducibility report

Run `lake build Bong.Papers.He2023ADC` and then
`lake env lean BongTest/He2023ADCAudit.lean`. Generate the independent Review Kit
from `papers/he2023adc/paper.json`. Verify the publisher PDF against its manifest
hash; the kit excludes PDFs even where redistribution may be licensed.

Toolchain: `leanprover/lean4:v4.32.1`, with dependencies locked in
`lake-manifest.json`. At code commit
`2a151a8024d10ae094df958cd3626dbd13c447c2`, the new support modules, paper entry
and audit file passed incremental Lean compilation. The existing local
dependency worktrees contain changes, so that incremental result alone is
not a clean-rebuild certificate.

## Published-profile CI evidence

[Paper Review Kits run 33929872783](https://github.com/hzldew-git/BongTheory/actions/runs/33929872783),
job `101206371209`, completed successfully for the ADC kit. The actual checkout
and packaged source commit was the PR merge-test revision
`6bf3bdf8bd272109e898335683f05bb76664330c`, not simply the branch head.
Its Git tree `673dce7c2eedc5a45aa3dc90d55aa55142d564c3` was independently
compared with branch head `db0398506b2e242288bc979217972c6a1d175674` and is
identical. That tree contains the completed Lemma 4.11-4.12 transport proofs.

The inspected log records source-only generation, extraction, 1906 verified
files, a successful build (4943 jobs), and the expanded paper audit, including
all thirteen published-family axiom checks. The artifact is
`paper-review-he2023adc-6bf3bdf8bd272109e898335683f05bb76664330c`, ID
`9958233657`. The dependency and build caches are infrastructure optimizations;
the source archive contains no local dependency worktree or local build tree.

## Later local proposition checkpoint

`9c432a685c96c134b12664800464ae4b1d0d6eec` adds Proposition 4.13 after that
remote checkpoint. Its new module, paper entry, and audit passed local Lean
checks and a separate cached review. The earlier CI artifact does not contain
this addition and does not certify it. Reproducibility for this newer
checkpoint remains `PARTIALLY_REPRODUCIBLE` pending its own clean-kit CI.

The subsequent code checkpoint `5fff59784a0a3dd4442405f204519c36e0a8e468`
adds both dyadic clauses of Proposition 4.16. Its new source module, canonical
entry and complete audit also passed local compilation. All six new queried
axiom sets contain only the three standard axioms. This check used the same
existing dependency worktrees; the older remote artifact contains neither
Proposition 4.13 nor this Proposition 4.16 addition. It cannot certify them.
