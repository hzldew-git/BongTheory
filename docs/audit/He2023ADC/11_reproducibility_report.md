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

GitHub workflow run `33924619385` builds freshly extracted paper-specific
archives for the earlier head `94c4dcfd81ef4924c0b5ee66cf3700233e962991`.
The result for that earlier revision must not be used to certify the new
profile commit. A new exact-revision clean-extract run is required after
publishing these changes. The subsequent `W/N` transport checkpoint
`976883e6cda7c17402c4c1f0bc768db555460eae` also passed both new module
checks, the paper entry and the expanded audit. It likewise requires its
own exact-revision clean-kit build. Current status: `PARTIALLY_REPRODUCIBLE` until that
new run and its audit logs have been inspected.
