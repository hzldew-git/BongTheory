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

## Later even-testing checkpoint

Code `d94cc797ad8ed83c53447c139b496d5a2ca8f4fb` additionally includes
all four clauses of Lemma 6.4. The new modules, canonical entry and expanded
audit passed local checks with twenty standard-only axiom reports. These
checks still use the existing modified dependency worktrees. Neither the
published-profile CI artifact nor the earlier local quaternary Review Kit
contains Lemma 6.4. Its own source-only kit and exact-revision clean-kit CI
are separate reproducibility obligations; no earlier green result is reused
as certification of these later proofs.

The standalone kit at checkpoint `0a49c89f5f4455756403a9fa3cc98c7a71626fee`
subsequently passed extraction and 1916 file hash checks, archive SHA-256
`2012E324DA7332B81CD16F37C463C80E97141EFD92C88E82E1BB79092F9FA585`.
This is structure validation, not its own clean Lean build.

## Later pointwise-obstruction checkpoint

`2a5d3afc90cbb55fef284c0678336aa58484c847` and
`9d6a4b103449e387d4c9d78de4899bd53e81e374` add Lemma 6.5(i) and (ii).
Both modules, canonical entry, complete audit and eight new standard-only
axiom checks passed locally and in independent cached review. None of the
earlier kits or remote CI results contains these two additions. Report 18
records the exact version boundary and pending clean-kit obligations.

## Full even corank-one theorem checkpoint

`272d810ea2ca8bd0e19ac97f6d9cda1853502cde` adds full Theorem 6.1 over
the independently reviewed concrete tests at `9fb5f14`. All three new
modules, 12 standard-only axiom queries, canonical entry and complete audit
passed local and independent cached checks. Report 19 records exact scope.
Neither the earlier published-profile remote artifact nor the local 6.4
kit contains this theorem. Exact-revision clean-kit CI remains pending;
local dependency-worktree warnings are not suppressed or reclassified.

The source-only ADC kit at clean commit
`a7345459f9737fffb482b3ef8d215f8feeca24b2` contains full Theorem 6.1
and the published Theorem 3.6 interface. Archive name:
`BongTheory-He2023ADC-checkpoint-20260905-even-corank-one-review-kit.zip`.
It has 1886 Lean sources, 1926 packaged files, and 5750530 bytes. Extraction
and all 1925 file hashes passed; archive SHA-256:
`7D0DD1177B92D091C86B0ABF23EB6D945298FAD075EBD8967C2895DEC4048C59`.
This is structure-only validation, not a clean Lean run or uploaded release.
It predates report 20 and the later Lemma 6.6 support development.
