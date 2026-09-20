# Completed-field order-scaling checkpoint

Status: `LEMMA_8_1_I_PROVED_FOR_FINITE_COMPLETIONS` /
`PARTIAL_LEMMA_8_1`.

Code checkpoint:
`a5c100249faf6ef2d10eb1385cd06fd54a1cb1d5` on
`release/heclassic-v0.5.0-rc.1-prep`.

## Source authority and statement

The sole semantic authority remains the author-corrected v5 TeX manuscript
`classic_dyadic-n-uni-v5.tex`, SHA-256
`C334676733163C7A521824E1F00C782A7BF0FD1ABE5366BF76D838238EDCA049`.

Let `L / K` be a finite number-field extension, let `P` lie over `p`, and
write `K_p` and `L_P` for the corresponding finite completions. For every
nonzero `x` in `K_p`, the new source-facing endpoint proves

`ord_P(x) = ord_p(x) * e(P / p)`.

Here the left side evaluates the image of `x` under the actual completed
embedding constructed in Report 39. This is the full completed-field scope of
v5 Lemma 8.1(i), not only its number-field-coefficient specialization.

## Proof chain

The proof does not infer a discrete equality from density alone. It uses the
following checked chain:

1. `valuation_liesOver` gives
   `v_P(x) = v_p(x)^e` on the number-field subfield.
2. `completionMap_coe` identifies the completed embedding with the original
   map on that subfield.
3. The lower and upper completed valuations are continuous because their
   adic valuations are surjective.
4. The two functions `x |-> v_P(x)` and `x |-> v_p(x)^e` are therefore equal
   on all of `K_p` by continuous extensionality from the dense subfield.
5. Applying the logarithm converts the multiplicative equality into the
   additive order formula.

The declaration `completionMap_valuation` proves step 4, and
`completionAdicOrder_liesOver` proves the displayed additive formula for
`(K_p)^x`.

`RemainingCompletionInputs.toLocalExtensionData` now uses the actual base and
upper completions, the actual completed map, and the actual order functions.
Its `lemma81Laws` theorem supplies order scaling, ramification-index
positivity, and the ramification tower internally. Only quadratic-defect
scaling and good-BONG transfer remain caller-supplied.

## Mechanical evidence

The completion module and focused audit complete a 5,651-job build. The
canonical paper entry and combined Classic audit complete a 5,674-job build.
The newly audited declarations use only `propext`, `Classical.choice`, and
`Quot.sound`. All 30 CI policy tests pass, and the comment-aware scanner checks
2,800 tracked Lean sources without a forbidden proof token outside comments.
The focused imported-closure gate reports
`AXIOM_GATE_PASS: 62857 declarations checked`.

These are incremental local checks at the stated code commit. A fresh exact
Review Kit for the newer checkpoint remains a separate reproducibility gate.

## Remaining boundary

This checkpoint completes only Lemma 8.1(i). It does not prove:

- the quadratic-defect inequality in Lemma 8.1(ii);
- preservation of an orthogonal basis and good BONG under scalar extension in
  Lemma 8.1(iii);
- the concrete global lattice, localization, positive-globalization,
  representation-transport, sum-of-squares, or strong-approximation inputs;
  or
- the false unrestricted odd Corollary 6.3 in authoritative v5.

The whole-paper grade remains D, the completion verdict remains
`NOT_COMPLETE`, and GitHub deployment remains disabled.
