# Completed defect and good-BONG coefficient-scaling checkpoint

Status: `LEMMA_8_1_COMPLETED_AT_FINITE_COMPLETION_COEFFICIENT_CRITERION_SCOPE` /
`PARTIAL_WHOLE_PAPER_FORMALIZATION`.

Code checkpoint:
`c6d22da9282e112597f805e9104eae1cb88fb938` on
`release/heclassic-v0.5.0-rc.1-prep`.

## Source authority and scope

The sole semantic authority remains the author-corrected v5 TeX manuscript
`classic_dyadic-n-uni-v5.tex`, SHA-256
`C334676733163C7A521824E1F00C782A7BF0FD1ABE5366BF76D838238EDCA049`.
The manuscript is author-held and is not redistributed.

Reports 38--40 constructed the finite-completion extension and proved the
order formula in Lemma 8.1(i). This checkpoint proves the remaining two
numerical ingredients for the actual completions:

- Lemma 8.1(ii), the relative quadratic-defect inequality for every nonzero
  element of the completed base field; and
- Lemma 8.1(iii), at the exact He--Hu Lemma 2.2 coefficient-criterion level:
  a coefficient sequence satisfying the two adjacent BONG inequalities and
  `R_i <= R_(i+2)` continues to satisfy them after applying the completed
  field embedding.

The second item is deliberately not described as a construction of a global
lattice scalar extension. It proves the numerical criterion for the mapped
coefficients. Connecting it to an actual orthogonal basis of a localized
global lattice remains part of the global lattice/localization boundary.

## Quadratic defect

`CompletionIsQuadraticApproximation p a n` is the completed-field predicate

`v(1 - x^2/a) <= exp(-n)`

for some `x`. It includes exact square approximations because the
multiplicative valuation of zero is zero. The definition
`completionQuadraticDefect p a : ENat` is the supremum of all attained
natural depths, so it also represents infinite defect.

`completionIsQuadraticApproximation_map` combines the normalized-error
identity with `completionMap_valuation`: an approximation of depth `n` maps
to one of depth `e(P/p) * n`. Taking suprema gives

`e(P/p) * d_p(a) <= d_P(a)`.

This is `completionQuadraticDefect_scale`. The companion declaration
`completionQuadraticDefectQ_scale` transports the result to `WithTop Rat`,
the scale used by the abstract Section 8 adapter.

## Good-BONG coefficient criterion

`CompletionBONGConditions` states, for every adjacent pair,

`0 <= R_(i+1) - R_i + d(-a_i a_(i+1))`

and

`-2e <= R_(i+1) - R_i`.

`CompletionGoodBONGCoefficients` adds `R_i <= R_(i+2)`. In
`completionGoodBONGCoefficients_map`, order differences are multiplied by
the nonnegative relative ramification index, the defect term is bounded by
`completionQuadraticDefect_scale`, and the absolute ramification indices are
related by `absoluteRamificationIndex_tower`. These calculations prove all
three coefficient conditions over the upper completion.

`completionLocalExtensionData` instantiates the abstract local-extension
data with the actual lower completion, mapped upper coefficients, completed
orders, completed defects, and the displayed criterion. Consequently
`completionLemma81Laws` fills every field of `Lemma81Laws` without a
caller-supplied order, defect, or good-BONG arithmetic premise.

## Mechanical evidence

The focused completion module and audit complete a 5,651-job build. The
canonical Classic paper entry together with all eight manifest-listed audit
modules completes a 5,674-job build. The newly audited declarations use only
`propext`, `Classical.choice`, and `Quot.sound`.

All 30 CI policy tests pass. The comment-aware proof-command scanner checks
2,800 tracked Lean sources without a forbidden proof token outside comments.
The focused imported-closure gate reports
`AXIOM_GATE_PASS: 62850 declarations checked`.

These are incremental local checks at the stated code commit. They are not a
fresh-extraction Review Kit receipt or GitHub CI result.

## Remaining boundary

This checkpoint closes Lemma 8.1 at the actual finite-completion numerical
and coefficient-criterion scope. It does not construct:

- the global number-field lattice carrier, its localization, or the
  identification of its local orthogonal basis with the mapped coefficient
  sequence;
- the place equivalence with the standard height-one spectrum;
- positive-definite globalization, representation transport, the three
  concrete sum-of-squares local branches, or strong approximation; or
- any valid unrestricted odd replacement for the false v5 Corollary 6.3 and
  the affected odd Section 8 statements.

The whole-paper grade therefore remains D, the completion verdict remains
`NOT_COMPLETE`, and GitHub deployment remains disabled.
