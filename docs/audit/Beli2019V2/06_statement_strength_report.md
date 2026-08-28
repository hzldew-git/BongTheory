# Statement Strength Report

> Historical snapshot notice (28 August 2026): the 49-slot statement audited
> below has been replaced by a public signature with no project-specific
> law/data parameters.  See `15_unconditional_completion_audit.md`.

## Assumption comparison

The Lean statement is stronger in assumptions:

- the paper assumes a dyadic local field;
- Lean assumes an abstract field with a dyadic context and 49 additional
  project-specific law-instance slots;
- several slots encode substantial local classification, scaling,
  Jordan-weight, lower-level Section 4, and Section 5 results.

Until instances are constructed from a concrete definition of every dyadic
local field, the Lean theorem applies only in models equipped with all those
laws.

## Domain comparison

Nominally, the Lean base-field type is more general than a finite extension of
\(\mathbb Q_2\). Semantically, the extra law parameters restrict it. This is
not a genuine generalization unless consistency and realizability of the full
law package are established.

The Lean rank encoding covers positive ranks because the two good BONGs have
lengths `m + 1` and `n + 1`. If the paper permits a zero lattice as a rank-zero
edge case, that edge case is outside the public theorem.

## Conclusion comparison

Conditional on the law instances and positive-rank convention, the Lean
conclusion is neither visibly weaker nor stronger:

- it produces a nonempty integral, injective, form-preserving linear map;
- this is the intended meaning of integral representation;
- the converse packages exactly four conditions;
- the revised theorem changes only condition (iii) to (iii').

## Quantifier and endpoint comparison

The paper uses one-based indices and an “ignore meaningless inequalities”
convention. Lean uses bounded index structures and separate terminal cases.
This removes undefined terms and makes quantifier domains executable. The
audit found no obvious lost ordinary index or reversed inequality in the
public condition packages, but endpoint equivalence remains
`MATCH_CANDIDATE` pending independent mathematical review.

## Circularity comparison

The public main theorem does not assume:

- `GoodBONGRepresentationLaws`, which would contain the desired equivalence;
- `Beli2019FinalStepLaws`, which formerly supplied the unresolved final
  descent.

The remaining `Beli2019SectionFiveLaws` and lower-level legacy Section 4
interfaces are narrower than Theorem 2.1, but they still encapsulate
substantial parts of its necessity proof. `Beli2019SectionFourLaws` itself is
now constructed rather than assumed. These interfaces do not make the Lean
theorem logically circular, yet they prevent the result from being an
unconditional formal proof of the paper.

## Final classification

- Local statement shape: `MATCH_CANDIDATE`.
- Assumptions: `FORMAL_ASSUMPTIONS_STRONGER`.
- Whole theorem: `FORMALIZATION_WEAKER`.
