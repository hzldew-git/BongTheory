# Definition dictionary

| Paper notion | Lean declaration |
|---|---|
| classic integral | `Bong.Lattice.IsClassicIntegral` |
| classic `n`-universal | `Bong.Lattice.IsClassicNUniversal` |
| classic-maximal | `Bong.Lattice.IsClassicMaximal` |
| scale ideal `s(L)` | `Bong.Lattice.scaleIdeal` |
| ordinary integral | `Bong.Lattice.IsIntegral` |
| integral representation | `Bong.Lattice.Represents` |
| global lattice and finite localization system | `Bong.GlobalLocalLatticeSystem` |
| positive definite global rank-`n` representation hypothesis | `HeClassic2024GlobalData.RepresentsAllPositiveDefiniteClassicAtRank` |
| Proposition 8.2 globalization/localization inputs | `HeClassic2024GlobalData.Proposition82Laws` |
| Theorem 1.9 local-to-global inputs | `HeClassic2024GlobalData.SumOfSquaresLocalGlobalLaws` |
| Theorem 1.9 finite-place branch inputs | `HeClassic2024GlobalData.SumOfSquaresLocalUniversalityLaws` |
| odd number-field discriminant | `HeClassic2024NumberField.DiscriminantOdd` |
| dyadic prime ideal | `HeClassic2024NumberField.IsDyadicPrime` |
| concrete discriminant/ramification equivalence | `HeClassic2024NumberField.discriminantOdd_iff_forall_ramificationIdx_eq_one` |
| abstract-to-number-field place identification | `HeClassic2024GlobalData.HeightOneSpectrumIdentification`, which derives `NumberFieldDiscriminantBridge` |
| canonical number-field Section 8 arithmetic | `HeClassic2024NumberFieldGlobalData.toGlobalData` and `sectionEightLaws` |
| additive order of a nonzero number-field coefficient at a finite prime | `HeClassic2024NumberFieldLocalExtension.adicOrder` |
| finite-prime order scaling and ramification tower | `adicOrder_liesOver` and `absoluteRamificationIndex_tower` |
| induced finite-completion embedding | `HeClassic2024NumberFieldLocalExtension.completionMap` |
| scoped finite completed extension | `HeClassic2024NumberFieldLocalExtension.CompletionLiesOver` |
| additive order on a finite completion | `HeClassic2024NumberFieldLocalExtension.completionAdicOrder` |
| completed-field order scaling | `completionMap_valuation` and `completionAdicOrder_liesOver` |
| generic one-way discriminant package | `HeClassic2024GlobalData.DiscriminantRamificationLaws` |

The formal definition includes source classic integrality rather than relying
on a standing prose convention.

`Proposition82Laws.positiveDefinite_globalization` represents the O'Meara
81:14 step only at the interface level.  It does not itself define or
construct a concrete number-field lattice; see Report 27.
The `strong_approximation` field in `SumOfSquaresLocalGlobalLaws` is likewise
an explicit arithmetic interface, not a proved concrete number-field theorem;
see Report 29.
`SumOfSquaresLocalUniversalityLaws` separates the three finite-place branches
of v5 line 1700; their all-places conclusion is derived rather than assumed;
see Report 31.
The concrete equivalence, its two directions, the ramified-prime witness, and
ramification-index positivity are proved in Report 32. The generic package is
constructed from `NumberFieldDiscriminantBridge`; it is no longer a separate
number-field arithmetic obligation.
`HeightOneSpectrumIdentification.numberFieldDiscriminantBridge` further
derives bridge primality and dyadic-prime coverage from the standard
height-one-spectrum place type; see Report 34.
`HeClassic2024NumberFieldGlobalData.toGlobalData` fixes the dyadic predicate,
ramification index, and discriminant proposition to their actual number-field
definitions, so the three compatibility proofs are reflexivity; see Report 36.
`HeClassic2024NumberFieldLocalExtension.adicOrder` is the negative logarithm
of mathlib's multiplicative adic valuation on `Kˣ`. Report 38 proves its
scaling under `P | p` for underlying number-field coefficients. It does not
define order or quadratic defect on all elements of the completions.
Report 39 constructs the continuous map between those completions and proves
that it restricts to the original number-field embedding. The scoped algebra
and scalar-tower instances make the upper completion finite-dimensional over
the lower one. No completed-field order or defect is defined by this step.
Report 40 defines the completed-field order on `K_pˣ`, proves its scaling under
the completed embedding, and supplies the order field of the Lemma 8.1
adapter. A completed-field quadratic-defect definition remains open.
