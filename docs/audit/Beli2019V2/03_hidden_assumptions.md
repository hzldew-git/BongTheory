# Hidden and Additional Assumptions

> Historical snapshot notice (28 August 2026): this report records the former
> explicit-law state.  Its law-slot counts and `FORMALIZATION_WEAKER` verdict
> are superseded by `15_unconditional_completion_audit.md`.

## Printed assumptions

The paper works over a dyadic local field \(F\), with integral quadratic
lattices \(M,N\), chosen good BONGs, ranks \(m\geq n\), and an ambient-space
representation \(FN\to FM\). Theorem 2.1 itself does not list a separate
family of local arithmetic law packages.

## Lean structural assumptions

The formal theorem uses:

- `Field K` and `CharZero K`;
- `ValuativeRel K`, `TopologicalSpace K`, and `DyadicContext K`;
- additive commutative groups and `Module K` structures for the two ambient
  vector spaces;
- explicit quadratic spaces, lattices, and good BONGs of lengths `m + 1` and
  `n + 1`;
- `n ≤ m` and an ambient representation.

Finite dimensionality is recovered from the good-BONG/lattice data rather
than appearing as an explicit theorem argument. The `m + 1` and `n + 1`
encoding means the public theorem covers positive ranks only.

## Additional mathematical law parameters

The current theorem signature contains 49 project-specific law/data-instance
slots besides the five foundational field, valuation, and topology structures
on `K`. Repeated entries below occur at different universe combinations and
are genuine theorem parameters. This count is taken from the elaborated
public signature, not inferred from source comments.

### Field and quadratic-defect layer

- `QuadraticDefectLaws`;
- `DyadicDiscriminantClassLaws`;
- `DyadicMaximalDefectClassLaws`;
- `DyadicUnramifiedNormLaws`;
- `DyadicResidueDefectProductLaws`;
- `DyadicHilbertDefectChoiceLaws`;
- `UnitQuadraticDefectParityLaws`;
- `DyadicUnitDefectSpectrumLaws`;
- `HilbertSymbolLaws`;
- `DyadicDiagonalClassificationLaws`.

### BONG, Jordan, and results inherited from earlier Beli work

- three `BONGStructuralLaws` instances;
- two `ScaledHyperbolicMaximalLaws` instances;
- `Beli2009WeightIdealData`;
- `Beli2019UnaryBinaryJordanLaws`;
- `Beli2009JordanWeightOrderLaws`;
- three `BeliLemma43ConstructionLaws` instances;
- four `GoodBONGClassificationLaws` instances;
- `BeliSectionFourLaws` and `BeliCorollary44Laws`;
- `BinaryNormGeneratorLocalLaws`;
- two `BeliLemma49Laws` and two `BeliLemma47Laws` instances;
- `DyadicAlternatingEndpointTowerNormalizationLaws`;
- `DyadicAlternatingEndpointTowerRepresentationLaws`;
- `Beli2009BinaryNormContainmentLaws`.

### Representation geometry and 2019-specific layer

- two `Beli2019Lemma310RepresentationLaws` instances;
- `DiagonalRepresentationParityLaws`;
- `DiagonalCodimensionOneCancellationLaws`;
- `DyadicDiagonalCodimensionTwoLaws`;
- `DiagonalIsometryInvariantLaws`;
- `DyadicQuaternaryComplementLaws`;
- `DyadicTernaryRepresentationObstructionLaws`;
- two `Beli2019SectionFiveLaws` instances;
- two `DyadicBinaryFirstScalingLaws` instances;
- two `DyadicQuaternaryFirstScalingLaws` instances.

## Highest-impact unresolved interfaces

The following are not mere convenience abstractions.

1. `Beli2019SectionFiveLaws.data` returns the complete Section 5 data for an
   arbitrary literal index-\(\mathfrak p\) inclusion.
2. `Beli2019UnaryBinaryJordanLaws` supplies three local Jordan and weight
   computations used in Lemma 9.5.
3. `DyadicBinaryFirstScalingLaws` and
   `DyadicQuaternaryFirstScalingLaws` supply ambient orthogonal-basis
   constructions used in Section 8.
4. The legacy `BeliSectionFourLaws` and `BeliCorollary44Laws`, together with
   several classification and local-representation interfaces, remain
   lower-level inputs to the concrete `Beli2019SectionFourLaws` construction.
5. The field-level defect and Hilbert-symbol classes provide existence and
   classification facts not currently derived from `DyadicContext`.

No global/default instance was found that discharges all these interfaces for
an arbitrary dyadic local field.

## Interfaces that are no longer hidden obligations

- `Beli2019FinalStepLaws` has been removed.
- `Beli2019Lemma310PrefixLaws`,
  `Beli2019Lemma310RepresentationLaws`, and
  `Beli2019Corollary311Laws` have derived instances from lower-level inputs.
- `Beli2019InclusionConditionsLaws` has a derived instance.
- `Beli2019SectionFourLaws` is constructed inside the main theorem from its
  lower-level inputs and is no longer a public theorem parameter.
- `GoodBONGDeepIntegralExtensionLaws` is constructed from good-BONG existence
  and the lattice API; the former `deepVV`, `deepVW`, and `deepWW` parameters
  have been removed.
- `GoodBONGRepresentationLaws` is not an assumption of either public main
  theorem; it remains only as a compatibility API.

## Assessment

The additional assumptions are explicit in Lean, so they are not kernel
axioms and are not hidden from the type checker. They are nevertheless hidden
from the printed mathematical statement unless the expanded theorem
signature is inspected. Their presence changes the semantic status to
`FORMAL_ASSUMPTIONS_STRONGER` and therefore makes the overall formalization
`FORMALIZATION_WEAKER` than the unconditional paper theorem.
