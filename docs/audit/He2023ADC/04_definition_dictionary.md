# Definition dictionary

| Paper notion | Lean declaration |
|---|---|
| local `n`-ADC | `Bong.Lattice.IsNADC` |
| integral lattice | `Bong.Lattice.IsIntegral` |
| ambient space representation | `QuadraticSpace.Represents` |
| scalar extension from `F` to `E` | `QuadraticSpace.scalarExtension` |
| one-dimensional arithmetic input in Lemma 2.2 | `QuadraticSpace.HasOneDimensionalSubspaceDescent` |
| nonzero square-class openness used in Lemma 2.2 | `QuadraticSpace.HasOpenNonzeroSquareClasses`, proved by `hasOpenNonzeroSquareClasses_of_complete` |
| descended global subspace in Lemma 2.2 | range submodule returned by `QuadraticSpace.heADC2025Lemma22_of_oneDimensionalDescent` |
| concrete number-field Lemma 2.2 | `QuadraticSpace.heADC2025Lemma22_numberFieldFiniteCompletion` |
| integral lattice representation | `Bong.Lattice.Represents` |
| `O_F`-maximal | `Bong.Lattice.IsOMaximal` |
| global `n`-ADC | `GlobalLocalLatticeSystem.IsGloballyNADC` (abstract system) |
| global `n`-universality with compatible signatures | `GlobalLocalLatticeSystem.IsGloballyNUniversal` (abstract system) |
| `n`-regular | `GlobalLocalLatticeSystem.IsNRegular` (abstract system) |
| alternating orders followed by a table tail | `heADCMaximalOrderProfile` |
| arbitrary-lattice equivalence on a specified table space | `GoodBONG.HeADCMaximalProfileCriterion` |
| unary `W_1^1(c)` and its maximal lattice | `heADCW1Unary`, `heADCN1Unary` |
| finite published unary table | `HeADC2025PublishedUnaryTestingIndex`, `HeADC2025PublishedUnaryTestingIndex.model` |
| minimal testing set in Lemma 4.9(ii) | `QuadraticLatticeModel.IsLiteralMinimalUniversalityTestingFamily` |
| unary unique excluding space `W_2^3(c)` | `QuadraticLatticeModel.heADC2025Proposition42iiiUnary` |
| finite integral defect index `d(c)` in the nonexceptional unit rows | integer cast of `(quadraticDefect K c).toNat`, with finiteness proved from `HeHuSharpDomain` |
| signed even n-prefix in Lemma 6.4, n=2k+2 | `(-1 : Kˣ) ^ (k+1) * a.prefixProduct (2*k+2)` |
| raw defect in Lemma 6.4(i)(iv) | `Dyadic.quadraticDefect K`, valued in extended naturals with infinity retained |
| unit kappa in Lemma 6.4(iv) | valuation unit with raw defect the finite natural `2*e-1`; its sharp domain is proved |
| failing indices in Lemma 6.5(i)(ii) | `RepresentationIndex.val` is one-based: n and n-1, respectively |
| bracketed defects in Lemma 6.5 | `truncatedPrefixDefect`, retaining source and target endpoint alpha caps |
| omitted empty-prefix alpha cap | infinity, not a defined alpha_0 or beta_0 |

The `*Published` endpoints use the named `heADCW*` and `heADCN*` families
directly. `isIsometric_publishedModel_iff_orderProfile` transports the concrete
model by an equal-rank space isometry and maximal-lattice uniqueness.

The concrete-model predicate expands to: for every good BONG `a` of `L`, if `L` is
integral and its space is isometric to the reference space, then `L` is
integrally isometric to the reference lattice if and only if every order of
`a` equals the displayed profile. Its BONG argument identifies the reference
space, lattice and rank; it does not assume the desired equivalence.

The source uses one-based indices. In Lean the even zero-based positions
correspond to the source's odd positions, with order zero; the odd zero-based
positions of a hyperbolic block have order `-2e`.

In Theorem 6.1, O-maximal means maximal among norm-integral full lattices
in the same quadratic space. A volume-order difference is twice a
nonnegative inclusion index; it is not a count of BONG order profiles.
The ADC and maximality predicates both include norm-integrality.

For Lemma 6.6, `quadraticDefect K (signedEvenPrefixProduct ...)` is raw,
whereas `heADCAdjacentCappedDefect` includes the source endpoint alpha cap.
`centralDefectTrigger` is the publisher's sum-of-two-defects trigger, not
the auxiliary-alpha trigger. Its conjunction with failure of the full
target-to-(n+1)-prefix embedding expresses the exact pointwise failure.

`HeADCEvenCentralAlphaAlternatives` in Lemma 6.7 is exactly alpha_(n+1)=0,
or alpha_(n+1)=1 and raw adjacent defect = capped adjacent defect =
1-R_(n+2). `adjacentDefect` contains no alpha cap. Equality with
`heADCAdjacentCappedDefect` is a proved conclusion, not a definitional alias.

In Lemma 6.8(i)--(ii), `q.IsIsometric` is the hypothesis on the ambient
quadratic space, while `Lattice.IsIsometric` is the stronger integral
conclusion on the actual lattices. The signed full product uses all m
values and sign (-1)^(m/2); a proper head prefix is kept distinct from it.

`HeHuSharpDomain c` excludes two square classes, not merely two scalars.
`HeHuPublishedSquareClassIndex.parameter U p` ranges over U and U*pi.
The printed-domain equivalence additionally exposes Delta in U; the
square representative is proved equal to 1 from normalization. The
`HeADCEvenCorankTwoThreeTests` structure is internal proof data and is
constructed from ADC plus ambient isometry, not a replacement ADC definition.

Report 25's even-leading tower normalization is a quadratic-space coordinate
rescaling by independently chosen squares. It does not preserve the integral
lattice or assert that its original leading orders coincide. The final
integral-isometry conclusion instead uses the proved full order-profile
criterion on the original lattice. The boundary n=2 is retained in (iii)
and explicitly excluded, not redefined, in `heADC2025Lemma68iv_of_pos`.

`HeADC2025Lemma68ivBinaryStatement` is an audit proposition, not a replacement
definition from the paper. It packages the literal n=2 implication using the
same `IsNADC`, ambient quadratic-space isometry, and integral lattice-isometry
notions already compared above. Its formal negation therefore exposes a
statement mismatch without changing any underlying mathematical definition.

`HeADC2025Theorem72BaseIndex U` is the literal finite type indexing
`U \ {1, Delta}`. `HeADC2025Theorem72Product` is the invariant product
family with an arbitrary sharp unit square class and a line of order zero or
one. `HeADC2025Theorem72PublishedProduct` is the same family after choosing
`U`; its Boolean line component is the source exponent in `{0,1}`. Their
formal equivalence uses integral lattice isometry, not equality of chosen
models or ambient-space isometry alone.

`heADC2025Remark73Plane delta l` is the paper's general plane
`A(pi^l,-(delta-1)pi^-l)`. `heADCAForm` is the already checked coordinate
model `(1/2)A(2,2rho)`. Thus rescaling it by `pi` is the printed
`(1/2)pi A(2,2rho)`. `halfHyperbolicExtensionForm` and its lattice are the
literal repeated orthogonal product with the paper's half-hyperbolic `H`.
The formal conclusions are integral lattice isometries, not coefficient-list
abbreviations.

## Section 8 genus and class number

Paper terms: `gen(M)` and class number one, used on pp. 1017--1018.

Formal terms: `HeADC2025GlobalData.inGenus` and
`HeADC2025GlobalData.HasClassNumberOne`. The latter means that every global
lattice `M'` satisfying `inGenus M' M` is integrally isometric to `M`.
`ClassNumberRegularityLaws.genus_lift_of_local_represents` uses exactly this
orientation when lifting an everywhere locally represented target.

The relation `inGenus` remains abstract: the project has not yet constructed
it from actual localizations of integral quadratic lattices over a number
field. Status: `PROVISIONAL_MATCH` for the quantifier and orientation;
`FORMAL_DEFINITION_AMBIGUITY` until an author or domain expert confirms that
the abstract relation is instantiated by the publisher's genus convention.
See Report 73.

## Section 8 local maximality

Paper terms: `O_{F_p}`-maximal, local `n`-ADC, and `O_F`-maximal in Theorem
1.5 and Lemma 8.1(ii), on pp. 984 and 1016--1017.

Formal terms: `GlobalLocalLatticeSystem.localMaximal`, `IsNADCAt`, and
`HeADC2025GlobalData.isGlobalMaximal`. `LocalMaximalityLaws` records maximal
extension and representation transport; its theorem
`localMaximal_isNADCAt` constructs the full `IsNADCAt` predicate.
`local_theorem15` adds the classification-dependent necessity direction.
The relations remain abstract until a concrete number-field localization
instance is constructed. See Report 74.

## Section 8 spinor genus

Paper terms: definite, indefinite, spinor genus in `gen(M)`, and the unique
class representing the selected sublattice in Theorem 8.2 on p. 1017.

Formal terms: `HeADC2025GlobalData.isDefinite`, `inSpinorGenus`, and
`DistinguishingSublatticeLaws`. The latter separates the definite Meyer case,
Xu's indefinite rank-`n` construction, and the O'Meara 104:5 isometry step.
The predicates remain abstract pending a concrete number-field model. Status:
`PROVISIONAL_MATCH`; see Report 75.

## Section 8 stability and scaling

Paper terms: stability at every prime, the local alternatives
`H -> M_p` or `M_p` isometric to `A orthogonal-sum A(p)`, and scaling by two
in Lemma 8.4 on p. 1018.

Formal terms: `HeADC2025GlobalData.isStableAt`, `hasLemma84LocalForm`, and
`ScalingStabilityLaws`. The named local-form predicate represents exactly the
source disjunction, while the law package separates its classification,
scaling, and placewise-global consequences. These predicates remain abstract
pending a concrete number-field model. Status: `PROVISIONAL_MATCH`; see
Report 76.

`ScalingRegularityLaws.isHalfScaleOf_iff` fixes the formal orientation of the
paper's statement that `M` is isometric to `L(1/2)`: formally this means
`L = scaleTwo M`. Its other field records regularity invariance as a
biconditional for every rank. The concrete scaling operation and proof of
these laws remain pending. Status: `PROVISIONAL_MATCH`; see Report 77.
