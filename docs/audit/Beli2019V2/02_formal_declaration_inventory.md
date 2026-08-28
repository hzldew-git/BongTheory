# Formal Declaration Inventory

## Inventory scale

At the audited snapshot:

- `Bong/Bong` contains 1,244 Lean modules;
- 1,075 module names begin with `Beli2019`;
- those 1,075 files contain approximately 11.77 MB of Lean source;
- a case-sensitive direct-declaration scan finds 5,378 declaration lines:
  4,900 theorems, 4 lemmas, 193 definitions, 216 structures, 40 inductives,
  23 classes, and 2 explicitly matched instances.

The direct-line count is not an environment or semantic count: declarations
with additional modifiers, generated equations, and namespace-generated
declarations require different accounting. It is therefore unsuitable as a
coverage denominator. The inventory below identifies the public theorem
spine and maps every paper section to its formal module family.

## Public theorem spine

| Declaration | File and line | Formal role |
|---|---|---|
| `QuadraticSpace.Representation` | `Bong/Bong/Representation.lean:36` | Injective form-preserving linear map between ambient spaces. |
| `QuadraticSpace.Represents` | `Bong/Bong/Representation.lean:48` | Nonempty ambient representation. |
| `Lattice.Representation` | `Bong/Bong/Representation.lean:122` | Integral injective form-preserving map. |
| `Lattice.Represents` | `Bong/Bong/Representation.lean:140` | Nonempty integral representation. |
| `RepresentationConditions` | `Bong/Bong/Representation.lean:529` | Original four conditions (i)--(iv). |
| `RepresentationConditionsPrime` | `Bong/Bong/Beli2019MainConditions.lean:140` | v2 package with condition (iii'). |
| `Beli2019RepresentationProblem` | `Bong/Bong/Beli2019RepresentationProblem.lean:32` | Concrete counterexample node for rank-volume descent. |
| `BONG.GoodBONG.beli2019Lemma216` | `Bong/Bong/Beli2019Lemma216Complete.lean:31` | Pointwise equivalence of the original and v2 central triggers. |
| `beli2019_necessity` | `Bong/Bong/Beli2019NecessityComplete.lean:25` | Necessity of all four original conditions. |
| `beli2019_sufficiency_complete` | `Bong/Bong/Beli2019SufficiencyComplete.lean:108` | Sufficiency for all permitted positive rank pairs. |
| `beli2019Theorem21` | `Bong/Bong/Beli2019MainTheorem.lean:97` | Original Theorem 2.1 equivalence. |
| `beli2019Theorem21_prime` | `Bong/Bong/Beli2019MainTheorem.lean:185` | Revised-v2 Theorem 2.1 equivalence. |

## Four-condition correspondence

| Paper component | Formal declaration |
|---|---|
| Condition (i) | `BONG.GoodBONG.RepresentationOrderCondition` |
| Condition (ii) | `BONG.GoodBONG.RepresentationDefectCondition` |
| Condition (iii) | `BONG.GoodBONG.CentralRepresentationConditions` |
| Condition (iii') | `BONG.GoodBONG.CentralRepresentationConditionsPrime` |
| Condition (iv) | `BONG.GoodBONG.LongRepresentationConditions` |
| Original trigger | `BONG.GoodBONG.centralAlphaTrigger` |
| v2 trigger | `BONG.GoodBONG.centralDefectTrigger` |
| Trigger equivalence | `BONG.GoodBONG.CentralTriggerEquivalence` and `beli2019Lemma216` |

## Paper-to-module map

| Paper objects | Principal formal modules or declaration families | Status |
|---|---|---|
| Definitions 1--3; Section 1 | `Beli2019TruncatedDefect*`, `Beli2019NestedOrder*`, `Beli2019Dual*`, `Beli2019Weight*` | Decomposed formal counterparts |
| Definition 4; Theorem 2.1(ii) | `Representation`, `Beli2019DefectMin`, `Beli2019CappedDefect*` | Formal counterpart |
| Definitions 5--7; Lemmas 2.7--2.18 | `Beli2019AuxiliaryAlpha*`, `Beli2019EssentialIndex`, `Beli2019Lemma2*` | Decomposed formal counterparts |
| Definition 8; Lemmas 2.19--2.21 | `Beli2019RepresentationProblem`, `Beli2019RankCompletion*`, `Beli2019SufficiencyCompletion` | Formal counterpart |
| Definitions 9--10; Section 3 | `Beli2019Approximation*`, `Beli2019Lemma310*`, `Beli2019Corollary311` | Decomposed formal counterparts |
| Section 4 | `Beli2019KeyLemma`, `Beli2019Transitivity*`, `Beli2019PrimeChainDecoration`, `Beli2019SectionFourLaws` | Decomposed; the 2019 package is constructed from lower-level legacy Section 4 inputs |
| Section 5 | `Beli2019IndexP*`, `Beli2019Projection*`, `Beli2019Enlarged*`, `Beli2019Lemma513`, `Beli2019Lemma517` | Decomposed; one-prime-step package is parameterized by `Beli2019SectionFiveLaws` |
| Definition 11; Section 6 | `Beli2019Lemma63*`, `Beli2019Lemma65`, `Beli2019Lemma66*`, `Beli2019Lemma67*`, `Beli2019Lemma69*` | Decomposed formal counterparts |
| Lemmas 7.1--7.9 | `Beli2019Lemma71*` through `Beli2019Lemma79*` | Decomposed formal counterparts |
| Lemmas 7.10--7.20 | `Beli2019Lemma710*` through `Beli2019Lemma720*`, `Beli2019SectionSeven*` | Decomposed formal counterparts |
| Lemmas 8.1--8.6 | `Beli2019Lemma81`, `82*`, `83`, `84`, `85`, `86` | Formal counterparts with explicit field/scaling interfaces |
| Note 8.7; Lemma 8.8 | `Beli2019Remark87`, `Beli2019Lemma88*` | Decomposed formal counterpart |
| Corollaries 8.9--8.11 | `Beli2019Corollary89`, `810`, `811` | Formal counterparts |
| Lemma 8.12; Note 8.13; Lemma 8.14 | `Beli2019Lemma812*`, `813*`, `814*` | Formal counterparts |
| Lemmas 9.1--9.3 | `Beli2019Lemma91*`, `92*`, `93*` | Complete rank-stratified formal counterparts |
| Lemmas 9.4--9.6 | `Beli2019Lemma94`, `95*`, `96*` | Complete rank-stratified formal counterparts |
| Lemmas 9.7--9.12 | `Beli2019Lemma97`, `98`, `99`, `910*`, `911`, `912*` | Complete rank-stratified formal counterparts |
| Section 7 reduction | `Beli2019SectionSevenReduction` | Concrete smaller-counterexample or equal-norm result |
| Section 9 reduction | `Beli2019SectionNineComplete` | Concrete result for rank three, rank four, and rank at least five |
| Equal-rank theorem | `Beli2019EqualRankComplete` | Concrete rank-volume induction, including unary/binary bases |
| Strict-rank theorem | `Beli2019RankCompletionSufficiency`, `Beli2019SufficiencyCompletion` | Deep-complement reduction to equal rank |
| Theorem 2.1 | `Beli2019NecessityComplete`, `Beli2019SufficiencyComplete`, `Beli2019MainTheorem` | Kernel-checked conditional theorem |

## Derived interfaces versus unresolved interfaces

The following former assembly interfaces have concrete derived instances:

- `Beli2019Lemma310PrefixLaws`;
- `Beli2019Lemma310RepresentationLaws`;
- `Beli2019Corollary311Laws`;
- `Beli2019InclusionConditionsLaws`.

The theorem-level `Beli2019FinalStepLaws` class has been removed. The legacy
`GoodBONGRepresentationLaws` class still exists for compatibility, but
neither `beli2019Theorem21` nor `beli2019Theorem21_prime` assumes it.

Non-default mathematical interfaces that remain in the public theorem are
catalogued in `03_hidden_assumptions.md` and
`07_trust_and_axiom_report.md`.
