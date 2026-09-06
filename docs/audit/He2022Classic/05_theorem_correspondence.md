# Theorem correspondence

| Source | Formal endpoint | Correspondence |
|---|---|---|
| Standing definition of classic integrality | `IsClassicIntegral` | Direct normalization bridge; review pending |
| Maximal testing principle used in Theorem 1.3 | `heClassicMaximalTestingReduction` | Abstract core proved |
| Theorem 1.1 | `Bong.BONG.GoodBONG.he2022ClassicTheorem11` | Both directions proved for n >= 2 and arbitrary source rank; semantic assessment remains provisional |
| Theorem 1.3 explicit lists and minimality | indexed models, `he2022ClassicLemma74_even`, and `he2022ClassicTheorem13_even_literalMinimal` | `PARTIAL_FORMALIZATION`: the complete even testing equivalence and every even deletion witness are checked; odd sufficiency/minimality and unconditional numerical counting remain |
| Theorem 1.5 | `Bong.BONG.GoodBONG.he2022ClassicTheorem15_allRanks` | `PARTIAL_FORMALIZATION`: complete local implication for n >= 1; number-field localization and global discriminant clause excluded |
| Theorems 1.7, 1.8, 1.9 | no complete published endpoint | `NOT_FORMALIZED` |
| Theorems 4.1, 5.1 | `he2022ClassicTheorem41`, `he2022ClassicTheorem51` | Checked local parity criteria used in Theorem 1.1 |
| Corollary 6.3 | `he2022ClassicCorollary63_even` | `PARTIAL_FORMALIZATION`: even branch |
| Lemma 7.1(ii), literal disjunction | `he2022ClassicLemma71ii_literal_disjunction_fails` | Refuted for e > 1; no positive correspondence is asserted |
| Lemma 7.4 | `he2022ClassicLemma74_even` | `PARTIAL_FORMALIZATION`: even branch only |
| Lemma 7.7 | `he2022ClassicLemma77_boundary_conditions`, the two condition packages, and the two bundled representation endpoints | `FULLY_FORMALIZED`; correspondence remains provisional pending human review |
| Lemma 7.10(i)--(iii) | the three exceptional deletion-witness endpoints, `he2022ClassicLemma710iii_publishedC_deletionWitness`, and `he2022ClassicLemma710_publishedEven_deletionWitness` | `FULLY_FORMALIZED` on the literal published even index; correspondence remains provisional pending human review |

Theorem names in abbreviated rows are resolved by the canonical paper and
audit modules. Source differences and the distinction between a repaired
helper and the printed assertion are mandatory parts of this correspondence;
see `SOURCE_DELTA.md`. No row is marked `VERIFIED_MATCH` without human approval.
