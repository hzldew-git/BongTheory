# Theorem correspondence

Current semantic authority is author-corrected v6 (Report 44). This table was
first compiled for v5; unchanged local statements retain their checked Lean
endpoints. The historical `v5` suffixes in implementation names are not a
claim that v5 remains authoritative. Section 8 rows below must be read with
Report 44's explicit ambient/basis-transport and arithmetic exclusions.

| Source | Formal endpoint | Correspondence |
|---|---|---|
| Standing definition of classic integrality | `IsClassicIntegral` | Direct normalization bridge; review pending |
| Maximal testing principle used in Theorem 1.3 | `heClassicMaximalTestingReduction` | Abstract core proved |
| Theorem 1.1 | `Bong.BONG.GoodBONG.he2022ClassicTheorem11` | Both directions proved for n >= 2 and arbitrary source rank; semantic assessment remains provisional |
| Theorem 1.3 explicit lists and minimality | indexed models, `he2022ClassicTheorem13_even_literalMinimal`, `he2022ClassicTheorem13_odd_literalMinimal_v5`, and the counts in Report 21 | `FULLY_FORMALIZED_PROVISIONAL_MATCH` to unchanged author-corrected v6: both testing equivalences, every deletion witness, and all numerical counts are checked |
| Theorem 1.5 | `Bong.BONG.GoodBONG.he2022ClassicTheorem15_allRanks`, `HeClassic2024NumberFieldGlobalData.sectionEightLaws`, `HeClassic2024GlobalData.SectionEightLaws.he2022ClassicTheorem15_discriminantOdd` | local implication fully proved for n >= 1; the discriminant theorem, finite-place bridge, and all arithmetic compatibility fields are derived once a place equivalence is supplied (Reports 32, 34, and 36); the concrete global lattice/localization model and place equivalence remain |
| Theorems 1.7, 1.8, 1.9 | `HeClassic2024GlobalData.SectionEightLaws.he2022ClassicTheorem17_even`, `he2022ClassicTheorem17_of_localAdjacentDefectsLarge`, `HeClassic2024ExtensionData.Lemma83Laws.he2022ClassicTheorem18_even`, `HeClassic2024GlobalData.SectionEightLaws.he2022ClassicTheorem19` | `CONDITIONAL_FORMALIZATION`: Theorems 1.7--1.8 have v6-matching `n >= 2` even endpoints (Reports 33 and 28). Theorem 1.7 also has a parity-independent final contradiction with its missing local-defect calculation explicit; Theorem 1.9's finite-place and local-to-global conclusions are derived from lower laws (Reports 31 and 29); the concrete discriminant equivalence and ramified-prime witness are proved in Report 32; remaining global/completion instances are pending |
| Theorems 4.1, 5.1 | `he2022ClassicTheorem41`, `he2022ClassicTheorem51` | Checked local parity criteria used in Theorem 1.1 |
| Corollary 6.3 | `he2022ClassicCorollary63_even`, `exists_he2022ClassicCorollary63_odd_counterexample` | `V6_EVEN_STATEMENT_PROVED`: an `e=2`, `n=3` counterexample refutes only the obsolete unrestricted v5 statement; Reports 24 and 26 |
| Lemma 7.1 | the `he2022ClassicLemma71v5_*` family and the retained `he2022ClassicLemma71ii_literal_disjunction_fails` regression | `FULLY_FORMALIZED_PROVISIONAL_MATCH` to unchanged v6; the regression applies only to the obsolete broader publisher clause |
| Lemma 7.4 | `he2022ClassicLemma74_even`, `he2022ClassicLemma74_odd_v5` | `FULLY_FORMALIZED_PROVISIONAL_MATCH` to unchanged v6 in both parity branches |
| Lemma 7.7 | `he2022ClassicLemma77_boundary_conditions`, the two condition packages, and the two bundled representation endpoints | `FULLY_FORMALIZED`; correspondence remains provisional pending human review |
| Lemma 7.10(i)--(iii) | the three exceptional deletion-witness endpoints, `he2022ClassicLemma710iii_publishedC_deletionWitness`, and `he2022ClassicLemma710_publishedEven_deletionWitness` | `FULLY_FORMALIZED` on the literal published even index; correspondence remains provisional pending human review |
| Lemma 8.1; Proposition 8.2; Lemma 8.3 | `HeClassic2024NumberFieldLocalExtension.completionMap_valuation`, `completionAdicOrder_liesOver`, `completionQuadraticDefect_scale`, `completionGoodBONGCoefficients_map`, `completionLemma81Laws`, `HeClassic2024NumberFieldBONGBridge.goodBONG_mappedValues_haveRealization`, `HeClassic2024NumberFieldBONGBridge.mappedValues_order_monotone_of_lower`, `HeClassic2024Carrier.he2022ClassicLemma83_carrier_eq_of_basisTransport`, the `he2022ClassicLemma81*` endpoints, `Proposition82Laws.he2022ClassicProposition82_positive`, the two `SectionEightLaws` Proposition 8.2 wrappers, `HeClassic2024NumberFieldGlobalData.sectionEightLaws`, and `he2022ClassicLemma83_even` | `MIXED`: Lemma 8.1(i)--(ii) are proved for actual finite completions; v6 part (iii) has a concrete upper-lattice good-BONG realization in standard diagonal ambient, with the literal scalar-extension ambient isometry still missing. Upper-order monotonicity and the abstract carrier-equality deduction for v6 Lemma 8.3 are checked; concrete basis transport and its local obstruction are not. Proposition 8.2 and remaining global statements depend on explicit but uninstantiated globalization, localization, and arithmetic packages. No odd v6 Lemma 8.3 claim is asserted; Report 44 gives the current source map |

Theorem names in abbreviated rows are resolved by the canonical paper and
audit modules. Source differences and the distinction between v5 and obsolete
comparison text are mandatory parts of this correspondence;
see `SOURCE_DELTA.md`. No row is marked `VERIFIED_MATCH` without human approval.
