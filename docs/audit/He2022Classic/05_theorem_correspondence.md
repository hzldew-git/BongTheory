# Theorem correspondence

| Source | Formal endpoint | Correspondence |
|---|---|---|
| Standing definition of classic integrality | `IsClassicIntegral` | Direct normalization bridge; review pending |
| Maximal testing principle used in Theorem 1.3 | `heClassicMaximalTestingReduction` | Abstract core proved |
| Theorem 1.1 | `Bong.BONG.GoodBONG.he2022ClassicTheorem11` | Both directions proved for n >= 2 and arbitrary source rank; semantic assessment remains provisional |
| Theorem 1.3 explicit lists and minimality | indexed models, `he2022ClassicTheorem13_even_literalMinimal`, `he2022ClassicTheorem13_odd_literalMinimal_v5`, and the counts in Report 21 | `FULLY_FORMALIZED_PROVISIONAL_MATCH` to author-corrected v5: both testing equivalences, every deletion witness, and all numerical counts are checked |
| Theorem 1.5 | `Bong.BONG.GoodBONG.he2022ClassicTheorem15_allRanks`, `HeClassic2024GlobalData.SectionEightLaws.he2022ClassicTheorem15_discriminantOdd` | local implication fully proved for n >= 1; final all-dyadic-primes deduction is a `CONDITIONAL_FORMALIZATION` over explicit number-field laws |
| Theorems 1.7, 1.8, 1.9 | `HeClassic2024GlobalData.SectionEightLaws.he2022ClassicTheorem17`, `HeClassic2024ExtensionData.Lemma83Laws.he2022ClassicTheorem18`, `HeClassic2024GlobalData.SectionEightLaws.he2022ClassicTheorem19` | `CONDITIONAL_FORMALIZATION`: source logic proved from explicit localization, extension, discriminant, and strong-approximation inputs; concrete instances are pending; Theorem 1.7 lacks its claimed odd calculation, and Theorem 1.8 depends on the unsupported odd Lemma 8.3 step |
| Theorems 4.1, 5.1 | `he2022ClassicTheorem41`, `he2022ClassicTheorem51` | Checked local parity criteria used in Theorem 1.1 |
| Corollary 6.3 | `he2022ClassicCorollary63_even`, `exists_he2022ClassicCorollary63_odd_counterexample` | `SOURCE_STATEMENT_FALSE_IN_ODD_RANK`: the even branch is proved, while an `e=2`, `n=3` counterexample refutes the unrestricted statement; Reports 24 and 26 |
| Lemma 7.1 | the `he2022ClassicLemma71v5_*` family and the retained `he2022ClassicLemma71ii_literal_disjunction_fails` regression | `FULLY_FORMALIZED_PROVISIONAL_MATCH` to v5; the regression applies only to the obsolete broader publisher clause |
| Lemma 7.4 | `he2022ClassicLemma74_even`, `he2022ClassicLemma74_odd_v5` | `FULLY_FORMALIZED_PROVISIONAL_MATCH` to v5 in both parity branches |
| Lemma 7.7 | `he2022ClassicLemma77_boundary_conditions`, the two condition packages, and the two bundled representation endpoints | `FULLY_FORMALIZED`; correspondence remains provisional pending human review |
| Lemma 7.10(i)--(iii) | the three exceptional deletion-witness endpoints, `he2022ClassicLemma710iii_publishedC_deletionWitness`, and `he2022ClassicLemma710_publishedEven_deletionWitness` | `FULLY_FORMALIZED` on the literal published even index; correspondence remains provisional pending human review |
| Lemma 8.1; Proposition 8.2; Lemma 8.3 | the `he2022ClassicLemma81*` endpoints, `he2022ClassicProposition82_positive`, `he2022ClassicProposition82`, and `he2022ClassicLemma83` | `CONDITIONAL_FORMALIZATION`: all deductions and premises are typed, but their concrete local-extension and number-field instances remain pending; the odd proof of Lemma 8.3 invokes the false odd extension of Corollary 6.3 and requires replacement |

Theorem names in abbreviated rows are resolved by the canonical paper and
audit modules. Source differences and the distinction between v5 and obsolete
comparison text are mandatory parts of this correspondence;
see `SOURCE_DELTA.md`. No row is marked `VERIFIED_MATCH` without human approval.
