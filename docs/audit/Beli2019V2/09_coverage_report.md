# Coverage Report

> Historical snapshot notice (28 August 2026): the inventory remains useful,
> but the conditional-coverage verdict below is superseded by
> `15_unconditional_completion_audit.md`.

## Paper inventory coverage

| Layer | Inventory | Located in formal project | Semantic status |
|---|---:|---:|---|
| Definitions | 11 | 11 section-level counterparts | Mapped; key definitions reviewed |
| Theorem-like results | 96 | 96 section-level counterparts or decomposed proof families | Mapped; main spine reviewed |
| Numbered notes | 31 | 31 mapped to supporting definitions/lemmas or explicit proof steps | Mapped; not all have one named declaration |
| Total | 138 | 138 inventoried and section-mapped | Structural coverage complete |

“Located” does not mean that one paper item equals one Lean declaration.
Long paper lemmas, especially 6.7, 6.9, 7.9, 8.8, 8.14, 9.3, 9.6, and 9.12,
are intentionally split into many data structures, arithmetic lemmas,
rank-specific endpoints, and assembly theorems.

## Section coverage

| Section | Formal coverage | Main caveat |
|---|---|---|
| 1 | Truncated defects, order poset, duality, and weight sequence | Relies on foundational BONG/defect laws |
| 2 | All invariants, Lemma 2.16, rank completion, and main conditions | Deep complement is now constructed; positive-rank scope remains |
| 3 | Approximation theory and BONG independence | Classification/cancellation inputs remain parameters |
| 4 | Comparison and transitivity architecture | `Beli2019SectionFourLaws` is constructed; lower-level legacy Section 4 inputs remain parameters |
| 5 | Index-\(\mathfrak p\) analysis and prefix extension | One-prime-step data remains `Beli2019SectionFiveLaws` |
| 6 | Type classification and complete alpha/order profiles | Unary-binary Jordan calculation remains a parameter |
| 7 | Ordinary and exceptional volume reductions | Uses earlier law boundary but no final-step oracle |
| 8 | Defect/Hilbert choices, scaling, and obstruction analysis | Field and scaling constructions remain parameters |
| 9 | Rank-three, rank-four, and higher-rank final cases | Concrete descent; local interfaces persist transitively |

## Main-theorem proof coverage

- Necessity: present as `beli2019_necessity`.
- Equal-rank sufficiency: present as
  `not_counterexample_of_equalRank_complete`.
- Unary base: present.
- Binary base: present in `Beli2019RankTwoComplete`.
- Section 7 descent: present in `Beli2019SectionSevenReduction`.
- Lemma 9.3 ordinary head: present at all relevant ranks.
- Lemma 9.6 exceptional head: present at all relevant ranks.
- Lemma 9.12 residual descent: present at all relevant ranks.
- Strict-rank completion: present.
- Original theorem: present.
- Revised-v2 theorem: present.
- Theorem-level final-step oracle: removed.

## Coverage metrics and their limits

The project has 100% inventory and section-level mapping of the 138 numbered
paper objects. It does not claim 138 independently human-verified
statement matches. The decomposition is too fine for a reliable automatic
one-to-one count, and no independent author review has confirmed every
quantifier and endpoint.

The main theorem is logically complete only relative to its explicit law
parameters. Therefore:

- syntactic proof coverage: complete at the planned modular boundary;
- unconditional paper coverage: incomplete;
- semantic project grade: C.
