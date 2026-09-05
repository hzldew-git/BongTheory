# Lemma 6.8(iii) and the n>=4 part of (iv)

Date: 2026-09-05. Sole authority: Zilong He, *On n-ADC integral quadratic
lattices over algebraic number fields*, Doc. Math. 30 (2025), 981--1022,
DOI 10.4171/DM/1003, pp. 1002--1003. Publisher PDF SHA-256:
`E26190C88B16624DCCB7F269C6C3FFDA02BC6830677A5BC0C8E0AD48A36E72D6`.

## Frozen scope and verdict

Code: `074f2cdcd63637fb6f6d8c65879e55968a1dc675`, branch
`feat/he-formalization`, Lean 4.32.1, pinned mathlib revision
`520045ab14e26149ee970e2e617ca04b09bde5d6`.

The five added modules are `AlternatingEndpointEvenOrders`,
`He2023ADCEvenEndpointExclusion`, `He2023ADCEvenSecondEndpointOrders`,
`He2023ADCEvenSecondEndpointTests`, and `He2023ADCEvenCorankTwoSecond`.
The canonical paper entry imports them and the ADC audit queries all twelve
new theorems. Unfrozen later boundary-candidate work is excluded.

| Publisher statement | Public declaration | Logical strength | Proof and semantic status |
|---|---|---|---|
| 6.8(iii), all even n>=2 | `Bong.Lattice.heADC2025Lemma68iii` | `LOGICALLY_EQUIVALENT` | `FULLY_FORMALIZED` / `PROVISIONAL_MATCH` |
| 6.8(iv), all even n>=2 | `Bong.Lattice.heADC2025Lemma68iv_of_pos` | `SPECIAL_CASE_ONLY`, n>=4 | `SPECIAL_CASE_ONLY` / `PARTIAL_FORMALIZATION` |

The completed whole clauses are now (i),(ii),(iii),(v),(vi): 5/6. Clause (iv)
also has its n>=4 proof, but is not counted as a completed whole clause.
Lemma 6.8 remains partial; Section 6 remains at 5/12 fully completed numbered
items and 1/2 classification theorems. Whole-paper Grade C and `NOT_COMPLETE`
remain. No human `VERIFIED_MATCH` approval is recorded.

## Independent extraction and comparison

The independent reviewer read and visually inspected publisher pp. 1002--1003
before extracting the frozen formal statements. Both printed clauses assume
an actual n-ADC lattice M of rank n+2 and the specified ambient W_2 class;
their conclusion identifies M integrally with the corresponding maximal N_2.
The section-wide range is even n>=2, as stated on p. 998.

The formal endpoints put n=2k+2 and retain n-ADC and an actual ambient
isometry. Rank and a good BONG on the same arbitrary lattice are constructed
internally. Norm integrality follows from ADC. The conclusion is an actual
integral lattice isometry, not equality of ambient spaces or numerical
invariants alone. For (iv), `0 < k` is explicit and narrows the range to n>=4.

The common dyadic context is a nontrivial nonarchimedean local field with
compatible normalized valuation, uniformizer and positive valuation of 2.
The distinguished Delta and its discriminant properties are proved
constructions. No unproved paper-specific classification instance is added.
The ADC universe parameters are `{u,u,u}`, as in the preceding checkpoints.

## Proof and trust audit

The complementary first/second maximal tests follow from actual ambient
embeddings and ADC. A unit kappa of defect 2e-1 is constructed internally;
its positivity and strict inequalities also hold when e=1. Lemma 6.4 supplies
the alternating head and the next-order choices 0,1,2. The signed full defect
is at least 2e, with the full determinant sign (-1)^(k+2).

The new tower lemma normalizes each even leading order by a coordinate
square in the quadratic space. This is not claimed to preserve the integral
lattice, nor to equate the original leading orders. It includes a final
leading order of 2. The resulting space classification excludes a terminal
order -2e in the second column.

For a raised final order, Lemma 6.7 gives the central alpha alternatives.
The zero case yields the excluded even-leading tower; the one case has raw
terminal defect below 2e and contradicts the full signed defect by strict
domination. Raw, capped and full defects are never identified by definition.
The remaining profile is exactly the alternating head followed by 1,1-2e.
The proved published Lemma 4.11(ii) then identifies the actual maximal model.

All intermediate test, profile, alpha and maximality premises are discharged
before the public endpoints. There is no imported target assertion, circular
ADC/maximality premise, custom axiom, unfinished proof or native shortcut.

## Boundary limitation

For (iii), n=2 uses the defined N_1^2(Delta) and N_2^2(Delta). For (iv),
the printed proof on p. 1003 invokes N_2^n(1) explicitly with n>=4, and no
separate n=2 argument follows there. The current formalization does not
invent N_2^2(1), silently alter the published statement, or infer falsity
from the omitted argument. The n=2 case remains `INSUFFICIENT_EVIDENCE`
pending a separate proof or certified obstruction. See `SOURCE_DELTA.md`.

## Reproducibility

Main and independent frozen-source replay passed all five modules, the
canonical entry and the full ADC audit. All 159 printed axiom reports stay
within the standard allowance; all 12 new theorem sets are exactly
`propext`, `Classical.choice`, `Quot.sound`. The independent focused
imported-environment gate passed on 57,667 declarations. Main also passed
the 23 supplemental scanner tests, 2687 tracked-source scan and 100-column
checks on the new code.

These are cached-local checks, not a clean build. Existing dependency
modifications were preserved. The independent reviewer also encountered
`bad tree object HEAD` when inspecting aesop/batteries Git state; neither
dependency was repaired or substituted. The earlier f6f7485/c82668b clean
kit and the later d05a898 structure-only kit both predate this increment.
Its own exact-revision clean CI and release promotion remain pending.
Reproducibility status: `PARTIALLY_REPRODUCIBLE`.

## Author and expert review card

Author: confirm the intended n=2 statement of (iv) and supply or approve its
missing independent argument. Domain expert: check the complementary tests,
even-leading tower classification and strict defect domination. Formalization
expert: check internal BONG construction and rank casts, actual lattice
transport, the endpoint cap handling and the full imported trust closure.

Independent AI review found no substantive mismatch in the certified scope.
It is not a substitute for author, domain-expert or formalization-expert
human confirmation. Names, dates and human approval records: not supplied.
