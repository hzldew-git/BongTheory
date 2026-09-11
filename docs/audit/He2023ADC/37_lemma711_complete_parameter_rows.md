# Lemma 7.11 complete normalized parameter rows

Status: `FULLY_FORMALIZED` / `PROVISIONAL_MATCH`.

Code checkpoint: `832d10c95f56dd3ae80fc4f912de248f25316da1`.

## Source authority

The sole semantic authority is the publisher version of record:

- Zilong He, *On n-ADC integral quadratic lattices over algebraic number
  fields*, *Documenta Mathematica* 30 (2025), no. 4, 981--1022;
- DOI: <https://doi.org/10.4171/DM/1003>;
- publisher PDF SHA-256:
  `E26190C88B16624DCCB7F269C6C3FFDA02BC6830677A5BC0C8E0AD48A36E72D6`.

Lemma 7.11 and its proof occur on p. 1011. The post-publication arXiv
revision remains comparison-only.

## OCR correction and parameter normalization

The publisher formula has `d(a_[1,4])=infinity`. Plain-text extraction turns
the infinity glyph into `1`; the following proof explicitly uses
`a_[1,4] in F^(times 2)`. The formal hypothesis

`defectOrder (a.prefixProduct 4) = top`

therefore records the source mathematics, not the OCR output.

The source proof writes every parameter as `c=epsilon` or `epsilon*pi` with
`epsilon` a unit. The combined theorem `heADC2025Lemma711` has exactly these
two rows, universally quantified over a valuation unit `delta`. Thus the
normalization changes the presentation but omits no source square class.

## Unit row

For `N_2^3(delta)`, the source profile is

`S_1=0, S_2=2-2e, S_3=0`.

The formal target BONG is `heHuLemma311OddSecondUnitTail`. Its auxiliary unit
`kappa` and the identity `d(kappa)=2e-1` are constructed internally by
`exists_unit_defectOrder_eq_twoE_sub_one`; they are not public assumptions.

`heADC2025Lemma711Even_previousDefect_ge` combines:

1. the exact mixed-prefix defect supplied by Lemma 7.6(ii);
2. the source adjacent-pair bound from Proposition 2.7(iv); and
3. truncated-defect domination.

It obtains the lower bound `2e-1` required in equation (7.2).
`heADC2025Lemma711Even_defectTrigger` then uses `R_5>1=S_3+1` to prove the
literal condition-(iii) trigger at paper index `4`.

For non-representation, the square-prefix hypothesis identifies the first
four source coefficients with the split quaternary class. The codimension-one
exactness theorem for the two ternary space classes shows that a source prefix
representing the first class cannot also represent the second. The actual
unit-row BONG is transported to that second class, yielding
`heADC2025Lemma711Even_not_represents`. The conjunction is exported as
`heADC2025Lemma711Even`, with a direct logical-failure wrapper
`heADC2025Lemma711Even_not_centralRepresentationConditionsPrime`.

## Unit-times-uniformizer row

For `N_2^3(delta*pi)`, the source profile is

`S_1=0, S_2=-2e, S_3=1`.

The corrected rank-five instance of He--Hu Lemma 5.7 proves the trigger and
prefix non-representation. It is exposed by `heADC2025Lemma711Odd` and by the
second conjunct of `heADC2025Lemma711`. The separate theorem
`heADC2025Lemma711_exists_represented_oddTarget` selects an actually
represented target in this row, and `heADC2025Lemma711_badBranch_impossible`
continues to discharge exactly the exceptional branch used in the necessity
proof of Lemma 7.5(iii).

## Statement-strength conclusion

The combined theorem retains the source hypotheses `n=3`, the alternating
rank-five order profile, square four-entry prefix, and `R_5>1`. Its conclusion
contains both parts of the failure of Theorem 3.6(iii): the numerical trigger
and failure of the required prefix representation. The internally installed
classification instance is the repository's proved implementation, not a
caller-supplied law. The result is therefore `LOGICALLY_EQUIVALENT` after the
source's own two-row square-class normalization.

This completion does not alter the independent Lemma 7.13 issue. Its printed
per-target conclusion remains stronger than the simultaneous-failure
argument in the publisher proof.

## Mechanical trust checks

The Lemma 7.11 module, canonical paper entry, and focused audit compile
directly with Lean 4.32.1. The transitive axiom reports for
`heADC2025Lemma711Even` and `heADC2025Lemma711` contain exactly `propext`,
`Classical.choice`, and `Quot.sound`. The enforcing focused gate reports
`AXIOM_GATE_PASS: 59204 declarations checked`. The comment-aware scanner
checks 2,727 tracked Lean files and finds no forbidden proof token outside
comments. All changed Lean source lines satisfy the 100-column limit, and
`git diff --check` passes.

These are local checks at the stated code commit. Exact-revision Review Kit
CI, release promotion, and independent human sign-off remain separate gates.

## Coverage consequence

Section 7 now has ten fully formalized numbered items: Theorems 7.1 and 7.4
and Lemmas 7.5--7.12. Lemma 7.13 is formalized only in the weaker quantifier
form supported by its proof. Theorem 7.2, Remark 7.3, Lemmas 7.14--7.15,
Definition 7.16, Remark 7.17, Lemmas 7.18--7.20, and Corollary 7.21 remain
pending.

Author decision: unsigned. Domain-expert decision: unsigned.
Formalization-expert decision: unsigned.
