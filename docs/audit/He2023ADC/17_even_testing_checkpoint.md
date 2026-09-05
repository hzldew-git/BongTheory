# Lemma 6.4: even-rank testing checkpoint

Date: 2026-09-05. Source: Zilong He, *On n-ADC integral quadratic lattices
over algebraic number fields*, Doc. Math. 30 (2025), Lemma 6.4, pp. 998--999.
The sole semantic authority is the publisher PDF, SHA-256
`E26190C88B16624DCCB7F269C6C3FFDA02BC6830677A5BC0C8E0AD48A36E72D6`.
The Section 6 standing assumptions are dyadic F, even n at least two, an
integral source lattice of rank at least n, and a supplied good BONG.

## Frozen checkpoints and coverage

| Code checkpoint | Source scope | Independent AI verdict |
|---|---|---|
| `b8515ff1292af4fd1aab2d1d42d165b96cd2fc55` | Three representation support lemmas; no completed numbered source result | No correctness or scope blocker |
| `c06742fd646b5eda4fc60c046ff0a0490027b71a` | Lemma 6.4(ii) | `FULLY_FORMALIZED` / `PROVISIONAL_MATCH` |
| `cd5da6cab7b8fcdff1991a138ce2f570d16bdbb3` | Lemma 6.4(i) | `FULLY_FORMALIZED` / `PROVISIONAL_MATCH` |
| `e2f847a2a611af0adaf0e73d3909e94086cfe984` | Lemma 6.4(iii) | `FULLY_FORMALIZED` / `PROVISIONAL_MATCH` |
| `d94cc797ad8ed83c53447c139b496d5a2ca8f4fb` | Lemma 6.4(iv), completing all four clauses | `FULLY_FORMALIZED` / `PROVISIONAL_MATCH` |

At the last frozen checkpoint, all four clauses of the numbered Lemma 6.4
have complete proofs and independent AI correspondence checks. Local proof
coverage is `FULLY_FORMALIZED`, with `PROVISIONAL_MATCH` semantics. This is
proof-coverage accounting, not release promotion: exact-revision clean-kit
CI and the other roadmap gates remain pending. The four clauses count as
one numbered paper result, not four. None of Theorems 6.1--6.2, the
remaining Section 6 lemmas, Section 7, or the global
classification is completed by this checkpoint.

## Author-facing statements and correspondence

Write n = 2k+2. Lean coordinate i is the paper's coordinate i+1. The target
N lattices are the chosen norm-maximal lattices in Definition 4.1's W spaces.
Statements involving an arbitrary isometric copy follow by integral-isometry
transport; the proofs below are on the actual named representatives.

| Clause | Mathematical statement proved | Public endpoint |
|---|---|---|
| (i) | Representing N_1^n(1) or N_1^n(Delta) forces alternating orders 0,-2e through n. If the next order exists and is positive, the raw defect of the signed n-prefix is infinity or 2e, respectively. | `Bong.BONG.GoodBONG.heADC2025Lemma64i` |
| (ii) | Representing both first-column tests forces the same alternating prefix and next order zero. The source is necessarily of strictly larger rank. | `Bong.BONG.GoodBONG.heADC2025Lemma64ii` |
| (iii) | Representing N_2^n(Delta), or N_2^n(1) when n is at least four, forces an alternating head through n-2 and final pair (0,-2e), (0,2-2e), or (1,1-2e). | `Bong.BONG.GoodBONG.heADC2025Lemma64iii` |
| (iv) | Representing one of N_1^n(1), N_1^n(Delta), N_2^n(Delta), and one of N_1^n(kappa), N_2^n(kappa), where kappa is a valuation unit of defect 2e-1, forces the next order to be 0, 1 or 2. | `Bong.BONG.GoodBONG.heADC2025Lemma64iv` |

These are necessary conditions on representation, as in the paper. They are
not sufficient ADC criteria and are not advertised as classification
biconditionals. The formal statements translated into mathematical English
have the same assumptions, quantifiers and conclusions as the four clauses,
with the index-existence condition below made explicit. Logical strength for
each completed clause: `LOGICALLY_EQUIVALENT` under that index convention.

## Definitions, auxiliary data, and trust boundaries

`heADCMaximalGoodBONG` constructs a good BONG on each actual named maximal
lattice. The first- and second-column order lemmas obtain its orders from
the already proved published Lemma 4.11 criteria and reflexive isometries.
No caller-supplied order profile is substituted for these constructions.

The determinant of W_1^n(c) is (-1)^(k+1)c. Exact diagonalization and
determinant invariance identify its square class with the BONG value product.
The two first-column determinant classes are distinct because Delta has
finite defect 2e and is nonsquare. The signed source prefix in clause (i) is
exactly (-1)^(n/2) times a_1 through a_n; its defect is the raw relative
quadratic defect in extended naturals, not a capped bracketed defect.

The three support lemmas in `He2023ADCEvenRepresentationBounds.lean` use
actual integral representations. They extend the needed rank range to
codimension one via a constructed deep integral completion and Beli's
endpoint-aware Corollary 2.10. They are not claimed to extend every older
abstract order/defect interface with the same hypotheses.

The public paper endpoints have the dyadic context, ordinary quadratic-space
and lattice data, source good BONG, integrality and the stated actual
representations. The order profiles, determinant separation, representation
completion data and project-law results are internally proved. In clause
(iii), `HeHuEvenSecondDefined` means positive tower length or a nonsquare
parameter; for c=1 or Delta this excludes exactly N_2^2(1).

In part (iv), the caller's kappa conditions are exactly the source's stated
valuation-unit and raw finite-defect conditions. `heADCKappaSharpDomain`
derives its nonexceptional class; `heADCKappaTest_lastOrders` proves the
last orders of both actual kappa targets from the published profile criteria.
The five last orders are -2e, -2e, 1-2e, 2-2e and 2-2e. Both columns carry
the same signed parameter class. Different raw parameter defects imply
different determinant classes, with the common sign cancelled by a square.

## Boundary and adversarial checks

- n=2 is k=0 throughout; codimension one is included.
- In clause (i), rank at least n is derived. The unconditional order assertion
  retains equal rank. The stronger rank inequality is quantified only inside
  the conditional conclusion, because R_(n+1) is defined only if that index
  exists; it is not an extra assumption on the order assertion.
- In clause (ii), representing two ambient spaces of different determinant
  classes is impossible in equal rank. Strict rank, and therefore existence
  of R_(n+1), is derived from this contradiction.
- In clause (iii), the binary discriminant head is empty. The printed proof's
  preceding head indices are not used there. If p,q are the final orders,
  p >= 0, q-p >= -2e and p+q <= 2-2e force p in {0,1}. The remaining forbidden
  value is ruled out because an odd adjacent order gap must be positive.
- At e=1 the three final pairs in (iii) are (0,-2), (0,0), and (1,-1).
- Infinity in clause (i) is retained as the top value. No conversion from
  infinity to a finite natural is used to obtain its conclusion.
- In clause (iv), all five targets are defined at n=2. The finite kappa
  defect is established before converting it with `toNat`; e>0 justifies
  natural subtraction. Equal rank is impossible by determinant separation.
  A next order greater than two would force the two determinant classes
  to agree. Integrality supplies the lower bound zero.

## Independent review and author card

A separate read-only AI reviewer inspected each frozen implementation,
source statement, proof route and elaborated public signature. It independently
compiled the frozen source with queries, the canonical entry and complete
audit for each of (i), (ii), (iii), and (iv). No semantic mismatch or circularity
was found. The reviewer confirmed the actual named targets, derived rank
inequalities, precise signs, raw-defect convention, and boundary arguments.
At the final frozen commit it also verified that the previously audited
clauses and support files were unchanged. Its combined verdict covers
4/4 clauses of Lemma 6.4, not the remaining Section 6 classification.
This is independent AI review, not human author or domain-expert sign-off.

Author/domain-expert questions: confirm the one-based/zero-based dictionary,
the existing-index interpretation of clause (i), and the empty binary head
in (iii). Formalization-expert questions: check determinant transport and
the complete cross-gap lemma at codimension one, and the finite-defect
arithmetic and both named kappa rows in (iv).

Author decision, name, date and signature: not supplied. Domain-expert and
human formalization-expert approval: not supplied.

## Reproducibility and release status

Lean 4.32.1; dependencies are pinned by the committed Lake manifest.
All four new paper modules, canonical entry and expanded audit passed local
checks. The six new axiom queries for (ii), four for (i), three for (iii), and
seven for (iv) contain exactly `propext`, `Classical.choice`, and `Quot.sound`. The support
module's three queries also use only those axioms. No admitted proof, new
axiom or native-evaluation mechanism is present in these modules.

These are cached local checks. Existing mathlib, aesop and batteries worktree
changes were preserved; the checks are not a clean-environment certificate.
The older successful published-profile CI artifact contains none of this
checkpoint. Each newer packaged revision still needs its own clean-kit CI.
Whole-paper coverage grade: C. Whole-paper verdict: `NOT_COMPLETE`.
