# Lemma 6.7: terminal alpha alternatives and equality of raw and capped defects

Date: 2026-09-05. Authority: Zilong He, *On n-ADC integral quadratic
lattices over algebraic number fields*, Doc. Math. 30 (2025), Lemma 6.7,
pp. 1001--1002. Publisher PDF SHA-256, independently reconfirmed:
`E26190C88B16624DCCB7F269C6C3FFDA02BC6830677A5BC0C8E0AD48A36E72D6`.

## Frozen scope and verdict

Code: `b0f832e5ff4dd1fe0f305371c029ce2015b004e5`.
Module: `Bong/Bong/He2023ADCEvenCentralAlpha.lean`.
Both numbered endpoints are `FULLY_FORMALIZED / PROVISIONAL_MATCH` after
separate read-only AI review. This is 2/2 clauses of one numbered lemma.
Section 6 has 5/12 locally complete numbered results: Theorem 6.1 and
Lemmas 6.4--6.7. Theorem 6.2 and the remaining seven items are not completed
by this checkpoint. Human approval and exact-revision clean-kit CI remain open.

## Paper and formal statements

Let n=2k+2, m=n+2, and let the integral source lattice have a good BONG
whose first n orders alternate 0,-2e. Assume R_(n+2) >= 2-2e.

| Clause | Additional alternative | Actual represented lattice | Public endpoint |
|---|---|---|---|
| (i), n >= 2 | R_(n+1) even, or raw signed-prefix defect 2e | N_2^n(Delta) | `Bong.BONG.GoodBONG.heADC2025Lemma67i` |
| (ii), n >= 4 | R_(n+1) even, or raw signed-prefix defect infinity | N_2^n(1) | `Bong.BONG.GoodBONG.heADC2025Lemma67ii` |

Both conclude exactly:

    alpha_(n+1) = 0, or
    alpha_(n+1) = 1 and
    raw d(-a_(n+1)*a_(n+2)) = capped d[-a_(n+1,n+2)] = 1-R_(n+2).

`HeADCEvenCentralAlphaAlternatives` names this proposition without changing
its content. The raw defect is `adjacentDefect`; the capped one is
`heADCAdjacentCappedDefect`. Both lie in rationally embedded extended defect
orders. Infinity remains distinct from every finite value. The signed even
prefix has sign (-1)^(k+1), exactly (-1)^(n/2).

Primary statement relationship: `LOGICALLY_EQUIVALENT`. The hypothesis is
integral lattice representation of the actual named maximal model, not
merely representation of its ambient space. The target BONG and integrality
are constructed internally. No target order profile, zero next order,
representation criterion, project law or desired defect equality is assumed.

## Proof fidelity

Actual representation satisfies the published Theorem 3.6 package. If the
capped adjacent defect exceeded 1-R_(n+2), Lemma 6.6 would give its literal
central trigger and failure of the required prefix representation at n+1.
This contradicts that exact central condition; the older auxiliary-alpha
trigger is not substituted without its equivalence hypotheses.

Source integrality gives R_(n+1) >= 0. The proved capped adjacent alpha
bound then gives alpha_(n+1) <= 1. The established discreteness theorem
gives zero or one. In the one case the rearranged lower alpha bound and
the upper capped-defect bound force capped defect = 1-R_(n+2).

The alternating head gives R_n=-2e. Therefore R_(n+1)-R_n >= 2e and
Proposition 3.3 gives alpha_n >= 2e. The terminal cap alpha_(n+2) is absent
because n+2=m, precisely represented by top. Hence the capped adjacent
defect is min(raw adjacent defect, alpha_n). Since
1-R_(n+2) < 2e <= alpha_n, its equality to the finite lower value forces
the raw defect to equal the capped one. No cap is discarded without proof.

## Boundary and independent trust review

For n=2 the Delta model is defined and the preceding alpha still exists;
there is no invalid empty-prefix or zeroth-alpha reference. The square
second model is undefined at n=2, and `0 < k` in clause (ii) is exactly
n >= 4. The strict uncapping inequality remains valid at e=1. The parity
alternative never requires R_(n+1)=0.

The frozen source module, canonical entry and complete ADC audit were
independently re-elaborated with exit zero. All five new support/public
queries have exactly `propext`, `Classical.choice`, `Quot.sound`. No hidden
law premise, incomplete proof, native shortcut or circular argument was
found. These are cached-local checks, not clean-rebuild evidence.

## Author review card

Paper/formal statement and definitions: the table and alternatives above.
Assumption, quantifier and conclusion differences found by AI review: none.
Author question: confirm the actual lattice-representation hypothesis and
the raw/capped equality in the alpha-one branch. Domain-expert question:
review the strict uncapping inequality and n=2/e=1 boundaries. Formalization-
expert question: review index casts in the central-condition contradiction
and the endpoint cap convention. Author name, decision, signature and date:
not supplied. Independent human domain and Lean approvals: not supplied.

## Reproducibility and remaining deployment

Lean 4.32.1 and the committed dependency lock remain fixed. Existing modified
mathlib, aesop and batteries worktrees were preserved. The `e77a50b` local
source-only kit contains the new enforcing axiom gate but predates this
lemma. Neither it nor the much older published-profile remote artifact
certifies this addition. Its own exact-revision kit, clean CI and appropriate
release remain required. Overall paper Grade C and `NOT_COMPLETE` remain.
