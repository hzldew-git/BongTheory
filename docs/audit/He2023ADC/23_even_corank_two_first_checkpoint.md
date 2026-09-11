# Lemma 6.8(i)--(ii): first-column corank-two endpoint classes

Date: 2026-09-05. Sole authority: Zilong He, *On n-ADC integral quadratic
lattices over algebraic number fields*, Doc. Math. 30 (2025), Lemma 6.8,
p. 1002, DOI 10.4171/DM/1003. The publisher PDF hash was reconfirmed:
`E26190C88B16624DCCB7F269C6C3FFDA02BC6830677A5BC0C8E0AD48A36E72D6`.

## Frozen scope and verdict

Code: `b624d40be62d4e939f28715e631ce7c42a9e642e`.
Modules: `He2023ADCEvenCorankTwoTests`, `He2023ADCSignedDeterminant`,
and `He2023ADCEvenCorankTwoFirst`, under `Bong/Bong/`.

The two clauses individually have local proof status `FULLY_FORMALIZED`
and semantic status `PROVISIONAL_MATCH` after separate read-only AI review.
The whole Lemma 6.8 is `PARTIALLY_FORMALIZED`, 2/6 clauses. Clauses
(iii)--(vi) are not supplied by this checkpoint. Section 6 still has 5/12
fully completed numbered items, not six. Whole-paper Grade C and
`NOT_COMPLETE` are unchanged; no human approval is supplied.

## Statement correspondence

Put n=2k+2 and m=n+2. The source is an arbitrary full lattice over a field
in the repository's dyadic context, and is n-ADC in the actual lattice sense.

| Published clause | Ambient model | Additional restriction | Public endpoint | Conclusion |
|---|---|---|---|---|
| 6.8(i) | W_1^(n+2)(1) | none beyond even n>=2 | `Bong.Lattice.heADC2025Lemma68i` | actual integral isometry to N_1^(n+2)(1) |
| 6.8(ii) | W_1^(n+2)(Delta) | k>0, exactly n>=4 | `Bong.Lattice.heADC2025Lemma68ii` | actual integral isometry to N_1^(n+2)(Delta) |

Both statement relationships are `LOGICALLY_EQUIVALENT` on the published
even-rank local scope. Rank follows from the ambient isometry, integrality
from n-ADC, and a good BONG is constructed internally. The conclusions are
not merely ambient isometry, matching orders, or maximality in a different
space. No supplied order profile, test table, representation criterion,
classification law or maximality conclusion occurs in either public type.

## Proof and normalization audit

An explicit hyperbolic extension embeds the smaller same-parameter W_1
space. For distinct parameter square classes, the already proved dyadic
codimension-two theorem gives a genuine ambient embedding. Its determinant
test is checked with the signs (-1)^(k+1) and (-1)^(k+2); their relative
minus sign is essential. The n-ADC definition then yields representation
of each actual named maximal lattice.

For (i) these are N_1^n(1), N_1^n(Delta), N_2^n(Delta). For (ii) they are
N_1^n(1), N_1^n(Delta), N_2^n(1). Lemma 6.4(ii) derives the alternating
first n orders and R_(n+1)=0. If R_(n+2)>=2-2e, Proposition 3.4 rules out
alpha_(n+1)=0. Lemma 6.7 gives the raw terminal defect 1-R_(n+2)<2e.
Proposition 3.5 first supplies the capped signed-head bound; passing to
the raw defect is justified by the minimum inequality.

The signed full product factors as the signed head times the negative
last adjacent product. Strict domination makes its raw defect the small
terminal defect. Actual ambient isometry, however, identifies the full
signed determinant class with 1 or Delta, whose defect is at least 2e.
This contradiction gives R_(n+2)<2-2e. The good-BONG gap bound and
Corollary 3.2(i) exclude the remaining odd value 1-2e, so R_(n+2)=-2e.
The complete profile then satisfies the proved published Lemma 4.11(i),
which yields the required integral lattice isometry.

The full determinant transport uses the entire BONG product, never a
proper prefix standing in for the ambient determinant. The signed factor
is exactly (-1)^((n+2)/2). Arbitrary ramification remains quantified.

## Boundary checks and alternative proof

The paper proves (i) at n=2 using separate 2-universality results. The
formal proof instead uses the same three actual tests uniformly at n=2.
The Delta second-column binary space is defined, so this route is valid
and never invokes the undefined N_2^2(1). Clause (ii) deliberately retains
n>=4. At e=1 the strict defect comparison remains valid, and the excluded
odd terminal value is negative. No endpoint or sign restriction is lost.

The reviewer checked the alternative route, the actual test embeddings,
the full-prefix casts and determinant signs, the raw/capped distinction,
the e=1 and n=2 cases, and the final lattice identification. No circular
dependency or hidden law premise was found.

## Trust, reproducibility and author card

Main-agent and independent replay passed all three frozen source modules,
the canonical entry and the complete ADC audit. The 6+4+5 new support/public
declarations have exactly `propext`, `Classical.choice`, `Quot.sound` in
all 15 queried transitive sets. All new source lines satisfy the 100-column
limit. The 23 supplemental scanner tests and 2678-source scan also pass;
these textual checks do not replace compiled dependency enforcement.

These are cached-local checks with existing modified mathlib, aesop and
batteries worktrees preserved. The earlier f6f7485/c82668b clean-kit run
includes full Lemma 6.7 but does not contain this addition. An independent
exact-revision kit, clean CI and appropriate release remain required.

Author question: confirm the two actual lattice-isometry conclusions and
the retained n>=4 boundary in (ii). Domain reviewer question: review the
uniform n=2 replacement proof and signed-determinant domination. Lean
reviewer question: review rank casts, imported theorem hypotheses and full
product transport. Author name, decision, date and signature: not supplied.
Independent human domain and formalization approvals: not supplied.
