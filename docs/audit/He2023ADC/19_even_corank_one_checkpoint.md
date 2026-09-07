# Theorem 6.1: even-rank ADC lattices of corank one

Date: 2026-09-05. Authority: Zilong He, *On n-ADC integral quadratic
lattices over algebraic number fields*, Doc. Math. 30 (2025), Theorem 6.1
and its proof in Section 6. The publisher version is the sole authority,
DOI 10.4171/DM/1003, PDF SHA-256
`E26190C88B16624DCCB7F269C6C3FFDA02BC6830677A5BC0C8E0AD48A36E72D6`.

## Frozen scope and verdict

The independently reviewed proof commit is
`272d810ea2ca8bd0e19ac97f6d9cda1853502cde`. The concrete corank-one
testing support was separately reviewed at
`9fb5f145cf2ca6dd2f5f6fc4786c6ceec2ef6dd9` and is unchanged in this commit.

Theorem 6.1: `FULLY_FORMALIZED` / `PROVISIONAL_MATCH`.
This adds one completed numbered theorem, not completion of Theorem 6.2,
Section 6, the paper, or the three-paper project. Section 6 now has complete
local proofs for 3/12 numbered items: Theorem 6.1 and Lemmas 6.4 and 6.5.
Human review and exact-revision clean-kit CI remain pending.

## Paper statement and formal statement

Over a dyadic local field, for every even integer n at least two, an
integral lattice of rank n+1 is n-ADC if and only if it is O-maximal.

The public endpoint is `Bong.Lattice.heADC2025Theorem61` in
`Bong/Bong/He2023ADCEvenCorankOne.lean`. Its elaborated statement quantifies
over an arbitrary full lattice in a nondegenerate quadratic space, n >= 2,
even n, and ambient rank n+1. It proves exactly the equivalence above.
Both formal predicates include norm-integrality. Thus the omission of a
separate integral-lattice premise does not change the claim on integral
lattices and makes both sides false outside that class.

| Check | Result |
|---|---|
| Field scope | The dyadic Section 6 standing context, not an arbitrary non-dyadic field |
| Lattice and rank | Arbitrary full lattice; its ambient dimension equals n+1 |
| ADC quantification | All integral rank-n test lattices whose spaces embed; `IsNADC.{u,u,u}` |
| Extra premises | No good BONG, supplied profile, test representation, ambient row or classification-law premise |
| Conclusion | Both necessity and sufficiency; actual norm-maximality |
| Boundary | n=2 and e=1 are included |
| Primary logical relationship | `LOGICALLY_EQUIVALENT` under the recorded definition dictionary |

## Proof and dependency disclosure

The proof constructs a good BONG. Actual maximal tests of discriminant
Delta and of unit-uniformizer type, together with all clauses already
proved in Lemmas 6.4 and 6.5, force an alternating head, penultimate pair
(0,-2e) or (0,2-2e), and last order in {0,1}.

`heADC2025Lemma46iEvenCorankOne` proves the needed actual exactly-one
lattice test result, including negative clauses. It is a bounded
specialization of Lemma 4.6(i), not completion of every part of Lemma 4.6.
Ambient representability is derived, not assumed as a replacement for the
paper's named tests.

The necessity proof uses an alternative proved volume argument. A maximal
superlattice P exists, and inclusion gives

    volumeOrder(L) = volumeOrder(P) + 2*j, with j a nonnegative integer.

The bound `volumeOrder(L) <= volumeOrder(P)+1` forces j=0. Equal-volume
inclusion then gives L=P. For the standard tail, the bound follows from
the already proved possible maximal profiles and the common alternating
head sum. This does not reverse Proposition 4.13: the maximal profile is
applied only to P, whose maximality was already proved.

For the raised tail, two explicit coordinate embeddings exclude the three
wrong normalized ambient rows, using ADC lifting and Lemma 6.4(i).
The surviving row is W_2^(n+1)(delta), with delta a valuation unit. The
profile of its actual maximal lattice is derived by published Lemma
4.12(ii), and the volume bound proves maximality. The source proof's
Hilbert-symbol citation is not assumed as an extra law in this route.
Sufficiency is the previously proved maximal-implies-ADC theorem.

## Adversarial, trust and boundary checks

The independent read-only reviewer inspected the frozen paper and source
types, expanded the predicates, checked the two embedding directions and
the exhaustion of ambient rows, and found no mismatch or circularity.
At n=2 the head is empty and the embeddings are binary-to-ternary; the
constructed BONG has rank three. At e=1 the two tail alternatives remain
distinct and all estimates still apply. No nonexistent model is used.

All three new modules, the canonical entry and the complete ADC audit
passed both author-side and independent cached re-elaboration. All 12 new
queried transitive axiom sets are exactly `propext`, `Classical.choice`,
and `Quot.sound`. The four earlier concrete-test queries have the same
trust set. No admitted proof, project axiom, native solver, assumed main
theorem or supplied classification table is used by the new endpoint.
The existing proved Beli and He--Hu infrastructure is intentionally reused.

## Author review card

Paper and formal statement: the equivalence stated above, for all even
n >= 2 in the dyadic setting and rank n+1. Definitions requiring
confirmation: norm-integrality, full lattice, ambient representation,
n-ADC and norm-maximality. No difference in quantifier order, conclusion,
exceptional cases or equality convention was found by the AI review.

Author question: confirm the equivalence and the handling of integrality
inside both predicates. Domain-expert question: confirm the independent
volume proof and the two ambient exclusions, including n=2. Formalization-
expert question: inspect maximal-superlattice existence, the inclusion
index formula, the internal good-BONG construction and the public universe
parameters.

Author decision, name, date and signature: not supplied. Human domain-
expert and formalization-expert approvals: not supplied. Independent AI
review does not fill these fields and does not justify `VERIFIED_MATCH`.

## Reproducibility and deployment

Lean 4.32.1, mathlib revision
`520045ab14e26149ee970e2e617ca04b09bde5d6`, and the committed Lake lock
remain fixed. Modified dependency worktrees were preserved. The successful
cached-local checks are not a clean build; reproducibility is
`PARTIALLY_REPRODUCIBLE` for this new checkpoint.

The earlier remote published-profile artifact and the local Lemma 6.4 kit
do not contain this theorem. A new source-only kit and exact-revision
clean-kit CI are required before release promotion. No release or merge is
certified by this report. Whole-paper grade: C; verdict: `NOT_COMPLETE`.
