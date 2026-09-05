# Publisher/preprint source delta

Authority is assigned only to the Doc. Math. version of record. arXiv:2306.00334v3
was revised on 25 December 2025, after publication, and is comparison-only.
Post-publication differences must be logged statement by statement; they cannot
silently alter the formal target. The Lean scope described here was extracted
from the publisher version.

## Implicit representative alignment in Lemma 6.8(v)--(vi)

Publisher p. 983 defines U by normalized unit square-class representatives
and V=U union pi U. The normalization d(delta)=ord(delta-1) forces the
square representative to equal 1, but does not uniquely fix the scalar in
the Delta class. The prior choice of Delta is not explicitly required to
belong to U. The literal exclusion V minus {1,Delta} in Lemma 6.8 therefore
uses an implicit compatible representative choice.

At `b728bce20942191785d0b50f2c068e0b5ee7c2f7`, the representative-independent
core excludes the two square classes. A separately proved printed-domain
bridge and wrappers expose `exists i, U i = Delta`. This is a disclosed
source convention, not an added lattice classification premise or an
unannounced correction from arXiv. Bare unequal scalars are not sufficient.
Author confirmation of the intended compatible choice remains pending;
report 24 records the independent AI domain and proof checks.

## Refuted n=2 boundary in Lemma 6.8(iv)

The publisher's statement on p. 1002, under the even n>=2 convention on
p. 998, includes n=2 in (iv). Page 1003 invokes the test N_2^n(1) explicitly
with n>=4, but supplies no separate argument for n=2 there. The following
Lemmas 6.9--6.12 concern W_1^4(Delta), not the W_2^4(Delta) ambient case.

At `074f2cdcd63637fb6f6d8c65879e55968a1dc675`, the formalization proves
the n>=4 special case as `heADC2025Lemma68iv_of_pos`. The later boundary
development constructs an actual integral nonmaximal lattice in
`W_2^4(Delta)`, exhausts every relevant maximal binary test, and proves that
the candidate is 2-ADC. At `fe2a459a4152ade94299a61d1c4958fefa646ba0`,
`not_heADC2025Lemma68ivBinaryStatement` records the resulting negation of the
printed binary implication. A concrete `Q_2` module rules out vacuity.

Independent source-first and code-second review checked the literal Theorem
3.6 conditions, square-class exhaustion, actual integral transports, hidden
assumptions, universe scope, and noncircular dependency closure. The result is
`SEMANTIC_MISMATCH` for Lemma 6.8(iv) at n=2. No arXiv amendment or replacement
classification is adopted. Reports 30--31 give the exact evidence and limits.

## Refuted n=2 boundary in Theorem 6.2

The publisher's Theorem 6.2 includes every even `n>=2`. At `n=2` it claims
that every rank-four 2-ADC lattice is either maximal or isometric to the
exceptional lattice in `W_1^4(Delta)` from Lemma 6.12.

At `70580bbd2b4386bec53f046b54a96e3dd69bcaae`, the already audited boundary
lattice in `W_2^4(Delta)` is used as an actual integral counterexample. It is
2-ADC and nonmaximal, and Proposition 4.2(i)'s proved nonisometric ambient
pair shows that it cannot be isometric to the `W_1^4(Delta)` exception.
`not_heADC2025Theorem62BinaryStatement` therefore proves the negation of the
exact published `n=2` biconditional.

The same checkpoint proves the complete `n>=4` restriction as
`heADC2025Theorem62_of_four_le`, using both columns of Proposition 4.2(ii)
and all six valid branches of Lemma 6.8. The published target is not silently
altered: the source theorem remains `SEMANTIC_MISMATCH` at `n=2`, while the
restricted theorem is recorded separately. Report 34 gives the formal and
source-level evidence.
