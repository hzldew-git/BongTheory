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

## Unresolved n=2 proof boundary in Lemma 6.8(iv)

The publisher's statement on p. 1002, under the even n>=2 convention on
p. 998, includes n=2 in (iv). Page 1003 invokes the test N_2^n(1) explicitly
with n>=4, but supplies no separate argument for n=2 there. The following
Lemmas 6.9--6.12 concern W_1^4(Delta), not the W_2^4(Delta) ambient case.

At `074f2cdcd63637fb6f6d8c65879e55968a1dc675`, the formalization proves
the n>=4 special case as `heADC2025Lemma68iv_of_pos`. The restriction is
visible and does not alter the published target. Status of the remaining
argument: `INSUFFICIENT_EVIDENCE` / `AUTHOR_CONFIRMATION_REQUIRED`.
An omitted argument is not a refutation. No arXiv amendment or new source
convention is silently adopted to fill this gap. Report 25 records the
independent source comparison and the fully proved neighboring clause (iii).
