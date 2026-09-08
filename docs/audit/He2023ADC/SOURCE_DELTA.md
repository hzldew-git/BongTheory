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

## Incomplete published proof of Theorem 7.1

The publisher's Theorem 7.1 on p. 1006 states the odd-rank equivalence
correctly. Its proof descends from `n`-ADC to `(n-1)`-ADC and invokes the
unqualified Theorem 6.2. At `n=3`, it lists and excludes only the
`W_1^4(Delta)` exceptional lattice from Lemma 6.12. The additional
`W_2^4(Delta)` nonmaximal 2-ADC class established above is not considered.

At `c3e6092f05a0f3b2872fefbd21554cc5461104ce`, the formalization proves a
corrected complete rank-four classification with both nonmaximal classes.
It also proves that the omitted second class is not 3-ADC. The exact published
Theorem 7.1 then follows: at `n=3` both exceptions are excluded, and at odd
`n>=5` only the valid stable restriction of Theorem 6.2 is used.

Accordingly, the theorem statement is `PROVISIONAL_MATCH`, while the printed
proof is `INCOMPLETE_PROOF`. The formal target is not changed, and the false
Lemma 6.8(iv) and Theorem 6.2 boundaries remain recorded as semantic
mismatches. Report 35 gives the full source-to-formal correspondence.

## Lemma 7.11 extracted symbol and normalized coverage

The publisher PDF on p. 1011 states the exceptional rank-five hypothesis
`d(a_[1,4])=infinity`. Plain-text extraction renders the infinity glyph as
`1`, but the proof on the same page explicitly uses
`a_[1,4] in F^(times 2)`, confirming infinite defect. The formalization uses
the square-prefix formulation and does not adopt the OCR error.

At `832d10c95f56dd3ae80fc4f912de248f25316da1`,
`heADC2025Lemma711` proves the source conclusion in both normalized rows
`N_2^3(delta)` and `N_2^3(delta*pi)` for every valuation unit `delta`. This is
the paper's own split `c=epsilon` or `epsilon*pi`, so no nonzero square class
is omitted. The derived represented-target contradiction still closes
Lemma 7.5(iii). Lemma 7.11 is now `FULLY_FORMALIZED` /
`PROVISIONAL_MATCH`; report 37 gives the exact scope.

## Lemma 7.13 printed quantifier versus proof

The printed Lemma 7.13(ii) on pp. 1011--1012 introduces either of two targets
and says the source prefix fails to represent the selected target. Its proof,
however, assumes that the prefix represents both targets simultaneously and
derives a Hilbert-symbol contradiction. This establishes only that at least
one target fails. The necessity proof of Lemma 7.5 on p. 1013 explicitly uses
this weaker `either` conclusion.

At `2417a4f`, `heADC2025Lemma713` records the proof-supported disjunction in
both target columns, and `heADC2025Lemma713_trigger_impossible` supplies the
downstream contradiction. The stronger printed pointwise conclusion is not
asserted. The source statement is therefore marked `SEMANTIC_MISMATCH` in
quantifier strength, while Theorem 7.4 and Lemma 7.5 remain proved from the
weaker result actually justified by the published argument. Report 36 records
the formal correspondence.

## Corollary 7.21 cited cardinality theorem

The publisher's proof on p. 1016 obtains its two numerical formulas by using
`|U|=[O_F^times:O_F^(times 2)]=2(N p)^e`, citing O'Meara 63:9. At
`bd0c9a3f66d3465cd518bae2d75386887f79d5a5`, the formalization proves the
complete and irredundant isometry catalogue, its exact maximal partition, and
the intermediate counts `(4e+3)|U|` and `(4e-1)|U|` without that citation.

At `4ad37e1`, the formalization proves the cited identity from the power-ideal
and principal-unit filtrations, odd square-class layers, even collapse, and
the two-class discriminant endpoint. The compatibility namespace
`HeADC2025Corollary721CountingLaw` now contains unconditional theorems, not a
law typeclass. The published numerical formulas are therefore unconditional
repository theorems. Reports 46 and 57 give the catalogue and arithmetic
accounting.

## Refuted binary specialization of Theorem 1.9(ii)

Theorem 1.9(ii) on p. 985 inherits the even-rank classification of Theorem
6.2. At `n=2` it therefore omits the same second-discriminant nonmaximal
2-ADC class. At `f7e8fb7e1b8d43b66a62e500f61f7eeba004f136`,
`not_heADC2025Theorem19iiBinaryStatement` proves the negation of the exact
binary source statement, while `heADC2025Theorem19ii_binary_corrected` proves
the complete three-way alternative. This is a downstream source mismatch,
not a new independent counterexample; report 48 gives the catalogue-level
evidence.

## Refuted binary count in Theorem 1.10

Theorem 1.10 on p. 986 prints `8(N p)^e+1` rank-four 2-ADC isometry classes.
Its proof on p. 1017 counts only the single nonmaximal class listed by
Theorem 1.9(ii). The exact formal catalogue has four maximal copies of `U`
and two distinct nonmaximal classes, hence `4|U|+2`. Under the publisher's
own O'Meara 63:9 input this is `8(N p)^e+2`.

At the catalogue checkpoint,
`not_heADC2025Theorem110BinaryCountStatement` formally refutes the printed
`+1` formula, and `heADC2025Theorems19iiAnd110BinaryCorrected` packages the
corrected classification and count. Report 57 subsequently discharges the
O'Meara cardinality premise, so both the formal refutation and corrected count
are unconditional at `4ad37e1`.

At `125dcf24f39f0b22a5f69fb33241885169314c06`, report 51 checks that this
is the only dyadic count discrepancy: every other dyadic rank/parity branch
is realized by an exact complete and irredundant integral-isometry catalogue
and has the coefficient printed in Theorem 1.10. Report 57 makes those dyadic
counts unconditional. The non-dyadic branch is not part of that conclusion.

## Lemma 7.14 determinant parity

The publisher proof on p. 1013 says that the order of the full coefficient
product is even for `W_nu^(n+2)(epsilon)` and odd for
`W_nu^(n+2)(epsilon*pi)`. At `6c52803`, the formalization proves this for both
ambient columns by comparing determinant square classes; it does not assume
that the two spaces are equal. Theorem 7.4 supplies an even sum through the
penultimate order and restricts the last order to `{0,1}`. Hence
`heADC2025Lemma714i` and `heADC2025Lemma714ii` recover the two displayed
conclusions without an extra parity premise. Report 38 gives the exact scope.
