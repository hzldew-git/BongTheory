# Source-version delta

Authority is assigned to the author-corrected v5 TeX manuscript
`classic_dyadic-n-uni-v5.tex`, SHA-256
`C334676733163C7A521824E1F00C782A7BF0FD1ABE5366BF76D838238EDCA049`.
The publisher version and arXiv:2206.04885v3 are comparison sources. Every v5
change is recorded here rather than silently transferred from one version to
another. See Report 22 for the v5 and latexdiff hashes.

## Lemma 2.9(iii): odd-rank `C_2`, even-order branch

The publisher version (p. 568) and arXiv v3 use the same short proof sentence
`d(-b_{n-1}b_n)=d(c)=1`.  For the displayed row
`<c omega#, -c omega# omega, c omega>`, however, the final adjacent product is
square-equivalent to `omega#`; the preceding adjacent product is
square-equivalent to `omega` and has defect one.  The theorem statement is
unchanged.  The formal proof applies formula (2.4) to that preceding
defect-one candidate, then uses Proposition 2.4(vi) to propagate
`beta_i = 1`.  This is recorded explicitly rather than silently identifying
the two adjacent products.

## Lemma 3.1(iv): lower endpoint of the index range

The publisher version (p. 569) and arXiv v3 both state `1 < j < m` and infer
that `R_(j+1)+R_(j+2)=0 <= S_(j-2)+S_(j-1)` makes `j` nonessential.  At
`j=2`, however, `S_(j-2)=S_0` does not exist.  Beli (2006), Definition 4.7
and its endpoint convention explicitly omit this second essentiality
inequality at `j=2`; at that endpoint essentiality is determined by
`R_3>S_1`.  Consequently the displayed proof does not justify the stated
`j=2` case.

All later uses in Lemma 3.2 apply clause (iv) only to odd indices at least
three.  The formal endpoint therefore records the proof-supported lower
bound `2 < j`, and keeps the ordinary/terminal central-index distinction
explicit.  No unproved repair of the publisher statement is introduced.

## Lemma 3.4: parity phrase in the equal-prefix subcase

The publisher proof (p. 571) says that both `k-1` and `j+2` are odd.  The
lemma assumes that `j` is even, so `j+2` is even.  The conclusion used at
that point is only `R_(j+2) >= 0`; it follows directly from good-BONG
two-step monotonicity `R_j <= R_(j+2)` together with the hypothesis
`R_j = 0`.  The formal proof uses this valid argument and does not encode
the typographical parity claim.

## Corollary 3.13(iii): missing preceding-gap premise

The publisher version (p. 575) assumes only
`R_(n+3)-R_(n+2) <= 2e` in part (iii), then says that the conclusion for
all `2 <= i <= n+1` is clear from Lemma 3.1(v).  Applying Lemma 3.1(v) at
`i=n` also requires
`R_(n+2)-R_(n+1) <= 2e`.  This preceding inequality does not follow from
the displayed hypotheses `R_1=...=R_n=0` and `R_(n+1) in {0,1}` alone.

The formalization therefore proves parts (i) and (ii) literally, states
part (iii) with the missing preceding-gap premise exposed, and also proves
the commonly used specialization in which both `R_(n+1)` and `R_(n+2)`
belong to `{0,1}`.  No stronger conclusion is attributed to the published
proof without that additional premise.

## Lemma 3.14 / obsolete publisher Lemma 7.1

Lemma 3.14 of the publisher version (p. 575) assumes that its target rank
`n` is odd and uses the sign `(-1)^((n+1)/2)`.  Lemma 7.1 (p. 587), however,
assumes that the target rank `n` is even and applies Lemma 3.14 with the same
letter `n`; its displayed sign is again `(-1)^((n+1)/2)`, whose exponent is
not an integer under that hypothesis.  Thus the invocation, as printed,
does not instantiate the cited lemma.

The literal publisher conclusion of Lemma 7.1(ii) is false when the
ramification index satisfies `e>1`. Take the classic integral target
`H_e^(2p+2)(1)`.  Both displayed rank-`2p+3` sources `C_1(omega)` and
`C_2(omega)` have terminal BONG order zero and preceding alpha invariant one.
At the terminal representation index, Theorem 2.5 forces their representation
alpha to be at most one, whereas its half-gap and primary candidates are both
strictly greater than one.  Hence neither source represents the target.

This contradiction remains machine checked by
`he2022ClassicLemma71ii_literal_disjunction_fails` in
`Bong/Bong/He2022ClassicSectionSeven.lean`.

The author-corrected v5 supplies the required resolution. Its Lemma 7.1(ii)
assumes either `e=1`, or that the target is `C_k^n(c)` with `k` equal to one or
two and `d(c)` equal to zero or one. Its last assertion additionally assumes
representation of `C_1^(n+1)(1)` when `e>1`. The new proof checks the terminal
condition directly in the first two branches and uses the integral identity
`C_1^(n+1)(1) -> H_e^n(1)` in the exceptional branch.

The corresponding Lean endpoints live in
`Bong/Bong/He2022ClassicLemma71V5.lean`. They yield the full corrected
Corollary 7.2 bridge, the odd part of Lemma 7.4, and the odd minimality part of
Theorem 1.3 without assuming the obsolete publisher statement.

## Corollary 6.3 and Lemma 8.3: false odd clause and downstream gap

The author-corrected v5 Corollary 6.3 is stated without a parity restriction,
but its proof begins by saying, without a cited reduction, that one may assume
`n >= 2` is even.  The displayed argument then uses the even clause of Theorem
1.1 to obtain `R_1 = ... = R_(n+1) = 0` and
`R_(n+2) in {0,1}`.  The odd clause of Theorem 1.1 does not give these same
terminal conditions, so the printed monotonicity proof cannot simply be
replayed in odd rank.

The omission is not only a proof-coverage gap.  For `e=2` and `n=3`, Lean
constructs a classic `3`-universal rank-six lattice with good-BONG order
sequence `[0,0,0,0,2,0]`.  The diagonal lattice made from the same six
coefficients, after swapping the final two entries, has good-BONG order
sequence `[0,0,0,0,0,2]`.  Good-BONG orders are invariant under integral
isometry, so the two lattices are not isometric.  This kernel-checked
counterexample is
`exists_he2022ClassicCorollary63_odd_counterexample`; Report 26 gives its
complete certificate.

The same unsupported parity step reappears in Lemma 8.3: its statement has no
parity condition, while its proof again assumes that `n >= 2` is even and
then invokes the now-refuted odd extension of Corollary 6.3.  This does not by
itself disprove Lemma 8.3, but its odd proof must be replaced.  The proof of
Theorem 1.7 writes out only its even case and calls the odd case similar, so
that odd calculation also remains unsupported.

Lean therefore exposes the valid `he2022ClassicCorollary63_even` together
with the odd counterexample.  It now also exposes only
`he2022ClassicLemma83_even` and `he2022ClassicTheorem18_even`, each with
explicit `n >= 2` and evenness hypotheses.  No unrestricted Lemma 8.3 or
Theorem 1.8 endpoint remains. It exposes `he2022ClassicTheorem17_even` with
the same parity scope, and separately exposes
`he2022ClassicTheorem17_of_localAdjacentDefectsLarge` for the common final
contradiction with the missing local-defect calculation as a premise. No
unrestricted odd Theorem 1.7 endpoint remains. Reports 24, 26, 28, and 33 give
the conservative source scope.
