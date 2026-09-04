# Publisher/preprint source delta

Authority is assigned only to the publisher version. arXiv:2206.04885v3 was
revised on 25 December 2025, after the version of record, and is therefore not
used to supply or silently repair a statement. Pagination, typesetting, and
potential post-publication changes require numbered-statement comparison before
any semantic match is promoted.

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

## Lemma 3.14 / Lemma 7.1: incompatible parity in the cited application

Lemma 3.14 of the publisher version (p. 575) assumes that its target rank
`n` is odd and uses the sign `(-1)^((n+1)/2)`.  Lemma 7.1 (p. 587), however,
assumes that the target rank `n` is even and applies Lemma 3.14 with the same
letter `n`; its displayed sign is again `(-1)^((n+1)/2)`, whose exponent is
not an integer under that hypothesis.  Thus the invocation, as printed,
does not instantiate the cited lemma.

The formalization does not add a parity coercion or an unproved replacement
lemma.  The rank exclusions needed in Section 7 are instead derived from
the independently formalized He--Hu ambient-space classification together
with the equal-rank and codimension-one representation obstructions.  This
keeps the publisher statement visible while avoiding a silent repair.
