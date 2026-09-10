# Author-corrected v5 odd-parity source gap

## Finding

The author-corrected v5 manuscript still has one unresolved proof-coverage
issue relevant to whole-paper formalization.

- Corollary 6.3 is stated for unrestricted `n`, but its proof at source lines
  1361--1365 begins: "Without loss of generality, assume that `n >= 2` is
  even."  No reduction from odd `n` to even `n` is stated or cited.
- The proof uses the even branch of Theorem 1.1 to obtain
  `R_1 = ... = R_(n+1) = 0` and `R_(n+2) in {0,1}`.  The odd branch instead
  has different conditions on `R_(n+1)`, `R_(n+2)`, and the final defects;
  therefore the displayed nondecreasing-order argument does not cover it.
- Lemma 8.3, at source lines 1681--1692, again has an unrestricted statement
  but starts its proof by assuming without reduction that `n >= 2` is even.
  It invokes Corollary 6.3, so the same parity gap is downstream-critical.
- The proof of Theorem 1.7 writes the even case and closes with "A similar
  argument can be applied for odd `n >= 1`"; that odd calculation is not yet
  represented by an unconditional Lean endpoint.

This audit does **not** claim that the unrestricted statements are false.  It
claims only that v5 does not provide the missing parity reduction or odd-rank
argument needed for a source-faithful proof.

## Current Lean boundary

`Bong/Bong/He2022ClassicCorollary63.lean` proves
`he2022ClassicCorollary63_even` with hypotheses `2 <= n` and `Even n`.  It does
not manufacture the missing odd branch.  The Section 8 endpoints for Lemma
8.3 and Theorems 1.7--1.8 are consequently labelled
`CONDITIONAL_FORMALIZATION`; their law packages are ordinary theorem premises,
not Lean axioms, but they do not discharge this source gap.

## Recommended manuscript repair

There are two sound routes.

1. **Conservative restriction.**  Add `n >= 2` and `n` even to Corollary 6.3
   and Lemma 8.3, and propagate the same restriction to every result whose
   proof uses them (in particular Theorem 1.8).  For Theorem 1.7, either add
   the same restriction or retain a separately proved odd clause.
2. **Retain the all-ranks statements.**  Insert an explicit odd-rank lemma
   proving that a rank-`n+3` classic `n`-universal lattice has an integral
   orthogonal basis, then give the odd scalar-extension obstruction needed by
   Lemma 8.3.  The new proof must derive the odd terminal-order cases from
   Theorem 1.1(iii); citing the even calculation as "similar" is not enough for
   the formal proof.

Until one of these repairs becomes the approved source authority, the v5
formalization can advance and verify independent results, but it cannot be
certified as a complete formalization of the whole paper.
