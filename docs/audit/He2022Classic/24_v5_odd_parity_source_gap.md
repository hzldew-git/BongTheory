# Author-corrected v5 odd-parity source failure

## Updated finding

The author-corrected v5 manuscript has a substantive odd-parity failure.

- Corollary 6.3 is stated for unrestricted `n`, but its proof at source lines
  1361--1365 begins by assuming without reduction that `n >= 2` is even.
- The proof uses the even branch of Theorem 1.1 to obtain
  `R_1 = ... = R_(n+1) = 0` and `R_(n+2) in {0,1}`.  The odd branch has
  different terminal conditions and permits a final order drop.
- The unrestricted odd conclusion is false.  Report 26 gives a
  kernel-checked `e=2`, `n=3`, rank-six counterexample with BONG orders
  `[0,0,0,0,2,0]`, and proves nonisometry to the diagonal lattice made from
  the same six coefficients.
- Lemma 8.3, at source lines 1681--1692, again assumes without reduction that
  `n >= 2` is even and invokes Corollary 6.3.  Its odd proof is therefore
  invalid as written.  The counterexample to Corollary 6.3 does not by itself
  decide whether Lemma 8.3 has a different odd proof.
- The proof of Theorem 1.7 writes the even case and closes by calling the odd
  case similar.  That odd calculation remains unsupported independently of
  the Corollary 6.3 counterexample.

The earlier version of this report classified Corollary 6.3 as an unresolved
proof gap and explicitly made no counterexample claim.  That assessment is
superseded by the formal construction in Report 26.

## Current Lean boundary

`Bong/Bong/He2022ClassicCorollary63.lean` proves
`he2022ClassicCorollary63_even` under `2 <= n` and `Even n`.
`Bong/Bong/He2022ClassicCorollary63OddCounterexample.lean` proves
`exists_he2022ClassicCorollary63_odd_counterexample` at `e=2`, `n=3`.

The Section 8 endpoints for Lemma 8.3 and Theorems 1.7--1.8 remain
`CONDITIONAL_FORMALIZATION`.  Their law packages are ordinary theorem
premises rather than Lean axioms, but they do not repair the source failure.

## Required manuscript repair

The conservative repair is now the only route that preserves the present
Corollary 6.3 conclusion: add `n >= 2` and `n` even to Corollary 6.3.  Apply
the same restriction to Lemma 8.3 and Theorem 1.8 unless a new odd-rank proof
with a different local input is supplied.  Theorem 1.7 likewise needs either
a written odd proof or a proof-supported restriction.

Consequently v5 may remain the authority for every unaffected result, but it
cannot support a faithful complete formalization or Classic release as a
whole-paper verification artifact.
