# Author review cards

## Lemma 6.8(iv), binary boundary

Paper location: pp. 1002--1003.

Paper statement: if an integral rank-four lattice is 2-ADC and its ambient
space is `W_2^4(Delta)`, then it is integrally isometric to the maximal lattice
`N_2^4(Delta)`.

Formal finding: an explicit integral lattice in that ambient space has good
BONG orders `(0,-2e,1,3-2e)`, represents every relevant maximal binary lattice,
is 2-ADC, and is not maximal. Therefore it is not integrally isometric to
`N_2^4(Delta)`. The argument is instantiated over `Q_2` and has no dependency
on Lemma 6.8 or Theorem 6.2.

Current audit status: `SEMANTIC_MISMATCH` at n=2; `PROVISIONAL_MATCH` for the
separately formalized n>=4 statement.

Questions for the paper author and domain expert:

1. Was Lemma 6.8(iv) intended to include n=2?
2. Should the candidate with orders `(0,-2e,1,3-2e)` be added to the
   exceptional classification, or is there an intended hypothesis that
   excludes it?
3. Which downstream statements should be revised after the use of Lemma
   6.7(ii) outside its n>=4 range?

Author decision: unsigned. Domain-expert decision: unsigned.

Report 25 contains the historical cards for full Lemma 6.8(iii) and the
restricted n>=4 part of (iv). Reports 30--31 replace the former open question
about n=2 with the formal counterexample recorded above.

The full author-facing card for the newly completed Proposition 4.13, with
its assumptions, boundary checks, and unsigned approval fields, is in
`15_odd_maximal_structure_checkpoint.md`.
The corresponding card for dyadic Proposition 4.16, including exact Gram
normalization, the integral exceptional class and form scaling, is in
`16_quaternary_maximal_checkpoint.md`.
The result-level card for Lemma 6.4, including raw versus capped defects,
derived ranks, all five tests and the binary boundary, is in
`17_even_testing_checkpoint.md`.
The card for both clauses of Lemma 6.5, including exact failing indices,
capped-defect endpoints and the repaired empty-head explanation, is in
`18_even_obstruction_checkpoint.md`.
The full Theorem 6.1 card, including the arbitrary-lattice equivalence,
alternative volume proof and empty-head boundary, is in
`19_even_corank_one_checkpoint.md`.
The exact published representation card is in report 20. The complete
Lemma 6.6 card, including parity versus raw defect, target transport and
the precise failing central condition, is in report 21.
The complete Lemma 6.7 card, including actual lattice representation, alpha
discreteness and equality of raw and capped defects, is in report 22.
The card for only Lemma 6.8(i)--(ii), including the uniform n=2 replacement
proof, signed full determinant and actual lattice conclusion, is in report 23.

1. Confirm the direction and meaning of ambient quadratic-space representation.
2. Confirm source integrality is part of the local predicate rather than only a
   standing convention.
3. Confirm Lemma 2.1's maximal over-lattice argument preserves ambient space and
   rank exactly as encoded.
4. Keep the dyadic specialization visibly separate from the general and global
   statements.
5. Review the now-proved transport from the ten concrete model criteria to
   thirteen published-family branches of Lemmas 4.11--4.12, including the
   sign of `Delta` and the factor `1/2` in the hyperbolic plane. Report 14
   contains the two result-level cards and the exact public names.
6. Confirm that the profile is read as `k` copies of `0,-2e` followed by the
   listed tail, with zero-based Lean indices. Check the rank-one first-column
   rows and the absent binary second-column square row.
7. Review the arithmetic fields of `Theorem13Laws` against the cited
   localization, maximal-lattice and local-global theorems. Their concrete
   proofs are still required before promoting the global results.

All cards are unsigned. No independent human semantic approval is recorded.

Report 24 adds the card for Lemma 6.8(v),(vi). In particular, confirm that
the fixed Delta is intended to belong to U before the literal exclusion
V minus {1,Delta}. Review the three actual tests, signed-defect argument
and return to the original parameter after internal normalization.
