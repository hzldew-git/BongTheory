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
The full Lemma 6.12 card is in report 32. It asks reviewers to check the exact
exceptional lattice, complete maximal-binary catalogue, the omitted
`N_2^2(Delta)` ambient class, and the terminal ternary obstruction.

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

Report 35 adds the card for Theorem 7.1. Reviewers should confirm that the
publisher proof's invocation of Theorem 6.2 at `n-1=2` omits the additional
`W_2^4(Delta)` boundary class; that the corrected three-way classification
exhausts both ambient columns and all parameter square classes; that both
nonmaximal classes are excluded by actual not-3-ADC theorems; and that the
odd `n>=5` branch invokes only the valid stable restriction. The theorem
statement is provisionally matched, but the publisher proof remains marked
`INCOMPLETE_PROOF` pending human confirmation.

Report 36 adds the cards for Theorem 7.4 and Lemmas 7.5, 7.11, and 7.13.
Reviewers should confirm the four-condition Lemma 7.5 equivalence, especially
the `n=3` large-gap branch and the endpoint `R_(n+1)=2-2e`; confirm that the
He--Hu Lemma 5.7 source-rank boundary really permits `m=3`. Report 37 replaces
the former partial Lemma 7.11 card: reviewers should verify that the unit and
unit-times-uniformizer rows exhaust the source normalization `c=delta` or
`delta*pi`, and that the unit-row auxiliary `kappa` is constructed rather than
assumed. For Lemma 7.13, reviewers should compare the pointwise
wording with the proof by contradiction from simultaneous representation and
confirm that the disjunctive form used on p. 1013 is the intended correction.

Report 38 adds the Lemma 7.14 card. Reviewers should check that the two
published ambient columns have the same determinant parity, that the unit and
unit-times-uniformizer rows exhaust `c in V`, and that the Theorem 7.4 profile
makes the sum of the first `n+1` orders even. These facts, together with the
last-order set `{0,1}`, are exactly what selects the two conclusions.

Report 39 adds the Lemma 7.15 card. Reviewers should check the zero-based
translation of `R_(n+1)`; that ambient isometry plus Lemma 7.14 identifies
the final order; that formula (7.5) gives every alpha used in Beli condition
(ii); and that the signed-prefix and domination arguments cover every index
in condition (iii). For condition (iv), verify that only `i=n-1` can trigger
and that Proposition 3.5(iv)--(v) together with Lemma 4.4(ii) supplies the
actual prefix representation. Finally, confirm that the `R_(n+1)=-2e`
branch may equivalently be closed by the proved maximal-lattice uniqueness
route.

Report 40 adds the Definition 7.16 and Remark 7.17 card. Reviewers should
confirm that `ord(c) in {0,1}` is the paper's normalized set `V`, that the
zero-based index names `R_(n+1)`, and that the formal property does not assert
existence for every symbol. The uniqueness and exhaustion arguments should
be checked against Lemma 7.15, equation (7.3)(b), and the four normalized
odd ambient rows.

Report 41 adds the Lemma 7.18 card. Reviewers should confirm that the actual
second-column maximal profile gives an order incompatible with `-2e`, and
that the maximality/uniqueness route is equivalent to the paper's direct use
of Lemma 7.14(i) and Proposition 3.5(v).

Report 42 adds the Lemma 7.19 card. Reviewers should verify the conversion of
`d(delta)<2e` to an odd integer defect, the appended-good-BONG endpoint
inequalities, and the two-sided proof of `alpha_n=1`. They should also check
that the diagonal representation identifies each explicit maximal base with
the correct named `N_nu`, and that the final isometry transport reaches the
literal orthogonal product printed in the paper.

Report 43 adds the Lemma 7.20 card. Reviewers should check the four
Hilbert-symbol column combinations and the sign convention
`(-1)^nuPrime=(-1)^nu*(omega,c)_p`; verify that determinant completion adds
the line `<omega*c>`; and confirm that the resulting penultimate order is
`1-(2r+1)=-2r`. They should also confirm that units of every odd defect
`2r+1<2e` exist under the paper's local-field hypotheses and that the final
definedness biconditional has exactly the exceptional triple `(2,e,U)`.

Report 44 adds the Theorem 7.2 card. Reviewers should confirm that
`d(delta)<2e` is exactly the square-class content of
`delta in U \ {1,Delta}`; that the line-order alternatives normalize to
`epsilon*pi^j`, `j in {0,1}`; and that every square normalization is an
integral lattice isometry. For the overlap, verify the four maximal-profile
comparisons and that only the second-column unit row survives before its
parameter is normalized into `U`.

Report 45 adds the Remark 7.3 card. Reviewers should compare the exact
general plane `A(pi^l,-(delta-1)pi^-l)`, the outside scales `pi^-l` and
`delta# pi^-l`, and the equation `2l=d(delta)-1<=2e-2`. For the third row,
confirm that `heADCAForm` is `(1/2)A(2,2rho)`, that its scale is `pi`, and
that the final unary factor is exactly `<Delta epsilon>` after the binary
block. Confirm also that the first two parameters lie in
`U \ {1,Delta}` and the third lies in `U`.

Report 46 adds the Corollary 7.21 card. Reviewers should confirm that the
three top rows and four rows for every `r<=e-1` are counted without omission;
that the Lemma 7.20(ii) row is included exactly once in the catalogue and is
the only maximal lower row; and that Lemma 7.15 plus ambient-row uniqueness
really proves pairwise nonisometry. They should separately verify that
O'Meara 63:9 gives `|U|=2(N p)^e` under the repository's normalization. That
identity is now proved internally in report 57, so the review question is
semantic correspondence rather than discharge of a theorem parameter.

Report 50 adds the unary table card. Reviewers should confirm that rank one
has only the `N_1^1(c)` column; that the normalized parameters `delta` and
`delta*pi` exhaust and irredundantly represent all unary square classes; and
that the exact excluding space is `W_2^3(c)`. They should check that deleting
any one row leaves an integral ternary witness which represents every other
row but not the deleted row. Finally, the unconditional table count `2|U|`
should be checked separately from the printed `4(N p)^e`; report 57 proves
the O'Meara 63:9 conversion internally.

Report 51 adds the dyadic Theorem 1.10 card. Reviewers should verify that the
two generic catalogue constructors prove integral-isometry completeness and
irredundancy, rather than merely counting table parameters. They should check
the parity translation for all equal-rank and corank-one branches, the
`n>=4` boundary in stable even corank two, and the reuse of the exact
Corollary 7.21 catalogue in odd corank two. The corrected binary catalogue
and its `+2` value must remain visibly separate from the publisher's formally
refuted `+1` claim. They should confirm the new O'Meara 63:9 filtration proof
and keep the entire non-dyadic branch outside the proved unconditional scope.

Report 52 adds the non-dyadic Theorem 1.10 card. Reviewers should verify that
the binary index omits exactly the undefined row `N_2^2(1)`, that every rank
at least three has all eight column/square-class pairs, and that Theorem 5.1
is applied only in coranks one and two. They should separately audit whether
the fields of `CatalogueLaws` exactly match Proposition 4.2, Remark 4.3,
Lemmas 4.7--4.8, and Proposition 4.15. A concrete instance of those fields is
not yet certified.

Report 53 adds the two global enumeration cards. For Corollary 1.8,
reviewers should confirm that Hanke's 115 rational classes and Kirschmer's
471 non-rational totally real classes form the stated disjoint exhaustive
partition. For Theorem 1.11, they should compare the literal selected source
rows 1--15, 19, 25, 30--32, and 44 against Tables 1--2; verify each omitted
row's listed local obstruction; verify the 21 retained rows prime by prime;
and check that only new row `L_10` is nonmaximal. The current formal endpoint
proves the downstream logic but does not replace those external computations.

Report 59 now gives reviewers executable models for all 48 Table 1 rows. They
should compare the ten coordinates, discriminant, and last-column entry of
every row against p. 1019, paying particular attention to the negative entries
in rows 38 and 46. Lean and the independent Mathematica script check symmetry,
determinants, rational positive definiteness, selected rows, and the count 21.
Reviewers must still verify that these matrices represent the intended global
lattices, exhaust Oh's catalogue, and satisfy the asserted local `2`-ADC tests;
none of those semantic and arithmetic tasks follows from the matrix checks.

Author decision: unsigned. Domain-expert decision: unsigned.
Formalization-expert decision: unsigned.

## Lemma 2.2, subspace descent

Paper location: pp. 986--987.

Paper statement: for a finite-place completion `F_p`, every nondegenerate
subspace of the scalar-extended quadratic space `V_p` is the completion of a
nondegenerate subspace of `V`, up to isometry.

Formal finding: the complete induction on dimension, orthogonal-complement
step, scalar extension, Witt cancellation, and actual range-submodule
construction are proved at `04b7210`. At `83cc791`, the one-dimensional step
is proved for every number-field finite completion: mathlib supplies density,
and the inverse function theorem proves openness of every nonzero square
class. The combined endpoint has the publisher's literal subspace conclusion.

Questions for the paper author and domain expert:

1. Does the formal density-plus-openness argument exactly match the use of
   `[31, 63:1b Corollary, 21:1]` in the publisher proof, despite using the
   inverse function theorem to prove the required openness?
2. Is the tensor-product scalar extension definition compatible with the
   paper's completion notation in every later use of Lemma 2.2?
3. Does the returned range submodule express the intended global subspace,
   including nondegeneracy and equality of dimension?

Author decision: unsigned. Domain-expert decision: unsigned.
Formalization-expert decision: unsigned.
