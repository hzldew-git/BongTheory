# Number-field discriminant--ramification theorem

Status: `PROVED_NUMBER_FIELD_ARITHMETIC` / `SOURCE_LOGIC_MATCH`.

Code checkpoint:
`229343195a243e1f2f946a8c5827d2610fb51f61` on
`release/heclassic-v0.5.0-rc.1-prep`.

## Source authority and locator

The sole semantic authority is the author-corrected v5 TeX manuscript
`classic_dyadic-n-uni-v5.tex`, SHA-256
`C334676733163C7A521824E1F00C782A7BF0FD1ABE5366BF76D838238EDCA049`.
Line 217 identifies “2 is unramified in K” with odd field discriminant.
Theorem 1.7 at line 227 and its proof at lines 1675--1679 use the
contrapositive: even discriminant supplies a dyadic prime with ramification
index greater than one.  Theorem 1.9 at lines 1697--1700 uses both directions,
including odd discriminant to ramification index one in the unary dyadic case.

## Concrete theorem

`Bong/Lattice/He2022ClassicNumberFieldDiscriminant.lean` defines

- `DiscriminantOdd K` as `not (2 : Int) divides NumberField.discr K`;
- `IsDyadicPrime K P` as membership of the image of 2 in the prime ideal P;
- `discriminantOdd_iff_forall_ramificationIdx_eq_one`, the equivalence between
  odd discriminant and ramification index one at every dyadic prime ideal of
  the ring of integers;
- the two directed consequences, the ramified-prime witness under even
  discriminant, and positivity of every prime-ideal ramification index.

The proof combines
`NumberField.not_dvd_discr_iff_forall_mem` with
`Ideal.ramificationIdx_eq_one_iff`.  It does not add a project axiom or a
paper-specific arithmetic law.

## Connection to the abstract global layer

`NumberFieldDiscriminantBridge` records only the structural identification
between an abstract finite place and a prime ideal of the ring of integers:
the ideal at a place, primality, the dyadic predicate, equality of the two
ramification-index functions, equality of the two odd-discriminant
predicates, and coverage of all dyadic prime ideals.

Supersession note: Report 34 derives primality and dyadic-prime coverage from
an equivalence with the standard height-one spectrum. Those two items no
longer need to be supplied independently by a concrete implementation.

From this bridge Lean constructs:

- `DiscriminantRamificationLaws` for the necessity arguments;
- odd-discriminant-to-index-one for the unary sufficiency argument;
- positivity of the abstract ramification index; and
- `SumOfSquaresLocalUniversalityLaws` from only its three remaining local
  representation branches.

Consequently the discriminant theorem itself and both of its logical
directions are no longer unproved Section 8 arithmetic premises.  What remains
is the type-level identification of the repository's abstract place data with
the standard height-one spectrum and compatibility of the three arithmetic
predicates/functions; Report 34 records this reduced interface.

## Mechanical evidence

With Lean 4.32.1, the concrete module, Section 8 module, canonical paper entry,
and focused discriminant audit build successfully; the final combined build
completes 5,660 jobs.  The audit prints only `propext`, `Classical.choice`, and
`Quot.sound` for the concrete equivalence, witness, bridge constructions, and
the affected global endpoints.  The enforcing imported-closure gate reports
`AXIOM_GATE_PASS: 62721 declarations checked`.

All 30 CI policy tests pass.  The comment-aware scanner checks 2,795 tracked
Lean sources without a forbidden proof token outside comments.  All changed
Lean lines are at most 100 columns and `git diff --check` passes.

## Remaining fidelity boundary

This checkpoint does not construct the full number-field lattice and
completion model, positive-definite globalization, the local
sum-of-squares representation branches, or strong approximation.  It also
does not supply the missing odd coefficient calculation in Theorem 1.7 and
does not repair the false unrestricted odd clause of v5 Corollary 6.3.
Therefore it narrows the concrete Section 8 boundary but does not change the
Grade-D whole-paper verdict.
