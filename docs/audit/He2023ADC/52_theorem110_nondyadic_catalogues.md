# Theorem 1.10 non-dyadic catalogue checkpoint

## Verdict

The finite-catalogue and counting deduction in the non-dyadic branch of
Theorem 1.10 is formalized at `d4c56cc`.  The result is exact at the abstract
non-dyadic interface: it gives rank, `n`-ADC, completeness up to integral
isometry, irredundancy, and the published cardinalities for all three rank
branches.

This is a `CONDITIONAL_FORMALIZATION`, not yet an unconditional local-field
formalization.  The concrete construction of the non-dyadic lattice/Jordan
system and its catalogue laws remains open.

## Published source

The sole semantic authority is the publisher version of record, Theorem 1.10
on p. 986 and its proof on p. 1017.  For a non-dyadic local field the
ramification index in the paper is `e = 0`.  Therefore the printed formula
specializes to:

- seven isometry classes in rank two;
- eight isometry classes in every rank at least three.

The proof uses Proposition 4.15 for equal rank, Theorem 5.1 for coranks one
and two, and the maximal-lattice classification and count in Remark 4.3.

## Formal declarations

The module is `Bong/Bong/He2023ADCNonDyadicTheorem110.lean`.

- `HeADC2025NonDyadicBinaryIndex` contains the four first-column rows and the
  three defined second-column rows.  It omits exactly `N_2^2(1)`.
- `HeADC2025NonDyadicGeneralIndex` is the product of the two columns and four
  square classes.
- `card_heADC2025NonDyadicBinaryIndex` proves cardinality seven.
- `card_heADC2025NonDyadicGeneralIndex` proves cardinality eight.
- `HeADC2025NonDyadicSystem.IsExactNADCIsometryCatalogue` requires the right
  rank and `n`-ADC property, completeness, and irredundancy.
- `CatalogueLaws.binary_exactCatalogue` proves the exact binary catalogue.
- `CatalogueLaws.general_exactCatalogue_of_isMaximal` converts each relevant
  maximality implication into an exact eight-row catalogue.
- `CatalogueLaws.heADC2025Theorem110NonDyadic` assembles equal rank, corank
  one, and corank two, and proves both formulas at exponent zero.

The index counts are theorem-level finite computations.  They are not assumed
inside the catalogue-law package.

## Explicit trust boundary

`HeADC2025NonDyadicSystem.CatalogueLaws` contains:

1. the already audited `SectionFiveLaws` package;
2. maximality of every defined table row;
3. exhaustion of maximal lattices by a defined row;
4. irredundancy of rows up to the supplied integral-isometry relation;
5. the equal-rank `n`-ADC-implies-maximal implication.

These are the concrete non-dyadic inputs corresponding to Proposition 4.2,
Remark 4.3, Lemmas 4.7--4.8, and Proposition 4.15.  The structure does not
contain any exact-catalogue conclusion, cardinality identity, or branch of
Theorem 1.10 as a field.

This paragraph records the historical `d4c56cc` interface. Report 65
supersedes its Proposition 4.15 boundary: that final necessity conclusion is
no longer a structure field and is now derived from lower-level
maximal-lattice existence and same-rank transfer laws.

## Kernel and axiom checks

The following checks pass at `d4c56cc`:

```text
lake env lean Bong/Bong/He2023ADCNonDyadicTheorem110.lean
lake build Bong.Papers.He2023ADC
lake env lean BongTest/He2023ADCAudit.lean
```

The assembled theorem reports only Lean's standard foundational dependencies
`propext`, `Classical.choice`, and `Quot.sound`.  No `sorry`, `admit`, new
axiom, opaque proof, unsafe declaration, or native decision bypass occurs in
the module.

## Scope consequence

The former gap “non-dyadic branch of Theorem 1.10” is now split accurately:

- the finite table, all rank branches, exact-catalogue logic, and numerical
  specialization are closed;
- a concrete non-dyadic instance of `SectionFiveLaws` and `CatalogueLaws`
  remains open.

Accordingly the unrestricted theorem and the paper remain `NOT_COMPLETE`.
The whole-paper grade remains D pending concrete non-dyadic and number-field
instances, the other missing main results, a fresh exact Review Kit, GitHub
CI, and independent human semantic approval.

## Later table-data refinement

Report 61 supplies a concrete kernel certificate for the literal publisher
Table 4.7 row data used by this theorem: every even and odd row, the total
rank and two Jordan-rank identities, the seven defined binary rows, and the
unique missing binary row.  The finite catalogue theorem therefore no longer
trusts an informal transcription of the table.  Its remaining conditional
boundary is mathematical rather than combinatorial: realizing those rows as
actual non-dyadic local lattices and proving maximality, exhaustion,
irredundancy, Lemma 4.7(ii), Lemma 4.8, and the required representation laws.

Report 62 corrects the shared predicate at rank one without changing the
rank-two or rank-at-least-three catalogues. Report 63 uses the same table to
prove the rank-four Proposition 4.16 split, while keeping its concrete
realization and transport inputs separate from the finite deduction.
