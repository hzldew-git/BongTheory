# Corollary 1.8 and Theorem 1.11 enumeration checkpoint

## Verdict

The finite deductions in Corollary 1.8 and Theorem 1.11 are formalized at
`8cdd338`.  The formalization preserves the two distinct trust boundaries:

- Corollary 1.8 is a theorem-level deduction of `115 + 471 = 586` from the
  cited Hanke and Kirschmer classification catalogues.
- Theorem 1.11 proves the exact 21-row conclusion from an explicit Oh-table
  and local-verification law package.  Its Table 2 row selection, cardinality,
  and nonrepetition are machine-checked rather than assumed.

Both results remain `CONDITIONAL_FORMALIZATION`.  The repository does not yet
construct the external catalogues, the 48 integral matrix models, or the
prime-by-prime local checks used in the publisher's proof.

## Published source

The sole semantic authority is the publisher version of record.

- Corollary 1.8 is on p. 985.  It cites 115 rational classes from Hanke and
  471 classes over other totally real fields from Kirschmer, then states the
  total 586.
- Theorem 1.11 is on p. 986.  It states that there are exactly 21 positive
  definite quaternary `2`-ADC integral `Z`-lattices up to isometry, that each
  is a half-scaled Table 1 lattice, that each has class number one, and that
  every row except `L_10` is `Z`-maximal.
- Tables 1--2 and the proof are on pp. 1018--1020.  Table 2 selects published
  Table 1 rows 1--15, 19, 25, 30--32, and 44.  The proof reduces the candidate
  list through Corollary 8.5 and leaves finitely many local checks at primes
  dividing the discriminant and at 2.

## Formal declarations

The module is `Bong/Lattice/He2023ADCEnumerativeMain.lean`.

For Corollary 1.8:

- `HeADC2025Corollary18EnumerationData` separates the rational catalogue, the
  non-rational totally real catalogue, and their disjoint union.
- `HeADC2025Corollary18EnumerationData.heADC2025Corollary18` proves that the
  union has cardinality 586 from the two cited cardinalities 115 and 471.

For Theorem 1.11:

- `heADC2025Theorem111TableTwoSourceIndex` is the literal zero-based list
  `[0,...,14,18,24,29,30,31,43]`.
- `heADC2025Theorem111TableTwoSourceIndex_selected` proves that every listed
  source row satisfies the selection predicate.
- `heADC2025Theorem111TableTwoSourceIndex_injective` proves that no source row
  is repeated.
- `card_heADC2025Theorem111Index` proves that the selected subtype has exactly
  21 entries.
- `HeADC2025Theorem111Laws` states the external catalogue and local-checking
  inputs without assuming the final theorem.
- `HeADC2025Theorem111Laws.heADC2025Theorem111` derives rank four, positive
  definiteness, global `2`-ADC, completeness, irredundancy, the 21-class
  count, half-scaling, class number one, and maximality except at row 10.

The global `2`-ADC property of a selected row is derived with the already
formalized Corollary 8.5 from local `2`-ADC, stability, `2`-regularity, and
half-scaling.  It is deliberately not a field of `HeADC2025Theorem111Laws`.

## Explicit trust boundary

`HeADC2025Corollary18EnumerationData` still supplies:

1. the three types of isometry classes;
2. the partition equivalence;
3. the cited cardinalities 115 and 471.

`HeADC2025Theorem111Laws` still supplies:

1. the existing Theorem 1.3 and Section 8 arithmetic packages;
2. the rank and positive definiteness of all 48 candidates;
3. stability and `2`-regularity of the 48 source rows;
4. the half-scaling relation;
5. the prime-by-prime local-check result selecting exactly the 21 rows;
6. exhaustion and irredundancy of the external Oh catalogue;
7. class-number-one and maximality data read from the published table.

No concrete matrix presentation of the 48 rows is present yet.  Consequently
this checkpoint verifies the paper's finite logic and literal row bookkeeping,
but does not independently certify the external enumeration or hand-computed
local arithmetic.

## Kernel and axiom checks

The following checks pass at `8cdd338`:

```text
lake env lean Bong/Lattice/He2023ADCEnumerativeMain.lean
lake build Bong.Papers.He2023ADC
lake env lean BongTest/He2023ADCAudit.lean
lake env lean BongTest/AxiomGate.lean
```

The full paper entry builds successfully in 5,035 jobs.  The selected axiom
reports contain only `propext`, `Classical.choice`, and `Quot.sound`.  The new
module contains no `sorry`, `admit`, project axiom, opaque proof, unsafe
declaration, or native decision bypass.

## Scope consequence

The former gap “Corollary 1.8 and Theorem 1.11” is now split accurately:

- the cardinality arithmetic, exact Table 2 source-row selection, 21-row
  count, and all logical consequences are closed;
- concrete Hanke--Kirschmer--Oh catalogue imports, the 48 integral models,
  and the local computations remain open.

The whole-paper verdict remains `NOT_COMPLETE`, with grade D unchanged by
this checkpoint.  A new exact Review Kit, GitHub CI, release promotion, and
independent human semantic approval remain separate deployment gates.
