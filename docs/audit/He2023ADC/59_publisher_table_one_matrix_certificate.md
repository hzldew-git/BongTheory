# Publisher Table 1 matrix certificate

## Status

Checkpoint: `e0ef0330a8eaa85c74dfa9b91cc706ce3c81efad`.

Classification: `CONCRETE_DATA_CERTIFICATE` and
`CONDITIONAL_FORMALIZATION` for Theorem 1.11 as a whole.

This report advances the earlier Report 53 boundary. It does not change the
Grade-D whole-paper verdict or certify the external classifications and local
computations used by the publisher.

## Authoritative source

The sole statement authority is Zilong He, *On n-ADC integral quadratic
lattices over algebraic number fields*, *Documenta Mathematica* 30 (2025),
no. 4, 981--1022, DOI 10.4171/DM/1003. The publisher PDF has SHA-256

`E26190C88B16624DCCB7F269C6C3FFDA02BC6830677A5BC0C8E0AD48A36E72D6`.

The coordinate convention and introduction to Table 1 occur on p. 1018;
the 48 rows and their discriminant and bad-prime columns occur in Table 1 on
p. 1019. Table 2 and the proof of Theorem 1.11 begin on p. 1020. The later
arXiv revision remains a comparison source, not a statement authority.

## What is now internal

`Bong.Lattice.He2023ADCTableOne` transcribes every printed coordinate row
`[a,b,c,d,f1,f2,f3,f4,f5,f6]` and constructs the corresponding symmetric
integral Gram matrix. In particular, the negative entries in rows 38 and 46
are retained rather than lost during PDF extraction.

The following claims are proved in Lean:

- all 48 matrices are symmetric;
- every determinant equals the discriminant printed in Table 1;
- every printed discriminant and the first three leading principal minors
  are positive;
- a generic exact rational `LDL^T` factorization is proved once;
- the four positive pivots imply positive definiteness of every rational
  Gram matrix;
- the last column is transcribed as `none` or its unique printed bad prime;
- `None` occurs exactly in rows 1--15, 19, 25, 30--32, and 44, hence in
  exactly 21 rows; and
- this literal last-column predicate is identical to the abstract Table 2
  selection predicate used in `He2023ADCEnumerativeMain`.

The finite row certificates use kernel `decide`. No `native_decide` proof is
used. The positive-definiteness proof is not a floating-point test: it is an
exact proof over the ordered field of rational numbers.

The independent Mathematica program
`scripts/verification/verify_he2023adc_table1.wl` reconstructs the same 48
matrices with exact integers and separately checks determinants, symmetry,
positive definiteness, selected rows, and the count 21.

## What remains external

This certificate does not prove any of the following:

- that the 48 displayed matrices, viewed as global integral lattices up to
  isometry, exhaust Oh's primitive stable 2-regular catalogue;
- the precise semantic identification between Oh's catalogue, the
  publisher's half-scaling convention, and the formal global lattice type;
- the prime-by-prime local `2`-ADC calculations asserted by the last column;
- class number one, maximality, and global exhaustion for the retained rows;
  or
- the Hanke and Kirschmer external enumerations used in Corollary 1.8.

Those facts remain visible fields of the external law packages. Consequently,
the final Theorem 1.11 endpoint remains conditional even though its literal
matrix data, printed invariants, and finite selection logic are now internal.

## Mechanical evidence and trust boundary

The new module, the enumeration bridge, canonical paper entry, and expanded
audit complete a combined 5,555-job build with Lean 4.32.1. The scoped source
scanner checks 2,770 tracked Lean files and finds no forbidden proof token.
All changed Lean lines are at most 100 columns, and `git diff --check` passes.

Focused axiom reports for the determinant, leading-minor, rational
positive-definiteness, last-column, cardinality, and selection-bridge
endpoints contain only `propext`, `Classical.choice`, and `Quot.sound`, with
some purely finite endpoints requiring only `propext`. These reports certify
the Lean trust boundary, not source fidelity or the truth of uninstantiated
law-package fields.

An exact clean Review Kit generated and rebuilt from this checkpoint remains
a separate reproducibility gate. Author, domain-expert, and formalization-
expert semantic sign-off also remain separate and unsigned.
