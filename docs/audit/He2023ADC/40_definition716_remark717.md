# Definition 7.16 and Remark 7.17 classification symbols

Status: `FULLY_FORMALIZED` / `PROVISIONAL_MATCH`.

Code checkpoint: `7b21fe0e07e97ba082dd9e78a79e3ec8091630af`.

## Source authority

The sole semantic authority is the publisher version of record:

- Zilong He, *On n-ADC integral quadratic lattices over algebraic number
  fields*, *Documenta Mathematica* 30 (2025), no. 4, 981--1022;
- DOI: <https://doi.org/10.4171/DM/1003>;
- publisher PDF SHA-256:
  `E26190C88B16624DCCB7F269C6C3FFDA02BC6830677A5BC0C8E0AD48A36E72D6`.

Definition 7.16 starts on p. 1014 and Remark 7.17 is on p. 1015. The
post-publication arXiv revision remains comparison-only.

## Formal definition

For odd `n=2k+3`, `HeADC2025Definition716 k rIndex nu c a` records exactly
the property defining the paper's symbol `M_(nu,r)^(n+2)(c)`:

- `nu` belongs to the two-element type `HeADC716Column`;
- `0 <= rIndex <= e`;
- `c` belongs to the normalized parameter set `V`, represented exactly by
  `ordUnit K c = 0 or 1`;
- the rank-`n+2` lattice is `n`-ADC;
- its ambient space is the selected `W_nu^(n+2)(c)`;
- the zero-based entry `2k+3`, namely the paper's `R_(n+1)`, equals `-2r`.

The definition is a property of a supplied lattice and good BONG. It does
not assert existence for every triple `(nu,r,c)`, matching the paper's
qualification "provided that such lattice exists."

## Uniqueness

`heADC2025Remark717_unique` takes two realizations of the same symbol. Their
ambient spaces are both isometric to the same published `W` model and their
penultimate orders both equal `-2r`. Lemma 7.15 then gives an actual integral
lattice isometry. No uniqueness principle is included as a field of the
definition or assumed separately.

## Exhaustion

`heADC2025Remark717_exhaustion` starts with an arbitrary rank-`n+2`, `n`-ADC
lattice. Theorem 7.4 makes `R_(n+1)` even and confines it to `[-2e,0]`; the
proof constructs the unique natural index `r` with `R_(n+1)=-2r` and
`r<=e`. The proved normalized odd-space exhaustion supplies one of the four
rows `W_1(delta)`, `W_2(delta)`, `W_1(delta*pi)`, or `W_2(delta*pi)`.
Their parameter orders are proved to be zero or one, producing the required
`nu`, `r`, and `c` witnesses.

## Statement-strength conclusion

The formal definition preserves every source field and the existence
qualification. The two parts of Remark 7.17 are proved from Lemma 7.15,
Theorem 7.4, and the published ambient-space exhaustion. They are therefore
`LOGICALLY_EQUIVALENT` to the publisher text under the standing good-BONG
convention.

## Mechanical trust checks

All six new Section 7 modules, the canonical paper entry, and the expanded
audit compile directly with Lean 4.32.1. The selected transitive dependency
reports contain exactly `propext`, `Classical.choice`, and `Quot.sound`.
The focused enforcing gate reports
`AXIOM_GATE_PASS: 59555 declarations checked`. The comment-aware scanner
checks 2,735 tracked Lean files without a forbidden proof token outside
comments. The scoped 100-column check and `git diff --check` pass.

These are local checks at the stated code commit. Exact-revision Review Kit
CI, release promotion, and independent human sign-off remain separate gates.

Author decision: unsigned. Domain-expert decision: unsigned.
Formalization-expert decision: unsigned.
