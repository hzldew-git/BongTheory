# Lemma 7.20 complete classification

Status: `FULLY_FORMALIZED` / `PROVISIONAL_MATCH`.

Code checkpoint: `b86a9d4cca78d1f016b1d550fc586df3b90bd8d4`.

## Source authority

The sole semantic authority is the publisher version of record:

- Zilong He, *On n-ADC integral quadratic lattices over algebraic number
  fields*, *Documenta Mathematica* 30 (2025), no. 4, 981--1022;
- DOI: <https://doi.org/10.4171/DM/1003>;
- publisher PDF SHA-256:
  `E26190C88B16624DCCB7F269C6C3FFDA02BC6830677A5BC0C8E0AD48A36E72D6`.

Lemma 7.20 and its proof occur on pp. 1015--1016. The post-publication arXiv
revision remains comparison-only.

## Formal endpoints

`He2023ADCLemma720Maximal` proves parts (i)--(ii) on the actual named maximal
lattices. The first column has penultimate order `-2e` for both permitted
parameter orders. The second column has order `-2e` for an order-one
parameter, while its unit row has `2-2e=-2(e-1)`. The three corresponding
`isometricNamed` theorems use Remark 7.17 to identify every realization of
the class with the named maximal lattice.

`He2023ADCLemma720Ambient` proves the Hilbert-symbol selection in part (iii).
After cancelling the common hyperbolic tower, the first/first representation
is equivalent to `(omega,c)=1`. Source-pair and target-pair exclusivity then
give all four column combinations. The resulting theorem
`heADC2025Lemma720_columnRepresentation_iff` is exactly

```text
W_(nuPrime)^(n+1)(omega) represents W_nu^(n+2)(c)
  iff (-1)^nuPrime = (-1)^nu * (omega,c)_p.
```

The determinant square classes of both even and both odd columns are proved
from Definition 4.1. Consequently the missing one-dimensional coefficient
has square class `omega*c`. Determinant completion and the local
determinant--Hasse classification then give an actual ambient isometry

```text
W_(nuPrime)^(n+1)(omega) orthogonal-sum <omega*c>
  isometric to W_nu^(n+2)(c).
```

No second column-selection law or ambient isometry is assumed.

## Named products and existence

`He2023ADCLemma720` proves both named-product branches of part (iii). From
`d(omega)=2r+1` and `r<=e-1`, it derives `d(omega)<2e`; multiplication by the
unit `omega` preserves the allowed order of `c`. Lemma 7.19 therefore
constructs a good BONG on the named product, proves it `n`-ADC, and gives

```text
R_(n+1) = 1-d(omega) = -2r.
```

The ambient isometry above completes every field of Definition 7.16. The
branch-independent endpoint `heADC2025Lemma720iii` retains the paper's
arbitrary `nuPrime` and exact Hilbert equation. The two `isometricNamed`
endpoints then identify any other realization with the selected named
product by Lemma 7.15 and Remark 7.17.

The paper's phrase "is defined" is also formalized, rather than left as a
side convention. For each `r<=e-1`, the local-field defect-spectrum theorem
constructs a unit of defect `2r+1`; the sign of the Hilbert product selects
one of the two columns. Conversely Lemma 7.18 rules out the unit second
column at `r=e`. Thus `heADC2025Lemma720_defined_iff` proves that, throughout
the paper's index and parameter domains, Definition 7.16 is inhabited
exactly away from `(nu,r,c)=(2,e,U)`.

## Statement-strength conclusion

The public endpoints retain `0<=r<=e`, `c` of order zero or one, the exact
odd defect `2r+1`, and the Hilbert-symbol equation. The defect unit,
column choice, good BONG, `n`-ADC property, penultimate order, ambient
isometry, named-lattice isometry, and unique exceptional triple are all
proved internally. The encoded result is therefore `LOGICALLY_EQUIVALENT`
to Lemma 7.20 under the paper's standing local-field and good-BONG
conventions.

## Mechanical trust checks

At the stated code checkpoint, all three Lemma 7.20 modules,
`Bong.Papers.He2023ADC`, and `BongTest.He2023ADCAudit` compile directly with
Lean 4.32.1. The eleven selected Lemma 7.20 dependency reports contain
exactly `propext`, `Classical.choice`, and `Quot.sound`. The focused enforcing
gate reports `AXIOM_GATE_PASS: 59643 declarations checked`. The comment-aware
scanner checks 2,738 tracked Lean files without a forbidden proof token
outside comments. The scoped 100-column check and `git diff --check` pass.

These are local checks at the stated revision. Exact-revision Review Kit CI,
release promotion, and independent human sign-off remain separate gates.

## Coverage consequence

Section 7 now has seventeen fully formalized numbered items: Theorems 7.1
and 7.4; Lemmas 7.5--7.12 and 7.14--7.15; Definition 7.16; Remark 7.17; and
Lemmas 7.18--7.20. Lemma 7.13 remains a documented quantifier mismatch.
Theorem 7.2, Remark 7.3, and Corollary 7.21 remain pending.

Author decision: unsigned. Domain-expert decision: unsigned.
Formalization-expert decision: unsigned.
