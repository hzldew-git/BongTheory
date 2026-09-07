# Remark 7.3 explicit models

Status: `FULLY_FORMALIZED` / `PROVISIONAL_MATCH`.

Code checkpoint:
`287b202cfd78c97efe00761798c6914d9715e151` on
`feat/he-formalization`.

## Source authority and locator

The semantic authority is the published *Documenta Mathematica* version,
DOI 10.4171/DM/1003, SHA-256
`E26190C88B16624DCCB7F269C6C3FFDA02BC6830677A5BC0C8E0AD48A36E72D6`.
Remark 7.3 is printed on p. 1006. The later arXiv revision is
comparison-only.

For odd `n`, the publisher prints three integral-isometry formulas. For
`delta in U \ {1,Delta}` and `2l=d(delta)-1<=2e-2`, the first two are

`N_1^(n+1)(delta) isometric H^((n-1)/2) perp`
`pi^-l A(pi^l,-(delta-1)pi^-l)`

and

`N_2^(n+1)(delta) isometric H^((n-1)/2) perp`
`delta# pi^-l A(pi^l,-(delta-1)pi^-l)`.

For `epsilon in U`, the third is

`N_2^(n+2)(epsilon) isometric H^((n-1)/2) perp`
`(1/2)pi A(2,2rho) perp <Delta epsilon>`.

The audit treats every sign, exponent, scale, product order, and parameter
domain in these displays as semantically material.

## First and second displayed formulas

`heADC2025Remark73Plane delta l` is the literal general plane
`A(pi^l,-(delta-1)pi^-l)`. Its nondegeneracy is proved directly. The
normalization theorem identifies `ord(delta-1)` with the finite quadratic
defect of the selected representative.

`HeADC719UnitDefectData.exists_remark73Exponent` derives an integer `l` and
all three printed constraints:

- `2l=d(delta)-1`;
- `0<=l`;
- `2l<=2e-2`.

The normalized binary determinant parameter is proved to be
`-delta*pi^(-2l)`. The prescribed shear is exactly `pi^-l`; its two
integrality conditions are derived from the displayed defect order and the
bound `l<e`. A direct Gram calculation then identifies the binary model with
the scaled general plane. Binary-shear uniqueness proves that the result is
independent of the arbitrary admissible shear selected by the canonical
model.

The Lemma 7.19 base isometries identify the two explicit binary towers with
the named `N_1` and `N_2` lattices. Extending the binary isometry through the
common half-hyperbolic tower proves:

- `heADC2025Remark73_firstPublished` with outside scale `pi^-l`;
- `heADC2025Remark73_secondPublished` with outside scale
  `delta#*pi^-l`.

Both the finite representative system and the exclusions of the square and
discriminant classes are inherited from the exact Theorem 7.2 base index.

## Third displayed formula

`heADCAForm` was already verified by its Gram matrix to be
`(1/2)A(2,2rho)`. The new discriminant-binary theorem proves an integral
isometry from the exact unit-row endpoint to `pi*heADCAForm`. It uses the
standard shear `1/2` and proves its agreement with the canonical admissible
shear inside the integral lattice.

The source ternary model is ordered as

`<Delta epsilon> perp pi*heADCAForm`.

The formal ternary isometry applies the binary identification and then the
proved orthogonal-product swap, yielding exactly the printed order

`pi*heADCAForm perp <Delta epsilon>`.

An auxiliary unit of defect `2e-1` is constructed from the dyadic defect
spectrum. The corresponding rank-three lattice is maximal by the proved
He--Hu proposition. Its diagonal representation gives the required ambient
isometry to the named `W_2` space; maximal-lattice uniqueness then identifies
it integrally with `N_2`. Extending through the common hyperbolic tower gives
`heADC2025Remark73_thirdPublished`.

That theorem holds for every valuation unit `epsilon`, which is stronger in
parameter generality. The wrapper
`heADC2025Remark73_thirdPublishedRepresentative` specializes it to
`epsilon=U i`, exactly matching the printed domain `epsilon in U`.

## Statement-strength verdict

The three representative-system endpoints are `LOGICALLY_EQUIVALENT` to
the three formulas printed in Remark 7.3 under the same explicit convention
for `U` used by Theorem 7.2. Every conclusion is an integral lattice
isometry. None is weakened to equality of coefficient lists, equality of
orders, or ambient quadratic-space isometry.

The unrestricted unit version of the third formula is
`LOGICALLY_STRONGER` only in its parameter domain; the exact printed
specialization is separately exported. All local-field and representative
hypotheses remain visible in the public types. The semantic verdict remains
provisional pending author and independent domain-expert sign-off.

## Trust and mechanical evidence

At the stated checkpoint:

- `He2023ADCRemark73.lean`, the canonical paper entry, and the paper audit
  compile directly with Lean 4.32.1;
- eight selected dependency reports contain exactly `propext`,
  `Classical.choice`, and `Quot.sound`;
- the focused transitive gate reports
  `AXIOM_GATE_PASS: 59743 declarations checked`;
- the comment-aware scanner checks 2,741 tracked Lean sources and finds no
  forbidden proof token outside comments;
- the scoped 100-column check and `git diff --check` pass.

The warnings about locally modified `mathlib`, `aesop`, and `batteries`
dependency worktrees were pre-existing and were not edited. Exact-revision
clean Review Kit CI, release packaging, and human semantic approval remain
pending. Section 7 now has 19 of 21 numbered items fully formalized. Lemma
7.13 retains its documented source mismatch, and Corollary 7.21 remains the
only unformalized numbered item in Section 7.
