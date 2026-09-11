# Theorem 7.2 published classification

Status: `FULLY_FORMALIZED` / `PROVISIONAL_MATCH`.

Code checkpoint:
`07cd54844a61931cb8b7b6e0ec237448e94b074c` on
`feat/he-formalization`.

## Source authority and locator

The semantic authority is the published *Documenta Mathematica* version,
DOI 10.4171/DM/1003, SHA-256
`E26190C88B16624DCCB7F269C6C3FFDA02BC6830677A5BC0C8E0AD48A36E72D6`.
Theorem 7.2 is printed on p. 1006. Its proof on p. 1016 says that the result
follows from Definition 7.16, Remark 7.17, and Lemma 7.20. The later arXiv
revision is comparison-only.

For odd `n=2k+3` and a rank-`n+2` lattice, the source classifies `n`-ADC
lattices as either maximal or

`N_nu^(n+1)(delta) perp <epsilon*pi^j>`,

where `nu` is 1 or 2, `delta` runs through the published unit representative
system with the square and discriminant classes removed, `epsilon` runs
through the same unit representative system, and `j` is 0 or 1. It also
states that a lattice which is both maximal and in the displayed product
family is isometric to `N_2^(n+2)(epsilon)` for a unit representative
`epsilon`.

## Representative-independent classification

`He2023ADCTheorem72.lean` first removes the arbitrary choice of a finite
representative system. `HeADC2025Theorem72Product q L k` uses a valuation
unit `delta` whose defect is strictly below `2e`, and a line coefficient of
order zero or one. This is the intrinsic square-class content of the
published parameter restrictions.

The necessity theorem derives every premise of this product family:

- Remark 7.17 exhausts the Definition 7.16 classes.
- In a lower row `r<e`, Lemma 7.20(iii) supplies the selected column, named
  product, unit parameter, defect, and line-order data.
- At the endpoint `r=e`, Lemma 7.20(i) gives maximality. The second-column
  unit endpoint is eliminated by Lemma 7.18.

Sufficiency has no classification axiom: maximal lattices are ADC, while
each displayed product is transported from the literal integral-isometry
models proved in Lemma 7.19. Thus
`heADC2025Theorem72` is a biconditional on an arbitrary lattice carrying a
good BONG of the required length.

## Literal finite presentation

`He2023ADCTheorem72Published.lean` converts the intrinsic theorem to the
finite presentation printed in the paper. The public hypotheses are:

- `U` is a finite complete normalized representative system for unit square
  classes;
- the distinguished discriminant unit occurs in `U`.

The second hypothesis only connects the literal exclusion
`delta != Delta` to the intrinsic sharp domain. It is not a supplied
classification theorem. The two exclusions `delta != 1` and
`delta != Delta` imply the required defect bound internally.

Every intrinsic base parameter is normalized to a member of `U` by a unit
square. Every order-zero-or-one line coefficient is similarly normalized to
`epsilon` or `epsilon*pi`. The conversion proves integral lattice
isometries under these square changes for both even base columns and for the
odd second-column overlap model; it does not identify only their ambient
quadratic spaces. Consequently
`heADC2025Theorem72Product_iff_published` is a genuine equivalence between
the two families, and `heADC2025Theorem72Published` is the literal published
biconditional.

## Maximal overlap

The overlap theorem is proved rather than encoded as an extra premise.
Lemma 7.19 fixes the penultimate order of a product at `1-d(delta)`. If the
same lattice is maximal, Proposition 4.13 supplies the four normalized odd
maximal profiles. Comparing these orders eliminates the first-column unit
row and both uniformizer rows because `d(delta)<2e`. The sole remaining row
is the second-column unit class. Its unit parameter is normalized into `U`
by an integral lattice isometry. This proves
`heADC2025Theorem72Published_overlap`, the final assertion of Theorem 7.2.

## Statement-strength verdict

Under the displayed `U` completeness and discriminant-representative
hypotheses, the formal result is `LOGICALLY_EQUIVALENT` to the full published
Theorem 7.2. The representative-independent result is also retained because
it is invariant under a change of `U`. All local-field, rank, good-BONG, and
representative-system hypotheses are visible in the public types.

The proof is a provisional semantic match pending independent author and
domain-expert sign-off. This status does not rely on the false binary
boundary of Theorem 6.2 or on the stronger printed quantifier of Lemma 7.13.

## Mechanical evidence

At the stated checkpoint:

- both Theorem 7.2 proof modules, the canonical paper entry, and the
  paper-specific audit entry compile with Lean 4.32.1;
- the six selected public dependency reports contain exactly `propext`,
  `Classical.choice`, and `Quot.sound`;
- the focused axiom gate reports
  `AXIOM_GATE_PASS: 59692 declarations checked`;
- the forbidden-token scanner checks 2,740 tracked Lean sources;
- the scoped 100-column check and `git diff --check` pass.

Exact-revision clean Review Kit CI, release packaging, and human semantic
approval remain pending. Section 7 now has 18 of 21 numbered items fully
formalized. Lemma 7.13 retains its documented source mismatch; Remark 7.3
and Corollary 7.21 remain pending.
