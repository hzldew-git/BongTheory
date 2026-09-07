# Sections 5 and 8 logical checkpoint

Status: `CONDITIONAL_FORMALIZATION` / `SOURCE_LOGIC_MATCH`.

Code checkpoint:
`d447cd3af10de9ff176df7f9bb48594d72fc4e44` on
`feat/he-formalization`.

## Source authority and locators

The semantic authority is the published *Documenta Mathematica* version,
DOI 10.4171/DM/1003, SHA-256
`E26190C88B16624DCCB7F269C6C3FFDA02BC6830677A5BC0C8E0AD48A36E72D6`.
Theorem 5.1 and Lemmas 5.2--5.4 are printed on pp. 996--997. Lemma 8.1,
Theorem 8.2, and Corollary 8.3 are on p. 1017; the proof of Theorem 1.7,
Lemma 8.4, and Corollary 8.5 are on p. 1018. The later arXiv revision is
comparison-only.

## Section 5

`HeADC2025NonDyadicSystem` supplies an abstract interface for non-dyadic
local lattices, ambient spaces, Jordan components, the four square classes,
and the two maximal-lattice columns. `SectionFiveLaws` lists the earlier
non-dyadic Jordan and Section 4 inputs used by the publisher. None of the
numbered Section 5 conclusions is a field of that structure.

From those inputs the formalization proves:

- `heADC2025Lemma52`;
- all four clauses `heADC2025Lemma53i`--`heADC2025Lemma53iv`;
- `heADC2025Lemma54`, in both ranks `n+1` and `n+2`; and
- `heADC2025Theorem51`, the exact maximality/`n`-ADC equivalence for those
  ranks and `n>=2`.

The finite square-class choices used in the paper are implemented by
inductive types, so no informal choice of an omitted class remains inside
the deductions. The remaining boundary is concrete: the repository does
not yet instantiate `SectionFiveLaws` with non-dyadic local quadratic
lattices and prove its Jordan and maximal-lattice fields.

## Section 8 and global main results

`HeADC2025GlobalData` extends the existing global/local interface with genus,
isometry, global maximality, scaling, and stability. `SectionEightLaws`
exposes the precise number-field inputs used by the source: localization of
maximality, local Theorem 1.5, class-number-one regularity, the Meyer--Xu--
O'Meara distinguishing lattice, transport inside a genus, and scaling
stability.

Relative to those inputs, the formalization proves:

- both clauses of Lemma 8.1;
- Theorem 8.2 and Corollary 8.3;
- both local/global clauses of Theorem 1.5;
- Theorem 1.7;
- Lemma 8.4; and
- Corollary 8.5.

The proof of Corollary 8.3 explicitly transports a represented
distinguishing lattice through the genus before applying `n`-regularity.
Theorem 1.7 explicitly combines local maximality and class number one; it is
not reduced to either condition alone.

The concrete arithmetic content of the fields remains to be implemented.
In particular, `distinguishing_rank_sublattice` packages the source's Meyer,
Xu, spinor-genus, and O'Meara 104:5 input. Kernel acceptance of the resulting
theorems does not prove that package for number fields.

## Trust and mechanical evidence

At the stated checkpoint, both new modules, the canonical paper entry, and
the expanded audit module compile with Lean 4.32.1. Selected `#print axioms`
reports for every exported numbered endpoint contain only `propext`,
`Classical.choice`, and `Quot.sound`. No new Lean `axiom`, `opaque`, `sorry`,
or `admit` declaration is introduced: both law packages are ordinary
proposition-valued structures supplied as theorem hypotheses.

Exact-revision clean Review Kit CI, concrete instances of the two law
packages, and independent human semantic approval remain separate gates.
