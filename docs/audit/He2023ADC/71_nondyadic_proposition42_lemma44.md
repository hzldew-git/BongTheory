# Non-dyadic Proposition 4.2 and Lemma 4.4 invariant derivation

## Status

Checkpoint: `ae494c5f23391e7f84eaaf4a428dcdd6471f7436`.

Classification: `CONDITIONAL_FORMALIZATION` / `SOURCE_LOGIC_MATCH`.
Proposition 4.2(ii)--(iii) and all three parts of Lemma 4.4 are derived from
an explicit determinant--Hasse--Hilbert invariant interface. No table
exhaustion, table-row uniqueness, codimension-one/two table representation,
unique-excluding-space conclusion, or Lemma 4.6 conclusion is an input field.

## Authoritative source and exact scope

The sole statement authority is Zilong He, *On n-ADC integral quadratic
lattices over algebraic number fields*, *Documenta Mathematica* 30 (2025),
no. 4, 981--1022, pp. 990--993, DOI 10.4171/DM/1003. Publisher-PDF SHA-256:

`E26190C88B16624DCCB7F269C6C3FFDA02BC6830677A5BC0C8E0AD48A36E72D6`.

The formal endpoints preserve the publisher's standing definedness
conditions from (4.1). In particular, the second unary row and
`W_2^2(1)` are never treated as published spaces. The source statements are
represented as follows:

| Source item | Lean endpoint | Scope check |
|---|---|---|
| Proposition 4.2(ii) | `heADC2025Proposition42iiNonDyadic` | Every rank-`n` space, `n >= 1`, is isometric to a defined table row |
| Proposition 4.2(iii), all remaining spaces | `heADC2025Proposition42iiiNonDyadic` | The displayed opposite-column rank-`n+2` space represents every rank-`n` space not isometric to the named exception |
| Proposition 4.2(iii), exclusion | `heADC2025Proposition42iiiNonDyadic_excludes` | The displayed space does not represent the named exception |
| Proposition 4.2(iii), uniqueness | `heADC2025Proposition42iiiNonDyadic_unique` | Every rank-`n+2` space failing to represent that exception is isometric to the displayed space |
| Lemma 4.4(i) | `heADC2025Lemma44iNonDyadic` | Same-rank representation/isometry holds exactly for equal column and parameter |
| Lemma 4.4(ii) | `heADC2025Lemma44iiNonDyadic` | The Hilbert-symbol sign is the exact parity of the two columns |
| Lemma 4.4(iii) | `heADC2025Lemma44iiiNonDyadic` | Codimension-two representation holds exactly when parameters differ or both row indices agree |

The Boolean convention in part (ii) sends Hilbert symbol `+1` to `false`
and `-1` to `true`. Hence `Bool.xor nu'.hasseBit nu.hasseBit` is precisely
the source sign `(-1)^(nu' + nu)`.

## Formal construction

`Bong.Bong.He2023ADCNonDyadicProposition42` introduces
`Proposition42InvariantData`, consisting of:

- the normalized four-valued parameter of every quadratic space;
- the determinant class attached to a parameter; and
- the two-valued Hilbert symbol on parameters.

`Proposition42Laws` exposes only lower-level local-space facts:

- the Section 5 rank laws and the determinant--Hasse classification and
  codimension criteria from Report 70;
- reflexivity of isometry and transport of representation across isometry;
- injectivity of parameterized determinant classes and the determinant/Hasse
  values of the displayed rows;
- the Hasse bit forced in each omitted low-rank second-column case;
- automatic codimension-two representation for unequal determinant classes;
  and
- the codimension-one and codimension-two expected Hasse signs of the
  displayed stabilized rows.

From these inputs, Lean proves:

1. equal determinant and opposite Hasse bits for the two defined columns;
2. table-row uniqueness, including the converse by reflexivity;
3. the exact Hilbert-symbol criterion in codimension one;
4. the exact determinant/row criterion in codimension two;
5. exhaustion of all non-dyadic spaces, including both omitted-row boundary
   cases;
6. representation of every nonexceptional rank-`n` space, failure on the
   exception, and uniqueness of the rank-`n+2` excluding space.

The refactored `Lemma46Laws` now contains only a `Proposition42Laws` package
and actual-lattice-to-ambient representation. Its former target-pair
determinant, target-pair nonisometry, Proposition 4.2(iii), and isometry
transport fields have all been removed. Lemma 4.6(ii) invokes the proved
Proposition 4.2(iii) endpoint.

## Mechanical evidence

With Lean 4.32.1 at the checkpoint above:

- the focused Proposition 4.2/Lemma 4.4 audit completes 3,001 jobs;
- the canonical paper entry, canonical audit, Proposition 4.2 audit, and
  refactored Lemma 4.6 audit complete 5,564 jobs;
- Lemma 4.4(i) and Proposition 4.2(ii) report only `propext`;
- Lemma 4.4(ii)--(iii), and the exclusion endpoint report only `propext` and
  `Quot.sound`;
- Proposition 4.2(iii)'s all-other-spaces endpoint additionally reports
  `Classical.choice`, while its uniqueness endpoint reports only `propext`
  and `Quot.sound`;
- the existing Lemma 4.6 endpoints retain only the documented standard
  axioms;
- the comment-aware scanner checks 2,784 tracked Lean sources;
- all 27 CI policy tests pass; and
- changed Lean lines are at most 100 columns and `git diff --check` passes.

This is local exact-checkpoint evidence. It is not yet a fresh-extraction
Review Kit receipt or GitHub exact-tag evidence.

## Remaining trust boundary

The repository still needs a concrete non-dyadic local-field model providing
the invariant data and lower-level laws above. In particular, Lean has not
constructed a non-dyadic local field, its square-class/Hilbert-symbol
calculus, the actual displayed quadratic spaces and maximal lattices, or the
Jordan/classification laws from the existing dyadic hierarchy. These are
explicit proposition-valued mathematical inputs, not Lean axioms.

Human source-to-formalization approval and exact-revision clean-kit CI also
remain separate gates.
