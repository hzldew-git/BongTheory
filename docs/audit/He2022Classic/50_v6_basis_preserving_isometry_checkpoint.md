# He Classic v6: basis-preserving scalar-extension isometry

Status: `G_WORKTREE_DEVELOPMENT` / `DIRECT_SOURCE_CHECKED` /
`FOCUSED_PARTIAL_FIDELITY_AUDIT` / `GRADE_D_NOT_COMPLETE` /
`NOT_RELEASE_EVIDENCE`.

The semantic source is the user-approved author-held
`classic_dyadic-n-uni-v6.tex`, SHA-256
`4D3903083188E2823CCA930477A43F82A1FC3C69AD96056ADB099D924B14EC5A`.
It remains outside Git and Review Kits. This focused report covers only the
new uncommitted declaration based on repository commit
`5bfbafd06be4eba1f9a2e0af279ee5de93687eee`; it is not a fresh audit
of the full manuscript or a clean-commit release receipt.

## Paper claim extracted separately

The author-corrected v6 Lemma 8.3, at TeX lines 1680-1693, assumes even
`n >= 2` and a ramified finite extension of dyadic completions. Starting
from a classic `n`-universal lower lattice of rank `n+3`, its proof uses
the lower good-BONG vectors as an integral orthogonal basis and asserts that
the *same vectors* form an integral orthogonal basis of an upper lattice in
the scalar-extended ambient space. It identifies that upper lattice with
the specified scalar extension and then proves that the latter is not
classic `n`-universal. The same-vector assertion is stronger than an
unqualified isometry between two separately realized lattices.

## Formal declaration extracted separately

`Bong.Lattice.scalarExtension_basisLattice_isIsometric_of_mappedValues_with_vectors`
is in `Bong/Lattice/He2022ClassicScalarExtensionBasisPreservingIsometry.lean`.
It takes two dyadic fields related by an algebra map, finite-dimensional
lower and upper quadratic spaces, and one BONG in each space. Its explicit
premises say that every upper BONG coefficient equals the image of the
corresponding lower coefficient and that the algebra map preserves the
integer ring. It constructs an integral quadratic-lattice isometry from
the scalar extension of the **lower BONG basis lattice** to the **upper BONG
basis lattice**. For every index, this isometry sends the pure tensor of
the lower BONG vector to the corresponding upper BONG vector.

| Issue | v6 Lemma 8.3 | New formal declaration | Assessment |
|---|---|---|---|
| Ambient | The scalar-extended space containing the given lower vectors | Two quadratic spaces joined by an explicitly constructed isometry | The isometry transports vectors but does not make the ambients literally equal |
| Lattices | The specified lower lattice and its scalar extension | Their displayed BONG basis lattices only | Equality with the specified lattices is not part of this declaration |
| Coefficients | Lower BONG coefficients viewed in the upper field | Exact coefficient images are assumed | This premise is supplied by other mapped-value results only in their stated scope |
| Vectors | The same lower vectors after scalar extension | The constructed isometry maps each pure tensor to the corresponding upper vector | A genuine basis-preserving comparison, not literal same-vector identity |
| Ramification and non-universality | Ramification index greater than one forces the upper scalar extension to fail classic `n`-universality | Neither ramification nor the obstruction appears | The main contradiction remains open |

The relationship to the full paper lemma is `PARTIAL_FORMALIZATION`, with
the new declaration proving one generic intermediate basis comparison.
It is not a `VERIFIED_MATCH` for Lemma 8.3. The BONG hypotheses are explicit;
no existence theorem for arbitrary inputs follows from this statement.

## Trust and reproducibility boundary

The new file passed direct `lake env lean` source checking in the G
worktree. The paper entry and focused audit file also passed direct source
checking after importing it. The focused audit prints only the standard
axioms `propext`, `Classical.choice`, and `Quot.sound` for this declaration.
No `sorry`, `admit`, or custom `axiom` occurs in the new source. These checks
do not replace an exact-head complete build, a clean-extraction Review Kit,
or independent human review. The current draft PR has not merged.

## Author clarification and next proof obligations

The author has now confirmed that the vectors denoted again by `x_i` after
extension are the canonical images `1 ⊗ x_i`, and that the comparison of the
specified lower scalar extension with the constructed upper lattice is a
comparison of **integral quadratic-lattice isometry classes**. It does not
require literal equality of two separately presented subsets of one fixed
ambient space. This clarification removes the common-ambient equality item
as a prerequisite for the class-level local conclusion; it does not by
itself prove ramified non-universality.

1. Specialize the basis-preserving comparison to the actual number-field
   completions and discharge its coefficient and integer-ring premises.
2. Prove the ramified local non-universality contradiction without assuming
   its conclusion, then instantiate the outstanding Section 8 global laws.
3. Obtain independent author and formalization-expert semantic sign-off.

The generic basis-preserving theorem remains an optional stronger comparison
than the class-level identification. The new concrete ramified-obstruction
work is audited separately in Report 51. This Report 50 checkpoint alone is
not a full Lemma 8.3 verification receipt. The project remains
**Grade D / NOT_COMPLETE** pending the broader audit and global instances.
