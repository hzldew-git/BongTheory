# He Classic v6: mapped BONG isometry bridge

Status: `G_WORKTREE_DEVELOPMENT` / `TARGET_MODULES_BUILT` /
`GRADE_D_NOT_COMPLETE` / `NOT_RELEASE_EVIDENCE`.

The semantic source remains the user-approved, author-held
`classic_dyadic-n-uni-v6.tex`, SHA-256
`4D3903083188E2823CCA930477A43F82A1FC3C69AD96056ADB099D924B14EC5A`.
The manuscript is not included in Git or Review Kits. This report advances,
but does not close, the bridge left open in Report 45.

## Proven bridge

`Bong.Lattice.He2022ClassicScalarExtensionBONGIsometry` contains three
kernel-checked theorems:

| Declaration | Exact conclusion and premises |
| --- | --- |
| `scalarExtension_basisLattice_isIsometric_of_mappedValues` | The literal scalar extension of a lower BONG **basis lattice** is isometric to an upper BONG basis lattice if their exact value units match under the field map and the lower valuation ring maps into the upper one. The proof compares the two Gram matrices, including off-diagonal entries. |
| `scalarExtension_isIsometric_of_mappedValues` | The same result for specified lattices, assuming separately that each lattice equals the integral span of its BONG basis. |
| `scalarExtension_isIsometric_diagonalRealization` | For a standard diagonal realization of the mapped values, upper-order monotonicity supplies the upper basis-lattice equality. Lower basis-lattice equality and valuation-ring preservation are still explicit premises. |

This proves a **quadratic-lattice isometry** under stated hypotheses, not
equality of lattices in one ambient space. In particular, matching BONG
coefficients alone is not used to assert equality of carriers. The theorem
does not yet specialize the heavy actual finite-completion realization of
Lemma 8.1(iii), nor prove that its separately specified upper lattice is the
literal scalar extension needed in v6 Lemma 8.3.

## Verification and remaining boundary

On the G worktree, direct Lean source checking, the isolated module target,
the canonical paper entry, and the focused even-extension audit all exited
zero with Lean 4.32.1. The focused audit's `#print axioms` reported only
`propext`, `Classical.choice`, and `Quot.sound` for all three new declarations;
no custom axiom or `sorry` is used. All eight manifest audit modules built;
the focused enforcing gate reported `AXIOM_GATE_PASS: 63031 declarations
checked`. The comment-aware scan of 2,817 staged/tracked Lean sources found
no forbidden proof token, all five deployment-policy tests passed, and the
staged diff passed `git diff --check`.

Still open: a lightweight specialization to the actual dyadic number-field
completions; use of lower Corollary 6.3 and upper monotone-order
diagonalization to identify the concrete lattices; the ramified local
obstruction of Lemma 8.3; Section 8 arithmetic and global instances; and
independent human semantic sign-off. The result remains **Grade D /
NOT_COMPLETE**. This G worktree is not an exact clean merged commit or a
verified final Review Kit, and this report claims no release.
