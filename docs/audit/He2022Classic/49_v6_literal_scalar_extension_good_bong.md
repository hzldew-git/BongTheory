# He Classic v6: good BONG on the literal scalar extension

Status: `G_WORKTREE_DEVELOPMENT` / `TARGET_MODULE_BUILT` /
`FOCUSED_PARTIAL_FIDELITY_AUDIT` / `GRADE_D_NOT_COMPLETE` /
`NOT_RELEASE_EVIDENCE`.

The semantic source is the user-approved author-held
`classic_dyadic-n-uni-v6.tex`, SHA-256
`4D3903083188E2823CCA930477A43F82A1FC3C69AD96056ADB099D924B14EC5A`.
It remains outside Git and Review Kits. This focused report compares the
Section 8 claims with one new declaration in the G worktree based on local
commit `6e08de84f31922a8e8ae2fafbe81f866e7b5eaee`. The exact checkpoint
under review is the commit containing this report. This is not a complete
new audit of the entire paper.

## Independent paper extraction

In v6 Lemma 8.1(iii), the original lower good-BONG vectors yield a good
BONG for *some* upper integral lattice on the scalar-extended quadratic
space. Lemma 8.3, in its even `n >= 2` scope and under ramification index
greater than one, goes further: it says the *same vectors* are an integral
orthogonal basis of both the lower lattice and the upper lattice. Their
integral spans are then identified, so the upper lattice is the specified
scalar extension. Lemma 8.3 also asserts that the scalar extension is not
classic `n`-universal. These claims occur at v6 TeX lines 1632-1659 and
1680-1693. The manuscript's conclusion concerns the actual scalar-extension
lattice, not merely an abstract isometry class.

## Actual formal declaration

`Bong.HeClassic2024NumberFieldScalarExtension.completionScalarExtension_hasGoodBONG_of_evenUniversal`
is in `Bong/Lattice/He2022ClassicCompletionScalarExtensionGoodBONG.lean`.
For a finite extension of number fields, a dyadic prime `p`, a prime `P`
lying over `p`, a finite-dimensional quadratic space over the lower
completion, and a lower good BONG of rank `n+3`, it assumes `n >= 2`, even
`n`, classic integrality, and classic `n`-universality. It proves that the
*literal tensor scalar-extension lattice* over the upper completion has a
good BONG whose exact coefficient values are the images under the
completion embedding of the lower good-BONG values. Dyadic contexts and
the completion algebra structure are instantiated in the theorem. The
proof obtains a standard diagonal good-BONG realization, invokes the
previously proved integral isometry from that realization to the literal
scalar extension, and transports the good BONG along the inverse isometry.

| Comparison | Paper v6 | Formal declaration | Assessment |
|---|---|---|---|
| Lower hypotheses | Even `n >= 2`, rank `n+3`, classic `n`-universal lower lattice at a dyadic place | Same parity, rank, classic integrality and universality, with finite-dimensional ambient space | Narrow formal context is explicit |
| Extension | A finite ramified extension of dyadic completions | Completions induced by a finite number-field extension and a prime lying over a dyadic prime; no `e(P|p)>1` is needed for this intermediate existence claim | Special case of the paper's local-field setting, but no ramification restriction on this intermediate theorem |
| Upper lattice | The specified scalar extension | The literal tensor scalar-extension lattice | Match for the lattice object |
| BONG values | Lower coefficient values viewed in the upper field | Exact images under the completion embedding | Match for values |
| BONG vectors | The same lower vectors after scalar extension | Vectors transported through an integral isometry; no equality with the canonical pure tensors is proved | **Missing same-vector conclusion** |
| Final obstruction | Upper lattice is not classic `n`-universal | No such conclusion | **Not formalized here** |

The theorem is a substantive bridge but only a `PARTIAL_FORMALIZATION` of
the Section 8 argument. It is not a `VERIFIED_MATCH` for Lemma 8.3. No
claim is made here that an arbitrary finite extension of dyadic local
fields has been handled independently of number fields.

## Trust and adversarial checks

The new module passed direct Lean source checking and its isolated Lake
target build from the G worktree. The focused audit imports its declaration
and prints its transitive axioms: only `propext`, `Classical.choice`, and
`Quot.sound` occur. The paper entry and all eight manifest audit modules
built at one Lake job. The focused enforcing axiom gate returned
`AXIOM_GATE_PASS: 63034 declarations checked`. A comment-aware scan found
no forbidden proof tokens in 2,818 tracked Lean sources or the new untracked
module; five deployment-policy tests passed. No `sorry`, `admit`, or custom
`axiom` token is present in the new source. The construction is not vacuous merely
because it has an existential conclusion: an actual upper good BONG is
built by transporting a realized one. Nevertheless, the theorem assumes
that a lower good BONG and classic-universal lower lattice are supplied; it
does not establish existence of such input objects, nor the local
ramified contradiction.

The proof's `IsIsometric` witness cannot be silently interpreted as the
canonical scalar-extension map on each lower BONG vector. That is the
main adversarial semantic distinction. The exact trust and reproducibility
status for this development checkpoint is limited to the targeted checks above;
it is not a clean-extraction Review Kit verification or a release.

## Remaining work and author review

1. Identify the transported upper BONG vectors with the pure tensors of
   the given lower BONG vectors, or prove the equivalent common-ambient
   basis/lattice identity required by v6 Lemma 8.3.
2. Prove the ramified local non-universality contradiction using concrete
   defect and classification data, not a bundled assumption of that result.
3. Instantiate the Section 8 global arithmetic and approximation data.
4. Obtain independent mathematical-author and formalization-expert review.

`AUTHOR_CONFIRMATION_REQUIRED`: confirm that the author's intended use of
"the same vectors" in Lemma 8.3 means the canonical images of the given
lower BONG vectors, rather than an unspecified isometric copy. Until that
point and the obstruction are resolved, the project remains **Grade D /
NOT_COMPLETE**.
