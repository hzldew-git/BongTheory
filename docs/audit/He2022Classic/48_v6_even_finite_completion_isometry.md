# He Classic v6: even classic-universal finite-completion isometry

Status: `G_WORKTREE_DEVELOPMENT` / `TARGET_MODULE_BUILT` /
`GRADE_D_NOT_COMPLETE` / `NOT_RELEASE_EVIDENCE`.

The semantic source is the user-approved author-held
`classic_dyadic-n-uni-v6.tex`, SHA-256
`4D3903083188E2823CCA930477A43F82A1FC3C69AD96056ADB099D924B14EC5A`.
The manuscript remains outside Git and Review Kits.

## Proved bridge

The new helper
`Bong.BONG.GoodBONG.he2022ClassicCorollary63_even_order_monotone`
exports the lower good-BONG order monotonicity already proved within the
corrected even-rank Corollary 6.3. The original Corollary 6.3 theorem and
its statement are unchanged. The theorem
`Bong.HeClassic2024NumberFieldScalarExtension.completionScalarExtension_isIsometric_diagonalRealization_of_evenUniversal`
combines this helper, the Corollary 6.3 lower integral-basis equality, the
proved order-scaling bridge across a prime lying over a dyadic prime, and
the actual finite-completion scalar-extension isometry. For a classic
`n`-universal lower lattice with even `n >= 2`, the literal tensor scalar
extension is isometric to a standard upper diagonal realization whose BONG
values are exactly the images of the lower BONG values.

The proof uses the actual completion embedding and its established
valuation-ring preservation. It does not assume lower basis equality or
upper order monotonicity as separate hypotheses. Both new declarations
were checked by Lean from source and in their isolated Lake targets; the
focused audit records their axiom dependencies.

## Remaining boundary

An isometry to this standard diagonal realization does **not** identify the
separately constructed upper good-BONG lattice in a common ambient space
with the paper's specified scalar-extension lattice. It does not prove
literal carrier equality or the ramified local obstruction in Lemma 8.3.
Concrete Section 8 global arithmetic/approximation instances and human
semantic sign-off also remain open. This is **Grade D / NOT_COMPLETE**, not
a complete proof or release certificate.
