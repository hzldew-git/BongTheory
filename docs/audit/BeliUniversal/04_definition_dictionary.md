# Definition dictionary

| Paper notation | Lean object | Fidelity note |
| --- | --- | --- |
| `Q(M) subseteq O` | `Lattice.IsIntegral q L` | Equivalent norm-ideal formulation is proved. |
| `Q(M)=O` | `Lattice.IsUniversal q L` | Literal equality of value sets. |
| scalar representation | `Lattice.RepresentsScalar q L a` | Equivalent existential-vector formulation is proved. |
| universal quadratic space | `QuadraticSpace.IsLineUniversal q` | Represents every nonzero rescaled line. |
| good BONG `a_1,...,a_m` | `BONG.GoodBONG q L m` | Lean indices are zero based. |
| `R_i` | `a.order (i-1)` | Exact one-based/zero-based shift. |
| `alpha_i` | `a.alphaValue (i-1)` | Rational-valued finite invariant. |
| `[a_1,...,a_k]` isotropic | `DiagonalIsotropic (a.prefixValues k ...)` | Out-of-range prefixes cannot be formed. |
| Case I / Case II | `UniversalCaseI` / `UniversalCaseII` | Rank-dependent clauses carry typed guards. |
| floor of an integral half-gap | integer division `(gap / 2 : Int)` | Division by positive two is floor division. |
| Jordan component `M_k` | `J.component k` | `J` is a strict Jordan decomposition. |
| `u_k` | `J.UniversalNormOrder k` | Effective norm order used in Theorem 3.1. |
| `r_k` | `J.fundamentalScaleOrder k` | Order of the component scale ideal. |
| `w_k` | `J.fundamentalWeightIdeal k` | Exact ideal, with a separate order theorem. |
| `f_k` | `J.fundamentalIdeal z` | Boundary `k` is represented by zero-based `z=k-1`. |
| `4 p^s` | `powerIdeal (2*e+s)` | Since `ord(4)=2e`. |
| first components isotropic | `ComponentIsIsotropic`, `ComponentPrefixIsIsotropic` | Uses the actual prescribed Jordan decomposition. |
| `n`-universal | `Lattice.IsNUniversal q L n` or the model-level equivalent | Quantifies over all integral rank-`n` lattices. |
| `O`-maximal | `Lattice.IsOMaximal q L` | Maximal among integral superlattices. |
| Witt index at least/exactly `k` | `HasWittIndexAtLeast`, `HasWittIndexExactly` | Defined through standard half-hyperbolic summands. |
| printed Theorem 3.1 RHS | `UniversalTheorem31Conditions` | Preserves the paper's `r_1` coefficient. |
| direct Theorem 3.1 RHS | `UniversalTheorem31DirectConditions` | Uses the `2r_1` coefficient obtained from Theorem 2.1. |
