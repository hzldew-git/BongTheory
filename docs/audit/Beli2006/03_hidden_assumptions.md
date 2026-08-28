# Hidden-assumption expansion

`DyadicContext K` supplies the normalized dyadic local-field data, not a
classification or representation theorem. `q.IsIsometric r` means an ambient
quadratic-space isometry. `q.Represents r` is oriented from the smaller source
space into the larger target space by an injective form-preserving linear map.
`Lattice.IsIsometric` and `Lattice.Represents` add the integral lattice
membership conditions.

`GoodBONG` packages a BONG together with the paper's goodness inequalities.
The length parameters are `n+1` and `m+1`; they encode positive ranks and
translate the paper's one-based coordinates to Lean's zero-based finite
indices.

All of these correspondences are `PROVISIONAL_MATCH` pending independent
confirmation of orientation, normalization, and endpoints.
