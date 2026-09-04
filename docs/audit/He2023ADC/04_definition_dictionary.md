# Definition dictionary

| Paper notion | Lean declaration |
|---|---|
| local `n`-ADC | `Bong.Lattice.IsNADC` |
| integral lattice | `Bong.Lattice.IsIntegral` |
| ambient space representation | `QuadraticSpace.Represents` |
| integral lattice representation | `Bong.Lattice.Represents` |
| `O_F`-maximal | `Bong.Lattice.IsOMaximal` |
| global `n`-ADC | `GlobalLocalLatticeSystem.IsGloballyNADC` (abstract system) |
| global `n`-universality with compatible signatures | `GlobalLocalLatticeSystem.IsGloballyNUniversal` (abstract system) |
| `n`-regular | `GlobalLocalLatticeSystem.IsNRegular` (abstract system) |
| alternating orders followed by a table tail | `heADCMaximalOrderProfile` |
| arbitrary-lattice equivalence on a specified table space | `GoodBONG.HeADCMaximalProfileCriterion` |

The last predicate expands to: for every good BONG `a` of `L`, if `L` is
integral and its space is isometric to the reference space, then `L` is
integrally isometric to the reference lattice if and only if every order of
`a` equals the displayed profile. Its BONG argument identifies the reference
space, lattice and rank; it does not assume the desired equivalence.

The source uses one-based indices. In Lean the even zero-based positions
correspond to the source's odd positions, with order zero; the odd zero-based
positions of a hyperbolic block have order `-2e`.
