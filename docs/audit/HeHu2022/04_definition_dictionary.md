# Definition dictionary

| Paper notation | Lean declaration |
|---|---|
| integral lattice | `Bong.Lattice.IsIntegral` |
| `n`-universal | `Bong.Lattice.IsNUniversal` |
| good BONG `a_1,...,a_m` | `Bong.BONG.GoodBONG` |
| `R_i` | `heHuOrder a i ...` or zero-based `a.order` |
| `d(-a_j a_{j+1})` | `heHuAdjacentDefect a j ...` or `a.adjacentDefect` |
| `d(a_1...a_i)` | `heHuPrefixDefect a i` |
| `x in [r,s]_E` | `HeHuInEvenInterval x r s` |
| `O_F`-maximal | `Bong.Lattice.IsOMaximal` |

Lean uses zero-based `Fin`; named translators document the paper's one-based
indices.
