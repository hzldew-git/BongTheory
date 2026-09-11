# Definition dictionary

| Paper notation | Lean declaration |
|---|---|
| integral lattice | `Bong.Lattice.IsIntegral` |
| `n`-universal | `Bong.Lattice.IsNUniversal` |
| good BONG `a_1,...,a_m` | `Bong.BONG.GoodBONG` |
| `R_i` | `heHuOrder a i ...` or zero-based `a.order` |
| `d(-a_j a_{j+1})` | `heHuAdjacentDefect a j ...` or `a.adjacentDefect` |
| `d(a_1...a_i)` | `heHuPrefixDefect a i` |
| `c in F^x \ (F^{x2} union Delta F^{x2})` | `HeHuSharpDomain c` |
| `c#` | `heHuSharp c hc` (canonical equivalent choice) |
| `[1,-c]` | `heHuBinaryFirst c` |
| `[c#,-c#c]` | `heHuBinarySecond c hc` |
| `W_1^{2p+2}(c)`, `W_2^{2p+2}(c)` | `heHuEvenFirst p c`, `heHuEvenSecond p c hdefined` |
| `W_1^{2p+3}(c)`, `W_2^{2p+3}(c)` | `heHuOddFirst p c`, `heHuOddSecond p c` |
| represents every `n`-space except `W` | `HeHuMissesExactly W V` |
| unique excluding `(n+2)`-space | `HeHuUniqueExcludingTarget W V` |
| `x in [r,s]_E` | `HeHuInEvenInterval x r s` |
| `O_F`-maximal | `Bong.Lattice.IsOMaximal` |

Lean uses zero-based `Fin`; named translators document the paper's one-based
indices.  The published Definition 3.1 chooses a representative from an
auxiliary unit expansion.  Lean instead chooses one from the proved
Proposition 3.2 characterization; Proposition 3.3 proves that the resulting
binary isometry class is the same choice-independent object used later.
