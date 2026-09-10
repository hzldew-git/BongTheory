# Definition dictionary

| Paper notion | Lean declaration |
|---|---|
| classic integral | `Bong.Lattice.IsClassicIntegral` |
| classic `n`-universal | `Bong.Lattice.IsClassicNUniversal` |
| classic-maximal | `Bong.Lattice.IsClassicMaximal` |
| scale ideal `s(L)` | `Bong.Lattice.scaleIdeal` |
| ordinary integral | `Bong.Lattice.IsIntegral` |
| integral representation | `Bong.Lattice.Represents` |
| global lattice and finite localization system | `Bong.GlobalLocalLatticeSystem` |
| positive definite global rank-`n` representation hypothesis | `HeClassic2024GlobalData.RepresentsAllPositiveDefiniteClassicAtRank` |
| Proposition 8.2 globalization/localization inputs | `HeClassic2024GlobalData.Proposition82Laws` |
| Theorem 1.9 local-to-global inputs | `HeClassic2024GlobalData.SumOfSquaresLocalGlobalLaws` |

The formal definition includes source classic integrality rather than relying
on a standing prose convention.

`Proposition82Laws.positiveDefinite_globalization` represents the O'Meara
81:14 step only at the interface level.  It does not itself define or
construct a concrete number-field lattice; see Report 27.
The `strong_approximation` field in `SumOfSquaresLocalGlobalLaws` is likewise
an explicit arithmetic interface, not a proved concrete number-field theorem;
see Report 29.
