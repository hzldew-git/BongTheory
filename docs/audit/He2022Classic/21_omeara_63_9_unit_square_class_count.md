# O'Meara 63:5 and 63:9 square-class counts

Historical checkpoint: its claim that the odd-testing obstruction remains
predates author-corrected v5. Report 22 records the later closure; all counting
results below remain current.

This checkpoint removes the entire paper-specific counting interface used for
He, Proposition 2.8(ii). It does not resolve the separate odd-rank
testing-sufficiency obstruction.

## Internal derivation

`heClassicUnitRepresentativeClass` sends each entry of the finite published
system `U` to its class in
`O_F^times / O_F^{times 2}`. Completeness and irredundancy of `U` prove this
map surjective and injective, respectively. The resulting finite equivalence
transports the theorem
`Bong.Dyadic.card_valuationUnitClass`, already proved from the principal-unit
filtration, to

```text
Fintype.card I = 2 * (N p) ^ e.
```

The theorem is exposed as `card_heClassicUnitRepresentatives`. Hence
`he2022ClassicProposition28ii_odd` no longer takes
any paper-specific counting interface; its value `8 * (N p)^e` follows directly
from the four odd-table rows per unit square class.

## Defect-one balance

`heClassicUnitRepresentativeClass_mem_two_iff` proves that a published
representative has defect different from one exactly when its class lies in
the depth-two principal-unit subgroup. Restricting the full equivalence gives
`heClassicDeeperUnitRepresentativeEquiv`. The theorem
`card_principalUnitValuationClassSubgroup_two`, derived from the first paired
filtration step and O'Meara 63:9, computes this subgroup as
`2 * (N p)^(e-1)`. Partitioning `U` then proves
`card_heClassicDefectOne_balance`, the O'Meara 63:5 equality.

All three `he2022ClassicProposition28ii_*` endpoints now invoke these concrete
theorems and take no paper-specific counting premise.

## Verification

The defining module compiles with Lean 4.32.1. The canonical Classic audit
checks the maps, restricted equivalence, both counting theorems, and all three
numerical formulas, and prints their transitive axioms. The expected trust
boundary is `propext`, `Classical.choice`, and `Quot.sound`; no paper-specific
counting axiom is used.

This checkpoint is local only. In accordance with the deployment manifest,
no He Classic Review Kit or GitHub release is authorized at this stage.
