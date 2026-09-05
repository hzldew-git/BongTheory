# Binary representation conditions below the discriminant endpoint

Date: 2026-09-05. Frozen code:
`a074fae4509dfd00d1c3c389099dcaa16085b503`. Scope:
`He2023ADCQuaternaryBoundaryConditions`, its canonical-entry import, and
its twelve new axiom queries. Later candidate-instantiation and endpoint
modules are excluded.

## Exact scope and independent verdict

`heADCBoundary_represents_finite` proves an actual integral representation
from a rank-four lattice with profile `(0,-2e,1,3-2e)` to a rank-two target
with orders `(0,1-d)`, for `0 <= d < 2e`. It retains explicit hypotheses
that the source head is split, the source full raw defect is `2e`, the
target signed raw defect is `d`, and the ambient space is represented.
The field, source carrier, and target carrier have independent universes.

This is `NO_PAPER_COUNTERPART` supporting mathematics. Independent AI
review detected no discrepancy within the stated scope. It is not a proof
of 2-ADC, not a refutation, and not additional numbered-paper coverage.
In particular, "finite" in the declaration name does not include `d=2e`.
The discriminant endpoint and infinite defect are outside this theorem.

## Source and four-condition audit

The reviewer independently read Theorem 3.6, pp. 989--990, in the publisher
version of record before inspecting the formal statement. The PDF hash is
`E26190C88B16624DCCB7F269C6C3FFDA02BC6830677A5BC0C8E0AD48A36E72D6`,
DOI 10.4171/DM/1003. The proof applies the literal published capped-defect
form of the theorem.

Condition (i) holds by the direct order inequalities at both indices.
For (ii), the first half-gap bound is nonpositive. The second primary
candidate is at most `d`, because the mixed prefix has odd valuation and
defect zero. The second comparison defect is exactly `d`: the source
internal cap is `alpha_2 = 2e + 1/2`, and the target's terminal cap is
omitted. These are explicit calculations, not assumptions of the final
representation-condition package.

For (iii), the split binary head represents the required line. At the
terminal index the published strict trigger would require
`d > 4e-2-d`, impossible for `d <= 2e-1`. Both full-prefix caps are absent
in that terminal calculation. For (iv), the only index is 2, and its
trigger is impossible from target integrality and `e >= 1`.

Raw and capped defects remain distinct throughout. The proof includes
`d=0`, `d=2e-1`, and `e=1`. At the upper boundary the comparison is equality,
so the strict trigger still fails. No complete testing-family hypothesis
or ADC conclusion is hidden in the helper statement.

## Reproducibility and trust

Main and independent frozen-source replay passed the module, canonical
entry, and full ADC audit with Lean 4.32.1. All 178 printed axiom reports
have no unexpected axioms; each of the twelve new sets is exactly
`propext`, `Classical.choice`, and `Quot.sound`. The independent focused
gate passed on 57,708 imported declarations. The main supplemental scan
passed on 2689 tracked Lean files, with 100-column checks on the new file.

The independent reviewer used standard input and existing caches without
writing source or `.olean` files. Existing dependency dirty-state warnings
remain. This is not a clean CI rebuild or release certification of the
frozen revision. Reproducibility: `PARTIALLY_REPRODUCIBLE`.

## Remaining obligations

The retained mathematical hypotheses must be instantiated for the actual
candidate and each relevant target. The `2e` and infinite-defect tests
must be handled separately. Finally, the complete-maximal-testing reduction
must be applied. Until those tasks are checked, the n=2 case of published
Lemma 6.8(iv) remains unresolved. Whole-paper Grade C, `NOT_COMPLETE`,
and unsigned human-review cards remain unchanged.
