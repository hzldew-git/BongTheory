# Normalized nonexceptional binary boundary tests

Date: 2026-09-05. Frozen code:
`9a87464758b32ad47dde2436ee4ca68a2701c3f5`. This report covers
`He2023ADCQuaternaryBoundaryGeneric`, its canonical entry import, and six new
audit queries. The later arbitrary square normalization is excluded.

## Exact scope and verdict

Four public endpoints prove actual integral representations for the first and
second columns when the parameter is a valuation unit or a unit times the
uniformizer. The lower-level helper retains its determinant-class, profile,
and ambient-representation assumptions; the four named endpoints discharge
the determinant and profile facts internally.

These are `NO_PAPER_COUNTERPART` supporting results. Independent AI review
assigns `PROVISIONAL_MATCH` to their mathematical use within the boundary
argument. They do not themselves perform complete maximal testing or assert
2-ADC.

## Mathematical checks

The target order profile `(0,1-d(c))` is derived from the proved published
Lemma 4.11(iii) profiles. The binary signed determinant is `-b_1 b_2`, so the
transported defect is `d(c)`. `heHuSharpData` establishes finiteness before
`toNat` is used and proves the strict bound below `2e`. Unit-uniformizer
parameters have odd valuation and defect zero, including the case `e=1`.

The four named declarations retain only the ambient representation required by
the ADC test. They have no target-profile premise, classification-law premise,
or ADC premise.

## Trust and reproducibility

The frozen module, canonical entry, and full ADC audit passed. There were 195
axiom reports, and each of the six new dependency sets is exactly `propext`,
`Classical.choice`, and `Quot.sound`. An independent body traversal inspected
80,604 declarations and found no dependency on Lemma 6.8 or Theorem 6.2.

These were cached local checks with the disclosed dependency worktree warnings.
Reproducibility status for this increment: `PARTIALLY_REPRODUCIBLE`.
