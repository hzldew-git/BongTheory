# A nonmaximal integral lattice at the unresolved quaternary boundary

Date: 2026-09-05. Frozen code:
`9ec46e699552b375ad981b29511bf87973ca6370`. This report covers
`He2023ADCQuaternaryBoundaryCandidate`, its canonical-entry import, and its
seven new axiom queries. Later representation-condition work is excluded.

## Exact claim and verdict

`Bong.BONG.GoodBONG.exists_heADCQuaternaryBoundaryCandidate` constructs,
over every field in the stated dyadic context, an actual full integral
nonmaximal lattice in the fixed space W_2^4(Delta), together with a good
BONG of orders `(0,-2e,1,3-2e)`. It has no 2-ADC assumption or conclusion.

Classification: `NO_PAPER_COUNTERPART`, a proved supporting construction.
Independent AI review found no substantive mismatch within this scope.
There is no increase in completed numbered-paper results. In particular,
this construction neither proves nor refutes Lemma 6.8(iv), and does not
complete Theorem 6.2. Whole-paper Grade C and `NOT_COMPLETE` remain.

## Source anchor and semantic checks

The sole paper authority remains the publisher version of record, Doc.
Math. 30 (2025), 981--1022, DOI 10.4171/DM/1003, PDF SHA-256
`E26190C88B16624DCCB7F269C6C3FFDA02BC6830677A5BC0C8E0AD48A36E72D6`.
The independent reviewer visually rechecked Lemma 4.11(ii), p. 994, before
comparing its use in the nonmaximality argument.

The tail is constructed from an admissible binary parameter multiplied by
a uniformizer square. Admissibility is proved by an explicit integral-shear
witness. The exact binary BONG is then realized, not assumed. Its first
order is 1, which proves norm integrality; negative later BONG orders are
not treated as integral coefficients of a diagonal lattice basis.

The extension adjoins the literal half-hyperbolic plane. Coordinate-square
rescaling identifies only quadratic spaces. A subsequent isometry maps
the whole lattice into the fixed W_2^4(Delta) coordinates and transports
the BONG and its orders. Thus the final existence statement is about an
actual lattice, not a numerical profile or an unspecified model.

If the constructed lattice were maximal, uniqueness of the maximal
lattice and the proved published Lemma 4.11(ii) would force last order
`1-2e`, contradicting `3-2e`. This proof does not invoke Lemma 6.8 and does
not assume ADC. For e=1 the profile is `(0,-2,1,1)`, still distinct from the
maximal profile.

## Reproducibility and trust boundary

Main and independent frozen-source replay passed the new module, canonical
entry, and full ADC audit with Lean 4.32.1. All 166 printed axiom reports
stay within the standard allowance. Each of the seven new theorem reports
contains exactly `propext`, `Classical.choice`, and `Quot.sound`. The
independent focused imported-environment gate reports
`AXIOM_GATE_PASS: 57679 declarations checked`.

The main supplemental scan passed on 2688 tracked Lean files. The
independent replay wrote neither source files nor `.olean` artifacts.
These were cached-local checks. Existing dependency modifications and
Git-state warnings were preserved, not repaired or substituted. Neither
this reviewer nor the earlier clean f6f7485/c82668b run certifies a clean
build of this later commit. Reproducibility is `PARTIALLY_REPRODUCIBLE`.

## Remaining question and human review

It remains necessary to prove or disprove that the actual candidate is
2-ADC, by checking every relevant integral binary lattice or a proved
complete maximal-testing family. Checking some tests is not sufficient.
A missing printed low-rank argument is not itself a refutation. Any
future source discrepancy must be stated separately from the published
target; this report authorizes no silent change to that target.

Human author, domain-expert, and formalization-expert confirmations remain
unsigned. No `VERIFIED_MATCH` approval is claimed.
