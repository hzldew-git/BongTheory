# Formal declaration inventory

- `Bong.Lattice.IsClassicIntegral`: scale-integral lattice.
- `Bong.Lattice.IsClassicNUniversal`: representation of all classic integral
  rank-`n` lattices.
- `Bong.Lattice.IsClassicMaximal`: maximality among classic integral lattices.
- `exists_classicMaximal_superlattice`: proved extension theorem.
- `heClassicMaximalTestingReduction`: proved abstract testing equivalence.
- `HeClassicZeroOrOne`: the source alternative `R_i in {0,1}`.
- `heClassicAdjacentDefectAt`: adjacent binary defect with a zero-based index.
- `heClassicSignedPrefixDefect`: the signed prefix defect in Theorem 1.1.
- `HeClassicEvenConditions`: the complete even branch, Theorem 1.1(ii).
- `HeClassicOddConditions`: the complete odd branch, Theorem 1.1(iii).
- `HeClassicTheorem11Conditions`: the complete right-hand side of Theorem 1.1.
- `HeClassicTheorem11Statement`: the publisher theorem proposition, recorded
  as a definition and not asserted as a theorem.

The proposition-valued definition remains separate from its proof:

- `Bong.BONG.GoodBONG.he2022ClassicTheorem11`: proves the complete equivalence
  for n >= 2 and arbitrary source rank.
- `Bong.BONG.GoodBONG.he2022ClassicTheorem41` and
  `he2022ClassicTheorem51`: even and odd local criteria used by that proof.
- `Bong.BONG.GoodBONG.he2022ClassicTheorem15_unary`: proves the fixed-field
  implication at n = 1 through the scalar-universal alpha criterion.
- `Bong.BONG.GoodBONG.he2022ClassicTheorem15`: proves the fixed-field
  implication for n >= 2 through the classic criterion.
- `Bong.BONG.GoodBONG.he2022ClassicTheorem15_allRanks`: combines both branches
  over the complete published local range n >= 1. It has no global
  number-field conclusion.
- `Bong.BONG.GoodBONG.he2022ClassicCorollary63_even`: even branch only.
- `Bong.Lattice.QuadraticLatticeModel.he2022ClassicLemma74_even`: even-rank
  testing equivalence, not the full minimality theorem.
- `Bong.BONG.GoodBONG.he2022ClassicLemma710iii_largeC1_represents_other` and
  its `C2` converse: the integral `C`-row deletion witnesses outside the
  excluded ambient class; published defect-one and odd-order specializations
  are in `He2022ClassicSectionSeven.lean`.
- `Bong.Lattice.QuadraticLatticeModel.he2022ClassicLemma71ii_literal_disjunction_fails`:
  a refutation of the literal publisher disjunction, not its formal proof.

`BongTest/He2022ClassicAudit.lean` exposes additional branch endpoints and
their transitive axiom reports. The `C`-row mechanism is not yet the literal
all-indices statement, and no endpoint is claimed for full Theorem 1.3.
