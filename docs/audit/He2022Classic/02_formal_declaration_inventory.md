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
- `Bong.BONG.GoodBONG.he2022ClassicTheorem15`: proves e = 1 for a fixed dyadic
  field, n >= 2, source rank at least n + 3, classic n-universality, and all
  unsigned adjacent defects greater than one. It has no global conclusion.
- `Bong.BONG.GoodBONG.he2022ClassicCorollary63_even`: even branch only.
- `Bong.Lattice.QuadraticLatticeModel.he2022ClassicLemma74_even`: even-rank
  testing equivalence, not the full minimality theorem.
- `Bong.Lattice.QuadraticLatticeModel.he2022ClassicLemma71ii_literal_disjunction_fails`:
  a refutation of the literal publisher disjunction, not its formal proof.

`BongTest/He2022ClassicAudit.lean` exposes additional branch endpoints and
their transitive axiom reports. No endpoint is claimed for full Theorem 1.3.
