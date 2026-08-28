/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328NormalizedFirstComponents
import Bong.Lattice.OmearaScaledHyperbolicTowerInvariants

/-!
# The determinant of the normalized source head in O'Meara 93:28

After the simultaneous rank-four reduction, every source Jordan component
is a pair of scaled hyperbolic planes.  Normalizing the first component by
the inverse of its scale therefore identifies it with the normalized
standard two-plane tower.  Unimodular determinant rigidity then gives the
determinant-one hypothesis required by O'Meara 93:18(vi).
-/

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [DyadicDiscriminantClassLaws K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}
  {J : JordanDecomposition q L (n + 2)}
  {H : JordanDecomposition r M (n + 2)}

namespace Omeara9328RankFourReductionSystem

variable (S : Omeara9328RankFourReductionSystem J H)

/-- The normalized source first component is the normalized standard tower
of two zero-coefficient O'Meara planes. -/
noncomputable def sourceFirstNormalizedTowerIsometry :
    QuadraticSpace.Isometry S.sourceFirstNormalized
      ((QuadraticSpace.scaledZeroOmearaTowerForm S.firstScale 2).rescaleUnit
        S.firstScale⁻¹) := by
  let f₀ := Classical.choice (S.sourceJordan_componentSpace_hyperbolic 0)
  simpa only [sourceFirstNormalized, firstScale] using
    f₀.rescaleUnitBoth S.firstScale⁻¹

/-- The normalized source first component has refined determinant class
one, as asserted in Step 2 of the proof of O'Meara 93:28. -/
theorem sourceFirstNormalized_determinantClass :
    determinantClass S.sourceFirstNormalized
        (S.sourceJordan.component 0).lattice = 1 := by
  have htarget : IsUnimodular
      ((QuadraticSpace.scaledZeroOmearaTowerForm S.firstScale 2).rescaleUnit
        S.firstScale⁻¹)
      (scaledZeroOmearaTowerLattice (K := K) 2) :=
    (scaledZeroOmearaTowerLattice_isModular (K := K) S.firstScale 2)
      |>.isUnimodular_rescaleQuadraticInverse
  exact (determinantClass_eq_of_unimodular_spaceIsometry
    S.sourceFirstNormalized_unimodular htarget
      S.sourceFirstNormalizedTowerIsometry).trans
        (determinantClass_normalized_scaledZeroOmearaTower_two
          (K := K) S.firstScale)

end Omeara9328RankFourReductionSystem

end Lattice.JordanDecomposition

end Bong
