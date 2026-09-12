/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Lattice.He2023ADCSectionEight

/-!
# He (2025), regularity transport under scaling

This file lowers the remaining scaling-regularity premise used in Lemma 8.4
and Corollary 8.5.  Instead of assuming the finished biconditional
`IsNRegular (scaleTwo M) n ↔ IsNRegular M n`, it assumes only that scaling is
surjective on the ambient global-lattice type and transports rank,
integrality, and simultaneous local and global representation.  The
regularity biconditional is then a theorem.

The fields remain an explicit arithmetic interface.  A concrete
number-field implementation must construct them from scaling of quadratic
lattices; none is declared as a project axiom.
-/

namespace Bong

universe u v w

namespace HeADC2025GlobalData

variable {S : GlobalLocalLatticeSystem.{u, v, w}}
  (G : HeADC2025GlobalData S)

/-- Primitive transport facts for multiplication of a global quadratic
lattice by two.  These are strictly below the finished regularity statement:
they concern only the underlying lattice universe and the relations appearing
in the definition of `IsNRegular`. -/
structure ScalingTransportLaws : Prop where
  scaleTwo_surjective : Function.Surjective G.scaleTwo
  globalRank_scaleTwo (N : S.GlobalLattice) :
    S.globalRank (G.scaleTwo N) = S.globalRank N
  globalIntegral_scaleTwo_iff (N : S.GlobalLattice) :
    S.globalIntegral (G.scaleTwo N) ↔ S.globalIntegral N
  localRepresents_scaleTwo_iff
      (p : S.Place) (M N : S.GlobalLattice) :
    S.localRepresents
        (S.localize p (G.scaleTwo M)) (S.localize p (G.scaleTwo N)) ↔
      S.localRepresents (S.localize p M) (S.localize p N)
  globalRepresents_scaleTwo_iff (M N : S.GlobalLattice) :
    S.globalRepresents (G.scaleTwo M) (G.scaleTwo N) ↔
      S.globalRepresents M N
  isHalfScaleOf_iff (M L : S.GlobalLattice) :
    G.isHalfScaleOf M L ↔ L = G.scaleTwo M

namespace ScalingTransportLaws

/-- `n`-regularity is invariant under simultaneous multiplication of the
source and every test lattice by two.  Surjectivity supplies a half-scaled
test lattice in the reverse direction. -/
theorem nRegular_scaleTwo_iff
    (H : G.ScalingTransportLaws) (M : S.GlobalLattice) (n : Nat) :
    S.IsNRegular (G.scaleTwo M) n ↔ S.IsNRegular M n := by
  constructor
  · intro hScaled N hRank hIntegral hLocal
    have hScaledRank : S.globalRank (G.scaleTwo N) = n :=
      (H.globalRank_scaleTwo N).trans hRank
    have hScaledIntegral : S.globalIntegral (G.scaleTwo N) :=
      (H.globalIntegral_scaleTwo_iff N).mpr hIntegral
    have hScaledLocal : ∀ p : S.Place,
        S.localRepresents
          (S.localize p (G.scaleTwo M))
          (S.localize p (G.scaleTwo N)) := by
      intro p
      exact (H.localRepresents_scaleTwo_iff p M N).mpr (hLocal p)
    exact (H.globalRepresents_scaleTwo_iff M N).mp
      (hScaled (G.scaleTwo N) hScaledRank hScaledIntegral hScaledLocal)
  · intro hRegular N hRank hIntegral hLocal
    obtain ⟨N₀, hN₀⟩ := H.scaleTwo_surjective N
    have hN₀Rank : S.globalRank N₀ = n := by
      calc
        S.globalRank N₀ = S.globalRank (G.scaleTwo N₀) :=
          (H.globalRank_scaleTwo N₀).symm
        _ = S.globalRank N := congrArg S.globalRank hN₀
        _ = n := hRank
    have hN₀Integral : S.globalIntegral N₀ :=
      (H.globalIntegral_scaleTwo_iff N₀).mp (hN₀ ▸ hIntegral)
    have hN₀Local : ∀ p : S.Place,
        S.localRepresents (S.localize p M) (S.localize p N₀) := by
      intro p
      apply (H.localRepresents_scaleTwo_iff p M N₀).mp
      simpa only [hN₀] using hLocal p
    have hGlobal : S.globalRepresents M N₀ :=
      hRegular N₀ hN₀Rank hN₀Integral hN₀Local
    have hScaledGlobal :
        S.globalRepresents (G.scaleTwo M) (G.scaleTwo N₀) :=
      (H.globalRepresents_scaleTwo_iff M N₀).mpr hGlobal
    simpa only [hN₀] using hScaledGlobal

/-- Build the former scaling-regularity interface from primitive transport
facts.  Existing Section 8 theorems can therefore be reused unchanged. -/
theorem toScalingRegularityLaws
    (H : G.ScalingTransportLaws) : G.ScalingRegularityLaws where
  nRegular_scaleTwo_iff := H.nRegular_scaleTwo_iff (G := G)
  isHalfScaleOf_iff := H.isHalfScaleOf_iff

end ScalingTransportLaws

end HeADC2025GlobalData

end Bong
