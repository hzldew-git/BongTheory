/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328NormalizedFirstComponents

/-!
# The second component at the first-component normalization

O'Meara 93:19 acts on the second Jordan component after the first scale has
been normalized to one.  Its modular parameter is therefore
`s₀⁻¹ s₁`, which lies in the maximal ideal by strict increase of Jordan
scales.  The source and target second components retain equal norm groups
under this common rescaling.
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

/-- Scale of the second component in the normalization where the first
component is unimodular. -/
noncomputable def relativeSecondScale : Kˣ :=
  S.firstScale⁻¹ * J.scaleGenerator 1

noncomputable abbrev sourceSecondNormalized :
    QuadraticSpace K (S.sourceJordan.component 1).carrier :=
  (S.sourceJordan.component 1).space.rescaleUnit S.firstScale⁻¹

noncomputable abbrev targetSecondNormalized :
    QuadraticSpace K (S.targetJordan.component 1).carrier :=
  (S.targetJordan.component 1).space.rescaleUnit S.firstScale⁻¹

theorem sourceSecondNormalized_modular :
    IsModular S.sourceSecondNormalized
      (S.sourceJordan.component 1).lattice S.relativeSecondScale := by
  have h := (S.sourceJordan.modular 1).rescaleQuadraticUnit S.firstScale⁻¹
  simpa only [sourceSecondNormalized, relativeSecondScale,
    sourceJordan_scaleGenerator] using h

theorem targetSecondNormalized_modular :
    IsModular S.targetSecondNormalized
      (S.targetJordan.component 1).lattice S.relativeSecondScale := by
  have h := (S.targetJordan.modular 1).rescaleQuadraticUnit S.firstScale⁻¹
  simpa only [targetSecondNormalized, relativeSecondScale,
    targetJordan_scaleGenerator] using h

theorem sourceSecondNormalized_finrank :
    finrank K (S.sourceJordan.component 1).carrier = 4 := by
  simpa only [componentRank] using S.sourceJordan_componentRank 1

theorem targetSecondNormalized_finrank :
    finrank K (S.targetJordan.component 1).carrier = 4 := by
  simpa only [componentRank] using S.targetJordan_componentRank 1

/-- Strict increase of Jordan scales is exactly the maximal-ideal
hypothesis needed by 93:19. -/
theorem relativeSecondScale_isInMaximalIdeal :
    IsInMaximalIdeal K (S.relativeSecondScale : K) := by
  have hstrict : ordUnit K (J.scaleGenerator 0) <
      ordUnit K (J.scaleGenerator 1) := by
    have h := J.scaleOrder_strict (i := (0 : Fin (n + 2)))
      (j := Fin.succ (0 : Fin (n + 1))) (by simp)
    simpa using h
  rw [IsInMaximalIdeal, ← coe_ordUnit, relativeSecondScale,
    ordUnit_mul, ordUnit_inv]
  simp only [firstScale]
  exact_mod_cast (by omega :
    (0 : Int) < -ordUnit K (J.scaleGenerator 0) +
      ordUnit K (J.scaleGenerator 1))

theorem secondNormalized_normGroupSet_eq :
    normGroupSet S.sourceSecondNormalized
        (S.sourceJordan.component 1).lattice =
      normGroupSet S.targetSecondNormalized
        (S.targetJordan.component 1).lattice := by
  ext z
  rw [mem_normGroupSet_rescaleQuadraticUnit_iff,
    mem_normGroupSet_rescaleQuadraticUnit_iff,
    S.sourceJordan_component_normGroupSet,
    S.targetJordan_component_normGroupSet]

end Omeara9328RankFourReductionSystem

end Lattice.JordanDecomposition

end Bong
