/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.HeHu2022Theorem51

/-!
# He--Hu 2022, Theorem 5.3

This file rephrases Theorem 5.1 in the compact order-and-alpha form printed
as Theorem 5.3.  The two parenthetical equivalences in clause (i) are also
proved separately, rather than being accepted as notation.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- The compact right-hand side of He--Hu, Theorem 5.3, for odd target
rank `N=2*k+3`. -/
structure HeHuTheorem53Conditions {m : Nat}
    (a : GoodBONG q L (m + 3)) (k : Nat) (hm : 2 * k + 3 ≤ m) : Prop where
  initial : a.HeHuAlternatingInitialOrders (2 * k + 3) (by omega)
  lastGap : a.HeHuI3O (2 * k + 3) (by omega) (by omega)
  boundary :
    (a.alphaValue ⟨2 * k + 2, by omega⟩ = 0 ∧
        a.order ⟨2 * k + 4, by omega⟩ ≤ 1) ∨
      (a.alphaValue ⟨2 * k + 2, by omega⟩ = 1 ∧
        ((a.order ⟨2 * k + 3, by omega⟩ = 1 ∨
            1 < a.order ⟨2 * k + 4, by omega⟩) →
          a.alphaValue ⟨2 * k + 4, by omega⟩ ≤
            (a.heHuOddThreshold (2 * k + 3) (by omega) : ℚ)))

/-- Under the alternating initial profile, the first parenthetical
equivalence in Theorem 5.3(i) is exact:
`alpha_N=0` iff `R_(N+1)=-2e`. -/
theorem heHuTheorem53_alpha_zero_iff_boundaryOrder
    {m k : Nat} (a : GoodBONG q L (m + 3))
    (hm : 2 * k + 3 ≤ m)
    (hInitial : a.HeHuAlternatingInitialOrders (2 * k + 3) (by omega)) :
    a.alphaValue ⟨2 * k + 2, by omega⟩ = 0 ↔
      a.order ⟨2 * k + 3, by omega⟩ =
        -(2 * (ramificationIndex K : Int)) := by
  let boundary : Fin (m + 2) := ⟨2 * k + 2, by omega⟩
  have hPrevious : a.order ⟨2 * k + 2, by omega⟩ = 0 := by
    apply hInitial.1 ⟨2 * k + 2, by omega⟩
    change Odd (2 * k + 3)
    exact ⟨k + 1, by omega⟩
  have hGap : a.orderGap boundary =
      a.order ⟨2 * k + 3, by omega⟩ := by
    have hLeft : boundary.castSucc =
        (⟨2 * k + 2, by omega⟩ : Fin (m + 3)) := by
      apply Fin.ext
      rfl
    have hRight : boundary.succ =
        (⟨2 * k + 3, by omega⟩ : Fin (m + 3)) := by
      apply Fin.ext
      rfl
    unfold orderGap
    rw [hLeft, hRight, hPrevious, sub_zero]
  rw [(a.heHu2022Proposition26 boundary).alphaZero, hGap]

/-- For the integral lattice fixed in Section 5, the second parenthetical
equivalence in Theorem 5.3(i) is exact:
`R_(N+2)≤1` iff `R_(N+2)` is zero or one. -/
theorem heHuTheorem53_nextOrder_le_one_iff_zero_or_one
    {m k : Nat} (a : GoodBONG q L (m + 3))
    (hm : 2 * k + 3 ≤ m)
    (hIntegral : Lattice.IsIntegral q L) :
    a.order ⟨2 * k + 4, by omega⟩ ≤ 1 ↔
      a.order ⟨2 * k + 4, by omega⟩ = 0 ∨
        a.order ⟨2 * k + 4, by omega⟩ = 1 := by
  have hEven : Even (2 * k + 4) := ⟨k + 2, by omega⟩
  have hNonnegative : 0 ≤ a.order ⟨2 * k + 4, by omega⟩ :=
    (a.heHu2022Proposition27i hIntegral).oddIndexed
      ⟨2 * k + 4, by omega⟩ ⟨2 * k + 4, by omega⟩
      (le_refl _) hEven hEven |>.1
  constructor
  · intro hLe
    omega
  · rintro (hZero | hOne) <;> omega

/-- The three conditions in Theorem 5.1 are equivalent to the compact
case split printed in Theorem 5.3. -/
theorem heHuOddSectionConditions_iff_theorem53Conditions
    {m k : Nat} (a : GoodBONG q L (m + 3))
    (hm : 2 * k + 3 ≤ m)
    (hIntegral : Lattice.IsIntegral q L) :
    a.HeHuOddSectionConditions (2 * k + 3) (by omega) (by omega) ↔
      a.HeHuTheorem53Conditions k hm := by
  constructor
  · intro hOdd
    refine
      { initial := ⟨hOdd.i1.1, hOdd.i1.2.1⟩
        lastGap := hOdd.i3
        boundary := ?_ }
    rcases hOdd.i1.2.2 with hZero | hOne
    · exact Or.inl ⟨hZero, (a.heHuTheorem53_nextOrder_le_one_iff_zero_or_one
        hm hIntegral).2 (hOdd.i2.1 hZero)⟩
    · exact Or.inr ⟨hOne, hOdd.i2.2 hOne⟩
  · intro h53
    refine
      { i1 := ⟨h53.initial.1, h53.initial.2, ?_⟩
        i2 := ?_
        i3 := h53.lastGap }
    · rcases h53.boundary with hZero | hOne
      · exact Or.inl hZero.1
      · exact Or.inr hOne.1
    · constructor
      · intro hAlphaZero
        have hAlphaZero' : a.alphaValue ⟨2 * k + 2, by omega⟩ = 0 := by
          simpa only [show 2 * k + 3 - 1 = 2 * k + 2 by omega] using
            hAlphaZero
        rcases h53.boundary with hZero | hOne
        · exact (a.heHuTheorem53_nextOrder_le_one_iff_zero_or_one
            hm hIntegral).1 hZero.2
        · have hContra := hOne.1
          rw [hAlphaZero'] at hContra
          norm_num at hContra
      · intro hAlphaOne hTrigger
        have hAlphaOne' : a.alphaValue ⟨2 * k + 2, by omega⟩ = 1 := by
          simpa only [show 2 * k + 3 - 1 = 2 * k + 2 by omega] using
            hAlphaOne
        rcases h53.boundary with hZero | hOne
        · have hContra := hZero.1
          rw [hAlphaOne'] at hContra
          norm_num at hContra
        · apply hOne.2
          simpa only [show 2 * k + 3 + 1 = 2 * k + 4 by omega] using hTrigger

/-- He--Hu, Theorem 5.3, for odd target rank `N=2*k+3`. -/
theorem heHu2022Theorem53Odd
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    [DyadicDiagonalCodimensionTwoLaws K]
    [unitClassification : GoodBONGClassificationLaws.{u, u, u} K]
    [sourceClassification : GoodBONGClassificationLaws.{u, v, v} K]
    {m k : Nat} (a : GoodBONG q L (m + 3))
    (hm : 2 * k + 3 ≤ m)
    (hAIntegral : Lattice.IsIntegral q L) :
    Lattice.IsNUniversal.{u, v, u} q L (2 * k + 3) ↔
      Lattice.AmbientlyNUniversal.{u, v, u} q (2 * k + 3) ∧
        a.HeHuTheorem53Conditions k hm := by
  rw [(@heHu2022Theorem51Odd K _ _ _ _ _ V _ _ q L
    sourceLaws _ _ _ _ _ _ unitClassification sourceClassification
    m k a hm hAIntegral)]
  exact and_congr_right (fun _ =>
    a.heHuOddSectionConditions_iff_theorem53Conditions hm hAIntegral)

end BONG.GoodBONG

end Bong
