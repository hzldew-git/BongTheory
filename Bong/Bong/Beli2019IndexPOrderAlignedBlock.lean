/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019IndexPOrderCertificate
import Bong.Bong.JordanProfileOrder

/-!
# Coordinate certificates inside aligned Jordan blocks

These two lemmas package the recurring calculation in Beli (2019), Section
5.4.  When effective norm orders increase, even local coordinates compare
directly and odd coordinates use an adjacent-pair equality.  When they
decrease, the roles of the two parities are reversed.
-/

namespace Bong

/-- Aligned components with increasing effective norm order. -/
theorem Beli2019IndexPOrderCoordinateCertificate.aligned_of_effective_le
    {n : Nat} (x y : BeliOrderSequence n Int)
    (i : Nat) (hi : i < n) (localIndex : Nat)
    (scale sourceEffective targetEffective : Int)
    (hsourceScale : scale ≤ sourceEffective)
    (htargetScale : scale ≤ targetEffective)
    (heffective : sourceEffective ≤ targetEffective)
    (hsourceCurrent : x.entry i hi =
      JordanProfileOrder.localOrder scale sourceEffective localIndex)
    (htargetCurrent : y.entry i hi =
      JordanProfileOrder.localOrder scale targetEffective localIndex)
    (hpair : ¬Even localIndex →
      ∃ (hi0 : 0 < i) (hiNext : i + 1 < n),
        x.entry (i + 1) hiNext = sourceEffective ∧
          y.entry (i - 1) (by omega) = targetEffective) :
    Beli2019IndexPOrderCoordinateCertificate x y i hi := by
  by_cases heven : Even localIndex
  · apply Beli2019IndexPOrderCoordinateCertificate.direct
    rw [hsourceCurrent, htargetCurrent,
      JordanProfileOrder.localOrder_even_of_scale_le hsourceScale heven,
      JordanProfileOrder.localOrder_even_of_scale_le htargetScale heven]
    exact heffective
  · obtain ⟨hi0, hiNext, hsourceNext, htargetPrevious⟩ := hpair heven
    apply Beli2019IndexPOrderCoordinateCertificate.jordanPair
      hi0 hiNext scale sourceEffective targetEffective
      heffective
    · rw [hsourceCurrent,
        JordanProfileOrder.localOrder_odd_of_scale_le hsourceScale heven]
    · exact hsourceNext
    · exact htargetPrevious
    · rw [htargetCurrent,
        JordanProfileOrder.localOrder_odd_of_scale_le htargetScale heven]

/-- Aligned components with decreasing effective norm order. -/
theorem Beli2019IndexPOrderCoordinateCertificate.aligned_of_effective_ge
    {n : Nat} (x y : BeliOrderSequence n Int)
    (i : Nat) (hi : i < n) (localIndex : Nat)
    (scale sourceEffective targetEffective : Int)
    (hsourceScale : scale ≤ sourceEffective)
    (htargetScale : scale ≤ targetEffective)
    (heffective : targetEffective ≤ sourceEffective)
    (hsourceCurrent : x.entry i hi =
      JordanProfileOrder.localOrder scale sourceEffective localIndex)
    (htargetCurrent : y.entry i hi =
      JordanProfileOrder.localOrder scale targetEffective localIndex)
    (hpair : Even localIndex →
      ∃ (hi0 : 0 < i) (hiNext : i + 1 < n),
        x.entry (i + 1) hiNext = 2 * scale - sourceEffective ∧
          y.entry (i - 1) (by omega) = 2 * scale - targetEffective) :
    Beli2019IndexPOrderCoordinateCertificate x y i hi := by
  by_cases heven : Even localIndex
  · obtain ⟨hi0, hiNext, hsourceNext, htargetPrevious⟩ := hpair heven
    apply Beli2019IndexPOrderCoordinateCertificate.jordanPair hi0 hiNext scale
      (2 * scale - sourceEffective) (2 * scale - targetEffective)
      (by omega)
    · rw [hsourceCurrent,
        JordanProfileOrder.localOrder_even_of_scale_le hsourceScale heven]
      omega
    · exact hsourceNext
    · exact htargetPrevious
    · rw [htargetCurrent,
        JordanProfileOrder.localOrder_even_of_scale_le htargetScale heven]
      omega
  · apply Beli2019IndexPOrderCoordinateCertificate.direct
    rw [hsourceCurrent, htargetCurrent,
      JordanProfileOrder.localOrder_odd_of_scale_le hsourceScale heven,
      JordanProfileOrder.localOrder_odd_of_scale_le htargetScale heven]
    omega

end Bong
