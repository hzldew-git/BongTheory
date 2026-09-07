/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.AlternatingEndpointTowerRepresentationProof
import Bong.Bong.Beli2009FinalRemarksProof

/-!
# Endpoint towers with even leading valuations

Independent square changes of coordinates normalize the leading valuation
of every binary block to zero. This is a quadratic-space statement, not an
integral change of BONG or a claim that the original leading orders agree.
-/

namespace Bong.AlternatingEndpointTower

open Dyadic BONG.GoodBONG

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- Even leading orders can be normalized to unit scale by coordinate squares. -/
theorem exists_unitScale_of_even_leadingOrders {pairs : Nat}
    (a : Fin (2 * pairs) → Kˣ) (ha : AlternatingEndpointPairClasses a)
    (heven : ∀ t : Fin pairs, Even (ordUnit K (a ⟨2 * t.val, by omega⟩))) :
    ∃ b : Fin (2 * pairs) → Kˣ,
      AlternatingEndpointPairClasses b ∧ AlternatingEndpointLeadingOrdersAt b (1 : Kˣ) ∧
        DiagonalRepresents (diagonalUnitCoefficients b) (diagonalUnitCoefficients a) := by
  let s : Fin (2 * pairs) → Kˣ := fun i ↦ uniformizerPowerUnit K (-(ordUnit K (a i) / 2))
  let b : Fin (2 * pairs) → Kˣ := fun i ↦ a i * s i ^ 2
  refine ⟨b, ?_, ?_, ?_⟩
  · intro t
    let x : Fin (2 * pairs) := ⟨2 * t.val, by omega⟩
    let y : Fin (2 * pairs) := ⟨2 * t.val + 1, by omega⟩
    have heq : -(b x * b y) = -(a x * a y) * (s x * s y) ^ 2 := by
      simp only [b, neg_mul, pow_two]
      ac_rfl
    have hsq : IsSquare ((s x * s y) ^ 2) := ⟨s x * s y, pow_two _⟩
    change IsSquare (-(b x * b y)) ∨ IsSquare (-(b x * b y) * _)
    rw [heq]
    rcases ha t with h | h
    · exact Or.inl (h.mul hsq)
    · right
      let δ := (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
      change IsSquare (-(a x * a y) * δ) at h
      have heq' : -(a x * a y) * (s x * s y) ^ 2 * δ =
          (-(a x * a y) * δ) * (s x * s y) ^ 2 := by ac_rfl
      rw [heq']
      exact h.mul hsq
  · intro t
    obtain ⟨z, hz⟩ := heven t
    change ordUnit K (a ⟨2 * t.val, by omega⟩ * s ⟨2 * t.val, by omega⟩ ^ 2) = _
    rw [ordUnit_mul, ordUnit_pow]
    simp only [s, ordUnit_uniformizerPowerUnit, hz]
    have hone : ordUnit K (1 : Kˣ) = 0 := by
      have H := ordUnit_mul K (1 : Kˣ) 1
      simp only [mul_one] at H
      omega
    rw [hone]
    omega
  · exact Beli2009FinalRemarksProof.diagonalRepresents_of_pointwise_mul_square b a s
      (fun _ ↦ rfl)

/-- Endpoint towers with even leading orders are classified by their determinant class. -/
theorem equalDeterminantRepresentation_of_even_leadingOrders {pairs : Nat}
    (a b : Fin (2 * pairs) → Kˣ)
    (ha : AlternatingEndpointPairClasses a) (hb : AlternatingEndpointPairClasses b)
    (haEven : ∀ t : Fin pairs, Even (ordUnit K (a ⟨2 * t.val, by omega⟩)))
    (hbEven : ∀ t : Fin pairs, Even (ordUnit K (b ⟨2 * t.val, by omega⟩)))
    (hdet : IsSquare (diagonalUnitDeterminant a * diagonalUnitDeterminant b)) :
    DiagonalRepresents (diagonalUnitCoefficients b) (diagonalUnitCoefficients a) := by
  obtain ⟨a', ha', hao, hrepA⟩ := exists_unitScale_of_even_leadingOrders a ha haEven
  obtain ⟨b', hb', hbo, hrepB⟩ := exists_unitScale_of_even_leadingOrders b hb hbEven
  have hdA := DiagonalIsometryInvariantLaws.determinant_square a' a hrepA
  have hdB := DiagonalIsometryInvariantLaws.determinant_square b b' hrepB.symm_of_sameRank
  have hd := isSquare_mul_trans _ (diagonalUnitDeterminant a) _ hdA
    (isSquare_mul_trans _ (diagonalUnitDeterminant b) _ hdet hdB)
  exact hrepB.symm_of_sameRank.trans
    ((equalDeterminantRepresentation_proved a' b' 1 ha' hb' hao hbo hd).trans hrepA)

end Bong.AlternatingEndpointTower
