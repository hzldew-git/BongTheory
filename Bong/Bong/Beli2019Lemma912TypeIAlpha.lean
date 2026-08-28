/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma912TypeIDefect
import Bong.Bong.Beli2019AuxiliaryAlphaNormalForm

/-!
# Beli (2019), Lemma 9.12: comparison invariants after the type-I step

The claim in Lemma 9.12 requires `B_i ≤ C_i` from the third boundary
onward; its proof actually gives the stronger range `i ≥ 2`.  The new and
old BONGs have equal orders there, while Remark 6.16
shows that every relevant mixed-prefix defect can only decrease.  Comparing
the half-gap, primary, and secondary candidates proves the required bound,
including the complete-prefix endpoint.
-/

namespace Bong

open Dyadic

universe u v w z

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {U : Type z} [AddCommGroup U] [Module K U]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {s : QuadraticSpace K U}
  {M : Lattice K V} {P : Lattice K W} {Q : Lattice K U}
  {N : Nat}

namespace Beli2019Lemma910Data

/-- The comparison invariant after the Lemma 9.10 replacement is bounded
by the corresponding invariant before replacement.  This proves the
stronger inequality `B_i ≤ C_i` for `i ≥ 2`. -/
theorem representationAlpha_le_source
    [Beli2006AlphaLaws.{u, v} K]
    {R₁ R₂ β₁ : Int}
    (a : GoodBONG q M (3 + N))
    (c : GoodBONG s Q (N + 3))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ i : Fin 3,
      a.order (Fin.castAdd N i) = ![R₁, R₂, R₁] i)
    (hlength : 3 + N = N + 3)
    (hdefect : (a.castLength hlength).RepresentationDefectCondition
      (E.bong.castLength hlength))
    (i : RepresentationIndex (N + 3) (N + 3)) (hi : 2 ≤ i.val) :
    (E.bong.castLength hlength).representationAlpha c i ≤
      (a.castLength hlength).representationAlpha c i := by
  let source := a.castLength hlength
  let target := E.bong.castLength hlength
  have hiTwo : 2 ≤ i.val := hi
  have hcurrent :
      target.order (⟨i.val, i.lt_large⟩ : Fin (N + 3)) =
        source.order (⟨i.val, i.lt_large⟩ : Fin (N + 3)) := by
    exact E.order_castLength_eq_source_of_two_le a D horders hlength
      (⟨i.val, i.lt_large⟩ : Fin (N + 3)) hiTwo
  have hhalf : target.representationHalfGap c i =
      source.representationHalfGap c i := by
    unfold representationHalfGap
    rw [hcurrent]
  have hprimary : target.representationPrimaryDefect c i ≤
      source.representationPrimaryDefect c i := by
    unfold representationPrimaryDefect
    rw [hcurrent]
    exact add_le_add_right
      (E.mixedPrefixDefect_le_source_at a c D horders hlength hdefect
        (i.val + 1) (by omega) (Nat.succ_le_of_lt i.lt_large)
        (-1) (i.val - 1)) _
  rw [target.representationAlpha_eq_min_halfGap_prime c i,
    source.representationAlpha_eq_min_halfGap_prime c i]
  apply min_le_min (le_of_eq hhalf)
  by_cases hinterior : 1 < i.val ∧ i.val + 1 < N + 3
  · have hnext :
        target.order (⟨i.val + 1, hinterior.2⟩ : Fin (N + 3)) =
          source.order (⟨i.val + 1, hinterior.2⟩ : Fin (N + 3)) := by
      have hnextTwo : 2 ≤ i.val + 1 := by omega
      exact E.order_castLength_eq_source_of_two_le a D horders hlength
        (⟨i.val + 1, hinterior.2⟩ : Fin (N + 3)) hnextTwo
    have hsecondary : target.representationSecondaryDefect c i hinterior ≤
        source.representationSecondaryDefect c i hinterior := by
      unfold representationSecondaryDefect
      rw [hcurrent, hnext]
      exact add_le_add_right
        (E.mixedPrefixDefect_le_source_at a c D horders hlength hdefect
          (i.val + 2) (by omega) (by omega) 1 (i.val - 2)) _
    rw [target.representationAlphaPrime_eq_min_primary_secondary
        c i hinterior,
      source.representationAlphaPrime_eq_min_primary_secondary
        c i hinterior]
    exact min_le_min hprimary hsecondary
  · rw [target.representationAlphaPrime_eq_primary_of_not_interior
        c i hinterior,
      source.representationAlphaPrime_eq_primary_of_not_interior
        c i hinterior]
    exact hprimary

/-- Rational-valued form of `representationAlpha_le_source`, matching the
finite invariants used in the statement of Lemma 9.12. -/
theorem representationAlphaValue_le_source
    [Beli2006AlphaLaws.{u, v} K]
    {R₁ R₂ β₁ : Int}
    (a : GoodBONG q M (3 + N))
    (c : GoodBONG s Q (N + 3))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (E : Beli2019Lemma910Data a D)
    (horders : ∀ i : Fin 3,
      a.order (Fin.castAdd N i) = ![R₁, R₂, R₁] i)
    (hlength : 3 + N = N + 3)
    (hdefect : (a.castLength hlength).RepresentationDefectCondition
      (E.bong.castLength hlength))
    (i : RepresentationIndex (N + 3) (N + 3)) (hi : 2 ≤ i.val) :
    (E.bong.castLength hlength).representationAlphaValue c i ≤
      (a.castLength hlength).representationAlphaValue c i := by
  have h := E.representationAlpha_le_source
    a c D horders hlength hdefect i hi
  have hcoe :
      ((E.bong.castLength hlength).representationAlphaValue c i :
          WithTop ℚ) ≤
        ((a.castLength hlength).representationAlphaValue c i :
          WithTop ℚ) := by
    simpa only [coe_representationAlphaValue] using h
  exact WithTop.coe_le_coe.mp hcoe

end Beli2019Lemma910Data

end BONG.GoodBONG

end Bong
