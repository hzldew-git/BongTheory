/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.JordanDecompositionInvariants

/-!
# Property A is independent of the Jordan decomposition

The intrinsic norms of the scale truncations first recover the norm order of
each component of a property-A Jordan decomposition.  Scale matching then
forces every other Jordan decomposition to have the same component norm
orders.  Together with scale and rank invariance, this proves the special
case of Xu's Proposition 1.1 used by Beli (2003), Lemma 4.1(ii).
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace Lattice.JordanDecomposition

/-- In a property-A Jordan decomposition, the intrinsic effective norm at a
component scale is exactly that component's norm order. -/
theorem effectiveNormOrderAt_scale_eq_normOrder_of_hasPropertyA {t : Nat}
    (J : JordanDecomposition q L t) (hA : J.HasPropertyA) (i : Fin t) :
    BONG.jordanEffectiveNormOrderAt J i
        (ordUnit K (J.scaleGenerator i)) =
      ordUnit K (J.normGenerator i) := by
  apply le_antisymm
  · calc
      BONG.jordanEffectiveNormOrderAt J i
          (ordUnit K (J.scaleGenerator i)) ≤
          JordanProfileOrder.adjustedAt
            (fun j ↦ ordUnit K (J.scaleGenerator j))
            (fun j ↦ ordUnit K (J.normGenerator j))
            (ordUnit K (J.scaleGenerator i)) i :=
        JordanProfileOrder.effectiveAt_le _ _ _ _ _
      _ = ordUnit K (J.normGenerator i) := by
        simp [JordanProfileOrder.adjustedAt]
  · apply JordanProfileOrder.le_effectiveAt
    intro j
    rcases lt_trichotomy j i with hji | hji | hij
    · have hscale := J.scaleOrder_strict hji
      have hgap := (hA.2 hji).2
      simp only [JordanProfileOrder.adjustedAt, if_pos hscale]
      omega
    · subst j
      simp [JordanProfileOrder.adjustedAt]
    · have hscale := J.scaleOrder_strict hij
      have hgap := (hA.2 hij).1
      rw [JordanProfileOrder.adjustedAt, if_neg (not_lt_of_gt hscale)]
      omega

/-- A property-A Jordan decomposition gives a lower bound for the norm order
of the scale-matched component in every other Jordan decomposition. -/
theorem normOrder_le_scaleIndexEquiv_of_hasPropertyA {s t : Nat}
    (J : JordanDecomposition q L t) (H : JordanDecomposition q L s)
    (hA : J.HasPropertyA) (i : Fin t) :
    ordUnit K (J.normGenerator i) ≤
      ordUnit K (H.normGenerator (J.scaleIndexEquiv H i)) := by
  let e := J.scaleIndexEquiv H
  calc
    ordUnit K (J.normGenerator i) =
        BONG.jordanEffectiveNormOrderAt J i
          (ordUnit K (J.scaleGenerator i)) :=
      (J.effectiveNormOrderAt_scale_eq_normOrder_of_hasPropertyA hA i).symm
    _ = BONG.jordanEffectiveNormOrderAt H (e i)
          (ordUnit K (J.scaleGenerator i)) :=
      J.effectiveNormOrderAt_eq H i (e i)
        (ordUnit K (J.scaleGenerator i))
    _ ≤ JordanProfileOrder.adjustedAt
          (fun j ↦ ordUnit K (H.scaleGenerator j))
          (fun j ↦ ordUnit K (H.normGenerator j))
          (ordUnit K (J.scaleGenerator i)) (e i) :=
      JordanProfileOrder.effectiveAt_le _ _ _ _ _
    _ = ordUnit K (H.normGenerator (e i)) := by
      rw [JordanProfileOrder.adjustedAt]
      simp [e]

/-- Corresponding components in any two Jordan decompositions have the same
norm order once one of the decompositions has property A. -/
theorem normOrder_scaleIndexEquiv_eq_of_hasPropertyA {s t : Nat}
    (J : JordanDecomposition q L t) (H : JordanDecomposition q L s)
    (hA : J.HasPropertyA) (i : Fin t) :
    ordUnit K (H.normGenerator (J.scaleIndexEquiv H i)) =
      ordUnit K (J.normGenerator i) := by
  let e := J.scaleIndexEquiv H
  have hlower : ordUnit K (J.normGenerator i) ≤
      ordUnit K (H.normGenerator (e i)) :=
    J.normOrder_le_scaleIndexEquiv_of_hasPropertyA H hA i
  apply le_antisymm
  · by_contra hnot
    change ¬ ordUnit K (H.normGenerator (e i)) ≤
      ordUnit K (J.normGenerator i) at hnot
    have hstrict : ordUnit K (J.normGenerator i) <
        ordUnit K (H.normGenerator (e i)) := lt_of_not_ge hnot
    have heffective :
        BONG.jordanEffectiveNormOrderAt H (e i)
            (ordUnit K (J.scaleGenerator i)) =
          ordUnit K (J.normGenerator i) := by
      rw [← J.effectiveNormOrderAt_scale_eq_normOrder_of_hasPropertyA hA i]
      exact (J.effectiveNormOrderAt_eq H i (e i)
        (ordUnit K (J.scaleGenerator i))).symm
    have hplus : ordUnit K (J.normGenerator i) + 1 ≤
        BONG.jordanEffectiveNormOrderAt H (e i)
          (ordUnit K (J.scaleGenerator i)) := by
      apply JordanProfileOrder.le_effectiveAt
      intro a
      let k : Fin t := e.symm a
      have ha : e k = a := e.apply_symm_apply a
      have hnormLower : ordUnit K (J.normGenerator k) ≤
          ordUnit K (H.normGenerator a) := by
        rw [← ha]
        exact J.normOrder_le_scaleIndexEquiv_of_hasPropertyA H hA k
      have hscaleMatch : ordUnit K (H.scaleGenerator a) =
          ordUnit K (J.scaleGenerator k) := by
        rw [← ha]
        exact J.scaleOrder_scaleIndexEquiv H k
      rcases lt_trichotomy k i with hki | hki | hik
      · have hscaleJ := J.scaleOrder_strict hki
        have hgap := (hA.2 hki).2
        rw [JordanProfileOrder.adjustedAt,
          if_pos (by rw [hscaleMatch]; exact hscaleJ)]
        omega
      · have hstrictA : ordUnit K (J.normGenerator k) <
            ordUnit K (H.normGenerator a) := by
          calc
            ordUnit K (J.normGenerator k) =
                ordUnit K (J.normGenerator i) := by rw [hki]
            _ < ordUnit K (H.normGenerator (e i)) := hstrict
            _ = ordUnit K (H.normGenerator a) := by
              rw [← ha, hki]
        rw [JordanProfileOrder.adjustedAt,
          if_neg (by rw [hscaleMatch, hki]; exact lt_irrefl _)]
        rw [hki] at hstrictA
        omega
      · have hscaleJ := J.scaleOrder_strict hik
        have hgap := (hA.2 hik).1
        rw [JordanProfileOrder.adjustedAt,
          if_neg (not_lt_of_gt (by rw [hscaleMatch]; exact hscaleJ))]
        omega
    rw [heffective] at hplus
    omega
  · exact hlower

/-- Xu Proposition 1.1 in the precise form used by Beli: property A is
preserved when the Jordan decomposition of a fixed lattice is changed. -/
theorem hasPropertyA_of_hasPropertyA {s t : Nat}
    (J : JordanDecomposition q L t) (H : JordanDecomposition q L s)
    (hA : J.HasPropertyA) : H.HasPropertyA := by
  let e := J.scaleIndexEquiv H
  constructor
  · intro a
    let i : Fin t := e.symm a
    have ha : e i = a := e.apply_symm_apply a
    have hrank := J.componentRank_scaleIndexEquiv H i
    rw [ha] at hrank
    rw [hrank]
    exact hA.1 i
  · intro a b hab
    let i : Fin t := e.symm a
    let j : Fin t := e.symm b
    have hai : e i = a := e.apply_symm_apply a
    have hbj : e j = b := e.apply_symm_apply b
    have hscaleH := H.scaleOrder_strict hab
    have hJmono : Monotone
        (fun k : Fin t ↦ ordUnit K (J.scaleGenerator k)) := by
      have hstrict : StrictMono
          (fun k : Fin t ↦ ordUnit K (J.scaleGenerator k)) :=
        fun _ _ h ↦ J.scaleOrder_strict h
      exact hstrict.monotone
    have hij : i < j := by
      apply hJmono.reflect_lt
      calc
        ordUnit K (J.scaleGenerator i) =
            ordUnit K (H.scaleGenerator (e i)) :=
          (J.scaleOrder_scaleIndexEquiv H i).symm
        _ = ordUnit K (H.scaleGenerator a) := by rw [hai]
        _ < ordUnit K (H.scaleGenerator b) := hscaleH
        _ = ordUnit K (H.scaleGenerator (e j)) := by rw [hbj]
        _ = ordUnit K (J.scaleGenerator j) :=
          J.scaleOrder_scaleIndexEquiv H j
    have hgap := hA.2 hij
    have hnormI := J.normOrder_scaleIndexEquiv_eq_of_hasPropertyA H hA i
    have hnormJ := J.normOrder_scaleIndexEquiv_eq_of_hasPropertyA H hA j
    have hscaleI := J.scaleOrder_scaleIndexEquiv H i
    have hscaleJ := J.scaleOrder_scaleIndexEquiv H j
    rw [hai] at hnormI hscaleI
    rw [hbj] at hnormJ hscaleJ
    omega

end Lattice.JordanDecomposition

end Bong
