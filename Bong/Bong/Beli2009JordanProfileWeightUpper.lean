/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009JordanProfileInternal

/-!
# A profile endpoint upper bound for a fundamental weight

At an internal coordinate, Beli (2009), Lemma 2.16(i), identifies the
fundamental weight order with `R_i + alpha_i`.  If the coordinate is the
last coordinate of a component of rank at least two, the same identity at
the preceding coordinate and monotonicity of the left alpha endpoints give
the corresponding upper bound at the last coordinate.  This is the form
used in Beli (2019), Lemma 5.17, after an equal-scale pair has been
amalgamated.
-/

namespace Bong

open Dyadic Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG.JordanOrderProfileWitness

/-- For a Jordan component of rank at least two, its fundamental weight
order is bounded above by the left alpha endpoint at every non-final global
coordinate carried by that component. -/
theorem fundamentalWeightOrder_le_order_add_alpha_of_two_le_rank
    {n t : Nat} {a : GoodBONG q L (n + 2)}
    {J : Lattice.JordanDecomposition q L t}
    (P : JordanOrderProfileWitness a.toBONG J)
    (i : Fin (n + 1))
    (hrank : 2 ≤ J.componentRank (P.indexEquiv i.castSucc).1) :
    (J.fundamentalWeightOrder (P.indexEquiv i.castSucc).1 : ℚ) ≤
      (a.order i.castSucc : ℚ) + a.alphaValue i := by
  by_cases hinternal : (P.indexEquiv i.castSucc).2.val + 1 <
      J.componentRank (P.indexEquiv i.castSucc).1
  · exact (P.internal_weightOrder_eq_order_add_alpha i hinternal).le
  · have hlast : (P.indexEquiv i.castSucc).2.val + 1 =
        J.componentRank (P.indexEquiv i.castSucc).1 := by
      have hlocal : (P.indexEquiv i.castSucc).2.val <
          J.componentRank (P.indexEquiv i.castSucc).1 := by
        exact (P.indexEquiv i.castSucc).2.isLt
      omega
    have hlocalPos : 0 < (P.indexEquiv i.castSucc).2.val := by
      omega
    have hiPos : 0 < i.val := by
      have hindex := P.index_val_eq_componentStart_add_local i.castSucc
      change i.val =
        (∑ k ∈ Finset.Iio (P.indexEquiv i.castSucc).1,
          J.componentRank k) + (P.indexEquiv i.castSucc).2.val at hindex
      omega
    let j : Fin (n + 1) := ⟨i.val - 1, by omega⟩
    let k : Fin t := (P.indexEquiv i.castSucc).1
    let ell : Fin (J.componentRank k) := (P.indexEquiv i.castSucc).2
    let previousLocal : Fin (J.componentRank k) :=
      ⟨ell.val - 1, by
        have := ell.isLt
        omega⟩
    have hinverse := P.inverse_index_val_local_pred k ell hlocalPos
    change (P.indexEquiv.symm ⟨k, previousLocal⟩).val + 1 =
      (P.indexEquiv.symm ⟨k, ell⟩).val at hinverse
    have hcurrent : P.indexEquiv.symm ⟨k, ell⟩ = i.castSucc := by
      exact P.indexEquiv.symm_apply_apply i.castSucc
    have hpreviousVal :
        (P.indexEquiv.symm ⟨k, previousLocal⟩).val + 1 = i.val := by
      calc
        (P.indexEquiv.symm ⟨k, previousLocal⟩).val + 1 =
            (P.indexEquiv.symm ⟨k, ell⟩).val := by
          simpa only [previousLocal] using hinverse
        _ = i.val := by
          simpa using congrArg Fin.val hcurrent
    have hj : j.castSucc =
        P.indexEquiv.symm ⟨k, previousLocal⟩ := by
      apply Fin.ext
      dsimp only [j, Fin.val_mk, Fin.castSucc_mk]
      omega
    have hcoordinates : P.indexEquiv j.castSucc =
        ⟨k, previousLocal⟩ := by
      rw [hj, P.indexEquiv.apply_symm_apply]
    have hpreviousInternal :
        (P.indexEquiv j.castSucc).2.val + 1 <
          J.componentRank (P.indexEquiv j.castSucc).1 := by
      rw [hcoordinates]
      dsimp only [previousLocal, ell, k, Fin.val_mk]
      omega
    have hweightPrevious :=
      P.internal_weightOrder_eq_order_add_alpha j hpreviousInternal
    rw [hcoordinates] at hweightPrevious
    have hmono := a.alphaLeftEndpoint_monotone (show j ≤ i by
      apply Fin.mk_le_mk.mpr
      omega)
    unfold GoodBONG.alphaLeftEndpoint at hmono
    change (J.fundamentalWeightOrder k : ℚ) ≤
      (a.order i.castSucc : ℚ) + a.alphaValue i
    change (J.fundamentalWeightOrder k : ℚ) =
      (a.order j.castSucc : ℚ) + a.alphaValue j at hweightPrevious
    linarith

/-- Unary endpoint convention in Corollary 2.17(ii), transported to an
arbitrary profiled Jordan decomposition.  At the first component this is
the global weight formula; at every later unary component it is the
neighboring-alpha minimum. -/
theorem fundamentalWeightOrder_le_order_add_alpha_of_rank_one
    {n t : Nat} {a : GoodBONG q L (n + 2)}
    {J : Lattice.JordanDecomposition q L t}
    (P : JordanOrderProfileWitness a.toBONG J)
    (i : Fin (n + 1))
    (hrank : J.componentRank (P.indexEquiv i.castSucc).1 = 1) :
    (J.fundamentalWeightOrder (P.indexEquiv i.castSucc).1 : ℚ) ≤
      (a.order i.castSucc : ℚ) + a.alphaValue i := by
  obtain ⟨S⟩ := a.nonempty_strictJordanAdaptedAlignment a (fun _ ↦ rfl)
  let F := Lattice.JordanDecomposition.sameFundamentalTypeOfIsometry
    S.sourceJordan J (Lattice.Isometry.refl q L)
  have hcount : S.componentCount = t := by
    simpa only [Fintype.card_fin] using Fintype.card_congr F.indexEquiv
  subst t
  have hRank :
      S.sourceJordan.toOrthogonalDecomposition.componentRank =
        J.toOrthogonalDecomposition.componentRank := by
    funext k
    have hk := F.componentRank_eq k
    rw [F.indexEquiv_apply_eq_self] at hk
    exact hk.symm
  have hcoordinates :=
    S.sourceProfile.indexEquiv_coordinates_eq_of_componentRank_eq P hRank
      i.castSucc
  have hcomponent :
      (S.sourceProfile.indexEquiv i.castSucc).1 =
        (P.indexEquiv i.castSucc).1 := hcoordinates.1
  let k : Fin S.componentCount :=
    (S.sourceProfile.indexEquiv i.castSucc).1
  have hsourceRank : S.sourceJordan.componentRank k = 1 := by
    calc
      S.sourceJordan.componentRank k =
          J.componentRank k := congrFun hRank k
      _ = J.componentRank (P.indexEquiv i.castSucc).1 := by
        exact congrArg J.componentRank (by simpa only [k] using hcomponent)
      _ = 1 := hrank
  have hsourceLocalZero :
      (S.sourceProfile.indexEquiv i.castSucc).2.val = 0 := by
    have hlocal := (S.sourceProfile.indexEquiv i.castSucc).2.isLt
    change (S.sourceProfile.indexEquiv i.castSucc).2.val <
      S.sourceJordan.componentRank k at hlocal
    rw [hsourceRank] at hlocal
    omega
  have hindex :=
    S.sourceProfile.index_val_eq_componentStart_add_local i.castSucc
  change i.val = S.componentStart k +
    (S.sourceProfile.indexEquiv i.castSucc).2.val at hindex
  have hstart : S.componentStart k = i.val := by omega
  have hright : S.componentStart k < n + 1 := by
    rw [hstart]
    exact i.isLt
  have hsourceUpper :
      (S.sourceJordan.fundamentalWeightOrder k : ℚ) ≤
        (a.order i.castSucc : ℚ) + a.alphaValue i := by
    by_cases hk : 0 < k.val
    · rcases S.source_hasTwoBlockSplit_componentStart k hk with ⟨T⟩
      have hformula :=
        S.sourceFundamentalWeightOrder_eq_order_add_min_neighborAlphas_e_of_unary
          k hk T hsourceRank hright
      dsimp only at hformula
      change (S.sourceJordan.fundamentalWeightOrder k : ℚ) =
        (a.order (⟨S.componentStart k, hright⟩ : Fin (n + 1)).castSucc : ℚ) +
          min (a.alphaValue ⟨S.componentStart k - 1, by omega⟩)
            (min (a.alphaValue ⟨S.componentStart k, hright⟩)
              (ramificationIndex K : ℚ)) at hformula
      have hcurrent :
          (⟨S.componentStart k, hright⟩ : Fin (n + 1)) = i := by
        apply Fin.ext
        exact hstart
      rw [hcurrent] at hformula
      rw [hformula]
      have hinner : min (a.alphaValue i) (ramificationIndex K : ℚ) ≤
          a.alphaValue i := min_le_left _ _
      have houter :
          min (a.alphaValue ⟨S.componentStart k - 1, by omega⟩)
              (min (a.alphaValue i) (ramificationIndex K : ℚ)) ≤
            min (a.alphaValue i) (ramificationIndex K : ℚ) :=
        min_le_right _ _
      linarith
    · have hkzero : k.val = 0 := by omega
      have hkfirst : k = S.sourceFirstComponent := by
        apply Fin.ext
        exact hkzero
      have hstartZero : S.componentStart k = 0 := by
        rw [hkfirst]
        unfold StrictJordanAdaptedAlignment.componentStart
        rw [S.Iio_sourceFirstComponent_eq_empty]
        simp
      have hiZero : i = 0 := by
        apply Fin.ext
        rw [← hstart, hstartZero]
        rfl
      have hweightZero :=
        S.sourceJordan.fundamentalWeightOrder_zero S.componentCount_pos
      have hzeroIndex :
          (⟨0, S.componentCount_pos⟩ : Fin S.componentCount) = k := by
        apply Fin.ext
        exact hkzero.symm
      rw [hzeroIndex] at hweightZero
      have hweightGlobal := a.lemma214_weightIdealOrder_all
      have hweightGlobalLe :
          (Lattice.weightIdealOrder q L : ℚ) ≤
            (a.order (0 : Fin (n + 2)) : ℚ) +
              a.alphaValue (0 : Fin (n + 1)) := by
        rw [hweightGlobal]
        exact min_le_left _ _
      have hweightQ :
          (S.sourceJordan.fundamentalWeightOrder k : ℚ) =
            (Lattice.weightIdealOrder q L : ℚ) := by
        exact_mod_cast hweightZero
      rw [hweightQ, hiZero]
      simpa only [Fin.castSucc_zero] using hweightGlobalLe
  have hweight := F.fundamentalWeightOrder_eq k
  rw [F.indexEquiv_apply_eq_self] at hweight
  have hweightQ :
      (J.fundamentalWeightOrder k : ℚ) =
        (S.sourceJordan.fundamentalWeightOrder k : ℚ) := by
    exact_mod_cast hweight
  rw [← hcomponent]
  exact hweightQ.trans_le hsourceUpper

/-- Uniform endpoint upper bound for a non-final coordinate. -/
theorem fundamentalWeightOrder_le_order_add_alpha
    {n t : Nat} {a : GoodBONG q L (n + 2)}
    {J : Lattice.JordanDecomposition q L t}
    (P : JordanOrderProfileWitness a.toBONG J)
    (i : Fin (n + 1)) :
    (J.fundamentalWeightOrder (P.indexEquiv i.castSucc).1 : ℚ) ≤
      (a.order i.castSucc : ℚ) + a.alphaValue i := by
  have hpos : 0 < J.componentRank (P.indexEquiv i.castSucc).1 :=
    J.component_finrank_pos (P.indexEquiv i.castSucc).1
  by_cases hrank : J.componentRank (P.indexEquiv i.castSucc).1 = 1
  · exact P.fundamentalWeightOrder_le_order_add_alpha_of_rank_one i hrank
  · exact P.fundamentalWeightOrder_le_order_add_alpha_of_two_le_rank i
      (by omega)

end BONG.JordanOrderProfileWitness

end Bong
