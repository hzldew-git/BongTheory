/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009JordanAlphaTransport

/-!
# Beli (2009), Lemma 2.16(i), for an arbitrary Jordan profile

The concrete proof of Lemma 2.16(i) is carried by a Jordan decomposition
adapted to the given good BONG.  Applications such as Beli (2019), Section 5,
start instead with an independently constructed Jordan decomposition.  The
identity isometry gives equality of O'Meara's complete fundamental type, and
the increasing profile enumeration is unique.  Hence the concrete internal
weight formula transports to every profiled Jordan decomposition of the same
lattice.
-/

namespace Bong

open Dyadic Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG.JordanOrderProfileWitness

/-- Beli (2009), Lemma 2.16(i), transported from an adapted Jordan
decomposition to an arbitrary Jordan decomposition carrying the same good
BONG profile. -/
theorem internal_weightOrder_eq_order_add_alpha
    {m t : Nat} {a : GoodBONG q L (m + 1)}
    {J : Lattice.JordanDecomposition q L t}
    (P : JordanOrderProfileWitness a.toBONG J)
    (i : Fin m)
    (hlocal : (P.indexEquiv i.castSucc).2.val + 1 <
      J.componentRank (P.indexEquiv i.castSucc).1) :
    (J.fundamentalWeightOrder (P.indexEquiv i.castSucc).1 : ℚ) =
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
  have hindex := S.sourceProfile.index_val_eq_componentStart_add_local
    i.castSucc
  change i.val =
      (∑ z ∈ Finset.Iio (S.sourceProfile.indexEquiv i.castSucc).1,
        S.sourceJordan.componentRank z) +
        (S.sourceProfile.indexEquiv i.castSucc).2.val at hindex
  have hstart : S.componentStart k ≤ i.val := by
    change (∑ z ∈ Finset.Iio
      (S.sourceProfile.indexEquiv i.castSucc).1,
        S.sourceJordan.componentRank z) ≤ i.val
    rw [hindex]
    omega
  have hlocalSource :
      (S.sourceProfile.indexEquiv i.castSucc).2.val + 1 <
        S.sourceJordan.componentRank
          (S.sourceProfile.indexEquiv i.castSucc).1 := by
    calc
      (S.sourceProfile.indexEquiv i.castSucc).2.val + 1 =
          (P.indexEquiv i.castSucc).2.val + 1 := by rw [hcoordinates.2]
      _ < J.componentRank (P.indexEquiv i.castSucc).1 := hlocal
      _ = J.componentRank
          (S.sourceProfile.indexEquiv i.castSucc).1 := by rw [hcomponent]
      _ = S.sourceJordan.componentRank
          (S.sourceProfile.indexEquiv i.castSucc).1 :=
        (congrFun hRank (S.sourceProfile.indexEquiv i.castSucc).1).symm
  have hnext : i.val + 1 < S.componentStop k := by
    change i.val + 1 <
      (∑ z ∈ Finset.Iio
        (S.sourceProfile.indexEquiv i.castSucc).1,
          S.sourceJordan.componentRank z) +
        S.sourceJordan.componentRank
          (S.sourceProfile.indexEquiv i.castSucc).1
    calc
      i.val + 1 =
          (∑ z ∈ Finset.Iio
            (S.sourceProfile.indexEquiv i.castSucc).1,
              S.sourceJordan.componentRank z) +
            ((S.sourceProfile.indexEquiv i.castSucc).2.val + 1) := by
        rw [hindex]
        omega
      _ < _ := Nat.add_lt_add_left hlocalSource _
  have hinternal := (S.source_component_internal k i.val hstart hnext).1
  have hleft :
      (S.sourceInternalAlphaData k i.val hstart hnext).leftIndex =
        i.castSucc := by
    apply Fin.ext
    rfl
  have halpha :
      (S.sourceInternalAlphaData k i.val hstart hnext).alphaIndex = i := by
    apply Fin.ext
    rfl
  rw [hleft, halpha] at hinternal
  have hinternal' :
      (a.order i.castSucc : ℚ) + a.alphaValue i =
        (S.sourceJordan.fundamentalWeightOrder k : ℚ) := by
    change (a.order i.castSucc : ℚ) + a.alphaValue i =
      ((S.sourceFundamentalWeight k).order : ℚ) at hinternal
    rw [S.sourceFundamentalWeight_order] at hinternal
    exact hinternal
  have hweight := F.fundamentalWeightOrder_eq k
  rw [F.indexEquiv_apply_eq_self] at hweight
  rw [← hcomponent]
  have hweightQ :
      (J.fundamentalWeightOrder k : ℚ) =
        (S.sourceJordan.fundamentalWeightOrder k : ℚ) := by
    exact_mod_cast hweight
  exact hweightQ.trans hinternal'.symm

end BONG.JordanOrderProfileWitness

end Bong
