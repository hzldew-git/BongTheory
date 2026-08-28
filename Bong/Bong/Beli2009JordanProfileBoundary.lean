/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009JordanAlphaTransport

/-!
# Beli (2009), Lemma 2.16(ii), for an arbitrary Jordan profile

The proof of Beli's boundary formula is first established for a Jordan
decomposition adapted to the chosen good BONG.  The identity isometry
identifies that decomposition with any other Jordan decomposition of the same
lattice at the level of O'Meara's complete fundamental type.  This file
transports the formula needed in Beli (2019), Lemma 5.14:

`alpha = min (order of the fundamental ideal) (half of the order gap)`.

The ordered fractional ideal in the conclusion has exactly the carrier of the
fundamental ideal of the arbitrary decomposition; consequently the result can
be combined directly with ideal inclusions coming from scale truncations.
-/

namespace Bong

open Dyadic Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace Lattice.JordanDecomposition.SameFundamentalType

/-- Reindex only the source decomposition along an equality of its component
count.  This is the one-sided counterpart of `castComponentCount`. -/
noncomputable def castSourceComponentCount
    {c d e : Nat}
    {J : Lattice.JordanDecomposition q L c}
    {H : Lattice.JordanDecomposition q L d}
    (F : Lattice.JordanDecomposition.SameFundamentalType J H)
    (h : c = e) :
    Lattice.JordanDecomposition.SameFundamentalType
      (J.castComponentCount h) H := by
  subst e
  exact F

end Lattice.JordanDecomposition.SameFundamentalType

namespace BONG.JordanOrderProfileWitness

/-- Beli (2009), Lemma 2.16(ii), transported to an arbitrary profiled Jordan
decomposition.  The carrier equality makes the existentially packaged order
usable without choosing generators for the arbitrary decomposition. -/
theorem exists_orderedFundamentalIdeal_alpha_eq_min
    {n t : Nat} {a : GoodBONG q L (n + 2)}
    {J : Lattice.JordanDecomposition q L (t + 1)}
    (P : JordanOrderProfileWitness a.toBONG J) (z : Fin t) :
    ∃ I : Lattice.OrderedFractionalIdeal K,
      I.carrier = J.fundamentalIdeal z ∧
        a.alphaValue (P.boundaryIndex z) =
          min (I.order : ℚ) (a.halfGapValue (P.boundaryIndex z)) := by
  obtain ⟨S⟩ := a.nonempty_strictJordanAdaptedAlignment a (fun _ ↦ rfl)
  let F := Lattice.JordanDecomposition.sameFundamentalTypeOfIsometry
    S.sourceJordan J (Lattice.Isometry.refl q L)
  have hcount : S.componentCount = t + 1 := by
    simpa only [Fintype.card_fin] using Fintype.card_congr F.indexEquiv
  let Js := S.sourceJordanSucc hcount
  let Ps := S.sourceProfileSucc hcount
  let Fs : Lattice.JordanDecomposition.SameFundamentalType Js J :=
    F.castSourceComponentCount hcount
  have hRank :
      Js.toOrthogonalDecomposition.componentRank =
        J.toOrthogonalDecomposition.componentRank := by
    funext k
    have hk := Fs.componentRank_eq k
    rw [Fs.indexEquiv_apply_eq_self] at hk
    exact hk.symm
  have hboundary : Ps.boundaryIndex z = P.boundaryIndex z := by
    apply Fin.ext
    have hs := Ps.boundaryIndex_succ_val_eq_componentRankPrefix z
    have ht := P.boundaryIndex_succ_val_eq_componentRankPrefix z
    rw [hRank] at hs
    omega
  have hfundamental : J.fundamentalIdeal z = Js.fundamentalIdeal z :=
    Fs.fundamentalIdeal_eq z
  by_cases heven : Even (Js.boundaryNormOrderSum z)
  · let I := Js.evenOrderedFundamentalIdeal z
      (Ps.boundaryLeftValue z) (Ps.boundaryRightValue z)
      (S.sourceBoundaryLeftValue_isNormGeneratorValue hcount z)
      (S.sourceBoundaryRightValue_isNormGeneratorValue hcount z) heven
    refine ⟨I, ?_, ?_⟩
    · change Js.fundamentalIdeal z = J.fundamentalIdeal z
      exact hfundamental.symm
    · have hformula :=
        S.sourceEvenBoundaryFundamentalOrder_eq_alpha
          (a := a) (b := a) (t := t) hcount z heven
      have hle := a.alphaValue_le_halfGapValue (Ps.boundaryIndex z)
      change (I.order : ℚ) = a.alphaValue (Ps.boundaryIndex z) at hformula
      rw [← hboundary]
      rw [← hformula]
      exact (min_eq_left (hformula.le.trans hle)).symm
  · have hodd : Odd (Js.boundaryNormOrderSum z) :=
      Int.not_even_iff_odd.mp heven
    let D := S.sourceOddBoundaryAlphaData hcount z hodd
    let I := D.fundamental
    refine ⟨I, ?_, ?_⟩
    · change Js.fundamentalIdeal z = J.fundamentalIdeal z
      exact hfundamental.symm
    · have hformula := S.sourceOddBoundaryAlphaData_lemma216
        (a := a) (b := a) (t := t) hcount z hodd
      have hindex : D.index = Ps.boundaryIndex z := rfl
      rw [← hboundary, ← hindex]
      by_cases hordinary : Even (a.orderGap D.index) ∨
          a.orderGap D.index ≤ 2 * (ramificationIndex K : Int)
      · have halpha := hformula.1 hordinary
        have hle := a.alphaValue_le_halfGapValue D.index
        change a.alphaValue D.index = (I.order : ℚ) at halpha
        rw [halpha]
        exact (min_eq_left (halpha.symm.le.trans hle)).symm
      · have hexceptional := hformula.2 hordinary
        have hmin : a.halfGapValue D.index ≤ (I.order : ℚ) := by
          change a.halfGapValue D.index ≤ (D.fundamental.order : ℚ)
          rw [← hexceptional.1]
          linarith [hexceptional.2.2.1, hexceptional.2.2.2.1]
        rw [hexceptional.1]
        exact (min_eq_right hmin).symm

end BONG.JordanOrderProfileWitness

end Bong
