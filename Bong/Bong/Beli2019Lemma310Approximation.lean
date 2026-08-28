/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Corollary311
import Bong.Bong.Beli2019Lemma310Central
import Bong.Bong.Beli2019Lemma310Long

/-!
# Beli (2019), Lemma 3.10 through arbitrary approximating spaces

This file separates the two mathematical layers used in Corollary 3.11.
Lemma 3.8 says that a prefix from a second good BONG is an approximating
space.  Lemma 3.10 then replaces the target and source prefixes, one at a
time, by arbitrary approximating spaces.  Full-rank source endpoints are
handled by the concrete BONG coordinate change.
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {m n : Nat}

variable
  [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
  [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
  [HilbertSymbolLaws K]
  [DiagonalRepresentationParityLaws K]
  [sourceAlpha : Beli2006AlphaLaws.{u, v} K]
  [targetAlpha : Beli2006AlphaLaws.{u, w} K]
  [DiagonalCodimensionOneCancellationLaws K]

omit [DiagonalCodimensionOneCancellationLaws K] in
/-- The central-prefix clause obtained from arbitrary approximating spaces. -/
theorem centralPrefix_change_of_approximation
    (a a' : GoodBONG q L (m + 1))
    (b b' : GoodBONG r M (n + 1)) (hRank : n ≤ m)
    (_horder : a.RepresentationOrderCondition b hRank)
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (m + 1) (n + 1))
    (htrigger : a.centralAlphaTrigger b i)
    (hrep : DiagonalRepresents
      (b.prefixValues (i.val - 1) (by
        have := i.le_small_succ
        omega))
      (a.prefixValues i.val (by
        have := i.lt_large
        omega))) :
    DiagonalRepresents
      (b'.prefixValues (i.val - 1) (by
        have := i.le_small_succ
        omega))
      (a'.prefixValues i.val (by
        have := i.lt_large
        omega)) := by
    let ia : Fin m := ⟨i.val - 1, by
      have := i.one_lt
      have := i.lt_large
      omega⟩
    let c := a'.prefixValueUnits (ia.val + 1) (by
      dsimp [ia]
      have := i.lt_large
      omega)
    have bridgeA : a.SpaceApproximationRepresentationBridge a' ia c := by
      letI := classificationV
      simpa only [c] using
        a.spaceApproximationRepresentationBridge_prefixValueUnits a' ia
    have hc : a.IsSpaceApproximation ia c := by
      letI := classificationV
      simpa only [c] using
        a.isSpaceApproximation_prefixValueUnits_of_bridge a' ia bridgeA
    have htoC := (a.centralTarget_iff_of_lemma218
      (sourceLaws := sourceAlpha) b hdefect i htrigger c hc).mp hrep
    have hi1 : (i.val - 1) + 1 = i.val := by
      have := i.one_lt
      omega
    have htoTarget :
        DiagonalRepresents
          (b.prefixValues (i.val - 1) (by
            have := i.le_small_succ
            omega))
          (a'.prefixValues i.val (by
            have := i.lt_large
            omega)) := by
      simp only [c, ia,
        BONG.GoodBONG.diagonalUnitCoefficients_prefixValueUnits] at htoC
      exact prefixRepresents_cast b a' rfl hi1 htoC
    by_cases hsource : i.val - 1 < n + 1
    · let ib : Fin n := ⟨i.val - 2, by
        have := i.one_lt
        have := hsource
        omega⟩
      let d := b'.prefixValueUnits (ib.val + 1) (by
        dsimp [ib]
        have := i.le_small_succ
        omega)
      have bridgeB : b.SpaceApproximationRepresentationBridge b' ib d := by
        letI := classificationW
        simpa only [d] using
          b.spaceApproximationRepresentationBridge_prefixValueUnits b' ib
      have hd : b.IsSpaceApproximation ib d := by
        letI := classificationW
        simpa only [d] using
          b.isSpaceApproximation_prefixValueUnits_of_bridge b' ib bridgeB
      have htoD := (a.centralSource_iff_of_lemma218
        (targetLaws := targetAlpha)
        b hdefect i htrigger hsource c d hc hd).mp htoC
      have hi2 : (i.val - 2) + 1 = i.val - 1 := by
        have := i.one_lt
        omega
      simp only [c, d, ia, ib,
        BONG.GoodBONG.diagonalUnitCoefficients_prefixValueUnits] at htoD
      exact prefixRepresents_cast b' a' hi2 hi1 htoD
    · have hfullIndex : i.val - 1 = n + 1 := by
        have := i.le_small_succ
        omega
      have hfull := b'.fullPrefix_represents b
      have hsourceChange :
          DiagonalRepresents
            (b'.prefixValues (i.val - 1) (by
              have := i.le_small_succ
              omega))
            (b.prefixValues (i.val - 1) (by
              have := i.le_small_succ
              omega)) := by
        exact prefixRepresents_cast b' b hfullIndex.symm
          hfullIndex.symm hfull
      exact hsourceChange.trans htoTarget
omit [DiagonalRepresentationParityLaws K] in
/-- The long-prefix clause obtained from arbitrary approximating spaces. -/
theorem longPrefix_change_of_approximation
    (a a' : GoodBONG q L (m + 1))
    (b b' : GoodBONG r M (n + 1)) (hRank : n ≤ m)
    (_horder : a.RepresentationOrderCondition b hRank)
    (i : LongRepresentationIndex (m + 1) (n + 1))
    (htrigger : a.longRepresentationTrigger b i)
    (hrep : DiagonalRepresents
      (b.prefixValues (i.val - 1) (by
        have := i.le_small_succ
        omega))
      (a.prefixValues (i.val + 1) (by
        have := i.succ_lt_large
        omega))) :
    DiagonalRepresents
      (b'.prefixValues (i.val - 1) (by
        have := i.le_small_succ
        omega))
      (a'.prefixValues (i.val + 1) (by
        have := i.succ_lt_large
        omega)) := by
    let ia : Fin m := ⟨i.val, by
      have := i.succ_lt_large
      omega⟩
    let c := a'.prefixValueUnits (ia.val + 1) (by
      dsimp [ia]
      have := i.succ_lt_large
      omega)
    have bridgeA : a.SpaceApproximationRepresentationBridge a' ia c := by
      letI := classificationV
      simpa only [c] using
        a.spaceApproximationRepresentationBridge_prefixValueUnits a' ia
    have hc : a.IsSpaceApproximation ia c := by
      letI := classificationV
      simpa only [c] using
        a.isSpaceApproximation_prefixValueUnits_of_bridge a' ia bridgeA
    have htoC := (a.longTarget_iff_of_cancellation
      (sourceLaws := sourceAlpha) b i htrigger c hc).mp hrep
    have htoTarget :
        DiagonalRepresents
          (b.prefixValues (i.val - 1) (by
            have := i.le_small_succ
            omega))
          (a'.prefixValues (i.val + 1) (by
            have := i.succ_lt_large
            omega)) := by
      simpa only [c, ia,
        BONG.GoodBONG.diagonalUnitCoefficients_prefixValueUnits]
        using htoC
    by_cases hsource : i.val - 1 < n + 1
    · let ib : Fin n := ⟨i.val - 2, by
        have := i.one_lt
        have := hsource
        omega⟩
      let d := b'.prefixValueUnits (ib.val + 1) (by
        dsimp [ib]
        have := i.le_small_succ
        omega)
      have bridgeB : b.SpaceApproximationRepresentationBridge b' ib d := by
        letI := classificationW
        simpa only [d] using
          b.spaceApproximationRepresentationBridge_prefixValueUnits b' ib
      have hd : b.IsSpaceApproximation ib d := by
        letI := classificationW
        simpa only [d] using
          b.isSpaceApproximation_prefixValueUnits_of_bridge b' ib bridgeB
      have htoD := (a.longSource_iff_of_cancellation
        (targetLaws := targetAlpha)
        b i htrigger hsource c d hc hd).mp htoC
      have hi2 : (i.val - 2) + 1 = i.val - 1 := by
        have := i.one_lt
        omega
      simp only [c, d, ia, ib,
        BONG.GoodBONG.diagonalUnitCoefficients_prefixValueUnits] at htoD
      exact prefixRepresents_cast b' a' hi2 rfl htoD
    · have hfullIndex : i.val - 1 = n + 1 := by
        have := i.le_small_succ
        omega
      have hfull := b'.fullPrefix_represents b
      have hsourceChange :
          DiagonalRepresents
            (b'.prefixValues (i.val - 1) (by
              have := i.le_small_succ
              omega))
            (b.prefixValues (i.val - 1) (by
              have := i.le_small_succ
              omega)) := by
        exact prefixRepresents_cast b' b hfullIndex.symm
          hfullIndex.symm hfull
      exact hsourceChange.trans htoTarget

end BONG.GoodBONG

/-- Lemmas 3.8 and 3.10, in their approximation forms, imply the pointwise
change-of-BONG prefix law.  A source prefix at the complete-rank endpoint is
transported by the concrete BONG coordinate change instead. -/
noncomputable instance lemma310PrefixLawsOfApproximationLaws
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [HilbertSymbolLaws K] [DiagonalRepresentationParityLaws K]
    [sourceAlpha : Beli2006AlphaLaws.{u, v} K]
    [targetAlpha : Beli2006AlphaLaws.{u, w} K]
    [DiagonalCodimensionOneCancellationLaws K] :
    Beli2019Lemma310PrefixLaws.{u, v, w} K where
  central := BONG.GoodBONG.centralPrefix_change_of_approximation
    (classificationV := classificationV)
    (classificationW := classificationW)
    (sourceAlpha := sourceAlpha) (targetAlpha := targetAlpha)
  long := BONG.GoodBONG.longPrefix_change_of_approximation
    (classificationV := classificationV)
    (classificationW := classificationW)
    (sourceAlpha := sourceAlpha) (targetAlpha := targetAlpha)

end Bong
