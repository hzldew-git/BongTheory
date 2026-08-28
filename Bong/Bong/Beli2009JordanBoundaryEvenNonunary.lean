/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009JordanBoundaryEven
import Bong.Bong.Beli2009JordanInternal
import Bong.Bong.Beli2009NeighborAlphaMinimum

/-!
# Beli (2009), Lemma 2.16(ii): non-unary even boundaries

This file identifies the two weight candidates in O'Meara's even boundary
formula with the predecessor and successor terms of Beli's Corollary 2.5.
It therefore proves the even branch of Lemma 2.16(ii) whenever both adjacent
Jordan components have rank at least two.
-/

namespace Bong
open Dyadic Module

namespace Lattice.JordanDecomposition

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

theorem castComponentCount_fundamentalScaleOrder
    {c d : Nat} (J : JordanDecomposition q L c) (h : c = d)
    (i : Fin d) :
    (J.castComponentCount h).fundamentalScaleOrder i =
      J.fundamentalScaleOrder (Fin.cast h.symm i) := by
  subst d
  rfl

theorem castComponentCount_fundamentalWeightOrder
    {c d : Nat} (J : JordanDecomposition q L c) (h : c = d)
    (i : Fin d) :
    (J.castComponentCount h).fundamentalWeightOrder i =
      J.fundamentalWeightOrder (Fin.cast h.symm i) := by
  subst d
  rfl

end Lattice.JordanDecomposition

namespace BONG.StrictJordanAdaptedAlignment

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {m : Nat}
  {a : GoodBONG q L (m + 1)} {b : GoodBONG r M (m + 1)}

theorem componentStop_eq_componentStart_of_val_succ
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k l : Fin S.componentCount) (hkl : l.val = k.val + 1) :
    S.componentStop k = S.componentStart l := by
  have hIio : Finset.Iio l = insert k (Finset.Iio k) := by
    ext x
    simp only [Finset.mem_Iio, Finset.mem_insert]
    change x.val < l.val ↔ x = k ∨ x.val < k.val
    rw [hkl]
    constructor
    · intro hx
      by_cases h : x.val = k.val
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (by omega)
    · rintro (rfl | hx) <;> omega
  unfold componentStop componentStart
  rw [hIio, Finset.sum_insert (by simp)]
  omega

theorem sourceEvenBoundaryRightTerm_eq_neighborAlphaCandidate
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1) (i : Fin t)
    (sidx : Fin m)
    (hsidx : sidx.val = ((S.sourceProfileSucc h).boundaryIndex i).val + 1)
    (hrank : 2 ≤ S.sourceJordan.componentRank
      (Fin.cast h.symm
        (Lattice.JordanDecomposition.boundaryRightIndex i))) :
    let P := S.sourceProfileSucc h
    let J := S.sourceJordanSucc h
    let j := P.boundaryIndex i
    (((ordUnit K (P.boundaryLeftValue i) -
        2 * J.fundamentalScaleOrder
          (Lattice.JordanDecomposition.boundaryLeftIndex i) +
        J.fundamentalWeightOrder
          (Lattice.JordanDecomposition.boundaryRightIndex i) : Int) : ℚ) :
      WithTop ℚ) = a.neighborAlphaCandidate j sidx := by
  dsimp only
  let P := S.sourceProfileSucc h
  let J := S.sourceJordanSucc h
  let li : Fin (t + 1) :=
    Lattice.JordanDecomposition.boundaryLeftIndex i
  let ri : Fin (t + 1) :=
    Lattice.JordanDecomposition.boundaryRightIndex i
  let k : Fin S.componentCount := Fin.cast h.symm ri
  let j : Fin m := P.boundaryIndex i
  have hk : 0 < k.val := by
    dsimp only [k, ri, Lattice.JordanDecomposition.boundaryRightIndex]
    change 0 < i.val + 1
    omega
  rcases S.source_hasTwoBlockSplit_componentStart k hk with ⟨T⟩
  have hweightRaw :=
    S.sourceFundamentalWeightOrder_eq_order_add_alpha_componentStart
      k hk T hrank
  have hstart : j.val + 1 = S.componentStart k := by
    dsimp only [j, P, k, ri]
    exact S.sourceBoundaryIndex_succ_val_eq_componentStart h i
  have hrankk : 2 ≤ S.sourceJordan.componentRank k := by
    simpa only [k, ri] using hrank
  have hstartLt : S.componentStart k < m := by
    have hstop := S.componentStop_le k
    unfold componentStop at hstop
    change 2 ≤ S.sourceJordan.toOrthogonalDecomposition.componentRank k at hrankk
    omega
  have hstartIdx :
      (⟨S.componentStart k, hstartLt⟩ : Fin m) = sidx := by
    apply Fin.ext
    rw [hsidx, hstart]
  have hweight :
      ((J.fundamentalWeightOrder ri : Int) : ℚ) =
        (a.order sidx.castSucc : ℚ) + a.alphaValue sidx := by
    dsimp only [J, sourceJordanSucc]
    rw [Lattice.JordanDecomposition.castComponentCount_fundamentalWeightOrder]
    change ((S.sourceJordan.fundamentalWeightOrder k : Int) : ℚ) = _
    change ((Lattice.weightIdealOrder q
      (S.sourceJordan.fundamentalLattice k) : Int) : ℚ) = _
    simpa only [hstartIdx] using hweightRaw
  have hleftGen := S.sourceBoundaryLeftValue_isNormGeneratorValue h i
  have hterminal := S.sourceTerminalValue_isNormGeneratorValue h li
  have hnorm := S.sourceNormGenerator_order_eq_fundamental h li
  have hu : ordUnit K (P.boundaryLeftValue i) =
      ordUnit K (J.fundamentalNormGenerator li) := by
    apply (Lattice.principalIdeal_eq_iff_ordUnit_eq _ _).mp
    exact hleftGen.2.symm.trans (J.fundamentalNormGenerator_spec li).2
  have horderLeft : a.order j.castSucc =
      2 * J.fundamentalScaleOrder li - ordUnit K (P.boundaryLeftValue i) := by
    rw [P.order_boundaryIndex i hterminal hnorm, hu]
  unfold GoodBONG.neighborAlphaCandidate GoodBONG.alphaGapValue
  apply congrArg (fun x : ℚ ↦ (x : WithTop ℚ))
  have hsidxSucc : sidx.castSucc = j.succ := by
    apply Fin.ext
    exact hsidx
  rw [← hsidxSucc]
  push_cast
  rw [hweight]
  dsimp only [J, P] at horderLeft ⊢
  have horderLeftQ : (a.order j.castSucc : ℚ) =
      2 * (J.fundamentalScaleOrder li : ℚ) -
        (ordUnit K (P.boundaryLeftValue i) : ℚ) := by
    exact_mod_cast horderLeft
  dsimp only [J, P] at horderLeftQ
  linarith

theorem sourceEvenBoundaryLeftTerm_eq_neighborAlphaCandidate
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1) (i : Fin t)
    (pidx : Fin m)
    (hpidx : pidx.val + 1 = ((S.sourceProfileSucc h).boundaryIndex i).val)
    (hrank : 2 ≤ S.sourceJordan.componentRank
      (Fin.cast h.symm
        (Lattice.JordanDecomposition.boundaryLeftIndex i))) :
    let P := S.sourceProfileSucc h
    let J := S.sourceJordanSucc h
    let j := P.boundaryIndex i
    (((ordUnit K (P.boundaryRightValue i) -
        2 * J.fundamentalScaleOrder
          (Lattice.JordanDecomposition.boundaryLeftIndex i) +
        J.fundamentalWeightOrder
          (Lattice.JordanDecomposition.boundaryLeftIndex i) : Int) : ℚ) :
      WithTop ℚ) = a.neighborAlphaCandidate j pidx := by
  dsimp only
  let P := S.sourceProfileSucc h
  let J := S.sourceJordanSucc h
  let li : Fin (t + 1) :=
    Lattice.JordanDecomposition.boundaryLeftIndex i
  let ri : Fin (t + 1) :=
    Lattice.JordanDecomposition.boundaryRightIndex i
  let kL : Fin S.componentCount := Fin.cast h.symm li
  let kR : Fin S.componentCount := Fin.cast h.symm ri
  let j : Fin m := P.boundaryIndex i
  have hkval : kR.val = kL.val + 1 := by
    dsimp only [kR, kL, ri, li,
      Lattice.JordanDecomposition.boundaryRightIndex,
      Lattice.JordanDecomposition.boundaryLeftIndex]
    rfl
  have hstopStart : S.componentStop kL = S.componentStart kR :=
    S.componentStop_eq_componentStart_of_val_succ kL kR hkval
  have hstartRight : j.val + 1 = S.componentStart kR := by
    dsimp only [j, P, kR, ri]
    exact S.sourceBoundaryIndex_succ_val_eq_componentStart h i
  have hstop : S.componentStop kL = j.val + 1 := by
    omega
  have hrankL : 2 ≤
      S.sourceJordan.toOrthogonalDecomposition.componentRank kL := by
    change 2 ≤ S.sourceJordan.componentRank kL at hrank
    exact hrank
  have hpidxj : pidx.val + 1 = j.val := by
    dsimp only [j, P]
    exact hpidx
  have hjpos : 0 < j.val := by
    have hstartNonneg : 0 ≤ S.componentStart kL := Nat.zero_le _
    unfold componentStop at hstop
    omega
  have hinsideStart : S.componentStart kL ≤ j.val - 1 := by
    unfold componentStop at hstop
    omega
  have hinsideNext : (j.val - 1) + 1 < S.componentStop kL := by
    omega
  have hinternal :=
    S.source_component_internal kL (j.val - 1) hinsideStart hinsideNext
  let D := S.sourceInternalAlphaData kL (j.val - 1)
    hinsideStart hinsideNext
  have hDleft : D.leftIndex = pidx.castSucc := by
    apply Fin.ext
    dsimp only [D, GoodBONG.InternalJordanAlphaData.leftIndex,
      sourceInternalAlphaData, GoodBONG.JordanBlockCoordinates.index,
      sourceComponentCoordinates]
    change j.val - 1 = pidx.val
    omega
  have hDalpha : D.alphaIndex = pidx := by
    apply Fin.ext
    dsimp only [D, GoodBONG.InternalJordanAlphaData.alphaIndex,
      sourceInternalAlphaData]
    change j.val - 1 = pidx.val
    omega
  have hweight :
      (a.order pidx.castSucc : ℚ) + a.alphaValue pidx =
        (J.fundamentalWeightOrder li : ℚ) := by
    have hleft := hinternal.1
    rw [hDleft, hDalpha] at hleft
    change (a.order pidx.castSucc : ℚ) + a.alphaValue pidx =
      ((S.sourceFundamentalWeight kL).order : ℚ) at hleft
    rw [S.sourceFundamentalWeight_order] at hleft
    dsimp only [J, sourceJordanSucc]
    rw [Lattice.JordanDecomposition.castComponentCount_fundamentalWeightOrder]
    simpa only [kL, li] using hleft
  have hsumInt :=
    (S.sourceComponentCoordinates kL).adjacent_order_sum
      (j.val - 1) hinsideStart hinsideNext
  have hinside : j.val - 1 <
      (S.sourceComponentCoordinates kL).stop := by
    change j.val - 1 < S.componentStop kL
    omega
  have hleftIndex :
      (S.sourceComponentCoordinates kL).index (j.val - 1) hinside =
        pidx.castSucc := by
    apply Fin.ext
    dsimp only [GoodBONG.JordanBlockCoordinates.index]
    change j.val - 1 = pidx.val
    omega
  have hrightIndex :
      (S.sourceComponentCoordinates kL).index ((j.val - 1) + 1)
          hinsideNext = j.castSucc := by
    apply Fin.ext
    dsimp only [GoodBONG.JordanBlockCoordinates.index]
    change (j.val - 1) + 1 = j.val
    omega
  rw [hleftIndex, hrightIndex] at hsumInt
  have hscaleCast : J.fundamentalScaleOrder li =
      S.sourceJordan.fundamentalScaleOrder kL := by
    dsimp only [J, sourceJordanSucc]
    rw [Lattice.JordanDecomposition.castComponentCount_fundamentalScaleOrder]
  have hsum : (a.order pidx.castSucc : ℚ) +
      (a.order j.castSucc : ℚ) =
        2 * (J.fundamentalScaleOrder li : ℚ) := by
    rw [hscaleCast]
    exact_mod_cast hsumInt
  have hrightGen := S.sourceBoundaryRightValue_isNormGeneratorValue h i
  have hv : ordUnit K (P.boundaryRightValue i) =
      ordUnit K (J.fundamentalNormGenerator ri) := by
    apply (Lattice.principalIdeal_eq_iff_ordUnit_eq _ _).mp
    exact hrightGen.2.symm.trans (J.fundamentalNormGenerator_spec ri).2
  have horderRight : a.order j.succ =
      ordUnit K (P.boundaryRightValue i) := by
    rw [P.order_boundaryIndex_succ i, hv]
  unfold GoodBONG.neighborAlphaCandidate GoodBONG.alphaGapValue
  apply congrArg (fun x : ℚ ↦ (x : WithTop ℚ))
  push_cast
  have horderRightQ : (a.order j.succ : ℚ) =
      (ordUnit K (P.boundaryRightValue i) : ℚ) := by
    exact_mod_cast horderRight
  linarith

theorem sourceEvenBoundaryCandidateMinimum_eq_alpha_of_nonunary
    {n : Nat}
    {a : GoodBONG q L (n + 2)} {b : GoodBONG r M (n + 2)}
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1) (i : Fin t)
    (hrankLeft : 2 ≤ S.sourceJordan.componentRank
      (Fin.cast h.symm
        (Lattice.JordanDecomposition.boundaryLeftIndex i)))
    (hrankRight : 2 ≤ S.sourceJordan.componentRank
      (Fin.cast h.symm
        (Lattice.JordanDecomposition.boundaryRightIndex i)))
    (heven : Even ((S.sourceJordanSucc h).boundaryNormOrderSum i)) :
    let P := S.sourceProfileSucc h
    let J := S.sourceJordanSucc h
    let j := P.boundaryIndex i
    J.evenBoundaryCandidateMinimum i
        (P.boundaryLeftValue i) (P.boundaryRightValue i) =
      (a.alphaValue j : WithTop ℚ) := by
  dsimp only
  let P := S.sourceProfileSucc h
  let J := S.sourceJordanSucc h
  let li : Fin (t + 1) :=
    Lattice.JordanDecomposition.boundaryLeftIndex i
  let ri : Fin (t + 1) :=
    Lattice.JordanDecomposition.boundaryRightIndex i
  let kL : Fin S.componentCount := Fin.cast h.symm li
  let kR : Fin S.componentCount := Fin.cast h.symm ri
  let j : Fin (n + 1) := P.boundaryIndex i
  have hkval : kR.val = kL.val + 1 := by
    dsimp only [kR, kL, ri, li,
      Lattice.JordanDecomposition.boundaryRightIndex,
      Lattice.JordanDecomposition.boundaryLeftIndex]
    rfl
  have hstopStart : S.componentStop kL = S.componentStart kR :=
    S.componentStop_eq_componentStart_of_val_succ kL kR hkval
  have hstartRight : j.val + 1 = S.componentStart kR := by
    dsimp only [j, P, kR, ri]
    exact S.sourceBoundaryIndex_succ_val_eq_componentStart h i
  have hstopLeft : S.componentStop kL = j.val + 1 := by omega
  have hrankL : 2 ≤
      S.sourceJordan.toOrthogonalDecomposition.componentRank kL := by
    change 2 ≤ S.sourceJordan.componentRank kL at hrankLeft
    exact hrankLeft
  have hjpos : 0 < j.val := by
    unfold componentStop at hstopLeft
    omega
  have hrankR : 2 ≤
      S.sourceJordan.toOrthogonalDecomposition.componentRank kR := by
    change 2 ≤ S.sourceJordan.componentRank kR at hrankRight
    exact hrankRight
  have hjsucc : j.val + 1 < n + 1 := by
    have hstopRight := S.componentStop_le kR
    unfold componentStop at hstopRight
    omega
  let p : Fin (n + 1) := ⟨j.val - 1, by omega⟩
  let s : Fin (n + 1) := ⟨j.val + 1, hjsucc⟩
  have hp : p.val + 1 = j.val := by
    dsimp only [p]
    omega
  have hs : s.val = j.val + 1 := rfl
  have hleftGen := S.sourceBoundaryLeftValue_isNormGeneratorValue h i
  have hrightGen := S.sourceBoundaryRightValue_isNormGeneratorValue h i
  have hterminal := S.sourceTerminalValue_isNormGeneratorValue h li
  have hnorm := S.sourceNormGenerator_order_eq_fundamental h li
  have hprofile := P.evenBoundaryCandidateMinimum_eq_profileMinimum i
    hleftGen hrightGen hterminal hnorm heven
  have hrightTerm :=
    S.sourceEvenBoundaryRightTerm_eq_neighborAlphaCandidate
      h i s hs hrankRight
  have hleftTerm :=
    S.sourceEvenBoundaryLeftTerm_eq_neighborAlphaCandidate
      h i p hp hrankLeft
  rw [hprofile, hrightTerm, hleftTerm]
  rw [min_comm (a.neighborAlphaCandidate j s)
    (a.neighborAlphaCandidate j p)]
  exact (a.alphaValue_eq_min_four_neighborCandidates j hjpos hjsucc).symm

theorem sourceEvenBoundaryFundamentalOrder_eq_alpha_of_nonunary
    {n : Nat}
    {a : GoodBONG q L (n + 2)} {b : GoodBONG r M (n + 2)}
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1) (i : Fin t)
    (hrankLeft : 2 ≤ S.sourceJordan.componentRank
      (Fin.cast h.symm
        (Lattice.JordanDecomposition.boundaryLeftIndex i)))
    (hrankRight : 2 ≤ S.sourceJordan.componentRank
      (Fin.cast h.symm
        (Lattice.JordanDecomposition.boundaryRightIndex i)))
    (heven : Even ((S.sourceJordanSucc h).boundaryNormOrderSum i)) :
    let P := S.sourceProfileSucc h
    let J := S.sourceJordanSucc h
    let hleft := S.sourceBoundaryLeftValue_isNormGeneratorValue h i
    let hright := S.sourceBoundaryRightValue_isNormGeneratorValue h i
    (((J.evenOrderedFundamentalIdeal i
        (P.boundaryLeftValue i) (P.boundaryRightValue i)
        hleft hright heven).order : Int) : ℚ) =
      a.alphaValue (P.boundaryIndex i) := by
  dsimp only
  apply (S.sourceJordanSucc h).evenOrderedFundamentalIdeal_order_eq_alpha_of_candidateMinimum
  exact S.sourceEvenBoundaryCandidateMinimum_eq_alpha_of_nonunary
    h i hrankLeft hrankRight heven

end BONG.StrictJordanAdaptedAlignment

end Bong
