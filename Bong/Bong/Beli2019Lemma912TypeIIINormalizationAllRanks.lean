/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma912TypeIIINormalization

/-!
# Beli (2019), Lemma 9.12: type-III normalization in every admissible rank

The normalization used in the type-III branch only changes the initial
ternary segment.  In particular, its proof does not use fourth or fifth BONG
coordinates.  This file records the construction at its natural lower bound,
rank three, with precisely the three local hypotheses used by the argument.
-/

namespace Bong

open Dyadic
open Module

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {T : Nat}

/-- The initial ternary segment, including the rank-three endpoint. -/
noncomputable def lemma912InitialThreeSegmentAllRanks
    (a : GoodBONG q L (T + 3)) :
    BONG.SegmentWitness a.toBONG 0 3 (by omega) :=
  a.toBONG.segmentWitness 0 3 (by omega)

/-- The initial ternary segment as a good BONG. -/
noncomputable def lemma912InitialThreeAllRanks
    (a : GoodBONG q L (T + 3)) :
    GoodBONG
      (q.restrict a.lemma912InitialThreeSegmentAllRanks.carrier
        a.lemma912InitialThreeSegmentAllRanks.nondegenerate)
      a.lemma912InitialThreeSegmentAllRanks.lattice 3 :=
  a.lemma912InitialThreeSegmentAllRanks.toGoodBONG a.good

theorem lemma912InitialThreeAllRanks_valueUnit_eq
    (a : GoodBONG q L (T + 3)) (i : Fin 3) :
    a.lemma912InitialThreeAllRanks.valueUnit i =
      a.valueUnit ⟨i.1, by omega⟩ := by
  let s := a.lemma912InitialThreeSegmentAllRanks
  change s.bong.valueUnit i = a.toBONG.valueUnit ⟨i.1, by omega⟩
  calc
    s.bong.valueUnit i = a.toBONG.valueUnit (s.sourceIndex i) :=
      s.valueUnit_eq i
    _ = a.toBONG.valueUnit ⟨i.1, by omega⟩ := by
      congr 1
      apply Fin.ext
      simp only [BONG.SegmentWitness.sourceIndex_val]
      omega

theorem lemma912InitialThreeAllRanks_order_eq
    (a : GoodBONG q L (T + 3)) (i : Fin 3) :
    a.lemma912InitialThreeAllRanks.order i =
      a.order ⟨i.1, by omega⟩ := by
  let s := a.lemma912InitialThreeSegmentAllRanks
  change s.bong.order i = a.toBONG.order ⟨i.1, by omega⟩
  calc
    s.bong.order i = a.toBONG.order (s.sourceIndex i) := s.order_eq i
    _ = a.toBONG.order ⟨i.1, by omega⟩ := by
      congr 1
      apply Fin.ext
      simp only [BONG.SegmentWitness.sourceIndex_val]
      omega

theorem lemma912InitialThreeAllRanks_adjacentDefect_eq
    (a : GoodBONG q L (T + 3)) (i : Fin 2) :
    a.lemma912InitialThreeAllRanks.adjacentDefect i =
      a.adjacentDefect ⟨i.1, by omega⟩ := by
  unfold adjacentDefect adjacentProduct
  rw [a.lemma912InitialThreeAllRanks_valueUnit_eq i.castSucc,
    a.lemma912InitialThreeAllRanks_valueUnit_eq i.succ]
  congr 2

theorem lemma912InitialThreeAllRanks_firstBinaryAlpha_eq
    (a : GoodBONG q L (T + 3)) :
    a.lemma912InitialThreeAllRanks.firstBinaryAlpha = a.firstBinaryAlpha := by
  unfold firstBinaryAlpha halfGapCandidate leftDefectCandidate
  rw [a.lemma912InitialThreeAllRanks_order_eq (0 : Fin 2).castSucc,
    a.lemma912InitialThreeAllRanks_order_eq (0 : Fin 2).succ,
    a.lemma912InitialThreeAllRanks_adjacentDefect_eq (0 : Fin 2)]
  rfl

def lemma912InitialThreeFirstLocalizationAllRanks :
    AlphaLocalizationIndex (T + 2) where
  start := 0
  pivot := 0
  stop := 2
  start_le_pivot := by omega
  pivot_lt_stop := by omega
  stop_lt := by omega

/-- Localization of the first alpha remains valid when the ambient rank is
exactly three. -/
theorem lemma912InitialThreeAllRanks_firstAlpha_eq
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    (a : GoodBONG q L (T + 3))
    (hbinary : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin (T + 2)) : WithTop ℚ)) :
    a.lemma912InitialThreeAllRanks.alphaValue (0 : Fin 2) =
      a.alphaValue (0 : Fin (T + 2)) := by
  let p := lemma912InitialThreeFirstLocalizationAllRanks (T := T)
  let w := a.toBONG.segmentWitness p.start p.length p.bound
  let s := w.toGoodBONG a.good
  have hw : w = a.lemma912InitialThreeSegmentAllRanks := by rfl
  have hs : s = a.lemma912InitialThreeAllRanks := by rfl
  have hpivot : p.pivotFin = (0 : Fin (T + 2)) := by
    apply Fin.ext
    rfl
  have hlocalPivot : p.localPivot = (0 : Fin 2) := by
    apply Fin.ext
    rfl
  have hglobalLeLocalRaw := a.beli2009Lemma21_le_segmentAlpha p w
  have hglobalLeLocal :
      (a.alphaValue (0 : Fin (T + 2)) : WithTop ℚ) ≤
        (s.alphaValue (0 : Fin 2) : WithTop ℚ) := by
    rw [a.coe_alphaValue, s.coe_alphaValue]
    rw [hpivot, hlocalPivot] at hglobalLeLocalRaw
    exact hglobalLeLocalRaw
  have hlocalLeBinary :
      (s.alphaValue (0 : Fin 2) : WithTop ℚ) ≤ s.firstBinaryAlpha := by
    unfold firstBinaryAlpha
    apply le_min
    · rw [s.coe_alphaValue]
      exact s.alpha_le_halfGapCandidate (0 : Fin 2)
    · rw [s.coe_alphaValue]
      exact s.alpha_le_leftDefectCandidate
        (i := (0 : Fin 2)) (j := (0 : Fin 2)) le_rfl
  have hlocalBinary : s.firstBinaryAlpha = a.firstBinaryAlpha := by
    rw [hs]
    exact a.lemma912InitialThreeAllRanks_firstBinaryAlpha_eq
  rw [hlocalBinary, hbinary] at hlocalLeBinary
  have heq : s.alphaValue (0 : Fin 2) =
      a.alphaValue (0 : Fin (T + 2)) := by
    exact_mod_cast le_antisymm hlocalLeBinary hglobalLeLocal
  rw [hs] at heq
  exact heq

/-- The type-III normalization at its natural rank-three lower bound. -/
structure Beli2019Lemma912TypeIIINormalizationDataAllRanks
    (a : GoodBONG q L (T + 3)) where
  transformed : GoodBONG q L (T + 3)
  sameOrders : a.SameOrders transformed
  sameAlphas : a.SameAlphas transformed
  pairBoundary :
    (((transformed.orderGap (1 : Fin (T + 2)) : Int) : ℚ) : WithTop ℚ) +
        transformed.adjacentDefect (1 : Fin (T + 2)) = 1

set_option maxHeartbeats 4000000 in
/-- The initial ternary type-III normalization works in every rank `T + 3`.
No out-of-range fourth or fifth coordinate is used. -/
theorem exists_beli2019Lemma912TypeIIINormalizationData_allRanks
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [DyadicDiagonalClassificationLaws K]
    (a : GoodBONG q L (T + 3))
    (houter : a.order (0 : Fin (T + 3)) =
      a.order (2 : Fin (T + 3)))
    (hgapEven : Even (a.orderGap (0 : Fin (T + 2))))
    (hsecond : a.alphaValue (1 : Fin (T + 2)) = 1) :
    Nonempty (Beli2019Lemma912TypeIIINormalizationDataAllRanks a) := by
  rcases a.beli2019Corollary811 (0 : Fin (T + 2)) with ⟨C⟩
  let a₀ := C.transformed
  have horders₀ : a.SameOrders a₀ := a.order_invariant a₀
  have halphas₀ : a.SameAlphas a₀ := a.alpha_invariant a₀
  have hfirstBinary : a₀.firstBinaryAlpha =
      (a₀.alphaValue (0 : Fin (T + 2)) : WithTop ℚ) := by
    rw [← a₀.adjacentBinaryAlpha_zero]
    exact C.adjacentBinaryAlpha_eq
  let s := a₀.lemma912InitialThreeAllRanks
  have hsFirst : s.alphaValue (0 : Fin 2) =
      a₀.alphaValue (0 : Fin (T + 2)) :=
    a₀.lemma912InitialThreeAllRanks_firstAlpha_eq hfirstBinary
  have houter₀ : a₀.order (0 : Fin (T + 3)) =
      a₀.order (2 : Fin (T + 3)) := by
    calc
      a₀.order (0 : Fin (T + 3)) = a.order 0 := (horders₀ 0).symm
      _ = a.order 2 := houter
      _ = a₀.order (2 : Fin (T + 3)) := horders₀ 2
  have hsecond₀ : a₀.alphaValue (1 : Fin (T + 2)) = 1 :=
    (halphas₀ 1).symm.trans hsecond
  have hsOuter : s.order (0 : Fin 3) = s.order (2 : Fin 3) := by
    rw [a₀.lemma912InitialThreeAllRanks_order_eq,
      a₀.lemma912InitialThreeAllRanks_order_eq]
    exact houter₀
  have hsSecond : s.alphaValue (1 : Fin 2) =
      a₀.alphaValue (1 : Fin (T + 2)) := by
    have hg := a₀.beli2019Remark87 (0 : Fin (T + 1)) houter₀
    have hl := s.beli2019Remark87 (0 : Fin 1) hsOuter
    have hg' := hg.previousAlpha_eq
    have hl' := hl.previousAlpha_eq
    change a₀.alphaValue (0 : Fin (T + 2)) =
      ((a₀.order (1 : Fin (T + 3)) -
        a₀.order (2 : Fin (T + 3)) : Int) : ℚ) +
        a₀.alphaValue (1 : Fin (T + 2)) at hg'
    change s.alphaValue (0 : Fin 2) =
      ((s.order (1 : Fin 3) - s.order (2 : Fin 3) : Int) : ℚ) +
        s.alphaValue (1 : Fin 2) at hl'
    rw [hsFirst,
      a₀.lemma912InitialThreeAllRanks_order_eq (1 : Fin 3),
      a₀.lemma912InitialThreeAllRanks_order_eq (2 : Fin 3)] at hl'
    have hone : (⟨(1 : Fin 3).1, by omega⟩ : Fin (T + 3)) =
        (1 : Fin (T + 3)) := by
      apply Fin.ext
      rfl
    have htwo : (⟨(2 : Fin 3).1, by omega⟩ : Fin (T + 3)) =
        (2 : Fin (T + 3)) := by
      apply Fin.ext
      rfl
    rw [hone, htwo] at hl'
    linarith
  let R₁ : Int := a₀.order (0 : Fin (T + 3))
  let R₂ : Int := a₀.order (1 : Fin (T + 3))
  let A : Int := R₂ - R₁ + 1
  have hfirstFormula : a₀.alphaValue (0 : Fin (T + 2)) = (A : ℚ) := by
    have hg := a₀.beli2019Remark87 (0 : Fin (T + 1)) houter₀
    have hg' := hg.previousAlpha_eq
    change a₀.alphaValue (0 : Fin (T + 2)) =
      ((a₀.order (1 : Fin (T + 3)) -
        a₀.order (2 : Fin (T + 3)) : Int) : ℚ) +
        a₀.alphaValue (1 : Fin (T + 2)) at hg'
    rw [houter₀.symm, hsecond₀] at hg'
    dsimp only [A, R₁, R₂]
    push_cast at hg' ⊢
    linarith
  have hsFirstFormula : s.alphaValue (0 : Fin 2) = (A : ℚ) :=
    hsFirst.trans hfirstFormula
  have hgapEven₀ : Even (R₂ - R₁) := by
    unfold orderGap at hgapEven
    change Even
      (a.order (1 : Fin (T + 3)) - a.order (0 : Fin (T + 3))) at hgapEven
    simpa only [R₁, R₂, horders₀ (0 : Fin (T + 3)),
      horders₀ (1 : Fin (T + 3))] using hgapEven
  have hAOdd : Odd A := by
    rcases hgapEven₀ with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    dsimp only [A]
    omega
  have hrefOrders : ∀ i : Fin 3, s.order i = ![R₁, R₂, R₁] i := by
    intro i
    fin_cases i <;>
      simp [s, R₁, R₂, a₀.lemma912InitialThreeAllRanks_order_eq, houter₀]
    apply congrArg a₀.order
    apply Fin.ext
    rfl
  have C₉₉ := Beli2019Lemma99Conditions.ofReferenceInvariants.{u, v}
    s R₁ R₂ A hrefOrders hsFirstFormula
  rcases beli2019Lemma99_moreover s R₁ R₂ R₁ A rfl hAOdd C₉₉ with
    ⟨D, hDDefect⟩
  have hsameOrders : s.SameOrders D.bong := by
    intro i
    rw [hrefOrders i, D.orders i]
  have hfirstSD : s.alphaValue (0 : Fin 2) =
      D.bong.alphaValue (0 : Fin 2) :=
    hsFirstFormula.trans D.firstAlpha.symm
  rcases (s.beli2019Lemma711 D.bong hsameOrders hsOuter).2 hfirstSD with ⟨f⟩
  let t : GoodBONG
      (q.restrict a₀.lemma912InitialThreeSegmentAllRanks.carrier
        a₀.lemma912InitialThreeSegmentAllRanks.nondegenerate)
      a₀.lemma912InitialThreeSegmentAllRanks.lattice 3 :=
    D.bong.mapLatticeIsometry f.symm
  have htValues : ∀ i, t.valueUnit i = D.bong.valueUnit i := by
    intro i
    apply Units.ext
    change (D.bong.toBONG.mapLatticeIsometry f.symm).value i =
      D.bong.toBONG.value i
    exact BONG.value_mapLatticeIsometry f.symm D.bong.toBONG i
  have htDefect : t.adjacentDefect (1 : Fin 2) =
      ((A : ℚ) : WithTop ℚ) := by
    unfold adjacentDefect adjacentProduct
    rw [htValues, htValues]
    simpa only [adjacentDefect, adjacentProduct] using hDDefect
  rcases a₀.toBONG.beliLemma49_ii a₀.good
      a₀.lemma912InitialThreeSegmentAllRanks t.toBONG t.good with ⟨R⟩
  let transformed : GoodBONG q L (T + 3) := ⟨R.bong, R.good⟩
  have hinsideValue (i : Fin 3) :
      transformed.valueUnit (⟨i.val, by omega⟩ : Fin (T + 3)) =
        t.valueUnit i := by
    apply Units.ext
    change R.bong.value ⟨i.val, by omega⟩ = t.toBONG.value i
    rw [← R.bong.quadratic_ambientVector,
      ← t.toBONG.quadratic_ambientVector]
    change q.quadratic (R.bong.ambientVector ⟨i.val, by omega⟩) =
      q.quadratic (t.toBONG.ambientVector i : V)
    simpa only [zero_add] using congrArg q.quadratic (R.inside_eq i)
  have htransformedDefect :
      transformed.adjacentDefect (1 : Fin (T + 2)) =
        ((A : ℚ) : WithTop ℚ) := by
    unfold adjacentDefect adjacentProduct
    have hcast : (Fin.castSucc (1 : Fin (T + 2))) =
        (⟨((1 : Fin 2).castSucc).val, by omega⟩ : Fin (T + 3)) := by
      apply Fin.ext
      rfl
    have hsucc : (Fin.succ (1 : Fin (T + 2))) =
        (⟨((1 : Fin 2).succ).val, by omega⟩ : Fin (T + 3)) := by
      apply Fin.ext
      rfl
    rw [hcast, hsucc, hinsideValue (1 : Fin 2).castSucc,
      hinsideValue (1 : Fin 2).succ]
    simpa only [adjacentDefect, adjacentProduct] using htDefect
  have hordersFinal : a.SameOrders transformed := a.order_invariant transformed
  have halphasFinal : a.SameAlphas transformed := a.alpha_invariant transformed
  have hpairGap : transformed.orderGap (1 : Fin (T + 2)) = R₁ - R₂ := by
    unfold orderGap
    change transformed.order (2 : Fin (T + 3)) -
      transformed.order (1 : Fin (T + 3)) = R₁ - R₂
    rw [← hordersFinal (1 : Fin (T + 3)),
      ← hordersFinal (2 : Fin (T + 3)),
      horders₀ (1 : Fin (T + 3)), horders₀ (2 : Fin (T + 3))]
    dsimp only [R₁, R₂]
    rw [← houter₀]
  refine ⟨{
    transformed := transformed
    sameOrders := hordersFinal
    sameAlphas := halphasFinal
    pairBoundary := ?_
  }⟩
  rw [hpairGap, htransformedDefect]
  change (((((R₁ - R₂ : Int) : ℚ) + (A : ℚ)) : ℚ) : WithTop ℚ) =
    ((1 : ℚ) : WithTop ℚ)
  congr 1
  dsimp only [A]
  push_cast
  ring

end BONG.GoodBONG

end Bong
