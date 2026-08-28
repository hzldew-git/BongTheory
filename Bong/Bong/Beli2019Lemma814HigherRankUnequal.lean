/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma814HigherRankAssembly

/-!
# Beli (2019), Lemma 8.14: the higher-rank unequal-outer branch

This file treats case `R₁ < R₃` in the converse direction of Lemma 8.14.
The first declarations isolate the initial ternary segment in arbitrary
ambient rank.  They then formalize the direct subcase in which the uncapped
defect already satisfies the rank-three inequality (paper, pp. 43--44).
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
  {L : Lattice K V} {M : Lattice K W} {N : Nat}

/-- The canonical initial ternary segment of a target of rank at least four. -/
noncomputable def lemma814InitialThreeSegment
    (a : GoodBONG q L (N + 4)) :
    BONG.SegmentWitness a.toBONG 0 3 (by omega) :=
  a.toBONG.segmentWitness 0 3 (by omega)

/-- The initial ternary segment, regarded as a good BONG. -/
noncomputable def lemma814InitialThree
    (a : GoodBONG q L (N + 4)) :
    GoodBONG
      (q.restrict a.lemma814InitialThreeSegment.carrier
        a.lemma814InitialThreeSegment.nondegenerate)
      a.lemma814InitialThreeSegment.lattice 3 :=
  a.lemma814InitialThreeSegment.toGoodBONG a.good

/-- Values of the initial ternary segment are the first three ambient values. -/
theorem lemma814InitialThree_valueUnit_eq
    (a : GoodBONG q L (N + 4)) (i : Fin 3) :
    a.lemma814InitialThree.valueUnit i =
      a.valueUnit ⟨i.1, by omega⟩ := by
  let s := a.lemma814InitialThreeSegment
  change s.bong.valueUnit i = a.toBONG.valueUnit ⟨i.1, by omega⟩
  calc
    s.bong.valueUnit i = a.toBONG.valueUnit (s.sourceIndex i) :=
      s.valueUnit_eq i
    _ = a.toBONG.valueUnit ⟨i.1, by omega⟩ := by
      congr 1
      apply Fin.ext
      simp only [BONG.SegmentWitness.sourceIndex_val]
      omega

/-- Orders of the initial ternary segment are the first three ambient orders. -/
theorem lemma814InitialThree_order_eq
    (a : GoodBONG q L (N + 4)) (i : Fin 3) :
    a.lemma814InitialThree.order i = a.order ⟨i.1, by omega⟩ := by
  let s := a.lemma814InitialThreeSegment
  change s.bong.order i = a.toBONG.order ⟨i.1, by omega⟩
  calc
    s.bong.order i = a.toBONG.order (s.sourceIndex i) := s.order_eq i
    _ = a.toBONG.order ⟨i.1, by omega⟩ := by
      congr 1
      apply Fin.ext
      simp only [BONG.SegmentWitness.sourceIndex_val]
      omega

/-- Initial prefix products agree with their ambient counterparts. -/
theorem lemma814InitialThree_prefixProduct_eq
    (a : GoodBONG q L (N + 4)) (k : Nat) (hk : k ≤ 3) :
    a.lemma814InitialThree.prefixProduct k = a.prefixProduct k := by
  induction k with
  | zero =>
      simp only [GoodBONG.prefixProduct, BONG.prefixProduct_zero]
  | succ k ih =>
      have hkThree : k < 3 := by omega
      have hkAmbient : k < N + 4 := by omega
      unfold GoodBONG.prefixProduct
      rw [a.lemma814InitialThree.toBONG.prefixProduct_succ k hkThree,
        a.toBONG.prefixProduct_succ k hkAmbient]
      have ih' := ih (by omega)
      change a.lemma814InitialThree.toBONG.prefixProduct k =
        a.toBONG.prefixProduct k at ih'
      rw [ih']
      congr 1
      exact a.lemma814InitialThree_valueUnit_eq ⟨k, hkThree⟩

/-- Prefix coefficient functions of length at most three agree. -/
theorem lemma814InitialThree_prefixValues_eq
    (a : GoodBONG q L (N + 4)) (k : Nat) (hk : k ≤ 3) :
    a.lemma814InitialThree.prefixValues k hk =
      a.prefixValues k (by omega) := by
  funext i
  unfold prefixValues
  rw [← a.lemma814InitialThree.coe_valueUnit, ← a.coe_valueUnit,
    a.lemma814InitialThree_valueUnit_eq]

/-- The literal initial ternary segment has exactly the isotropy status of
the first three coefficients in the ambient BONG. -/
theorem lemma814InitialThree_firstThreeIsotropic_iff
    (a : GoodBONG q L (N + 4)) :
    a.lemma814InitialThree.Lemma814FirstThreeIsotropic ↔
      a.Lemma814FirstThreeIsotropic := by
  unfold Lemma814FirstThreeIsotropic lemma814FirstThreeValues
  rw [a.lemma814InitialThree_prefixValues_eq 3 le_rfl]

/-- Adjacent defects inside the initial ternary segment are unchanged. -/
theorem lemma814InitialThree_adjacentDefect_eq
    (a : GoodBONG q L (N + 4)) (i : Fin 2) :
    a.lemma814InitialThree.adjacentDefect i =
      a.adjacentDefect ⟨i.1, by omega⟩ := by
  unfold adjacentDefect adjacentProduct
  rw [a.lemma814InitialThree_valueUnit_eq i.castSucc,
    a.lemma814InitialThree_valueUnit_eq i.succ]
  congr 2

/-- Literal binary alphas in the initial ternary segment agree with the two
corresponding ambient binary alphas. -/
theorem lemma814InitialThree_adjacentBinaryAlpha_eq
    (a : GoodBONG q L (N + 4)) (i : Fin 2) :
    a.lemma814InitialThree.adjacentBinaryAlpha i =
      a.adjacentBinaryAlpha ⟨i.1, by omega⟩ := by
  unfold adjacentBinaryAlpha halfGapCandidate leftDefectCandidate
  rw [a.lemma814InitialThree_order_eq i.castSucc,
    a.lemma814InitialThree_order_eq i.succ,
    a.lemma814InitialThree_adjacentDefect_eq i]
  congr 3

/-- The first binary alpha of the projected tail is the second ambient
literal binary alpha. -/
theorem tail_firstBinaryAlpha_eq_secondAdjacentBinaryAlpha
    (a : GoodBONG q L (N + 4)) :
    a.tail.firstBinaryAlpha =
      a.adjacentBinaryAlpha (1 : Fin (N + 3)) := by
  unfold firstBinaryAlpha adjacentBinaryAlpha
  simp only [a.halfGapCandidate_tail, a.leftDefectCandidate_tail]
  rfl

/-- The literal first-binary alpha is unchanged on the initial segment. -/
theorem lemma814InitialThree_firstBinaryAlpha_eq
    (a : GoodBONG q L (N + 4)) :
    a.lemma814InitialThree.firstBinaryAlpha = a.firstBinaryAlpha := by
  unfold firstBinaryAlpha halfGapCandidate leftDefectCandidate
  rw [a.lemma814InitialThree_order_eq (0 : Fin 2).castSucc,
    a.lemma814InitialThree_order_eq (0 : Fin 2).succ,
    a.lemma814InitialThree_adjacentDefect_eq (0 : Fin 2)]
  rfl

/-- Localization of the ambient first alpha to the first three entries. -/
def lemma814InitialThreeFirstLocalization : AlphaLocalizationIndex (N + 3) where
  start := 0
  pivot := 0
  stop := 2
  start_le_pivot := by omega
  pivot_lt_stop := by omega
  stop_lt := by omega

/-- Reduction (I) identifies the first alpha of the initial ternary segment
with the ambient first alpha. -/
theorem lemma814InitialThree_firstAlpha_eq
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    (a : GoodBONG q L (N + 4))
    (hbinary : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin (N + 3)) : WithTop ℚ)) :
    a.lemma814InitialThree.alphaValue (0 : Fin 2) =
      a.alphaValue (0 : Fin (N + 3)) := by
  let p := lemma814InitialThreeFirstLocalization (N := N)
  let w := a.toBONG.segmentWitness p.start p.length p.bound
  let s := w.toGoodBONG a.good
  have hw : w = a.lemma814InitialThreeSegment := by
    rfl
  have hs : s = a.lemma814InitialThree := by
    rfl
  have hpivot : p.pivotFin = (0 : Fin (N + 3)) := by
    apply Fin.ext
    rfl
  have hlocalPivot : p.localPivot = (0 : Fin 2) := by
    apply Fin.ext
    rfl
  have hglobalLeLocalRaw :=
    a.beli2009Lemma21_le_segmentAlpha p w
  have hglobalLeLocal :
      (a.alphaValue (0 : Fin (N + 3)) : WithTop ℚ) ≤
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
    exact a.lemma814InitialThree_firstBinaryAlpha_eq
  rw [hlocalBinary, hbinary] at hlocalLeBinary
  have heq : s.alphaValue (0 : Fin 2) =
      a.alphaValue (0 : Fin (N + 3)) := by
    exact_mod_cast le_antisymm hlocalLeBinary hglobalLeLocal
  rw [hs] at heq
  exact heq

/-- Reduction (II) identifies the second alpha of the initial ternary
segment with the ambient second alpha. -/
theorem lemma814InitialThree_secondAlpha_eq_of_tailFirstBinaryAlpha
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    (a : GoodBONG q L (N + 4))
    (htail : a.tail.firstBinaryAlpha =
      (a.tail.alphaValue (0 : Fin (N + 2)) : WithTop ℚ)) :
    a.lemma814InitialThree.alphaValue (1 : Fin 2) =
      a.alphaValue (1 : Fin (N + 3)) := by
  let i : Fin (N + 3) := ⟨1, by omega⟩
  let p := prefixPairLocalization (N := N + 2) i
  let s := suffixPairLocalization (N := N + 2) i
  let wp : BONG.SegmentWitness a.toBONG p.start p.length p.bound :=
    a.lemma814InitialThreeSegment
  let ws := a.toBONG.segmentWitness s.start s.length s.bound
  let front := wp.toGoodBONG a.good
  let suffix := ws.toGoodBONG a.good
  have hsuffix : ScalarAgreement suffix a.tail := by
    refine ⟨?_⟩
    intro j
    change ws.bong.valueUnit j = a.tail.valueUnit j
    calc
      ws.bong.valueUnit j = a.valueUnit (ws.sourceIndex j) :=
        ws.valueUnit_eq j
      _ = a.valueUnit j.succ := by
        congr 1
        apply Fin.ext
        simp only [BONG.SegmentWitness.sourceIndex_val]
        change 1 + j.1 = j.1 + 1
        omega
      _ = a.tail.valueUnit j := (a.valueUnit_goodTail j).symm
  have hpivot : p.localPivot = (1 : Fin 2) := by
    apply Fin.ext
    rfl
  have hspivot : s.localPivot = (0 : Fin (N + 2)) := by
    apply Fin.ext
    rfl
  have hformula := a.alpha_eq_min_prefixSuffixSegmentAlpha i wp ws
  have hsuffixAlpha : suffix.alphaValue s.localPivot =
      a.tail.alphaValue (0 : Fin (N + 2)) := by
    rw [hspivot]
    exact hsuffix.alphaValue_eq (0 : Fin (N + 2))
  have hfrontLeBinary :
      (front.alphaValue p.localPivot : WithTop ℚ) ≤
        front.adjacentBinaryAlpha p.localPivot := by
    unfold adjacentBinaryAlpha
    apply le_min
    · rw [front.coe_alphaValue]
      exact front.alpha_le_halfGapCandidate p.localPivot
    · rw [front.coe_alphaValue]
      exact front.alpha_le_leftDefectCandidate le_rfl
  have hfrontBinary : front.adjacentBinaryAlpha p.localPivot =
      a.tail.firstBinaryAlpha := by
    have hcanonical :
        a.lemma814InitialThree.adjacentBinaryAlpha (1 : Fin 2) =
          a.tail.firstBinaryAlpha := by
      have hindex :
          (⟨(1 : Fin 2).1, by omega⟩ : Fin (N + 3)) =
            (1 : Fin (N + 3)) := by
        apply Fin.ext
        rfl
      rw [a.lemma814InitialThree_adjacentBinaryAlpha_eq (1 : Fin 2),
        hindex, a.tail_firstBinaryAlpha_eq_secondAdjacentBinaryAlpha]
    change (a.lemma814InitialThreeSegment.toGoodBONG a.good).adjacentBinaryAlpha
        p.localPivot = a.tail.firstBinaryAlpha
    calc
      (a.lemma814InitialThreeSegment.toGoodBONG a.good).adjacentBinaryAlpha
          p.localPivot =
          a.lemma814InitialThree.adjacentBinaryAlpha (1 : Fin 2) := by
        congr 1
      _ = a.tail.firstBinaryAlpha := hcanonical
  have hfrontLeSuffix :
      (front.alphaValue p.localPivot : WithTop ℚ) ≤
        (suffix.alphaValue s.localPivot : WithTop ℚ) := by
    calc
      (front.alphaValue p.localPivot : WithTop ℚ) ≤
          (a.tail.alphaValue (0 : Fin (N + 2)) : WithTop ℚ) := by
        rw [hfrontBinary, htail] at hfrontLeBinary
        exact hfrontLeBinary
      _ = (suffix.alphaValue s.localPivot : WithTop ℚ) :=
        congrArg (fun x : ℚ ↦ (x : WithTop ℚ)) hsuffixAlpha.symm
  rw [min_eq_left hfrontLeSuffix] at hformula
  have hresult : front.alphaValue p.localPivot =
      a.alphaValue i := by
    exact_mod_cast hformula.symm
  have hfrontAlpha : front.alphaValue p.localPivot =
      a.lemma814InitialThree.alphaValue (1 : Fin 2) := by
    change (a.lemma814InitialThreeSegment.toGoodBONG a.good).alphaValue
        p.localPivot =
      a.lemma814InitialThree.alphaValue (1 : Fin 2)
    congr 1
  calc
    a.lemma814InitialThree.alphaValue (1 : Fin 2) =
        front.alphaValue p.localPivot := hfrontAlpha.symm
    _ = a.alphaValue i := hresult
    _ = a.alphaValue (1 : Fin (N + 3)) := by
      congr 1

/-- Data retained after reduction (II): the projected tail is in its first
binary normal form, while reduction (I), the Lemma 8.13 conditions, and the
exceptional-case exclusion have all been transported. -/
structure Beli2019Lemma814SecondNormalForm
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M 1) where
  transformed : GoodBONG q L (N + 4)
  firstOrder_eq : transformed.order (0 : Fin (N + 4)) =
    b.order (0 : Fin 1)
  firstBinaryAlpha_eq : transformed.firstBinaryAlpha =
    (transformed.alphaValue (0 : Fin (N + 3)) : WithTop ℚ)
  tailFirstBinaryAlpha_eq : transformed.tail.firstBinaryAlpha =
    (transformed.tail.alphaValue (0 : Fin (N + 2)) : WithTop ℚ)
  initialThreeFirstAlpha_eq :
    transformed.lemma814InitialThree.alphaValue (0 : Fin 2) =
      transformed.alphaValue (0 : Fin (N + 3))
  initialThreeSecondAlpha_eq :
    transformed.lemma814InitialThree.alphaValue (1 : Fin 2) =
      transformed.alphaValue (1 : Fin (N + 3))
  conditions : transformed.Lemma813Conditions b
  notExceptional : ¬transformed.Beli2019Lemma814Exceptional b

/-- Reduction (II) is implemented by Corollary 8.10 on the projected tail
and the good-tail replacement construction. -/
theorem exists_lemma814SecondNormalForm
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
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M 1)
    (horder : a.order (0 : Fin (N + 4)) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hbinary : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin (N + 3)) : WithTop ℚ))
    (hnotExceptional : ¬a.Beli2019Lemma814Exceptional b) :
    Nonempty (a.Beli2019Lemma814SecondNormalForm b) := by
  letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
  rcases a.tail.beli2019Corollary810 with ⟨C⟩
  let changed := a.replaceTailGood C.transformed
  have horders := a.order_invariant changed
  have halphas := a.alpha_invariant changed
  have hfirstValue : changed.valueUnit (0 : Fin (N + 4)) =
      a.valueUnit (0 : Fin (N + 4)) := by
    apply Units.ext
    change (a.replaceTailGood C.transformed).toBONG.value 0 =
      a.toBONG.value 0
    rw [(a.replaceTailGood C.transformed).toBONG.value_zero_eq_quadratic_head,
      a.toBONG.value_zero_eq_quadratic_head,
      a.replaceTailGood_head C.transformed]
  have hsecondValue : changed.valueUnit (1 : Fin (N + 4)) =
      a.valueUnit (1 : Fin (N + 4)) := by
    calc
      changed.valueUnit (1 : Fin (N + 4)) =
          changed.tail.valueUnit (0 : Fin (N + 3)) := by
        symm
        simpa using changed.valueUnit_goodTail (0 : Fin (N + 3))
      _ = C.transformed.valueUnit (0 : Fin (N + 3)) := by rfl
      _ = a.tail.valueUnit (0 : Fin (N + 3)) := C.headValue_eq
      _ = a.valueUnit (1 : Fin (N + 4)) := by
        simpa using a.valueUnit_goodTail (0 : Fin (N + 3))
  have hadjacent : changed.adjacentDefect (0 : Fin (N + 3)) =
      a.adjacentDefect (0 : Fin (N + 3)) := by
    unfold adjacentDefect adjacentProduct
    rw [show changed.valueUnit (0 : Fin (N + 3)).castSucc =
        a.valueUnit (0 : Fin (N + 3)).castSucc by simpa using hfirstValue,
      show changed.valueUnit (0 : Fin (N + 3)).succ =
        a.valueUnit (0 : Fin (N + 3)).succ by simpa using hsecondValue]
  have hfirstBinarySame : changed.firstBinaryAlpha = a.firstBinaryAlpha := by
    unfold firstBinaryAlpha halfGapCandidate leftDefectCandidate
    rw [← horders (0 : Fin (N + 3)).castSucc,
      ← horders (0 : Fin (N + 3)).succ, hadjacent]
  have hbinaryChanged : changed.firstBinaryAlpha =
      (changed.alphaValue (0 : Fin (N + 3)) : WithTop ℚ) := by
    calc
      changed.firstBinaryAlpha = a.firstBinaryAlpha := hfirstBinarySame
      _ = (a.alphaValue (0 : Fin (N + 3)) : WithTop ℚ) := hbinary
      _ = (changed.alphaValue (0 : Fin (N + 3)) : WithTop ℚ) :=
        congrArg (fun x : ℚ ↦ (x : WithTop ℚ))
          (halphas (0 : Fin (N + 3)))
  have htailChanged : changed.tail.firstBinaryAlpha =
      (changed.tail.alphaValue (0 : Fin (N + 2)) : WithTop ℚ) := by
    change C.transformed.firstBinaryAlpha =
      (C.transformed.alphaValue (0 : Fin (N + 2)) : WithTop ℚ)
    exact C.firstBinaryAlpha_eq
  have hconditions := a.lemma813Conditions_changeTargetBONG
    (classificationV := classificationV)
    (classificationW := classificationW) changed b horder conditions
  have hinvariant := a.lemma814Exceptional_changeBONG_iff_full
    (classificationV := classificationV)
    (classificationW := classificationW)
    (prefixChangeV := prefixChangeV)
    (prefixChangeW := prefixChangeW) changed b
  exact ⟨{
    transformed := changed
    firstOrder_eq := by
      rw [← horders (0 : Fin (N + 4))]
      exact horder
    firstBinaryAlpha_eq := hbinaryChanged
    tailFirstBinaryAlpha_eq := htailChanged
    initialThreeFirstAlpha_eq :=
      changed.lemma814InitialThree_firstAlpha_eq hbinaryChanged
    initialThreeSecondAlpha_eq :=
      changed.lemma814InitialThree_secondAlpha_eq_of_tailFirstBinaryAlpha
        htailChanged
    conditions := hconditions
    notExceptional := fun E ↦ hnotExceptional (hinvariant.mpr E)
  }⟩

/-- The unary-boundary capped defect is unchanged on the initial segment
once its first alpha has been identified. -/
theorem lemma814InitialThree_firstDefect_eq
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M 1)
    (halpha : a.lemma814InitialThree.alphaValue (0 : Fin 2) =
      a.alphaValue (0 : Fin (N + 3))) :
    a.lemma814InitialThree.truncatedPrefixDefect b 1 1 1 =
      a.truncatedPrefixDefect b 1 1 1 := by
  let s := a.lemma814InitialThree
  unfold truncatedPrefixDefect
  rw [a.lemma814InitialThree_prefixProduct_eq 1 (by omega),
    s.prefixAlphaCap_of_internal (by omega) (by omega),
    a.prefixAlphaCap_of_internal (by omega) (by omega),
    b.prefixAlphaCap_last]
  have hlocal : (⟨1 - 1, by omega⟩ : Fin 2) = (0 : Fin 2) := by
    apply Fin.ext
    rfl
  have hambient : (⟨1 - 1, by omega⟩ : Fin (N + 3)) =
      (0 : Fin (N + 3)) := by
    apply Fin.ext
    rfl
  rw [hlocal, hambient, halpha]

/-- On the rank-three initial segment the first-third bracket is uncapped. -/
theorem lemma814InitialThree_firstThirdDefect_eq_raw
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M 1) :
    a.lemma814InitialThree.truncatedPrefixDefect b (-1) 3 1 =
      defectOrder (K := K) ((-1) * a.prefixProduct 3 * b.prefixProduct 1) := by
  unfold truncatedPrefixDefect
  rw [a.lemma814InitialThree_prefixProduct_eq 3 (by omega),
    a.lemma814InitialThree.prefixAlphaCap_last, b.prefixAlphaCap_last]
  simp

/-- In a ternary BONG, equality of the first two left endpoints together
with a strict outer-order increase forces the second alpha to be realized by
the second adjacent-defect candidate. -/
theorem ternary_secondLeftDefectCandidate_eq_alpha_of_firstEndpoint_eq_of_outer_lt
    [Beli2006AlphaLaws.{u, v} K]
    (s : GoodBONG q L 3)
    (hendpoint :
      (s.order (0 : Fin 3) : ℚ) + s.alphaValue (0 : Fin 2) =
        (s.order (1 : Fin 3) : ℚ) + s.alphaValue (1 : Fin 2))
    (houter : s.order (0 : Fin 3) < s.order (2 : Fin 3)) :
    s.leftDefectCandidate (1 : Fin 2) (1 : Fin 2) =
      (s.alphaValue (1 : Fin 2) : WithTop ℚ) := by
  have hhalfQ : s.alphaValue (1 : Fin 2) <
      s.halfGapValue (1 : Fin 2) := by
    have hfirstHalf := s.alphaValue_le_halfGapValue (0 : Fin 2)
    unfold halfGapValue orderGap at hfirstHalf ⊢
    push_cast at hfirstHalf ⊢
    have houterQ : (s.order (0 : Fin 3) : ℚ) <
        (s.order (2 : Fin 3) : ℚ) := by
      exact_mod_cast houter
    linarith
  have hhalf : (s.alphaValue (1 : Fin 2) : WithTop ℚ) <
      s.halfGapCandidate (1 : Fin 2) := by
    rw [← s.coe_halfGapValue]
    exact_mod_cast hhalfQ
  have hleftZero : (s.alphaValue (1 : Fin 2) : WithTop ℚ) <
      s.leftDefectCandidate (1 : Fin 2) (0 : Fin 2) := by
    have hcandidate := s.alpha_le_leftDefectCandidate
      (i := (0 : Fin 2)) (j := (0 : Fin 2)) le_rfl
    rw [← s.coe_alphaValue] at hcandidate
    by_cases htop : s.adjacentDefect (0 : Fin 2) = ⊤
    · unfold leftDefectCandidate
      rw [htop]
      simp
      exact WithTop.lt_top_iff_ne_top.mpr (s.alpha_ne_top (1 : Fin 2))
    · obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp htop
      unfold leftDefectCandidate at hcandidate ⊢
      rw [← hd] at hcandidate ⊢
      norm_cast at hcandidate ⊢
      push_cast at hcandidate ⊢
      have houterQ : (s.order (0 : Fin 3) : ℚ) <
          (s.order (2 : Fin 3) : ℚ) := by
        exact_mod_cast houter
      linarith
  have hmem : (s.alphaValue (1 : Fin 2) : WithTop ℚ) ∈
      s.alphaCandidates (1 : Fin 2) := by
    rw [s.coe_alphaValue]
    exact Finset.min'_mem _ _
  simp only [alphaCandidates, Finset.mem_insert, Finset.mem_union] at hmem
  rcases hmem with hhalfEq | hleft | hright
  · exact (ne_of_lt hhalf hhalfEq).elim
  · rcases Finset.mem_image.mp hleft with ⟨j, hj, hcandidateEq⟩
    fin_cases j
    · exact (ne_of_lt hleftZero hcandidateEq.symm).elim
    · exact hcandidateEq
  · rcases Finset.mem_image.mp hright with ⟨j, hj, hcandidateEq⟩
    fin_cases j
    · simp at hj
    · exact hcandidateEq

/-- Under the same endpoint equality, the second adjacent defect is strictly
smaller than the first alpha.  This is the numerical content of the
candidate identity used in the paper's contradiction. -/
theorem ternary_secondAdjacentDefect_lt_firstAlpha_of_firstEndpoint_eq_of_outer_lt
    [Beli2006AlphaLaws.{u, v} K]
    (s : GoodBONG q L 3)
    (hendpoint :
      (s.order (0 : Fin 3) : ℚ) + s.alphaValue (0 : Fin 2) =
        (s.order (1 : Fin 3) : ℚ) + s.alphaValue (1 : Fin 2))
    (houter : s.order (0 : Fin 3) < s.order (2 : Fin 3)) :
    s.adjacentDefect (1 : Fin 2) <
      (s.alphaValue (0 : Fin 2) : WithTop ℚ) := by
  have hcandidate :=
    s.ternary_secondLeftDefectCandidate_eq_alpha_of_firstEndpoint_eq_of_outer_lt
      hendpoint houter
  unfold leftDefectCandidate at hcandidate
  by_cases htop : s.adjacentDefect (1 : Fin 2) = ⊤
  · rw [htop] at hcandidate
    simp at hcandidate
    exact (s.alpha_ne_top (1 : Fin 2) hcandidate.symm).elim
  · obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp htop
    rw [← hd] at hcandidate ⊢
    norm_cast at hcandidate ⊢
    push_cast at hcandidate ⊢
    have houterQ : (s.order (0 : Fin 3) : ℚ) <
        (s.order (2 : Fin 3) : ℚ) := by
      exact_mod_cast houter
    linarith

/-- The uncapped first-three defect factors as the prescribed multiplier
times the second adjacent product.  This is the ambient-rank form of the
ternary square-factor calculation: the discarded factor is `a₁²`. -/
theorem lemma814FirstThreeRawDefect_eq_epsilon_mul_secondAdjacent
    [QuadraticDefectLaws K]
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M 1) :
    defectOrder (K := K) ((-1) * a.prefixProduct 3 * b.prefixProduct 1) =
      defectOrder (K := K)
        (a.lemma814Epsilon b * a.adjacentProduct (1 : Fin (N + 3))) := by
  let s := a.lemma814InitialThree
  have hepsilon : s.lemma814Epsilon b = a.lemma814Epsilon b := by
    unfold lemma814Epsilon
    rw [a.lemma814InitialThree_valueUnit_eq (0 : Fin 3)]
    congr 3
  have hadjacent : s.adjacentProduct (1 : Fin 2) =
      a.adjacentProduct (1 : Fin (N + 3)) := by
    unfold adjacentProduct
    rw [a.lemma814InitialThree_valueUnit_eq (1 : Fin 2).castSucc,
      a.lemma814InitialThree_valueUnit_eq (1 : Fin 2).succ]
    congr 3
  calc
    defectOrder (K := K) ((-1) * a.prefixProduct 3 * b.prefixProduct 1) =
        s.truncatedPrefixDefect b (-1) 3 1 :=
      (a.lemma814InitialThree_firstThirdDefect_eq_raw b).symm
    _ = defectOrder (K := K)
        (s.lemma814Epsilon b * s.adjacentProduct (1 : Fin 2)) :=
      s.lemma814TernaryFullDefect_eq_epsilon_mul_secondAdjacent b
    _ = defectOrder (K := K)
        (a.lemma814Epsilon b * a.adjacentProduct (1 : Fin (N + 3))) := by
      rw [hepsilon, hadjacent]

/-- If the uncapped first-three defect is strictly larger than the third
alpha, the first two left endpoints cannot be equal.  This is the precise
contradiction used after reductions (I) and (II) in the unequal-outer branch.
-/
theorem lemma814_firstEndpoint_strict_of_thirdAlpha_lt_rawDefect
    [QuadraticDefectLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M 1)
    (conditions : a.Lemma813Conditions b)
    (hfirst : a.lemma814InitialThree.alphaValue (0 : Fin 2) =
      a.alphaValue (0 : Fin (N + 3)))
    (hsecond : a.lemma814InitialThree.alphaValue (1 : Fin 2) =
      a.alphaValue (1 : Fin (N + 3)))
    (houter : a.order (0 : Fin (N + 4)) < a.order (2 : Fin (N + 4)))
    (hraw : (a.alphaValue (2 : Fin (N + 3)) : WithTop ℚ) <
      defectOrder (K := K) ((-1) * a.prefixProduct 3 * b.prefixProduct 1)) :
    (a.order (0 : Fin (N + 4)) : ℚ) +
        a.alphaValue (0 : Fin (N + 3)) <
      (a.order (1 : Fin (N + 4)) : ℚ) +
        a.alphaValue (1 : Fin (N + 3)) := by
  have hle := (a.alpha_p1 (0 : Fin (N + 3)) (by norm_num)).1
  unfold alphaLeftEndpoint at hle
  change (a.order (0 : Fin (N + 4)) : ℚ) +
      a.alphaValue (0 : Fin (N + 3)) ≤
    (a.order (1 : Fin (N + 4)) : ℚ) +
      a.alphaValue (1 : Fin (N + 3)) at hle
  apply lt_of_le_of_ne hle
  intro hendpoint
  let s := a.lemma814InitialThree
  have hlocalEndpoint :
      (s.order (0 : Fin 3) : ℚ) + s.alphaValue (0 : Fin 2) =
        (s.order (1 : Fin 3) : ℚ) + s.alphaValue (1 : Fin 2) := by
    dsimp only [s]
    rw [a.lemma814InitialThree_order_eq,
      a.lemma814InitialThree_order_eq, hfirst, hsecond]
    simpa using hendpoint
  have hlocalOuter : s.order (0 : Fin 3) < s.order (2 : Fin 3) := by
    dsimp only [s]
    rw [a.lemma814InitialThree_order_eq,
      a.lemma814InitialThree_order_eq]
    have htwo : (⟨(2 : Fin 3).1, by omega⟩ : Fin (N + 4)) =
        (2 : Fin (N + 4)) := by
      apply Fin.ext
      rfl
    rw [htwo]
    exact houter
  have hlocalAdjacentLt :=
    s.ternary_secondAdjacentDefect_lt_firstAlpha_of_firstEndpoint_eq_of_outer_lt
      hlocalEndpoint hlocalOuter
  have hadjacentEq : s.adjacentDefect (1 : Fin 2) =
      a.adjacentDefect (1 : Fin (N + 3)) := by
    dsimp only [s]
    simpa using a.lemma814InitialThree_adjacentDefect_eq (1 : Fin 2)
  have hadjacentLtAlpha : a.adjacentDefect (1 : Fin (N + 3)) <
      (a.alphaValue (0 : Fin (N + 3)) : WithTop ℚ) := by
    rw [← hadjacentEq, ← hfirst]
    exact hlocalAdjacentLt
  have hadjacentLtEpsilon :
      defectOrder (K := K) (a.adjacentProduct (1 : Fin (N + 3))) <
        defectOrder (K := K) (a.lemma814Epsilon b) := by
    change a.adjacentDefect (1 : Fin (N + 3)) < _
    exact hadjacentLtAlpha.trans_le
      (a.alpha_le_lemma814EpsilonDefect b conditions)
  have hrawEqAdjacent :
      defectOrder (K := K) ((-1) * a.prefixProduct 3 * b.prefixProduct 1) =
        a.adjacentDefect (1 : Fin (N + 3)) := by
    rw [a.lemma814FirstThreeRawDefect_eq_epsilon_mul_secondAdjacent b,
      defectOrder_mul_eq_right_of_lt_left (K := K) hadjacentLtEpsilon]
    rfl
  have hadjacentNotTop : a.adjacentDefect (1 : Fin (N + 3)) ≠ ⊤ :=
    ne_top_of_lt hadjacentLtAlpha
  obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp hadjacentNotTop
  have hcandidate :=
    s.ternary_secondLeftDefectCandidate_eq_alpha_of_firstEndpoint_eq_of_outer_lt
      hlocalEndpoint hlocalOuter
  unfold leftDefectCandidate at hcandidate
  have hdLocal : (d : WithTop ℚ) = s.adjacentDefect (1 : Fin 2) :=
    hd.trans hadjacentEq.symm
  rw [← hdLocal] at hcandidate
  norm_cast at hcandidate
  push_cast at hcandidate
  have hcandidateAmbient :
      ((a.order (2 : Fin (N + 4)) - a.order (1 : Fin (N + 4)) : Int) : ℚ) + d =
        a.alphaValue (1 : Fin (N + 3)) := by
    dsimp only [s] at hcandidate
    rw [a.lemma814InitialThree_order_eq,
      a.lemma814InitialThree_order_eq, hsecond] at hcandidate
    have htwo : (⟨(2 : Fin 3).1, by omega⟩ : Fin (N + 4)) =
        (2 : Fin (N + 4)) := by
      apply Fin.ext
      rfl
    rw [htwo] at hcandidate
    simpa using hcandidate
  have hp1 := (a.alpha_p1 (1 : Fin (N + 3)) (by norm_num)).1
  unfold alphaLeftEndpoint at hp1
  change (a.order (1 : Fin (N + 4)) : ℚ) +
      a.alphaValue (1 : Fin (N + 3)) ≤
    (a.order (2 : Fin (N + 4)) : ℚ) +
      a.alphaValue (2 : Fin (N + 3)) at hp1
  have hdLe : d ≤ a.alphaValue (2 : Fin (N + 3)) := by
    push_cast at hcandidateAmbient
    linarith
  have hadjacentLe : a.adjacentDefect (1 : Fin (N + 3)) ≤
      (a.alphaValue (2 : Fin (N + 3)) : WithTop ℚ) := by
    rw [← hd]
    exact_mod_cast hdLe
  rw [hrawEqAdjacent] at hraw
  exact (not_lt_of_ge hadjacentLe hraw).elim

/-- A strict increase of the first two left endpoints recovers reduction
(I) for any good BONG of the same lattice.  The induction formula for the
first alpha makes the tail term strictly larger, so the binary term must be
the minimum. -/
theorem firstBinaryAlpha_eq_alpha_of_firstEndpoint_strict
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    (a : GoodBONG q L (N + 4))
    (hendpoint :
      (a.order (0 : Fin (N + 4)) : ℚ) +
          a.alphaValue (0 : Fin (N + 3)) <
        (a.order (1 : Fin (N + 4)) : ℚ) +
          a.alphaValue (1 : Fin (N + 3))) :
    a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin (N + 3)) : WithTop ℚ) := by
  have hshiftTop := a.alphaValue_shift_le_tail (0 : Fin (N + 2))
  have hshift : a.alphaValue (1 : Fin (N + 3)) ≤
      a.tail.alphaValue (0 : Fin (N + 2)) := by
    exact_mod_cast hshiftTop
  have hstrictQ : a.alphaValue (0 : Fin (N + 3)) <
      ((a.orderGap (0 : Fin (N + 3)) : Int) : ℚ) +
        a.tail.alphaValue (0 : Fin (N + 2)) := by
    unfold orderGap
    change a.alphaValue (0 : Fin (N + 3)) <
      ((a.order (1 : Fin (N + 4)) - a.order (0 : Fin (N + 4)) : Int) : ℚ) +
        a.tail.alphaValue (0 : Fin (N + 2))
    push_cast
    linarith
  let tailTerm : WithTop ℚ :=
    ((((a.orderGap (0 : Fin (N + 3)) : Int) : ℚ) : WithTop ℚ) +
      (a.tail.alphaValue (0 : Fin (N + 2)) : WithTop ℚ))
  have hstrict : (a.alphaValue (0 : Fin (N + 3)) : WithTop ℚ) <
      tailTerm := by
    dsimp only [tailTerm]
    exact_mod_cast hstrictQ
  have hformula := a.alpha_zero_eq_min_firstBinary_orderGap_add_tailAlpha
  have hbinaryLe : a.firstBinaryAlpha ≤ tailTerm := by
    by_contra hnot
    have htailLeBinary : tailTerm ≤ a.firstBinaryAlpha := le_of_not_ge hnot
    have hformula' : (a.alphaValue (0 : Fin (N + 3)) : WithTop ℚ) =
        tailTerm := by
      simpa only [tailTerm, min_eq_right htailLeBinary] using hformula
    exact (ne_of_lt hstrict) hformula'
  have hformula' : (a.alphaValue (0 : Fin (N + 3)) : WithTop ℚ) =
      a.firstBinaryAlpha := by
    simpa only [tailTerm, min_eq_left hbinaryLe] using hformula
  exact hformula'.symm

/-- In ambient rank at least four, the bracketed first-third defect is the
minimum of its raw value and the third alpha. -/
theorem lemma814FirstThirdCappedDefect_eq_min_raw
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M 1) :
    a.truncatedPrefixDefect b (-1) 3 1 =
      min
        (defectOrder (K := K)
          ((-1) * a.prefixProduct 3 * b.prefixProduct 1))
        (a.alphaValue (2 : Fin (N + 3)) : WithTop ℚ) := by
  unfold truncatedPrefixDefect
  rw [a.prefixAlphaCap_of_internal (by omega) (by omega),
    b.prefixAlphaCap_last]
  have hindex : (⟨3 - 1, by omega⟩ : Fin (N + 3)) =
      (2 : Fin (N + 3)) := by
    apply Fin.ext
    rfl
  rw [hindex]
  simp

/-- The uncapped inequality which makes the initial ternary segment safe. -/
def Lemma814InitialThreeRawBound
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M 1) : Prop :=
  (a.alphaValue (0 : Fin (N + 3)) : WithTop ℚ) +
      ((((a.order (2 : Fin (N + 4)) : Int) : ℚ) : WithTop ℚ) +
        defectOrder (K := K)
          ((-1) * a.prefixProduct 3 * b.prefixProduct 1)) ≤
    ((2 * (ramificationIndex K : ℚ) +
      (a.order (1 : Fin (N + 4)) : ℚ) : ℚ) : WithTop ℚ)

/-- If the raw defect is no larger than the third alpha, the capped
unequal-outer inequality is already the raw inequality. -/
theorem lemma814InitialThreeRawBound_of_raw_le_thirdAlpha
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M 1)
    (hbound : a.Lemma814UnequalOuterBound b)
    (hraw : defectOrder (K := K)
        ((-1) * a.prefixProduct 3 * b.prefixProduct 1) ≤
      (a.alphaValue (2 : Fin (N + 3)) : WithTop ℚ)) :
    a.Lemma814InitialThreeRawBound b := by
  unfold Lemma814InitialThreeRawBound
  have hcapped : a.truncatedPrefixDefect b (-1) 3 1 =
      defectOrder (K := K)
        ((-1) * a.prefixProduct 3 * b.prefixProduct 1) := by
    rw [a.lemma814FirstThirdCappedDefect_eq_min_raw b,
      min_eq_left hraw]
  rw [← hcapped]
  exact hbound.2

/-- The ambient uncapped bound is exactly the unequal-outer bound for the
initial rank-three segment. -/
theorem lemma814InitialThree_unequalOuterBound
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M 1)
    (halpha : a.lemma814InitialThree.alphaValue (0 : Fin 2) =
      a.alphaValue (0 : Fin (N + 3)))
    (houter : a.order (0 : Fin (N + 4)) < a.order (2 : Fin (N + 4)))
    (hraw : a.Lemma814InitialThreeRawBound b) :
    a.lemma814InitialThree.Lemma814UnequalOuterBound b := by
  constructor
  · rw [a.lemma814InitialThree_order_eq,
      a.lemma814InitialThree_order_eq]
    have hzero : (⟨(0 : Fin 3).1, by omega⟩ : Fin (N + 4)) =
        (0 : Fin (N + 4)) := by
      apply Fin.ext
      rfl
    have htwo : (⟨(2 : Fin 3).1, by omega⟩ : Fin (N + 4)) =
        (2 : Fin (N + 4)) := by
      apply Fin.ext
      rfl
    rw [hzero, htwo]
    exact houter
  · unfold Lemma814InitialThreeRawBound at hraw
    rw [halpha, a.lemma814InitialThree_order_eq,
      a.lemma814InitialThree_order_eq,
      a.lemma814InitialThree_firstThirdDefect_eq_raw]
    exact hraw

/-- Under unequal outer orders, the local Lemma 8.13 conditions are
automatic except for condition (a), which descends from the ambient target. -/
theorem lemma814InitialThree_conditions_of_unequalOuterBound
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M 1)
    (halpha : a.lemma814InitialThree.alphaValue (0 : Fin 2) =
      a.alphaValue (0 : Fin (N + 3)))
    (conditions : a.Lemma813Conditions b)
    (hbound : a.lemma814InitialThree.Lemma814UnequalOuterBound b) :
    a.lemma814InitialThree.Lemma813Conditions b := by
  let s := a.lemma814InitialThree
  refine {
    defectEquality := ?_
    binaryRankTwo := ?_
    binaryHigher := ?_
    ternaryRankThree := ?_
    ternaryHigher := ?_
  }
  · calc
      s.truncatedPrefixDefect b 1 1 1 =
          a.truncatedPrefixDefect b 1 1 1 :=
        a.lemma814InitialThree_firstDefect_eq b halpha
      _ = (a.alphaValue (0 : Fin (N + 3)) : WithTop ℚ) :=
        conditions.defectEquality
      _ = (s.alphaValue (0 : Fin 2) : WithTop ℚ) := by
        exact congrArg (fun x : ℚ ↦ (x : WithTop ℚ)) halpha.symm
  · intro hm
    omega
  · intro _hm htrigger
    exact (not_lt_of_ge hbound.2 htrigger.2).elim
  · intro _hm hequal
    exact (ne_of_lt hbound.1 hequal).elim
  · intro hm
    omega

/-- Unequal first and third orders exclude all three local exceptions. -/
theorem lemma814InitialThree_notExceptional_of_unequalOuterBound
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M 1)
    (hbound : a.lemma814InitialThree.Lemma814UnequalOuterBound b) :
    ¬a.lemma814InitialThree.Beli2019Lemma814Exceptional b := by
  intro E
  rcases E with A | B | C
  · exact (ne_of_lt hbound.1 A.firstThirdOrders_eq).elim
  · exact (ne_of_lt hbound.1 B.firstThirdOrders_eq).elim
  · exact (ne_of_lt hbound.1 C.firstThirdOrders_eq).elim

/-- Paper's direct higher-rank subcase: if the uncapped first-third defect
already obeys the displayed bound, rank-three Lemma 8.14 applies to the
initial segment and Lemma 4.9(ii) reinserts the result. -/
theorem beli2019Lemma814_higherRankUnequal_of_rawBound
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
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicDiagonalClassificationLaws K]
    (a original : GoodBONG q L (N + 4)) (b : GoodBONG r M 1)
    (horder : a.order (0 : Fin (N + 4)) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hbinary : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin (N + 3)) : WithTop ℚ))
    (houter : a.order (0 : Fin (N + 4)) < a.order (2 : Fin (N + 4)))
    (hraw : a.Lemma814InitialThreeRawBound b) :
    Nonempty (original.Beli2019PrescribedFirstValueTransform b) := by
  have halpha := a.lemma814InitialThree_firstAlpha_eq hbinary
  have hbound := a.lemma814InitialThree_unequalOuterBound
    b halpha houter hraw
  have hconditions := a.lemma814InitialThree_conditions_of_unequalOuterBound
    b halpha conditions hbound
  have hnotExceptional :=
    a.lemma814InitialThree_notExceptional_of_unequalOuterBound b hbound
  exact a.beli2019Lemma814_of_safeFirstThreeSegment_of_ambientOrder
    (classificationV := classificationV)
    (classificationW := classificationW)
    (prefixChangeV := prefixChangeV)
    (prefixChangeW := prefixChangeW)
    original b a.lemma814InitialThreeSegment horder hconditions
      hnotExceptional

/-- Convenient form of the direct subcase using the comparison
`d(-a₁a₂a₃b₁) ≤ α₃`. -/
theorem beli2019Lemma814_higherRankUnequal_of_raw_le_thirdAlpha
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
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicDiagonalClassificationLaws K]
    (a original : GoodBONG q L (N + 4)) (b : GoodBONG r M 1)
    (horder : a.order (0 : Fin (N + 4)) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hbinary : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin (N + 3)) : WithTop ℚ))
    (hbound : a.Lemma814UnequalOuterBound b)
    (hraw : defectOrder (K := K)
        ((-1) * a.prefixProduct 3 * b.prefixProduct 1) ≤
      (a.alphaValue (2 : Fin (N + 3)) : WithTop ℚ)) :
    Nonempty (original.Beli2019PrescribedFirstValueTransform b) := by
  exact a.beli2019Lemma814_higherRankUnequal_of_rawBound
    (classificationV := classificationV)
    (classificationW := classificationW)
    (prefixChangeV := prefixChangeV)
    (prefixChangeW := prefixChangeW)
    original b horder conditions hbinary hbound.1
      (a.lemma814InitialThreeRawBound_of_raw_le_thirdAlpha b hbound hraw)

end BONG.GoodBONG
end Bong
