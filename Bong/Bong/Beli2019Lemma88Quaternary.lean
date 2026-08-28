/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma88Critical

/-!
# Beli (2019), Lemma 8.8: the quaternary exceptional branch

The last branch of the induction applies Lemma 8.3 to the first four BONG
entries and then replaces that good segment inside the full lattice.  This
file proves the segment alpha identity, performs the replacement, and derives
the branch from exception (c) of the projected tail.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {N : Nat}

/-- Lemma 8.3 on the first quaternary segment, lifted to a good BONG of
arbitrary larger rank by Beli (2003), Lemma 4.9. -/
theorem firstValueTransform_of_firstQuaternarySegment
    [QuadraticDefectLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    (b : GoodBONG q L (N + 4))
    (hfirstOrders : b.order (0 : Fin (N + 4)) =
      b.order (2 : Fin (N + 4)))
    (hsecondOrders : b.order (1 : Fin (N + 4)) =
      b.order (3 : Fin (N + 4)))
    (hhalf : b.AttainsHalfGap (0 : Fin (N + 3)))
    (ε : Kˣ) (hunit : IsValuationUnit K (ε : K))
    (hdefect : defectOrder (K := K) ε =
      (b.alphaValue (0 : Fin (N + 3)) : WithTop ℚ)) :
    Nonempty b.Beli2019FirstValueTransform := by
  let loc : AlphaLocalizationIndex (N + 3) := {
    start := 0
    pivot := 0
    stop := 3
    start_le_pivot := by omega
    pivot_lt_stop := by omega
    stop_lt := by omega
  }
  rcases b.toBONG.exists_segmentWitness loc.start loc.length loc.bound with
    ⟨w⟩
  let s := w.toGoodBONG b.good
  have horder (i : Fin 4) :
      s.order i = b.order ⟨i.1, by omega⟩ := by
    change w.bong.order i = b.toBONG.order ⟨i.1, by omega⟩
    simp [BONG.SegmentWitness.sourceIndex, loc]
  have hsAlternating : s.HasQuaternaryAlternatingOrders := by
    constructor
    · calc
        s.order (0 : Fin 4) = b.order (0 : Fin (N + 4)) := horder 0
        _ = b.order (2 : Fin (N + 4)) := hfirstOrders
        _ = s.order (2 : Fin 4) := (horder 2).symm
    · calc
        s.order (1 : Fin 4) = b.order (1 : Fin (N + 4)) := horder 1
        _ = b.order (3 : Fin (N + 4)) := hsecondOrders
        _ = s.order (3 : Fin 4) := (horder 3).symm
  have hglobalLeSegment := b.beli2009Lemma21_le_segmentAlpha loc w
  have hpivot : loc.pivotFin = (0 : Fin (N + 3)) := by
    apply Fin.ext
    rfl
  have hlocal : loc.localPivot = (0 : Fin 3) := by
    apply Fin.ext
    rfl
  rw [hpivot, hlocal] at hglobalLeSegment
  have hglobalLeSegmentTop :
      (b.alphaValue (0 : Fin (N + 3)) : WithTop ℚ) ≤
        (s.alphaValue (0 : Fin 3) : WithTop ℚ) := by
    rw [b.coe_alphaValue, s.coe_alphaValue]
    exact hglobalLeSegment
  have hhalfCandidate : s.halfGapCandidate (0 : Fin 3) =
      b.halfGapCandidate (0 : Fin (N + 3)) := by
    have horderZero : s.order (0 : Fin 4) =
        b.order (0 : Fin (N + 4)) := by
      simpa using horder (0 : Fin 4)
    have horderOne : s.order (1 : Fin 4) =
        b.order (1 : Fin (N + 4)) := by
      simpa using horder (1 : Fin 4)
    unfold halfGapCandidate
    have hsCast : (0 : Fin 3).castSucc = (0 : Fin 4) := by
      apply Fin.ext
      rfl
    have hsSucc : (0 : Fin 3).succ = (1 : Fin 4) := by
      apply Fin.ext
      rfl
    have hbCast : (0 : Fin (N + 3)).castSucc =
        (0 : Fin (N + 4)) := by
      apply Fin.ext
      rfl
    have hbSucc : (0 : Fin (N + 3)).succ =
        (1 : Fin (N + 4)) := by
      apply Fin.ext
      rfl
    rw [hsCast, hsSucc, hbCast, hbSucc, horderZero, horderOne]
  have hsegmentLeGlobal :
      (s.alphaValue (0 : Fin 3) : WithTop ℚ) ≤
        (b.alphaValue (0 : Fin (N + 3)) : WithTop ℚ) := by
    calc
      (s.alphaValue (0 : Fin 3) : WithTop ℚ) =
          s.alpha (0 : Fin 3) := s.coe_alphaValue 0
      _ ≤ s.halfGapCandidate (0 : Fin 3) :=
        s.alpha_le_halfGapCandidate 0
      _ = b.halfGapCandidate (0 : Fin (N + 3)) := hhalfCandidate
      _ = (b.halfGapValue (0 : Fin (N + 3)) : WithTop ℚ) :=
        (b.coe_halfGapValue 0).symm
      _ = (b.alphaValue (0 : Fin (N + 3)) : WithTop ℚ) :=
        congrArg (fun x : ℚ => (x : WithTop ℚ)) hhalf.symm
  have hsAlpha : s.alphaValue (0 : Fin 3) =
      b.alphaValue (0 : Fin (N + 3)) := by
    apply WithTop.coe_injective
    exact le_antisymm hsegmentLeGlobal hglobalLeSegmentTop
  have hsDefect : defectOrder (K := K) ε =
      (s.alphaValue (0 : Fin 3) : WithTop ℚ) :=
    hdefect.trans (congrArg (fun x : ℚ => (x : WithTop ℚ)) hsAlpha.symm)
  have hsBound : (s.alphaValue (0 : Fin 3) : WithTop ℚ) ≤
      defectOrder (K := K) ε := by rw [hsDefect]
  rcases s.beli2019Lemma83 hsAlternating ε hunit hsBound with ⟨c, hc⟩
  rcases b.toBONG.beliLemma49_ii b.good w c.toBONG c.good with ⟨R⟩
  let transformed : GoodBONG q L (N + 4) := ⟨R.bong, R.good⟩
  have hinside := R.inside_eq (0 : Fin 4)
  have hvalue : transformed.valueUnit (0 : Fin (N + 4)) =
      c.valueUnit (0 : Fin 4) := by
    apply Units.ext
    change R.bong.value 0 = c.toBONG.value 0
    rw [← R.bong.quadratic_ambientVector,
      ← c.toBONG.quadratic_ambientVector]
    change q.quadratic (R.bong.ambientVector 0) =
      q.quadratic (c.toBONG.ambientVector 0 : V)
    have hinside0 : R.bong.ambientVector (0 : Fin (N + 4)) =
        (c.toBONG.ambientVector (0 : Fin 4) : V) := by
      convert hinside using 1
      congr 1
    rw [hinside0]
  have hsValue : s.valueUnit (0 : Fin 4) =
      b.valueUnit (0 : Fin (N + 4)) := by
    change w.bong.valueUnit 0 = b.toBONG.valueUnit 0
    simp [BONG.SegmentWitness.sourceIndex, loc, w.valueUnit_eq]
  refine ⟨{
    epsilon := ε
    epsilon_isValuationUnit := hunit
    epsilon_defect := hdefect
    transformed := transformed
    firstValue_eq := ?_
  }⟩
  calc
    transformed.valueUnit (0 : Fin (N + 4)) =
        c.valueUnit (0 : Fin 4) := hvalue
    _ = ε * s.valueUnit (0 : Fin 4) := hc
    _ = ε * b.valueUnit (0 : Fin (N + 4)) :=
      congrArg (ε * ·) hsValue

/-- In the critical half-gap induction, exception (c) for the projected
tail supplies the second pair of alternating orders.  The exceptional
half-gap equality for that tail supplies the first pair, so the first four
entries form precisely the quaternary segment to which Lemma 8.3 applies. -/
theorem beli2019Lemma88_critical_of_tailExceptionC
    [QuadraticDefectLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    (b : GoodBONG q L (N + 4))
    (hhalf : b.AttainsHalfGap (0 : Fin (N + 3)))
    (hnotA : ¬b.Beli2019Lemma88ExceptionA)
    (htailAlpha : b.tail.alphaValue (0 : Fin (N + 2)) =
      b.lemma88ComplementaryDefect)
    (htailExceptional : b.tail.Beli2019Lemma88Exceptional)
    (C : b.tail.Beli2019Lemma88ExceptionC) :
    Nonempty b.Beli2019FirstValueTransform := by
  have hfirstOrders : b.order (0 : Fin (N + 4)) =
      b.order (2 : Fin (N + 4)) :=
    b.firstThirdOrders_eq_of_tailExceptional htailAlpha htailExceptional
  have hsecondOrders : b.order (1 : Fin (N + 4)) =
      b.order (3 : Fin (N + 4)) := by
    have horders := C.outerOrders_eq
    simp only [b.order_goodTail] at horders
    convert horders using 1 <;> congr 1
  have hrealized : IsValuationUnitDefect (K := K)
      (b.alphaValue (0 : Fin (N + 3))) := by
    by_contra hnot
    exact hnotA hnot
  rcases hrealized with ⟨ε, hunit, hdefect⟩
  exact b.firstValueTransform_of_firstQuaternarySegment
    hfirstOrders hsecondOrders hhalf ε hunit hdefect

end BONG.GoodBONG

end Bong
