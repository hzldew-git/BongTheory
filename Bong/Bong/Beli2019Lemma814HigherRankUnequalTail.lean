/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma814HigherRankUnequalNormalization

/-!
# Beli (2019), Lemma 8.14: the unequal-outer tail beginning at `a₃`

The third-pair normal form identifies the first alpha of the suffix
`[a₃, ..., aₙ]` with the ambient third alpha.  This prepares the strict
and boundary applications of Lemma 8.8 in the remaining unequal-outer proof.
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

/-- The suffix `[a₃, ..., aₙ]` used in the unequal-outer branch. -/
noncomputable def lemma814UnequalTailSegment (a : GoodBONG q L (N + 4)) :
    BONG.SegmentWitness a.toBONG 2 (N + 2) (by omega) :=
  a.toBONG.segmentWitness 2 (N + 2) (by omega)

/-- The suffix `[a₃, ..., aₙ]`, regarded as a good BONG. -/
noncomputable def lemma814UnequalTail (a : GoodBONG q L (N + 4)) :
    GoodBONG
      (q.restrict a.lemma814UnequalTailSegment.carrier
        a.lemma814UnequalTailSegment.nondegenerate)
      a.lemma814UnequalTailSegment.lattice (N + 2) :=
  a.lemma814UnequalTailSegment.toGoodBONG a.good

/-- Values of the unequal-outer suffix are the ambient values shifted by two.
-/
theorem lemma814UnequalTail_valueUnit_eq
    (a : GoodBONG q L (N + 4)) (i : Fin (N + 2)) :
    a.lemma814UnequalTail.valueUnit i =
      a.valueUnit ⟨2 + i.1, by omega⟩ := by
  let w := a.lemma814UnequalTailSegment
  change w.bong.valueUnit i = a.toBONG.valueUnit ⟨2 + i.1, by omega⟩
  calc
    w.bong.valueUnit i = a.toBONG.valueUnit (w.sourceIndex i) :=
      w.valueUnit_eq i
    _ = a.toBONG.valueUnit ⟨2 + i.1, by omega⟩ := by
      congr 1

/-- Orders of the unequal-outer suffix are the ambient orders shifted by two.
-/
theorem lemma814UnequalTail_order_eq
    (a : GoodBONG q L (N + 4)) (i : Fin (N + 2)) :
    a.lemma814UnequalTail.order i = a.order ⟨2 + i.1, by omega⟩ := by
  let w := a.lemma814UnequalTailSegment
  change w.bong.order i = a.toBONG.order ⟨2 + i.1, by omega⟩
  calc
    w.bong.order i = a.toBONG.order (w.sourceIndex i) := w.order_eq i
    _ = a.toBONG.order ⟨2 + i.1, by omega⟩ := by
      congr 1

/-- The first half-gap of `[a₃, ..., aₙ]` is the ambient third half-gap.
-/
theorem lemma814UnequalTail_halfGapValue_zero_eq
    (a : GoodBONG q L (N + 4)) :
    a.lemma814UnequalTail.halfGapValue (0 : Fin (N + 1)) =
      a.halfGapValue (2 : Fin (N + 3)) := by
  unfold halfGapValue orderGap
  rw [a.lemma814UnequalTail_order_eq (0 : Fin (N + 1)).castSucc,
    a.lemma814UnequalTail_order_eq (0 : Fin (N + 1)).succ]
  congr 3

/-- Once Corollary 8.11 realizes the ambient third alpha on `[a₃,a₄]`,
the first alpha of the entire suffix `[a₃, ..., aₙ]` is the same alpha.
-/
theorem lemma814UnequalTail_alpha_zero_eq_thirdAlpha
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    (a : GoodBONG q L (N + 4))
    (hbinary : a.adjacentBinaryAlpha (2 : Fin (N + 3)) =
      (a.alphaValue (2 : Fin (N + 3)) : WithTop ℚ)) :
    a.lemma814UnequalTail.alphaValue (0 : Fin (N + 1)) =
      a.alphaValue (2 : Fin (N + 3)) := by
  let p := suffixPairLocalization (N := N + 2) (2 : Fin (N + 3))
  let w : BONG.SegmentWitness a.toBONG p.start p.length p.bound :=
    a.lemma814UnequalTailSegment
  let s := w.toGoodBONG a.good
  have hpivot : p.pivotFin = (2 : Fin (N + 3)) := by
    apply Fin.ext
    rfl
  have hlocalPivot : p.localPivot = (0 : Fin (N + 1)) := by
    apply Fin.ext
    rfl
  have hglobalLeLocal := a.beli2009Lemma21_le_segmentAlpha p w
  have hlocalLeBinary : (s.alphaValue p.localPivot : WithTop ℚ) ≤
      s.adjacentBinaryAlpha p.localPivot := by
    unfold adjacentBinaryAlpha
    apply le_min
    · rw [s.coe_alphaValue]
      exact s.alpha_le_halfGapCandidate p.localPivot
    · rw [s.coe_alphaValue]
      exact s.alpha_le_leftDefectCandidate le_rfl
  have hlocalBinary : s.adjacentBinaryAlpha p.localPivot =
      a.adjacentBinaryAlpha (2 : Fin (N + 3)) := by
    unfold adjacentBinaryAlpha
    have hstart : p.start ≤ p.pivotFin.1 := p.start_le_pivot
    have hstop : p.pivotFin.1 < p.stop := p.pivot_lt_stop
    have hlocalIndex : p.localAdjacent p.pivotFin hstart hstop =
        p.localPivot := by
      apply Fin.ext
      rfl
    have hleft : s.leftDefectCandidate p.localPivot p.localPivot =
        a.leftDefectCandidate p.pivotFin p.pivotFin := by
      calc
        s.leftDefectCandidate p.localPivot p.localPivot =
            s.leftDefectCandidate p.localPivot
              (p.localAdjacent p.pivotFin hstart hstop) := by
          rw [hlocalIndex]
        _ = a.leftDefectCandidate p.pivotFin p.pivotFin :=
          a.segment_leftDefectCandidate_local p w p.pivotFin hstart hstop
            le_rfl
    rw [a.segment_halfGapCandidate_local p w, hleft, hpivot]
  rw [hlocalBinary, hbinary] at hlocalLeBinary
  rw [hpivot, hlocalPivot] at hglobalLeLocal
  have hglobalLeLocalValue :
      (a.alphaValue (2 : Fin (N + 3)) : WithTop ℚ) ≤
        (s.alphaValue (0 : Fin (N + 1)) : WithTop ℚ) := by
    rw [a.coe_alphaValue, s.coe_alphaValue]
    simpa only [s] using hglobalLeLocal
  have heq : s.alphaValue (0 : Fin (N + 1)) =
      a.alphaValue (2 : Fin (N + 3)) := by
    exact_mod_cast le_antisymm hlocalLeBinary hglobalLeLocalValue
  change (a.lemma814UnequalTailSegment.toGoodBONG a.good).alphaValue
      (0 : Fin (N + 1)) = a.alphaValue (2 : Fin (N + 3))
  exact heq

end BONG.GoodBONG
end Bong
