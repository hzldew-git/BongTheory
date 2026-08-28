/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapOneTypeIIINonoverlapEvenIntegral

/-!
# Beli (2019), Lemma 7.9(ii), case 8: type-III order bounds

The nonoverlapping central source gap is even and at most one, hence it is
nonpositive.  Therefore the strict-tail base order `S` is at most `R + 1`.
Together with the norm-ideal inequality and even-index monotonicity this
puts every relevant even comparison order above `S`.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The paper's type-III strict-tail base satisfies `S <= R + 1`. -/
theorem beli2019Lemma79_typeIII_nonoverlap_tailBase_le_reference_add_one
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (hnotOverlap : a.orderGap
      (Fin.mk D.outer.transition.lastZero (by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega)) ≠ 1)
    (hlast : D.outer.last < n + 1) :
    b.order (Fin.mk D.outer.last hlast).castSucc <=
      a.orderSequence.entryOrZero D.outer.transition.lastZero + 1 := by
  let center : Fin (n + 1) :=
    Fin.mk D.outer.transition.lastZero (by
      have hbound := D.outer.transition.firstTwo_le_rank
      rw [D.adjacent] at hbound
      omega)
  have hgapEven := lemma78_typeIII_centralGap_even
    a b D hfirst hdefect hnotOverlap
  have hgapNonpos : a.orderGap center <= 0 := by
    rcases hgapEven with ⟨z, hz⟩
    have hgapLe : a.orderGap center <= 1 := by
      have halpha := a.beli2019Lemma69_i_typeIII
        (alphaV := inferInstance) (alphaW := inferInstance)
        b D hfirst hdefect
      exact a.orderGap_le_one_of_alphaValue_le_one center (by
        simpa only [center] using halpha)
    rw [hz] at hgapLe ⊢
    omega
  have hbase :=
    beli2019Lemma79_typeIII_nonoverlap_tailBase_eq_rightSource_add_one
      a b D hlast
  have hrightEq : D.outer.transition.firstTwo - 1 =
      D.outer.transition.lastZero + 1 := by
    rw [D.adjacent]
    omega
  have hleftOrder : a.order center.castSucc =
      a.orderSequence.entryOrZero D.outer.transition.lastZero := by
    rw [<- a.orderSequence_entryOrZero_eq_order center.castSucc]
    rfl
  have hrightOrder : a.order center.succ =
      a.orderSequence.entryOrZero
        (D.outer.transition.firstTwo - 1) := by
    rw [<- a.orderSequence_entryOrZero_eq_order center.succ]
    simp only [center, Fin.val_succ]
    rw [hrightEq]
  unfold orderGap at hgapNonpos
  rw [hleftOrder, hrightOrder] at hgapNonpos
  omega

/-- At an even case-8 index, the comparison order immediately preceding
the final pair is at least the strict-tail base `S`. -/
theorem beli2019Lemma79_typeIII_nonoverlap_even_previousOrder_ge_tailBase
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (hdefect : a.RepresentationDefectCondition b)
    (hnotOverlap : a.orderGap
      (Fin.mk D.outer.transition.lastZero (by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega)) ≠ 1)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (hlast : D.outer.last < n + 1)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiEven : Even i.val) (hiTwo : 2 <= i.val) :
    b.order (Fin.mk D.outer.last hlast).castSucc <=
      c.order (evenTargetPreviousAlphaIndex i).castSucc := by
  let p : Fin (n + 1) := evenTargetPreviousAlphaIndex i
  have hbase :=
    beli2019Lemma79_typeIII_nonoverlap_tailBase_le_reference_add_one
      a b D hfirst hdefect hnotOverlap hlast
  have hleftEven := D.outer.left_even_of_first_eq_zero hfirst
  have hsourceLeft := D.outer.source_leftEven_eq_first
    hfirst D.outer.transition.lastZero le_rfl hleftEven
  have hnormOrder := a.toBONG.order_zero_add_one_le_of_normIdeal_lt
    c.toBONG hnorm
  have hreferenceLower :
      a.orderSequence.entryOrZero D.outer.transition.lastZero + 1 <=
        c.order (0 : Fin (n + 2)) := by
    rw [hsourceLeft,
      show a.orderSequence.entryOrZero 0 =
          a.order (0 : Fin (n + 2)) by
        simpa using a.orderSequence_entryOrZero_eq_order
          (0 : Fin (n + 2))]
    exact hnormOrder
  have hpEven : Even p.val := by
    rcases hiEven with ⟨d, hd⟩
    refine ⟨d - 1, ?_⟩
    simp only [p, evenTargetPreviousAlphaIndex]
    omega
  have hzeroPreviousEntry := c.orderSequence.entryOrZero_le_of_evenGap
    0 p.val (Nat.zero_le _) (by omega) hpEven
  have hzeroPrevious : c.order (0 : Fin (n + 2)) <=
      c.order p.castSucc := by
    have hzeroEntry : c.orderSequence.entryOrZero 0 =
        c.order (0 : Fin (n + 2)) := by
      simpa using c.orderSequence_entryOrZero_eq_order
        (0 : Fin (n + 2))
    have hpEntry : c.orderSequence.entryOrZero p.val =
        c.order p.castSucc := by
      simpa using c.orderSequence_entryOrZero_eq_order p.castSucc
    rw [hzeroEntry, hpEntry] at hzeroPreviousEntry
    exact hzeroPreviousEntry
  simpa only [p] using hbase.trans (hreferenceLower.trans hzeroPrevious)

end BONG.GoodBONG

end Bong
