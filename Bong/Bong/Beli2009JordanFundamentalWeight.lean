/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009JordanSegmentIdentification
import Bong.Bong.Beli2009AlphaCompression
import Bong.Bong.Beli2009JordanWeightOrderBase
import Bong.Bong.GoodBONGScalarAgreement
import Bong.Bong.GoodMap
import Bong.Bong.Rescale
import Bong.Lattice.OrthogonalProductDecomposition
import Bong.Lattice.WeightIdealRescale

/-!
# Fundamental weights at an arbitrary strict Jordan component

This file computes the two concrete factors in

`L^(s_k) = L_{≥ k} ⊥ s_k (L_{<k})#`

from the actual consecutive BONG segments.  It is the numerical core of
Beli (2009), Lemma 2.16(i).  No abstract Jordan-alpha or reduction law is
used here.
-/

namespace Bong

open Dyadic Module

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {m : Nat}

namespace BONG.GoodBONG

/-- Interior form of Corollary 2.5(ii), with both optional segment terms
present. -/
theorem alphaValue_eq_min_four_segmentCandidates
    (b : GoodBONG q L (m + 2)) (i : Fin (m + 1))
    (hleft : 0 < i.val) (hright : i.val + 1 < m + 1) :
    (b.alphaValue i : WithTop ℚ) =
      min (b.halfGapCandidate i)
        (min (b.leftDefectCandidate i i)
          (min (b.prefixSegmentAlphaCandidate i hleft)
            (b.suffixSegmentAlphaCandidate i hright))) := by
  rw [b.coe_alphaValue, b.beli2009Corollary25_ii i]
  simp [segmentRecursiveAlphaCandidates, prefixSegmentAlphaCandidates,
    suffixSegmentAlphaCandidates, hleft, hright]

@[simp]
theorem valueUnit_castLength_fundamental
    {p t : Nat} {X : Type*} [AddCommGroup X] [Module K X]
    {s : QuadraticSpace K X} {N : Lattice K X}
    (c : GoodBONG s N p) (h : p = t) (j : Fin t) :
    (c.castLength h).valueUnit j = c.valueUnit ⟨j.val, by omega⟩ := by
  subst t
  rfl

@[simp]
theorem alphaValue_castLength_fundamental
    {p t : Nat} {X : Type*} [AddCommGroup X] [Module K X]
    {s : QuadraticSpace K X} {N : Lattice K X}
    (c : GoodBONG s N (p + 1)) (h : p = t) (j : Fin t) :
    (c.castLength (congrArg (fun z => z + 1) h)).alphaValue j =
      c.alphaValue (Fin.cast h.symm j) := by
  subst t
  rfl

/-- Scalar equality transports alpha even when the two length indices are
presented by propositionally equal, rather than definitionally equal,
natural-number expressions. -/
theorem alphaValue_eq_of_valueUnits_eq_cast
    {p t : Nat}
    {X Y : Type*} [AddCommGroup X] [Module K X]
    [AddCommGroup Y] [Module K Y]
    {s : QuadraticSpace K X} {z : QuadraticSpace K Y}
    {N : Lattice K X} {P : Lattice K Y}
    (c : GoodBONG s N (p + 1)) (d : GoodBONG z P (t + 1))
    (hlen : p = t)
    (hvalues : ∀ j, c.valueUnit j =
      d.valueUnit (Fin.cast (congrArg (fun z => z + 1) hlen) j))
    (j : Fin p) :
    c.alphaValue j = d.alphaValue (Fin.cast hlen j) := by
  subst t
  simpa using c.alphaValue_eq_of_valueUnits_eq d (by simpa using hvalues) j

/-- Endpoint form of Corollary 2.5(ii), expressed through the named suffix
candidate rather than its expanded localization formula. -/
theorem alphaValue_zero_eq_min_binaryCandidates_suffixCandidate
    {X : Type*} [AddCommGroup X] [Module K X]
    {s : QuadraticSpace K X} {N : Lattice K X}
    {p : Nat} (c : GoodBONG s N (p + 3)) :
    (c.alphaValue 0 : WithTop ℚ) =
      min (c.halfGapCandidate 0)
        (min (c.leftDefectCandidate 0 0)
          (c.suffixSegmentAlphaCandidate (n := p + 1)
            (0 : Fin (p + 2))
            (Nat.succ_lt_succ (Nat.zero_lt_succ p)))) := by
  rw [c.alphaValue_zero_eq_min_binaryCandidates_suffix]
  rfl

/-- Corollary 2.5(ii) compressed at an arbitrary noninitial cut.  The
second term is the first alpha of any scalar-identical realization of the
actual suffix. -/
theorem alphaValue_eq_min_prefix_suffix
    {n : Nat} {X : Type*} [AddCommGroup X] [Module K X]
    {s : QuadraticSpace K X} {N : Lattice K X}
    (b : GoodBONG q L (n + 2)) (i : Fin (n + 1))
    (hleft : 0 < i.val)
    {p : Nat} (c : GoodBONG s N (p + 2))
    (hlen : p + 2 = n + 2 - i.val)
    (hvalues : ∀ j, c.valueUnit j =
      b.valueUnit ⟨i.val + j.val, by omega⟩) :
    (b.alphaValue i : WithTop ℚ) =
      min (b.prefixSegmentAlphaCandidate i hleft)
        (c.alphaValue ⟨0, by omega⟩ : WithTop ℚ) := by
  by_cases hright : i.val + 1 < n + 1
  · let t := n - i.val - 1
    have hcast : p + 2 = t + 3 := by
      dsimp only [t]
      omega
    have hbase : p + 1 = t + 2 := by omega
    let c' := c.castLength hcast
    have hvalues' : ∀ j, c'.valueUnit j =
        b.valueUnit ⟨i.val + j.val, by omega⟩ := by
      intro j
      rw [show c' = c.castLength hcast by rfl,
        valueUnit_castLength_fundamental]
      exact hvalues _
    have horders' : ∀ j, c'.order j =
        b.order ⟨i.val + j.val, by omega⟩ := by
      intro j
      rw [show c' = c.castLength hcast by rfl,
        GoodBONG.order_castLength]
      change c.toBONG.order ⟨j.val, by omega⟩ =
        b.toBONG.order ⟨i.val + j.val, by omega⟩
      rw [c.toBONG.order_eq_ordUnit, b.toBONG.order_eq_ordUnit,
        show c.toBONG.valueUnit ⟨j.val, by omega⟩ =
          b.toBONG.valueUnit ⟨i.val + j.val, by omega⟩ from hvalues _]
    have hhalf : c'.halfGapCandidate 0 = b.halfGapCandidate i := by
      unfold halfGapCandidate
      simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one]
      rw [horders' 0, horders' 1]
      congr 2
    have hdefect : c'.leftDefectCandidate 0 0 =
        b.leftDefectCandidate i i := by
      unfold leftDefectCandidate adjacentDefect adjacentProduct
      simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one]
      rw [horders' 0, horders' 1, hvalues' 0, hvalues' 1]
      congr 4
    let ic : Fin (t + 2) := ⟨0, by dsimp [t]; omega⟩
    let sc := c'.suffixAlphaSegmentWitness (n := t + 1) ic (by
      dsimp [ic, t]
      omega)
    let sb := b.suffixAlphaSegmentWitness i hright
    have hsegmentLength :
        (suffixAlphaLocalizationIndex ic (by
          dsimp [ic, t]
          omega)).stop -
            (suffixAlphaLocalizationIndex ic (by
              dsimp [ic, t]
              omega)).start =
          (suffixAlphaLocalizationIndex i hright).stop -
            (suffixAlphaLocalizationIndex i hright).start := by
      dsimp [ic, t, suffixAlphaLocalizationIndex]
      omega
    have hsegmentValues : ∀ j,
        (sc.toGoodBONG c'.good).valueUnit j =
          (sb.toGoodBONG b.good).valueUnit
            (Fin.cast (congrArg (fun z => z + 1) hsegmentLength) j) := by
      intro j
      change sc.bong.valueUnit j = sb.bong.valueUnit _
      rw [sc.valueUnit_eq, sb.valueUnit_eq]
      change c'.valueUnit (sc.sourceIndex j) =
        b.valueUnit (sb.sourceIndex (Fin.cast _ j))
      rw [hvalues']
      congr 1
      apply Fin.ext
      simp [ic, suffixAlphaLocalizationIndex,
        BONG.SegmentWitness.sourceIndex]
      omega
    have hsegmentAlpha := alphaValue_eq_of_valueUnits_eq_cast
      (sc.toGoodBONG c'.good) (sb.toGoodBONG b.good)
      hsegmentLength hsegmentValues
      (suffixAlphaLocalizationIndex ic (by
        dsimp [ic, t]
        omega)).localPivot
    have hlocal :
        Fin.cast hsegmentLength
            (suffixAlphaLocalizationIndex ic (by
              dsimp [ic, t]
              omega)).localPivot =
          (suffixAlphaLocalizationIndex i hright).localPivot := by
      apply Fin.ext
      simp [ic, suffixAlphaLocalizationIndex,
        AlphaLocalizationIndex.localPivot]
    have hcurrentOrder :
        c'.order ic.castSucc = b.order i.castSucc := by
      calc
        c'.order ic.castSucc = c'.order (0 : Fin (t + 3)) := by congr 1
        _ = b.order ⟨i.val + (0 : Fin (t + 3)).val, by omega⟩ :=
          horders' (0 : Fin (t + 3))
        _ = b.order i.castSucc := by congr 1
    have hpivotOrder :
        c'.order
            (suffixAlphaLocalizationIndex ic (by
              dsimp [ic, t]
              omega)).pivotFin.castSucc =
          b.order (suffixAlphaLocalizationIndex i hright).pivotFin.castSucc := by
      calc
        c'.order
            (suffixAlphaLocalizationIndex ic (by
              dsimp [ic, t]
              omega)).pivotFin.castSucc =
            c'.order (1 : Fin (t + 3)) := by congr 1
        _ = b.order ⟨i.val + (1 : Fin (t + 3)).val, by omega⟩ :=
          horders' (1 : Fin (t + 3))
        _ = b.order
            (suffixAlphaLocalizationIndex i hright).pivotFin.castSucc := by
          congr 1
    have hsegmentAlpha' :
        (sc.toGoodBONG c'.good).alphaValue
            (suffixAlphaLocalizationIndex ic (by
              dsimp [ic, t]
              omega)).localPivot =
          (sb.toGoodBONG b.good).alphaValue
            (suffixAlphaLocalizationIndex i hright).localPivot := by
      simpa [hlocal] using hsegmentAlpha
    have hsuffixIC : c'.suffixSegmentAlphaCandidate (n := t + 1)
          ic (by dsimp [ic, t]; omega) =
        b.suffixSegmentAlphaCandidate i hright := by
      unfold suffixSegmentAlphaCandidate rightCompressionValue
      rw [hcurrentOrder, hpivotOrder]
      congr 2
    have hsuffix : c'.suffixSegmentAlphaCandidate (n := t + 1)
          (0 : Fin (t + 2)) (by dsimp [t]; omega) =
        b.suffixSegmentAlphaCandidate i hright := by
      simpa [ic] using hsuffixIC
    have hglobal := b.alphaValue_eq_min_four_segmentCandidates i hleft hright
    have htail := c'.alphaValue_zero_eq_min_binaryCandidates_suffixCandidate
    rw [hhalf, hdefect, hsuffix] at htail
    have hcastAlpha : c'.alphaValue (0 : Fin (t + 2)) =
        c.alphaValue (0 : Fin (p + 1)) := by
      simpa [c'] using
        (alphaValue_castLength_fundamental c hbase (0 : Fin (t + 2)))
    rw [hglobal]
    calc
      min (b.halfGapCandidate i)
          (min (b.leftDefectCandidate i i)
            (min (b.prefixSegmentAlphaCandidate i hleft)
              (b.suffixSegmentAlphaCandidate i hright))) =
          min (b.prefixSegmentAlphaCandidate i hleft)
            (min (b.halfGapCandidate i)
              (min (b.leftDefectCandidate i i)
                (b.suffixSegmentAlphaCandidate i hright))) := by
        simp [min_assoc, min_left_comm, min_comm]
      _ = min (b.prefixSegmentAlphaCandidate i hleft)
          (c'.alphaValue (0 : Fin (t + 2)) : WithTop ℚ) := by rw [← htail]
      _ = min (b.prefixSegmentAlphaCandidate i hleft)
          (c.alphaValue (0 : Fin (p + 1)) : WithTop ℚ) := by
        rw [hcastAlpha]
  · have hi : i.val = n := by omega
    have hp : p = 0 := by omega
    subst p
    have hvalues' : ∀ j, c.valueUnit j =
        b.valueUnit ⟨i.val + j.val, by omega⟩ := by
      intro j
      exact hvalues _
    have horders' : ∀ j, c.order j =
        b.order ⟨i.val + j.val, by omega⟩ := by
      intro j
      change c.toBONG.order j = b.toBONG.order ⟨i.val + j.val, by omega⟩
      rw [c.toBONG.order_eq_ordUnit, b.toBONG.order_eq_ordUnit,
        show c.toBONG.valueUnit j =
          b.toBONG.valueUnit ⟨i.val + j.val, by omega⟩ from hvalues _]
    have hhalf : c.halfGapCandidate 0 = b.halfGapCandidate i := by
      unfold halfGapCandidate
      simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one]
      rw [horders' 0, horders' 1]
      congr 2
    have hdefect : c.leftDefectCandidate 0 0 =
        b.leftDefectCandidate i i := by
      unfold leftDefectCandidate adjacentDefect adjacentProduct
      simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one]
      rw [horders' 0, horders' 1, hvalues' 0, hvalues' 1]
      congr 4
    have hglobal := b.beli2009Corollary25_ii i
    rw [b.coe_alphaValue, hglobal]
    simp [segmentRecursiveAlphaCandidates, prefixSegmentAlphaCandidates,
      suffixSegmentAlphaCandidates, hleft, hright]
    rw [← hhalf, ← hdefect, ← c.coe_alphaValue,
      c.binary_alpha_eq_min_candidates]
    simp [min_assoc, min_left_comm, min_comm]

end BONG.GoodBONG

namespace BONG.StrictJordanAdaptedAlignment

variable {a : GoodBONG q L (m + 1)}
  {b : GoodBONG r M (m + 1)}

/-- The actual source BONG segment before a noninitial Jordan component,
transported to the canonical Jordan-prefix lattice. -/
noncomputable def sourcePrefixGoodBONG
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) (hk : 0 < k.val)
    (T : a.toBONG.TwoBlockSplitWitness (S.componentStart k)
      (by
        exact le_trans (Nat.le_of_lt (S.componentStart_lt_componentStop k))
          (S.componentStop_le k))) :
    let D := S.sourceJordan.toOrthogonalDecomposition
    GoodBONG (D.prefixQuadraticSublattice k.val).space
      (D.prefixQuadraticSublattice k.val).lattice (S.componentStart k) :=
  (T.left.toGoodBONG a.good).mapLatticeIsometry
    (S.sourceSplitLeftLatticeIsometry k hk T)

/-- The actual source BONG segment beginning with a Jordan component,
transported to the canonical Jordan-suffix lattice. -/
noncomputable def sourceSuffixGoodBONG
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) (hk : 0 < k.val)
    (T : a.toBONG.TwoBlockSplitWitness (S.componentStart k)
      (by
        exact le_trans (Nat.le_of_lt (S.componentStart_lt_componentStop k))
          (S.componentStop_le k))) :
    let D := S.sourceJordan.toOrthogonalDecomposition
    GoodBONG (D.suffixQuadraticSublattice k.val).space
      (D.suffixQuadraticSublattice k.val).lattice
      (m + 1 - S.componentStart k) :=
  (T.right.toGoodBONG a.good).mapLatticeIsometry
    (S.sourceSplitRightLatticeIsometry k hk T)

@[simp]
theorem sourcePrefixGoodBONG_order
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) (hk : 0 < k.val)
    (T : a.toBONG.TwoBlockSplitWitness (S.componentStart k)
      (by
        exact le_trans (Nat.le_of_lt (S.componentStart_lt_componentStop k))
          (S.componentStop_le k)))
    (i : Fin (S.componentStart k)) :
    (S.sourcePrefixGoodBONG k hk T).order i =
      a.order ⟨i.val, by
        have hi := i.isLt
        have hstop := S.componentStop_le k
        have hstart := S.componentStart_lt_componentStop k
        omega⟩ := by
  unfold sourcePrefixGoodBONG
  rw [GoodBONG.order_mapLatticeIsometry]
  change T.left.bong.order i = a.toBONG.order _
  rw [T.left.order_eq]
  apply congrArg a.toBONG.order
  apply Fin.ext
  simp only [BONG.SegmentWitness.sourceIndex_val, Nat.zero_add]

@[simp]
theorem sourceSuffixGoodBONG_order
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) (hk : 0 < k.val)
    (T : a.toBONG.TwoBlockSplitWitness (S.componentStart k)
      (by
        exact le_trans (Nat.le_of_lt (S.componentStart_lt_componentStop k))
          (S.componentStop_le k)))
    (i : Fin (m + 1 - S.componentStart k)) :
    (S.sourceSuffixGoodBONG k hk T).order i =
      a.order ⟨S.componentStart k + i.val, by
        have hi := i.isLt
        omega⟩ := by
  unfold sourceSuffixGoodBONG
  rw [GoodBONG.order_mapLatticeIsometry]
  change T.right.bong.order i = a.toBONG.order _
  rw [T.right.order_eq]
  congr 1

/-- The first two orders in every non-unary strict Jordan component are
descending. -/
theorem source_component_head_descending
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount)
    (hrank : 2 ≤
      S.sourceJordan.toOrthogonalDecomposition.componentRank k) :
    a.order ⟨S.componentStart k + 1, by
        have hstop := S.componentStop_le k
        unfold componentStop at hstop
        omega⟩ ≤
      a.order ⟨S.componentStart k, by
        have hstop := S.componentStop_le k
        unfold componentStop at hstop
        omega⟩ := by
  let C := S.sourceComponentCoordinates k
  have hCstart : C.start = S.componentStart k := by
    rfl
  have hCstop : C.stop = S.componentStop k := by
    rfl
  have hnext : C.start + 1 < C.stop := by
    rw [hCstart, hCstop]
    unfold componentStop
    omega
  have hzero :=
    (C.beli2009Lemma213_i C.start le_rfl (by omega)).1 (by simp)
  have hone :=
    (C.beli2009Lemma213_i (C.start + 1) (by omega) hnext).2 (by simp)
  have hscale : C.scaleOrder ≤ C.normOrder := by
    change ordUnit K (S.sourceJordan.scaleGenerator k) ≤
      jordanEffectiveNormOrder S.sourceJordan k
    exact S.source_scaleOrder_le_effectiveNormOrder k
  have hindex0 : C.index C.start (by omega) =
      ⟨S.componentStart k, by
        have hstop := S.componentStop_le k
        unfold componentStop at hstop
        omega⟩ := by
    apply Fin.ext
    exact hCstart
  have hindex1 : C.index (C.start + 1) hnext =
      ⟨S.componentStart k + 1, by
        have hstop := S.componentStop_le k
        unfold componentStop at hstop
        omega⟩ := by
    apply Fin.ext
    exact congrArg (fun z : Nat ↦ z + 1) hCstart
  rw [hindex0] at hzero
  rw [hindex1] at hone
  omega

end BONG.StrictJordanAdaptedAlignment

end Bong
