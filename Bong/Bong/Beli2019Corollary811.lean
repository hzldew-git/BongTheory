/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Corollary810
import Bong.Bong.Beli2019DefectDual
import Bong.Bong.Beli2009AlphaLocalizationProof
import Bong.Bong.GoodExistence

/-!
# Beli (2019), Corollary 8.11

This file first packages the alpha of an arbitrary literal adjacent binary
segment.  It then proves the right-endpoint counterpart of Corollary 8.10 by
reverse duality.  These are the two endpoint operations used to normalize an
arbitrary adjacent pair.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {N : Nat}

/-- Transport a good BONG along equality of its lattice index. -/
noncomputable def castLattice {M P : Lattice K V} {n : Nat}
    (b : GoodBONG q M n) (h : M = P) : GoodBONG q P n :=
  h ▸ b

@[simp]
theorem valueUnit_castLattice {M P : Lattice K V} {n : Nat}
    (b : GoodBONG q M n) (h : M = P) (i : Fin n) :
    (b.castLattice h).valueUnit i = b.valueUnit i := by
  subst P
  rfl

@[simp]
theorem order_castLattice {M P : Lattice K V} {n : Nat}
    (b : GoodBONG q M n) (h : M = P) (i : Fin n) :
    (b.castLattice h).order i = b.order i := by
  subst P
  rfl

@[simp]
theorem alphaValue_castLattice {M P : Lattice K V} {n : Nat}
    (b : GoodBONG q M (n + 1)) (h : M = P) (i : Fin n) :
    (b.castLattice h).alphaValue i = b.alphaValue i := by
  subst P
  rfl

@[simp]
theorem alphaValue_castLength' {M : Lattice K V} {m n : Nat}
    (b : GoodBONG q M (m + 1)) (h : m = n) (i : Fin n) :
    (b.castLength (congrArg (fun k => k + 1) h)).alphaValue i =
      b.alphaValue (Fin.cast h.symm i) := by
  subst n
  rfl

/-- The alpha of the literal binary segment at an arbitrary adjacent index. -/
noncomputable def adjacentBinaryAlpha
    (b : GoodBONG q L (N + 1)) (i : Fin N) : WithTop ℚ :=
  min (b.halfGapCandidate i) (b.leftDefectCandidate i i)

@[simp]
theorem adjacentBinaryAlpha_castLength {M : Lattice K V} {m n : Nat}
    (b : GoodBONG q M (m + 1)) (h : m = n) (i : Fin n) :
    (b.castLength (congrArg (fun k => k + 1) h)).adjacentBinaryAlpha i =
      b.adjacentBinaryAlpha (Fin.cast h.symm i) := by
  subst n
  rfl

@[simp]
theorem adjacentBinaryAlpha_castLattice {M P : Lattice K V}
    (b : GoodBONG q M (N + 1)) (h : M = P) (i : Fin N) :
    (b.castLattice h).adjacentBinaryAlpha i = b.adjacentBinaryAlpha i := by
  subst P
  rfl

@[simp]
theorem firstBinaryAlpha_castLattice {M P : Lattice K V}
    (b : GoodBONG q M (N + 2)) (h : M = P) :
    (b.castLattice h).firstBinaryAlpha = b.firstBinaryAlpha := by
  subst P
  rfl

@[simp]
theorem adjacentBinaryAlpha_zero (b : GoodBONG q L (N + 2)) :
    b.adjacentBinaryAlpha (0 : Fin (N + 1)) = b.firstBinaryAlpha :=
  rfl

/-- The alpha of the literal final binary segment. -/
noncomputable def lastBinaryAlpha (b : GoodBONG q L (N + 2)) : WithTop ℚ :=
  b.adjacentBinaryAlpha (Fin.last N)

/-- An arbitrary adjacent binary alpha is the alpha of its canonical
rank-two segment. -/
theorem adjacentBinaryAlpha_eq_segmentAlpha
    (b : GoodBONG q L (N + 2)) (i : Fin (N + 1))
    (w : BONG.SegmentWitness b.toBONG i.1 2 (by omega)) :
    b.adjacentBinaryAlpha i =
      ((w.toGoodBONG b.good).alphaValue (0 : Fin 1) : WithTop ℚ) := by
  let s := w.toGoodBONG b.good
  rw [s.binary_alpha_eq_min_candidates]
  have hsource0 : w.sourceIndex (0 : Fin 2) = i.castSucc := by
    apply Fin.ext
    simp [BONG.SegmentWitness.sourceIndex]
  have hsource1 : w.sourceIndex (1 : Fin 2) = i.succ := by
    apply Fin.ext
    simp [BONG.SegmentWitness.sourceIndex]
  have horder0 : s.order (0 : Fin 2) = b.order i.castSucc := by
    change w.bong.order 0 = b.toBONG.order i.castSucc
    rw [w.order_eq, hsource0]
  have horder1 : s.order (1 : Fin 2) = b.order i.succ := by
    change w.bong.order 1 = b.toBONG.order i.succ
    rw [w.order_eq, hsource1]
  have hadjacent : s.adjacentDefect (0 : Fin 1) = b.adjacentDefect i := by
    unfold adjacentDefect adjacentProduct
    have hvalue0 := w.valueUnit_eq (0 : Fin 2)
    have hvalue1 := w.valueUnit_eq (1 : Fin 2)
    rw [hsource0] at hvalue0
    rw [hsource1] at hvalue1
    change defectOrder (K := K) (-(w.bong.valueUnit 0 * w.bong.valueUnit 1)) =
      defectOrder (K := K)
        (-(b.toBONG.valueUnit i.castSucc * b.toBONG.valueUnit i.succ))
    rw [hvalue0, hvalue1]
  have hsCast : (0 : Fin 1).castSucc = (0 : Fin 2) := by
    apply Fin.ext
    rfl
  have hsSucc : (0 : Fin 1).succ = (1 : Fin 2) := by
    apply Fin.ext
    rfl
  have hhalf : s.halfGapCandidate (0 : Fin 1) = b.halfGapCandidate i := by
    unfold halfGapCandidate
    rw [hsCast, hsSucc, horder0, horder1]
  have hleft : s.leftDefectCandidate (0 : Fin 1) (0 : Fin 1) =
      b.leftDefectCandidate i i := by
    unfold leftDefectCandidate
    rw [hsCast, hsSucc, horder0, horder1, hadjacent]
  unfold adjacentBinaryAlpha
  rw [hhalf, hleft]

/-- The full prefix ending with the adjacent pair indexed by `i`. -/
def prefixPairLocalization (i : Fin (N + 1)) :
    AlphaLocalizationIndex (N + 1) where
  start := 0
  pivot := i.1
  stop := i.1 + 1
  start_le_pivot := by omega
  pivot_lt_stop := by omega
  stop_lt := by omega

/-- The full suffix beginning with the adjacent pair indexed by `i`. -/
def suffixPairLocalization (i : Fin (N + 1)) :
    AlphaLocalizationIndex (N + 1) where
  start := i.1
  pivot := i.1
  stop := N + 1
  start_le_pivot := le_rfl
  pivot_lt_stop := by omega
  stop_lt := by omega

@[simp]
theorem prefixPairLocalization_pivotFin (i : Fin (N + 1)) :
    (prefixPairLocalization i).pivotFin = i := by
  apply Fin.ext
  rfl

@[simp]
theorem suffixPairLocalization_pivotFin (i : Fin (N + 1)) :
    (suffixPairLocalization i).pivotFin = i := by
  apply Fin.ext
  rfl

/-- The two overlapping endpoint segments recover the global alpha: the
global candidate set is the union of the left and right local candidate
families, with the common half-gap and adjacent defect duplicated. -/
theorem alpha_eq_min_prefixSuffixSegmentAlpha
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    (b : GoodBONG q L (N + 2)) (i : Fin (N + 1))
    (wp : BONG.SegmentWitness b.toBONG
      (prefixPairLocalization i).start
      (prefixPairLocalization i).length
      (prefixPairLocalization i).bound)
    (ws : BONG.SegmentWitness b.toBONG
      (suffixPairLocalization i).start
      (suffixPairLocalization i).length
      (suffixPairLocalization i).bound) :
    (b.alphaValue i : WithTop ℚ) =
      min
        ((wp.toGoodBONG b.good).alphaValue
          (prefixPairLocalization i).localPivot : WithTop ℚ)
        ((ws.toGoodBONG b.good).alphaValue
          (suffixPairLocalization i).localPivot : WithTop ℚ) := by
  let p := prefixPairLocalization i
  let s := suffixPairLocalization i
  let bp := wp.toGoodBONG b.good
  let bs := ws.toGoodBONG b.good
  have hpivot : p.pivotFin = i := by
    apply Fin.ext
    rfl
  have hspivot : s.pivotFin = i := by
    apply Fin.ext
    rfl
  have hglobalPrefix := b.beli2009Lemma21_le_segmentAlpha p wp
  have hglobalSuffix := b.beli2009Lemma21_le_segmentAlpha s ws
  rw [hpivot] at hglobalPrefix
  rw [hspivot] at hglobalSuffix
  rw [b.coe_alphaValue, bp.coe_alphaValue, bs.coe_alphaValue]
  apply le_antisymm
  · exact le_min hglobalPrefix hglobalSuffix
  · unfold alpha
    apply Finset.le_min'
    intro y hy
    simp only [alphaCandidates, Finset.mem_insert, Finset.mem_union] at hy
    rcases hy with rfl | hy | hy
    · have hlocal := bp.alpha_le_halfGapCandidate p.localPivot
      rw [b.segment_halfGapCandidate_local p wp, hpivot] at hlocal
      exact (min_le_left _ _).trans hlocal
    · rcases Finset.mem_image.mp hy with ⟨j, hj, rfl⟩
      have hji : j ≤ i := by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hj
      have hstart : p.start ≤ j.1 := by
        dsimp [p, prefixPairLocalization]
        omega
      have hstop : j.1 < p.stop := by
        dsimp [p, prefixPairLocalization]
        omega
      have hjpivot : j ≤ p.pivotFin := by
        simpa only [hpivot] using hji
      have hlocalIndex :
          p.localAdjacent j hstart hstop ≤ p.localPivot := by
        change j.1 - p.start ≤ p.pivot - p.start
        change j.1 ≤ i.1 at hji
        dsimp [p, prefixPairLocalization]
        omega
      have hlocal := bp.alpha_le_leftDefectCandidate hlocalIndex
      rw [b.segment_leftDefectCandidate_local p wp j hstart hstop
        hjpivot, hpivot] at hlocal
      exact (min_le_left _ _).trans hlocal
    · rcases Finset.mem_image.mp hy with ⟨j, hj, rfl⟩
      have hij : i ≤ j := by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hj
      have hstart : s.start ≤ j.1 := by
        change i.1 ≤ j.1
        exact hij
      have hstop : j.1 < s.stop := by
        dsimp [s, suffixPairLocalization]
        exact j.isLt
      have hpivotj : s.pivotFin ≤ j := by
        simpa only [hspivot] using hij
      have hlocalIndex :
          s.localPivot ≤ s.localAdjacent j hstart hstop := by
        change s.pivot - s.start ≤ j.1 - s.start
        change i.1 ≤ j.1 at hij
        dsimp [s, suffixPairLocalization]
        omega
      have hlocal := bs.alpha_le_rightDefectCandidate hlocalIndex
      rw [b.segment_rightDefectCandidate_local s ws j hstart hstop
        hpivotj, hspivot] at hlocal
      exact (min_le_right _ _).trans hlocal

/-- A segment replacement carries the local literal binary alpha at the
localized pivot to the corresponding global adjacent index. -/
theorem adjacentBinaryAlpha_eq_of_segmentReplacement
    (b : GoodBONG q L (N + 2)) (s : AlphaLocalizationIndex (N + 1))
    (w : BONG.SegmentWitness b.toBONG s.start s.length s.bound)
    (c : GoodBONG (q.restrict w.carrier w.nondegenerate)
      w.lattice s.length)
    (R : BONG.SegmentReplacementWitness b.toBONG w c.toBONG) :
    (⟨R.bong, R.good⟩ : GoodBONG q L (N + 2)).adjacentBinaryAlpha
        s.pivotFin =
      c.adjacentBinaryAlpha s.localPivot := by
  let transformed : GoodBONG q L (N + 2) := ⟨R.bong, R.good⟩
  have hsourceBound (j : Fin s.length) :
      s.start + j.1 < N + 2 :=
    (Nat.add_lt_add_left j.isLt s.start).trans_le s.bound
  let sourceIndex (j : Fin s.length) : Fin (N + 2) :=
    ⟨s.start + j.1, hsourceBound j⟩
  have hinsideValue (j : Fin s.length) :
      transformed.valueUnit (sourceIndex j) =
        c.valueUnit j := by
    apply Units.ext
    change R.bong.value (sourceIndex j) = c.toBONG.value j
    rw [← R.bong.quadratic_ambientVector,
      ← c.toBONG.quadratic_ambientVector]
    have hinside : R.bong.ambientVector (sourceIndex j) =
        (c.toBONG.ambientVector j : V) := by
      simpa only [sourceIndex] using R.inside_eq j
    exact congrArg q.quadratic hinside
  have hcastIndex :
      sourceIndex s.localPivot.castSucc =
        s.pivotFin.castSucc := by
    apply Fin.ext
    change s.start + (s.pivot - s.start) = s.pivot
    have hstart := s.start_le_pivot
    omega
  have hsuccIndex :
      sourceIndex s.localPivot.succ =
        s.pivotFin.succ := by
    apply Fin.ext
    change s.start + (s.pivot - s.start + 1) = s.pivot + 1
    have hstart := s.start_le_pivot
    omega
  have hvalue0 : transformed.valueUnit s.pivotFin.castSucc =
      c.valueUnit s.localPivot.castSucc := by
    rw [← hcastIndex]
    exact hinsideValue s.localPivot.castSucc
  have hvalue1 : transformed.valueUnit s.pivotFin.succ =
      c.valueUnit s.localPivot.succ := by
    rw [← hsuccIndex]
    exact hinsideValue s.localPivot.succ
  have horder0 : transformed.order s.pivotFin.castSucc =
      c.order s.localPivot.castSucc := by
    unfold GoodBONG.order
    rw [transformed.toBONG.order_eq_ordUnit, c.toBONG.order_eq_ordUnit]
    exact congrArg (ordUnit K) hvalue0
  have horder1 : transformed.order s.pivotFin.succ =
      c.order s.localPivot.succ := by
    unfold GoodBONG.order
    rw [transformed.toBONG.order_eq_ordUnit, c.toBONG.order_eq_ordUnit]
    exact congrArg (ordUnit K) hvalue1
  have hadjacent : transformed.adjacentDefect s.pivotFin =
      c.adjacentDefect s.localPivot := by
    unfold adjacentDefect adjacentProduct
    rw [hvalue0, hvalue1]
  unfold adjacentBinaryAlpha halfGapCandidate leftDefectCandidate
  rw [horder0, horder1, hadjacent]

/-- The output normal form at an arbitrary adjacent index. -/
structure Beli2019Corollary811Data
    (b : GoodBONG q L (N + 2)) (i : Fin (N + 1)) where
  transformed : GoodBONG q L (N + 2)
  adjacentBinaryAlpha_eq :
    transformed.adjacentBinaryAlpha i =
      (transformed.alphaValue i : WithTop ℚ)

/-- Reverse duality identifies the first literal binary alpha with the last
literal binary alpha of the original BONG. -/
theorem firstBinaryAlpha_eq_lastBinaryAlpha_of_reverseDual
    (b : GoodBONG q L (N + 2))
    (c : GoodBONG q (Lattice.dualLattice q L) (N + 2))
    (hvalues : ∀ j,
      c.valueUnit j = (b.valueUnit (Fin.rev j))⁻¹)
    (horders : ∀ j, c.order j = -b.order (Fin.rev j)) :
    c.firstBinaryAlpha = b.lastBinaryAlpha := by
  have hrevCast : Fin.rev ((0 : Fin (N + 1)).castSucc) =
      Fin.last (N + 1) := by
    apply Fin.ext
    simp
  have hrevSucc : Fin.rev ((0 : Fin (N + 1)).succ) =
      (Fin.last N).castSucc := by
    apply Fin.ext
    simp
  have hlastSucc : (Fin.last N).succ = Fin.last (N + 1) := by
    apply Fin.ext
    simp
  have hdefect : c.adjacentDefect (0 : Fin (N + 1)) =
      b.adjacentDefect (Fin.last N) := by
    unfold adjacentDefect adjacentProduct
    rw [hvalues, hvalues, hrevCast, hrevSucc, hlastSucc]
    have hproduct :
        -((b.valueUnit (Fin.last (N + 1)))⁻¹ *
          (b.valueUnit (Fin.last N).castSucc)⁻¹) =
        (-(b.valueUnit (Fin.last N).castSucc *
          b.valueUnit (Fin.last (N + 1))))⁻¹ := by
      rw [inv_neg, mul_inv_rev]
    rw [hproduct]
    exact defectOrder_inv _
  unfold firstBinaryAlpha lastBinaryAlpha adjacentBinaryAlpha
  unfold halfGapCandidate leftDefectCandidate
  rw [horders, horders, hrevCast, hrevSucc, hlastSucc, hdefect]
  rw [show
    -b.order (Fin.last N).castSucc -
        -b.order (Fin.last (N + 1)) =
      b.order (Fin.last (N + 1)) -
        b.order (Fin.last N).castSucc by ring]

/-- The opposite endpoint form of the same reverse-duality identity. -/
theorem lastBinaryAlpha_eq_firstBinaryAlpha_of_reverseDual
    (b : GoodBONG q L (N + 2))
    (c : GoodBONG q (Lattice.dualLattice q L) (N + 2))
    (hvalues : ∀ j,
      c.valueUnit j = (b.valueUnit (Fin.rev j))⁻¹)
    (horders : ∀ j, c.order j = -b.order (Fin.rev j)) :
    c.lastBinaryAlpha = b.firstBinaryAlpha := by
  have hvalues' : ∀ j,
      b.valueUnit j = (c.valueUnit (Fin.rev j))⁻¹ := by
    intro j
    rw [hvalues, Fin.rev_rev, inv_inv]
  have horders' : ∀ j, b.order j = -c.order (Fin.rev j) := by
    intro j
    rw [horders, Fin.rev_rev]
    ring
  let hbidual : L = Lattice.dualLattice q (Lattice.dualLattice q L) :=
    (Lattice.dualLattice_dualLattice q L).symm
  let b' : GoodBONG q
      (Lattice.dualLattice q (Lattice.dualLattice q L)) (N + 2) :=
    b.castLattice hbidual
  have hvalues'' : ∀ j,
      b'.valueUnit j = (c.valueUnit (Fin.rev j))⁻¹ := by
    intro j
    simpa only [b', valueUnit_castLattice] using hvalues' j
  have horders'' : ∀ j, b'.order j = -c.order (Fin.rev j) := by
    intro j
    simpa only [b', order_castLattice] using horders' j
  have h := c.firstBinaryAlpha_eq_lastBinaryAlpha_of_reverseDual
    b' hvalues'' horders''
  simpa only [b', firstBinaryAlpha_castLattice] using h.symm

/-- The right-endpoint normal form dual to Corollary 8.10. -/
structure Beli2019Corollary810RightData
    (b : GoodBONG q L (N + 2)) where
  transformed : GoodBONG q L (N + 2)
  lastValue_eq :
    transformed.valueUnit (Fin.last (N + 1)) =
      b.valueUnit (Fin.last (N + 1))
  lastBinaryAlpha_eq :
    transformed.lastBinaryAlpha =
      (transformed.alphaValue (Fin.last N) : WithTop ℚ)

/-- Dual Corollary 8.10: after changing the prefix, the last literal binary
segment realizes the final alpha. -/
theorem beli2019Corollary810_right
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
    (b : GoodBONG q L (N + 2)) :
    Nonempty b.Beli2019Corollary810RightData := by
  rcases b.exists_reverseDual_with_alpha with
    ⟨c, _hcVectors, hcValuesRaw, hcOrders, _hcAlphas⟩
  have hcValues : ∀ j,
      c.valueUnit j = (b.valueUnit (Fin.rev j))⁻¹ := by
    intro j
    change c.toBONG.valueUnit j =
      (b.toBONG.valueUnit (Fin.rev j))⁻¹
    apply Units.ext
    exact hcValuesRaw j
  rcases c.beli2019Corollary810 with ⟨D⟩
  rcases D.transformed.exists_reverseDual_with_alpha with
    ⟨e, _heVectors, heValuesRaw, heOrders, heAlphas⟩
  have heValues : ∀ j,
      e.valueUnit j = (D.transformed.valueUnit (Fin.rev j))⁻¹ := by
    intro j
    change e.toBONG.valueUnit j =
      (D.transformed.toBONG.valueUnit (Fin.rev j))⁻¹
    apply Units.ext
    exact heValuesRaw j
  let hbidual : Lattice.dualLattice q (Lattice.dualLattice q L) = L :=
    Lattice.dualLattice_dualLattice q L
  let transformed : GoodBONG q L (N + 2) := e.castLattice hbidual
  have hrevLastValue : Fin.rev (Fin.last (N + 1)) =
      (0 : Fin (N + 2)) := by
    apply Fin.ext
    simp
  have hrevLastAlpha : Fin.rev (Fin.last N) =
      (0 : Fin (N + 1)) := by
    apply Fin.ext
    simp
  have hlastValue : transformed.valueUnit (Fin.last (N + 1)) =
      b.valueUnit (Fin.last (N + 1)) := by
    simp only [transformed, valueUnit_castLattice]
    rw [heValues, hrevLastValue, D.headValue_eq, hcValues]
    have hrevZero : Fin.rev (0 : Fin (N + 2)) =
        Fin.last (N + 1) := by
      apply Fin.ext
      simp
    rw [hrevZero, inv_inv]
  have hlastBinary : transformed.lastBinaryAlpha =
      (transformed.alphaValue (Fin.last N) : WithTop ℚ) := by
    simp only [transformed, lastBinaryAlpha,
      adjacentBinaryAlpha_castLattice, alphaValue_castLattice]
    calc
      e.lastBinaryAlpha = D.transformed.firstBinaryAlpha :=
        D.transformed.lastBinaryAlpha_eq_firstBinaryAlpha_of_reverseDual
          e heValues heOrders
      _ = (D.transformed.alphaValue (0 : Fin (N + 1)) : WithTop ℚ) :=
        D.firstBinaryAlpha_eq
      _ = (e.alphaValue (Fin.last N) : WithTop ℚ) := by
        rw [heAlphas, hrevLastAlpha]
  exact ⟨{
    transformed := transformed
    lastValue_eq := hlastValue
    lastBinaryAlpha_eq := hlastBinary
  }⟩

/-- Beli (2019), Corollary 8.11: for every adjacent index, some good BONG
of the same lattice makes the global alpha occur on that literal binary
segment. -/
theorem beli2019Corollary811
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
    (b : GoodBONG q L (N + 2)) (i : Fin (N + 1)) :
    Nonempty (b.Beli2019Corollary811Data i) := by
  classical
  let p := prefixPairLocalization i
  let s := suffixPairLocalization i
  rcases b.toBONG.exists_segmentWitness p.start p.length p.bound with ⟨wp⟩
  rcases b.toBONG.exists_segmentWitness s.start s.length s.bound with ⟨ws⟩
  let bp := wp.toGoodBONG b.good
  let bs := ws.toGoodBONG b.good
  have hmin : (b.alphaValue i : WithTop ℚ) =
      min (bp.alphaValue p.localPivot : WithTop ℚ)
        (bs.alphaValue s.localPivot : WithTop ℚ) := by
    simpa only [p, s, bp, bs] using
      b.alpha_eq_min_prefixSuffixSegmentAlpha i wp ws
  rcases le_total
      (bp.alphaValue p.localPivot : WithTop ℚ)
      (bs.alphaValue s.localPivot : WithTop ℚ) with hprefix | hsuffix
  · have hchosen : (b.alphaValue i : WithTop ℚ) =
        (bp.alphaValue p.localPivot : WithTop ℚ) :=
      hmin.trans (min_eq_left hprefix)
    have hpDiff : p.stop - p.start = i.1 + 1 := by
      dsimp [p, prefixPairLocalization]
    let hpRank : p.length = (i.1 + 1) + 1 :=
      congrArg (fun k => k + 1) hpDiff
    let bpExact : GoodBONG
        (q.restrict wp.carrier wp.nondegenerate) wp.lattice
        ((i.1 + 1) + 1) :=
      bp.castLength hpRank
    rcases bpExact.beli2019Corollary810_right with ⟨D⟩
    let c : GoodBONG
        (q.restrict wp.carrier wp.nondegenerate) wp.lattice p.length :=
      D.transformed.castLength hpRank.symm
    have hsegmentAlphas := bpExact.alpha_invariant D.transformed
    have hc : c.adjacentBinaryAlpha p.localPivot =
        (bp.alphaValue p.localPivot : WithTop ℚ) := by
      calc
        c.adjacentBinaryAlpha p.localPivot =
            D.transformed.adjacentBinaryAlpha
              (Fin.cast (hpDiff.symm).symm p.localPivot) :=
          D.transformed.adjacentBinaryAlpha_castLength
            hpDiff.symm p.localPivot
        _ = D.transformed.lastBinaryAlpha :=
          congrArg D.transformed.adjacentBinaryAlpha (Eq.refl _)
        _ = (D.transformed.alphaValue (Fin.last i.1) : WithTop ℚ) :=
          D.lastBinaryAlpha_eq
        _ = (bp.alphaValue p.localPivot : WithTop ℚ) :=
          congrArg (fun x : ℚ => (x : WithTop ℚ))
            (hsegmentAlphas (Fin.last i.1)).symm
    rcases b.toBONG.beliLemma49_ii b.good wp c.toBONG c.good with ⟨R⟩
    let transformed : GoodBONG q L (N + 2) := ⟨R.bong, R.good⟩
    have hpivot : p.pivotFin = i := Eq.refl _
    have hinside := b.adjacentBinaryAlpha_eq_of_segmentReplacement p wp c R
    rw [hpivot] at hinside
    have hglobalAlphas := b.alpha_invariant transformed
    exact ⟨{
      transformed := transformed
      adjacentBinaryAlpha_eq := by
        calc
          transformed.adjacentBinaryAlpha i =
              c.adjacentBinaryAlpha p.localPivot := hinside
          _ = (bp.alphaValue p.localPivot : WithTop ℚ) := hc
          _ = (b.alphaValue i : WithTop ℚ) := hchosen.symm
          _ = (transformed.alphaValue i : WithTop ℚ) :=
            congrArg (fun x : ℚ => (x : WithTop ℚ)) (hglobalAlphas i)
    }⟩
  · have hchosen : (b.alphaValue i : WithTop ℚ) =
        (bs.alphaValue s.localPivot : WithTop ℚ) :=
      hmin.trans (min_eq_right hsuffix)
    have hsDiff : s.stop - s.start = (N - i.1) + 1 := by
      dsimp [s, suffixPairLocalization]
      omega
    let hsRank : s.length = ((N - i.1) + 1) + 1 :=
      congrArg (fun k => k + 1) hsDiff
    let bsExact : GoodBONG
        (q.restrict ws.carrier ws.nondegenerate) ws.lattice
        (((N - i.1) + 1) + 1) :=
      bs.castLength hsRank
    rcases bsExact.beli2019Corollary810 with ⟨D⟩
    let c : GoodBONG
        (q.restrict ws.carrier ws.nondegenerate) ws.lattice s.length :=
      D.transformed.castLength hsRank.symm
    have hlocalZero : Fin.cast hsDiff s.localPivot =
        (0 : Fin ((N - i.1) + 1)) := by
      apply Fin.ext
      dsimp [s, suffixPairLocalization, AlphaLocalizationIndex.localPivot]
      omega
    have hzeroLocal : Fin.cast hsDiff.symm
        (0 : Fin ((N - i.1) + 1)) = s.localPivot := by
      apply Fin.ext
      dsimp [s, suffixPairLocalization, AlphaLocalizationIndex.localPivot]
      omega
    have hsegmentAlphas := bsExact.alpha_invariant D.transformed
    have hlocalZero' : Fin.cast (hsDiff.symm).symm s.localPivot =
        (0 : Fin ((N - i.1) + 1)) := by
      apply Fin.ext
      change i.1 - i.1 = 0
      omega
    have htransportAlpha : bsExact.alphaValue
        (0 : Fin ((N - i.1) + 1)) = bs.alphaValue s.localPivot := by
      calc
        bsExact.alphaValue (0 : Fin ((N - i.1) + 1)) =
            (bs.castLength
              (congrArg (fun k => k + 1) hsDiff)).alphaValue
                (0 : Fin ((N - i.1) + 1)) := rfl
        _ = bs.alphaValue (Fin.cast hsDiff.symm
            (0 : Fin ((N - i.1) + 1))) :=
          alphaValue_castLength' bs hsDiff
            (0 : Fin ((N - i.1) + 1))
        _ = bs.alphaValue s.localPivot := congrArg bs.alphaValue hzeroLocal
    have hc : c.adjacentBinaryAlpha s.localPivot =
        (bs.alphaValue s.localPivot : WithTop ℚ) := by
      calc
        c.adjacentBinaryAlpha s.localPivot =
            D.transformed.adjacentBinaryAlpha
              (Fin.cast (hsDiff.symm).symm s.localPivot) :=
          D.transformed.adjacentBinaryAlpha_castLength
            hsDiff.symm s.localPivot
        _ = D.transformed.firstBinaryAlpha :=
          congrArg D.transformed.adjacentBinaryAlpha hlocalZero'
        _ = (D.transformed.alphaValue
            (0 : Fin ((N - i.1) + 1)) : WithTop ℚ) :=
          D.firstBinaryAlpha_eq
        _ = (bsExact.alphaValue
            (0 : Fin ((N - i.1) + 1)) : WithTop ℚ) :=
          congrArg (fun x : ℚ => (x : WithTop ℚ))
            (hsegmentAlphas (0 : Fin ((N - i.1) + 1))).symm
        _ = (bs.alphaValue
            s.localPivot : WithTop ℚ) := by
          exact congrArg (fun x : ℚ => (x : WithTop ℚ)) htransportAlpha
    rcases b.toBONG.beliLemma49_ii b.good ws c.toBONG c.good with ⟨R⟩
    let transformed : GoodBONG q L (N + 2) := ⟨R.bong, R.good⟩
    have hspivot : s.pivotFin = i := Eq.refl _
    have hinside := b.adjacentBinaryAlpha_eq_of_segmentReplacement s ws c R
    rw [hspivot] at hinside
    have hglobalAlphas := b.alpha_invariant transformed
    exact ⟨{
      transformed := transformed
      adjacentBinaryAlpha_eq := by
        calc
          transformed.adjacentBinaryAlpha i =
              c.adjacentBinaryAlpha s.localPivot := hinside
          _ = (bs.alphaValue s.localPivot : WithTop ℚ) := hc
          _ = (b.alphaValue i : WithTop ℚ) := hchosen.symm
          _ = (transformed.alphaValue i : WithTop ℚ) :=
            congrArg (fun x : ℚ => (x : WithTop ℚ)) (hglobalAlphas i)
    }⟩

end BONG.GoodBONG

end Bong
