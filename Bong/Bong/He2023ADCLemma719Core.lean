/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma710BONGProduct
import Bong.Bong.Beli2019Lemma79OrderTypeIIISourceAlpha
import Bong.Bong.He2023ADCTheorem74

/-!
# He (2025), Lemma 7.19: the unary-extension calculation

This file isolates the invariant calculation used in Lemma 7.19.  A maximal
even-rank row whose final binary block has orders `0, 1-d` and adjacent
defect `d` is extended by a unary row of order zero or one.  The resulting
good BONG satisfies all four clauses of Theorem 7.4.
-/

namespace Bong

open Dyadic Module

universe u

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type u} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- The exact part of the maximal even-rank profile used in Lemma 7.19. -/
structure HeADC719BaseConditions (k : Nat) (d : Int)
    (b : GoodBONG q L (2 * k + 4)) : Prop where
  initial : b.HeHuI1E (2 * k + 2) (by omega)
  last : b.order ⟨2 * k + 3, by omega⟩ = 1 - d
  adjacent : b.adjacentDefect ⟨2 * k + 2, by omega⟩ =
    (((d : Int) : ℚ) : WithTop ℚ)

/-- The paper's numerical hypotheses imply that the unary extension is a
good BONG. -/
private theorem heADC2025Lemma719_boundaryBounds (k : Nat) (d : Int)
    (c : Kˣ) (b : GoodBONG q L (2 * k + 4))
    (B : HeADC719BaseConditions k d b)
    (hdOdd : Odd d) (hdNonnegative : 0 ≤ d)
    (hcOrder : ordUnit K c = 0 ∨ ordUnit K c = 1) :
    b.order ⟨2 * k + 2, by omega⟩ ≤
        (BONG.unaryModelGoodBONG c).order 0 ∧
      b.order ⟨2 * k + 3, by omega⟩ ≤
        (BONG.unaryModelGoodBONG c).order 0 := by
  have hzero : b.order ⟨2 * k + 2, by omega⟩ = 0 := by
    apply B.initial.1 ⟨2 * k + 2, by omega⟩
    change Odd (2 * k + 3)
    exact ⟨k + 1, by omega⟩
  have hdPositive : 1 ≤ d := by
    rcases hdOdd with ⟨z, hz⟩
    omega
  rw [BONG.unaryModelGoodBONG_order]
  rcases hcOrder with hc | hc <;> rw [hc]
  · rw [hzero, B.last]
    omega
  · rw [hzero, B.last]
    omega

/-- Append the unary row occurring in Lemma 7.19. -/
noncomputable def heADC2025Lemma719Append (k : Nat) (d : Int)
    (c : Kˣ) (b : GoodBONG q L (2 * k + 4))
    (B : HeADC719BaseConditions k d b)
    (hdOdd : Odd d) (hdNonnegative : 0 ≤ d)
    (hcOrder : ordUnit K c = 0 ∨ ordUnit K c = 1) :
    GoodBONG
      (q.orthogonalSum
        ((QuadraticSpace.line K).rescaleUnit c))
      (Lattice.product L (BONG.unaryModelLattice (K := K)))
      (2 * k + 5) := by
  let x := BONG.unaryModelGoodBONG c
  have H := heADC2025Lemma719_boundaryBounds k d c b B
    hdOdd hdNonnegative hcOrder
  have Hpenultimate : b.order ⟨2 * k + 4 - 2, by omega⟩ ≤ x.order 0 := by
    simpa only [show 2 * k + 4 - 2 = 2 * k + 2 by omega] using H.1
  have Hlast : b.order ⟨2 * k + 4 - 1, by omega⟩ ≤ x.order 0 := by
    simpa only [show 2 * k + 4 - 1 = 2 * k + 3 by omega] using H.2
  let raw := b.orthogonalProductRight_of_endpointBounds x
    (by omega) Hpenultimate Hlast (fun hm ↦ by omega)
  exact raw.castLength (by omega)

@[simp]
theorem heADC2025Lemma719Append_order_left (k : Nat) (d : Int)
    (c : Kˣ) (b : GoodBONG q L (2 * k + 4))
    (B : HeADC719BaseConditions k d b)
    (hdOdd : Odd d) (hdNonnegative : 0 ≤ d)
    (hcOrder : ordUnit K c = 0 ∨ ordUnit K c = 1)
    (i : Fin (2 * k + 4)) :
    (heADC2025Lemma719Append k d c b B hdOdd hdNonnegative hcOrder).order
        ⟨i.val, by omega⟩ = b.order i := by
  unfold heADC2025Lemma719Append
  rw [order_castLength]
  have hindex : (⟨i.val, by omega⟩ : Fin (1 + (2 * k + 4))) =
      BONG.orthogonalProductLeftIndex 1 i := Fin.ext (by rfl)
  rw [hindex]
  apply order_orthogonalProductRight_left

@[simp]
theorem heADC2025Lemma719Append_order_last (k : Nat) (d : Int)
    (c : Kˣ) (b : GoodBONG q L (2 * k + 4))
    (B : HeADC719BaseConditions k d b)
    (hdOdd : Odd d) (hdNonnegative : 0 ≤ d)
    (hcOrder : ordUnit K c = 0 ∨ ordUnit K c = 1) :
    (heADC2025Lemma719Append k d c b B hdOdd hdNonnegative hcOrder).order
        ⟨2 * k + 4, by omega⟩ = ordUnit K c := by
  unfold heADC2025Lemma719Append
  rw [order_castLength]
  have hindex : (⟨2 * k + 4, by omega⟩ : Fin (1 + (2 * k + 4))) =
      BONG.orthogonalProductRightIndex (2 * k + 4) (0 : Fin 1) := by
    apply Fin.ext
    simp
  rw [hindex]
  change ordUnit K
      ((b.orthogonalProductRight_of_endpointBounds
        (BONG.unaryModelGoodBONG c) _ _ _ _).valueUnit
          (BONG.orthogonalProductRightIndex (2 * k + 4) (0 : Fin 1))) =
    ordUnit K c
  rw [valueUnit_orthogonalProductRight_of_endpointBounds_right]
  exact BONG.unaryModelGoodBONG_order c

/-- The adjacent defect at the old final binary edge is unchanged after
adjoining the unary row. -/
theorem heADC2025Lemma719Append_adjacent (k : Nat) (d : Int)
    (c : Kˣ) (b : GoodBONG q L (2 * k + 4))
    (B : HeADC719BaseConditions k d b)
    (hdOdd : Odd d) (hdNonnegative : 0 ≤ d)
    (hcOrder : ordUnit K c = 0 ∨ ordUnit K c = 1) :
    adjacentDefect
        (heADC2025Lemma719Append k d c b B hdOdd hdNonnegative hcOrder)
        ⟨2 * k + 2, by omega⟩ =
      (((d : Int) : ℚ) : WithTop ℚ) := by
  let a := heADC2025Lemma719Append k d c b B hdOdd hdNonnegative hcOrder
  have hfirst : a.valueUnit ⟨2 * k + 2, by omega⟩ =
      b.valueUnit ⟨2 * k + 2, by omega⟩ := by
    unfold a heADC2025Lemma719Append
    rw [valueUnit_castLength_heHu]
    have hindex : (⟨2 * k + 2, by omega⟩ : Fin (1 + (2 * k + 4))) =
        BONG.orthogonalProductLeftIndex 1
          (⟨2 * k + 2, by omega⟩ : Fin (2 * k + 4)) := Fin.ext (by rfl)
    rw [hindex]
    apply valueUnit_orthogonalProductRight_of_endpointBounds_left
  have hsecond : a.valueUnit ⟨2 * k + 3, by omega⟩ =
      b.valueUnit ⟨2 * k + 3, by omega⟩ := by
    unfold a heADC2025Lemma719Append
    rw [valueUnit_castLength_heHu]
    have hindex : (⟨2 * k + 3, by omega⟩ : Fin (1 + (2 * k + 4))) =
        BONG.orthogonalProductLeftIndex 1
          (⟨2 * k + 3, by omega⟩ : Fin (2 * k + 4)) := Fin.ext (by rfl)
    rw [hindex]
    apply valueUnit_orthogonalProductRight_of_endpointBounds_left
  let boundary : Fin (2 * k + 4) := ⟨2 * k + 2, by omega⟩
  have hcast : boundary.castSucc =
      (⟨2 * k + 2, by omega⟩ : Fin (2 * k + 5)) := Fin.ext (by rfl)
  have hsucc : boundary.succ =
      (⟨2 * k + 3, by omega⟩ : Fin (2 * k + 5)) := Fin.ext (by rfl)
  let baseBoundary : Fin (2 * k + 3) := ⟨2 * k + 2, by omega⟩
  have hbcast : baseBoundary.castSucc =
      (⟨2 * k + 2, by omega⟩ : Fin (2 * k + 4)) := Fin.ext (by rfl)
  have hbsucc : baseBoundary.succ =
      (⟨2 * k + 3, by omega⟩ : Fin (2 * k + 4)) := Fin.ext (by rfl)
  have hbaseAdjacent : defectOrder (K := K)
      (-(b.valueUnit ⟨2 * k + 2, by omega⟩ *
        b.valueUnit ⟨2 * k + 3, by omega⟩)) =
      (((d : Int) : ℚ) : WithTop ℚ) := by
    rw [← hbcast, ← hbsucc]
    simpa only [adjacentDefect, adjacentProduct, baseBoundary] using B.adjacent
  unfold adjacentDefect adjacentProduct
  rw [show (⟨2 * k + 2, by omega⟩ : Fin (2 * k + 4)) = boundary by rfl,
    hcast, hsucc, hfirst, hsecond]
  exact hbaseAdjacent

/-- He (2025), Lemma 7.19, invariant core: the appended lattice is
`n`-ADC for `n = 2k+3`. -/
theorem heADC2025Lemma719Core (k : Nat) (d : Int)
    (c : Kˣ) (b : GoodBONG q L (2 * k + 4))
    (B : HeADC719BaseConditions k d b)
    (hdOdd : Odd d) (hdNonnegative : 0 ≤ d)
    (hdLt : d < 2 * (ramificationIndex K : Int))
    (hcOrder : ordUnit K c = 0 ∨ ordUnit K c = 1) :
    Lattice.IsNADC.{u, u, u}
      (q.orthogonalSum ((QuadraticSpace.line K).rescaleUnit c))
      (Lattice.product L (BONG.unaryModelLattice (K := K)))
      (2 * k + 3) := by
  let a := heADC2025Lemma719Append k d c b B hdOdd
    hdNonnegative hcOrder
  apply a.heADC2025Theorem74Sufficiency k
  have hleft (i : Fin (2 * k + 4)) :
      a.order ⟨i.val, by omega⟩ = b.order i := by
    exact heADC2025Lemma719Append_order_left k d c b B hdOdd
      hdNonnegative hcOrder i
  have hzero : a.order ⟨2 * k + 2, by omega⟩ = 0 := by
    rw [hleft ⟨2 * k + 2, by omega⟩]
    apply B.initial.1 ⟨2 * k + 2, by omega⟩
    change Odd (2 * k + 3)
    exact ⟨k + 1, by omega⟩
  have hpenultimate : a.order ⟨2 * k + 3, by omega⟩ = 1 - d := by
    rw [hleft ⟨2 * k + 3, by omega⟩, B.last]
  have hgapConcrete : a.order ⟨2 * k + 3, by omega⟩ -
      a.order ⟨2 * k + 2, by omega⟩ = 1 - d
      := by
    rw [hzero, hpenultimate]
    omega
  have hgap : a.orderGap ⟨2 * k + 2, by omega⟩ = 1 - d := by
    unfold orderGap
    change a.order ⟨2 * k + 3, by omega⟩ -
      a.order ⟨2 * k + 2, by omega⟩ = 1 - d
    exact hgapConcrete
  have halphaUpper : a.alphaValue ⟨2 * k + 2, by omega⟩ ≤ 1 := by
    let boundary : Fin (2 * k + 4) := ⟨2 * k + 2, by omega⟩
    have hcandidate := a.alpha_le_leftDefectCandidate
      (i := boundary) (j := boundary) le_rfl
    rw [← a.coe_alphaValue] at hcandidate
    unfold leftDefectCandidate at hcandidate
    have hgap' : a.order boundary.succ - a.order boundary.castSucc =
        1 - d := by
      change a.order ⟨2 * k + 3, by omega⟩ -
        a.order ⟨2 * k + 2, by omega⟩ = 1 - d
      exact hgapConcrete
    rw [hgap',
      heADC2025Lemma719Append_adjacent k d c b B hdOdd
        hdNonnegative hcOrder] at hcandidate
    norm_cast at hcandidate
    push_cast at hcandidate
    linarith
  have halphaNe : a.alphaValue ⟨2 * k + 2, by omega⟩ ≠ 0 := by
    intro hzeroAlpha
    have hzeroGap :=
      (a.beli2009Lemma27_i ⟨2 * k + 2, by omega⟩).2.mp hzeroAlpha
    rw [hgap] at hzeroGap
    omega
  have halphaLower : (1 : ℚ) ≤
      a.alphaValue ⟨2 * k + 2, by omega⟩ :=
    a.one_le_alphaValue_of_ne_zero ⟨2 * k + 2, by omega⟩ halphaNe
  refine
    { initial := ?_
      penultimate := ?_
      last := ?_
      alpha := Or.inr (le_antisymm halphaUpper halphaLower) }
  · constructor
    · intro i hi
      rw [hleft ⟨i.val, by omega⟩]
      exact B.initial.1 i hi
    · intro i hi
      rw [hleft ⟨i.val, by omega⟩]
      exact B.initial.2 i hi
  · refine ⟨?_, ?_, ?_⟩
    · rw [hpenultimate]
      rcases hdOdd with ⟨z, hz⟩
      exact ⟨-z, by omega⟩
    · rw [hpenultimate]
      omega
    · rw [hpenultimate]
      rcases hdOdd with ⟨z, hz⟩
      omega
  · rw [heADC2025Lemma719Append_order_last]
    exact hcOrder

end BONG.GoodBONG

end Bong
