/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma710BONGProduct

/-!
# Beli (2019), Lemma 7.10: adjoining an internal BONG prefix

The right-end case of Lemma 7.10 does not split the first lattice into an
integral orthogonal product at the replacement point.  Instead it starts
with the replaced tail and adjoins the unchanged vectors
`x_(s-1), ..., x_1` one at a time.

`OrthogonalPrefixData` is the dependent certificate for that construction.
Its `stop` constructor accepts an arbitrary replacement BONG on the product
of the current projected lattice with the external right lattice.  Its
`cons` constructor performs one paper-style decreasing-induction step.  The
projection-product isometry keeps the recursive tail in the exact subtype
required by `BONG.cons`.
-/

namespace Bong

open Dyadic

namespace BONG

universe u v w

/-- A finite unchanged prefix together with a replacement BONG at its
projected tail.  `steps` is the number of original heads to be adjoined and
`baseLength` is the length of the replacement tail. -/
inductive OrthogonalPrefixData
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    {W : Type w} [AddCommGroup W] [Module K W]
    (r : QuadraticSpace K W) (M : Lattice K W) (baseLength : Nat) :
    {V : Type v} → [AddCommGroup V] → [Module K V] →
    {q : QuadraticSpace K V} → {L : Lattice K V} → {n steps : Nat} →
    BONG V q L n → Type (max (u + 1) (v + 1) (w + 1))
  | stop
      {V : Type v} [AddCommGroup V] [Module K V]
      {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
      (b : BONG V q L n)
      (base : BONG (V × W) (q.orthogonalSum r)
        (Lattice.product L M) baseLength) :
      OrthogonalPrefixData r M baseLength (steps := 0) b
  | cons
      {V : Type v} [AddCommGroup V] [Module K V]
      {q : QuadraticSpace K V} {L : Lattice K V} {n steps : Nat}
      {x : V}
      (generator : Lattice.IsNormGenerator q L x)
      (anisotropic : q.IsAnisotropic x)
      (tail : BONG (q.vectorOrthogonal x)
        (q.orthogonalSpace x anisotropic)
        (L.projectedLattice q x anisotropic) n)
      (rightNorm_le : Lattice.normIdeal r M ≤ Lattice.normIdeal q L)
      (tailData : OrthogonalPrefixData r M baseLength
        (steps := steps) tail) :
      OrthogonalPrefixData r M baseLength (steps := steps + 1)
        (BONG.cons x generator anisotropic tail)

namespace OrthogonalPrefixData

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}
  {n steps baseLength : Nat} {b : BONG V q L n}

/-- Adjoin one source head using the paper's order comparison rather than a
manually supplied containment of norm ideals.  The right BONG is used only
to expose the norm ideal of the fixed external lattice through its head. -/
noncomputable def consOfHeadOrder
    {rightLength : Nat}
    {x : V}
    (generator : Lattice.IsNormGenerator q L x)
    (anisotropic : q.IsAnisotropic x)
    (tail : BONG (q.vectorOrthogonal x)
      (q.orthogonalSpace x anisotropic)
      (L.projectedLattice q x anisotropic) n)
    (right : BONG W r M (rightLength + 1))
    (horder :
      (BONG.cons x generator anisotropic tail).order 0 ≤ right.order 0)
    (tailData : OrthogonalPrefixData r M baseLength
      (steps := steps) tail) :
    OrthogonalPrefixData r M baseLength (steps := steps + 1)
      (BONG.cons x generator anisotropic tail) :=
  .cons generator anisotropic tail
    (normIdeal_le_of_head_order_le
      (BONG.cons x generator anisotropic tail) right horder)
    tailData

/-- The actual BONG obtained by adjoining the certified prefix to the
replacement tail. -/
noncomputable def result
    (D : OrthogonalPrefixData r M baseLength (steps := steps) b) :
    BONG (V × W) (q.orthogonalSum r) (Lattice.product L M)
      (baseLength + steps) := by
  induction D with
  | stop _ base =>
      exact base
  | @cons V _ _ q L n steps x generator anisotropic tail
      rightNorm_le tailData tailResult =>
      let productGenerator :=
        generator.orthogonalProduct_left rightNorm_le
      let productAnisotropic := anisotropic.orthogonalSum_inl (r := r)
      let transportedTail := tailResult.mapLatticeIsometry
        (Lattice.projectedOrthogonalProductIsometry
          (q := q) (r := r) (L := L) (M := M) anisotropic).symm
      exact BONG.cons (x, 0) productGenerator productAnisotropic
        transportedTail

/-- A prefix certificate cannot adjoin more heads than the source BONG
contains. -/
theorem steps_le_length
    (D : OrthogonalPrefixData r M baseLength (steps := steps) b) :
    steps ≤ n := by
  induction D with
  | stop => simp
  | cons _ _ _ _ ih => omega

/-- The source BONG index corresponding to an adjoined prefix index. -/
def sourceIndex
    (D : OrthogonalPrefixData r M baseLength (steps := steps) b)
    (i : Fin steps) : Fin n :=
  ⟨i.val, lt_of_lt_of_le i.isLt D.steps_le_length⟩

@[simp]
theorem sourceIndex_val
    (D : OrthogonalPrefixData r M baseLength (steps := steps) b)
    (i : Fin steps) : (D.sourceIndex i).val = i.val :=
  rfl

/-- The scalar value sequence of the replacement tail stored at the stopping
point. -/
noncomputable def baseValue
    (D : OrthogonalPrefixData r M baseLength (steps := steps) b) :
    Fin baseLength → K := by
  induction D with
  | stop _ base => exact base.value
  | cons _ _ _ _ _ tailValue => exact tailValue

/-- The order sequence of the replacement tail stored at the stopping
point. -/
noncomputable def baseOrder
    (D : OrthogonalPrefixData r M baseLength (steps := steps) b) :
    Fin baseLength → Int := by
  induction D with
  | stop _ base => exact base.order
  | cons _ _ _ _ _ tailOrder => exact tailOrder

/-- The replacement-tail vectors transported back through all preceding
projection-product identifications. -/
noncomputable def baseAmbientVector
    (D : OrthogonalPrefixData r M baseLength (steps := steps) b) :
    Fin baseLength → V × W := by
  induction D with
  | stop _ base =>
      exact base.ambientVector
  | @cons V _ _ q L n steps x generator anisotropic tail
      rightNorm_le tailData tailBase =>
      exact fun i =>
        (((Lattice.projectedOrthogonalProductIsometry
            (q := q) (r := r) (L := L) (M := M)
            anisotropic).symm.toLinearEquiv (tailBase i) :
              (q.orthogonalSum r).vectorOrthogonal (x, 0)) : V × W)

/-- The adjoined prefix keeps exactly the corresponding initial values of
the source BONG. -/
@[simp]
theorem value_result_left
    (D : OrthogonalPrefixData r M baseLength (steps := steps) b)
    (i : Fin steps) :
    D.result.value (orthogonalProductLeftIndex baseLength i) =
      b.value (D.sourceIndex i) := by
  induction D with
  | stop => exact Fin.elim0 i
  | @cons V _ _ q L n steps x generator anisotropic tail
      rightNorm_le tailData ih =>
      cases i using Fin.cases with
      | zero =>
          simp [result, sourceIndex, orthogonalProductLeftIndex]
      | succ j =>
          have hleft : orthogonalProductLeftIndex baseLength j.succ =
              (orthogonalProductLeftIndex baseLength j).succ := by
            apply Fin.ext
            rfl
          have hsource :
              (OrthogonalPrefixData.cons generator anisotropic tail
                rightNorm_le tailData).sourceIndex j.succ =
                (tailData.sourceIndex j).succ := by
            apply Fin.ext
            rfl
          rw [hleft, hsource]
          simpa only [result, value_cons_succ,
            value_mapLatticeIsometry] using ih j

/-- The adjoined prefix keeps the corresponding source vectors, embedded in
the left factor of the ambient orthogonal product. -/
@[simp]
theorem ambientVector_result_left
    (D : OrthogonalPrefixData r M baseLength (steps := steps) b)
    (i : Fin steps) :
    D.result.ambientVector (orthogonalProductLeftIndex baseLength i) =
      (b.ambientVector (D.sourceIndex i), 0) := by
  induction D with
  | stop => exact Fin.elim0 i
  | @cons V _ _ q L n steps x generator anisotropic tail
      rightNorm_le tailData ih =>
      cases i using Fin.cases with
      | zero =>
          simp [result, sourceIndex, orthogonalProductLeftIndex]
      | succ j =>
          have hleft : orthogonalProductLeftIndex baseLength j.succ =
              (orthogonalProductLeftIndex baseLength j).succ := by
            apply Fin.ext
            rfl
          have hsource :
              (OrthogonalPrefixData.cons generator anisotropic tail
                rightNorm_le tailData).sourceIndex j.succ =
                (tailData.sourceIndex j).succ := by
            apply Fin.ext
            rfl
          rw [hleft, hsource]
          simp only [result, ambientVector_cons_succ]
          change
            (((tailData.result.mapLatticeIsometry
                (Lattice.projectedOrthogonalProductIsometry
                  (q := q) (r := r) (L := L) (M := M)
                  anisotropic).symm).ambientVector
              (orthogonalProductLeftIndex baseLength j) :
                (q.orthogonalSum r).vectorOrthogonal (x, 0)) : V × W) = _
          rw [BONG.ambientVector_mapLatticeIsometry, ih j]
          rfl

/-- The replacement-tail values occur unchanged after the adjoined prefix. -/
@[simp]
theorem value_result_right
    (D : OrthogonalPrefixData r M baseLength (steps := steps) b)
    (j : Fin baseLength) :
    D.result.value (orthogonalProductRightIndex steps j) =
      D.baseValue j := by
  induction D with
  | stop b base =>
      have hindex : orthogonalProductRightIndex 0 j = j := by
        apply Fin.ext
        simp [orthogonalProductRightIndex]
      rw [hindex]
      rfl
  | @cons V _ _ q L n steps x generator anisotropic tail
      rightNorm_le tailData ih =>
      have hindex : orthogonalProductRightIndex (steps + 1) j =
          (orthogonalProductRightIndex steps j).succ := by
        apply Fin.ext
        simp [orthogonalProductRightIndex]
        omega
      rw [hindex]
      simpa only [result, value_cons_succ,
        value_mapLatticeIsometry, baseValue] using ih

/-- The replacement-tail vectors in the result are precisely the vectors
stored at the stopping point, transported through the recursive projection
isometries. -/
@[simp]
theorem ambientVector_result_right
    (D : OrthogonalPrefixData r M baseLength (steps := steps) b)
    (j : Fin baseLength) :
    D.result.ambientVector (orthogonalProductRightIndex steps j) =
      D.baseAmbientVector j := by
  induction D with
  | stop b base =>
      have hindex : orthogonalProductRightIndex 0 j = j := by
        apply Fin.ext
        simp [orthogonalProductRightIndex]
      rw [hindex]
      rfl
  | @cons V _ _ q L n steps x generator anisotropic tail
      rightNorm_le tailData ih =>
      have hindex : orthogonalProductRightIndex (steps + 1) j =
          (orthogonalProductRightIndex steps j).succ := by
        apply Fin.ext
        simp [orthogonalProductRightIndex]
        omega
      rw [hindex]
      simp only [result, ambientVector_cons_succ,
        BONG.ambientVector_mapLatticeIsometry, baseAmbientVector]
      exact congrArg
        (fun z =>
          (((Lattice.projectedOrthogonalProductIsometry
              (q := q) (r := r) (L := L) (M := M)
              anisotropic).symm.toLinearEquiv z :
                (q.orthogonalSum r).vectorOrthogonal (x, 0)) : V × W))
        ih

/-- A BONG whose prefix and replacement-tail vectors agree with the
constructed prefix product belongs to the same lattice.  This is the exact
right-end lattice conclusion once the two vector blocks have been
identified. -/
theorem lattice_eq_of_matching_vectors
    {N : Lattice K (V × W)}
    (D : OrthogonalPrefixData r M baseLength (steps := steps) b)
    (target : BONG (V × W) (q.orthogonalSum r) N
      (baseLength + steps))
    (leftVectors : ∀ i : Fin steps,
      target.ambientVector (orthogonalProductLeftIndex baseLength i) =
        (b.ambientVector (D.sourceIndex i), 0))
    (rightVectors : ∀ j : Fin baseLength,
      target.ambientVector (orthogonalProductRightIndex steps j) =
        D.baseAmbientVector j) :
    N = Lattice.product L M := by
  apply target.lattice_eq_of_ambientVector_eq_from_projection D.result
  intro k
  by_cases hk : k.val < steps
  · let i : Fin steps := ⟨k.val, hk⟩
    have hindex : k = orthogonalProductLeftIndex baseLength i := by
      apply Fin.ext
      rfl
    rw [hindex, leftVectors, ambientVector_result_left]
  · let j : Fin baseLength := ⟨k.val - steps, by omega⟩
    have hindex : k = orthogonalProductRightIndex steps j := by
      apply Fin.ext
      simp [j, orthogonalProductRightIndex]
      omega
    rw [hindex, rightVectors, ambientVector_result_right]

/-- The adjoined prefix keeps the source order sequence. -/
@[simp]
theorem order_result_left
    (D : OrthogonalPrefixData r M baseLength (steps := steps) b)
    (i : Fin steps) :
    D.result.order (orthogonalProductLeftIndex baseLength i) =
      b.order (D.sourceIndex i) := by
  apply WithTop.coe_injective
  simp only [BONG.coe_order, value_result_left]

/-- The replacement tail keeps its stored order sequence. -/
@[simp]
theorem order_result_right
    (D : OrthogonalPrefixData r M baseLength (steps := steps) b)
    (j : Fin baseLength) :
    D.result.order (orthogonalProductRightIndex steps j) =
      D.baseOrder j := by
  induction D with
  | stop b base =>
      have hindex : orthogonalProductRightIndex 0 j = j := by
        apply Fin.ext
        simp [orthogonalProductRightIndex]
      rw [hindex]
      rfl
  | @cons V _ _ q L n steps x generator anisotropic tail
      rightNorm_le tailData ih =>
      have hindex : orthogonalProductRightIndex (steps + 1) j =
          (orthogonalProductRightIndex steps j).succ := by
        apply Fin.ext
        simp [orthogonalProductRightIndex]
        omega
      rw [hindex]
      change
        (tailData.result.mapLatticeIsometry
          (Lattice.projectedOrthogonalProductIsometry anisotropic).symm).order
            (orthogonalProductRightIndex steps j) = _
      apply WithTop.coe_injective
      simp only [BONG.coe_order, value_mapLatticeIsometry,
        value_result_right]
      change ord K (tailData.baseValue j) =
        ((tailData.baseOrder j : Int) : WithTop Int)
      have hbase := congrArg (fun z : Int => (z : WithTop Int)) ih
      rw [BONG.coe_order, value_result_right] at hbase
      exact hbase

/-- Bundle a completed prefix construction as a good BONG when the
paper's explicit goodness hypothesis for the new concatenation is supplied.
This keeps goodness as a checked proposition about the constructed BONG,
not as part of the recursive construction data. -/
noncomputable def toGoodBONG
    (D : OrthogonalPrefixData r M baseLength (steps := steps) b)
    (good : D.result.IsGood) :
    GoodBONG (q.orthogonalSum r) (Lattice.product L M)
      (baseLength + steps) :=
  ⟨D.result, good⟩

end OrthogonalPrefixData

end BONG

end Bong
