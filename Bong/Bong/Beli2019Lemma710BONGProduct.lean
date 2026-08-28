/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma710ProjectionProduct
import Bong.Bong.Beli2019Lemma710Orders
import Bong.Bong.Map
import Bong.Bong.Good
import Lean.Elab.Tactic.Omega

/-!
# Beli (2019), Lemma 7.10: concatenating orthogonal BONG blocks

Suppose every order in a left BONG is at most the head order of a nonempty
right BONG.  Each successive left head is then a norm generator after the
right lattice is adjoined orthogonally.  The projection-product isometry
identifies the recursive tail with the same construction one step lower.
This file packages that induction as an actual BONG of the orthogonal
product lattice.
-/

namespace Bong

open Dyadic

namespace BONG

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {m n : Nat}

/-- Embed an index of the left block into a left-first concatenation whose
type-level length is written `right + left`. -/
def orthogonalProductLeftIndex (right : Nat) {left : Nat}
    (i : Fin left) : Fin (right + left) :=
  ⟨i.val, by omega⟩

/-- Embed an index of the right block after all indices of the left block. -/
def orthogonalProductRightIndex (left : Nat) {right : Nat}
    (j : Fin right) : Fin (right + left) :=
  ⟨left + j.val, by omega⟩

@[simp]
theorem orthogonalProductLeftIndex_val (right : Nat) {left : Nat}
    (i : Fin left) :
    (orthogonalProductLeftIndex right i).val = i.val :=
  rfl

@[simp]
theorem orthogonalProductRightIndex_val (left : Nat) {right : Nat}
    (j : Fin right) :
    (orthogonalProductRightIndex left j).val = left + j.val :=
  rfl

/-- Concatenate a left BONG with a nonempty right BONG in the concrete
orthogonal-product model.  The length is written `right + left` because this
is definitionally compatible with recursion on the left BONG; the value
sequence itself is left-first. -/
noncomputable def orthogonalProductRight
    (b : BONG V q L n) (c : BONG W r M (m + 1))
    (horder : ∀ i : Fin n, b.order i ≤ c.order 0) :
    BONG (V × W) (q.orthogonalSum r) (Lattice.product L M)
      ((m + 1) + n) :=
  BONG.rec
    (motive := fun V _ _ q L n b =>
      ∀ {W : Type w} [AddCommGroup W] [Module K W]
        {r : QuadraticSpace K W} {M : Lattice K W} {m : Nat}
        (c : BONG W r M (m + 1)),
        (∀ i : Fin n, b.order i ≤ c.order 0) →
          BONG (V × W) (q.orthogonalSum r) (Lattice.product L M)
            ((m + 1) + n))
    (fun q L exhausted _ _ _ r M _ c _ =>
      c.mapLatticeIsometry
        (Lattice.orthogonalProductSndIsometryOfSubsingleton
          q r L M exhausted).symm)
    (fun x generator anisotropic tail appendTail _ _ _ r M _ c horder =>
      let b := BONG.cons x generator anisotropic tail
      let productGenerator :=
        b.head_isNormGenerator_orthogonalProduct_left c (horder 0)
      let productAnisotropic := anisotropic.orthogonalSum_inl (r := r)
      let tailProduct := appendTail c (fun i => horder i.succ)
      let transportedTail := tailProduct.mapLatticeIsometry
        (Lattice.projectedOrthogonalProductIsometry
          (q := _) (r := r) (L := _) (M := M) anisotropic).symm
      BONG.cons (x, 0) productGenerator productAnisotropic transportedTail)
    b c horder

/-- The left block occurs unchanged at the beginning of the concatenated
BONG value sequence. -/
@[simp]
theorem value_orthogonalProductRight_left
    (b : BONG V q L n) (c : BONG W r M (m + 1))
    (horder : ∀ i : Fin n, b.order i ≤ c.order 0) (i : Fin n) :
    (b.orthogonalProductRight c horder).value
        (orthogonalProductLeftIndex (m + 1) i) =
      b.value i := by
  induction b generalizing W with
  | nil => exact Fin.elim0 i
  | @cons V _ _ q L n x generator anisotropic tail ih =>
      cases i using Fin.cases with
      | zero =>
          simp [orthogonalProductRight, orthogonalProductLeftIndex]
      | succ j =>
          have hindex : orthogonalProductLeftIndex (m + 1) j.succ =
              (orthogonalProductLeftIndex (m + 1) j).succ := by
            apply Fin.ext
            rfl
          rw [hindex]
          simpa only [orthogonalProductRight, value_cons_succ,
            value_mapLatticeIsometry] using
            ih c (fun k => horder k.succ) j

/-- The right block occurs unchanged after the left block in the
concatenated BONG value sequence. -/
@[simp]
theorem value_orthogonalProductRight_right
    (b : BONG V q L n) (c : BONG W r M (m + 1))
    (horder : ∀ i : Fin n, b.order i ≤ c.order 0)
    (j : Fin (m + 1)) :
    (b.orthogonalProductRight c horder).value
        (orthogonalProductRightIndex n j) =
      c.value j := by
  induction b generalizing W with
  | @nil V _ _ q L exhausted =>
      simp [orthogonalProductRight, orthogonalProductRightIndex]
  | @cons V _ _ q L n x generator anisotropic tail ih =>
      have hindex : orthogonalProductRightIndex (n + 1) j =
          (orthogonalProductRightIndex n j).succ := by
        apply Fin.ext
        simp [orthogonalProductRightIndex]
        omega
      rw [hindex]
      simpa only [orthogonalProductRight, value_cons_succ,
        value_mapLatticeIsometry] using
        ih c (fun k => horder k.succ)

/-- The vectors of the left block occur literally in the first factor of
the left-first orthogonal concatenation. -/
@[simp]
theorem ambientVector_orthogonalProductRight_left
    (b : BONG V q L n) (c : BONG W r M (m + 1))
    (horder : ∀ i : Fin n, b.order i ≤ c.order 0) (i : Fin n) :
    (b.orthogonalProductRight c horder).ambientVector
        (orthogonalProductLeftIndex (m + 1) i) =
      (b.ambientVector i, 0) := by
  induction b generalizing W with
  | nil => exact Fin.elim0 i
  | @cons V _ _ q L n x generator anisotropic tail ih =>
      cases i using Fin.cases with
      | zero =>
          simp [orthogonalProductRight, orthogonalProductLeftIndex]
      | succ j =>
          have hindex : orthogonalProductLeftIndex (m + 1) j.succ =
              (orthogonalProductLeftIndex (m + 1) j).succ := by
            apply Fin.ext
            rfl
          let tailProduct := tail.orthogonalProductRight c
            (fun k => horder k.succ)
          let projected := Lattice.projectedOrthogonalProductIsometry
            (q := q) (r := r) (L := L) (M := M) anisotropic
          rw [hindex]
          simp only [orthogonalProductRight, ambientVector_cons_succ]
          change
            (((tailProduct.mapLatticeIsometry projected.symm).ambientVector
              (orthogonalProductLeftIndex (m + 1) j) :
                (q.orthogonalSum r).vectorOrthogonal (x, 0)) : V × W) = _
          rw [BONG.ambientVector_mapLatticeIsometry]
          have htail := ih c (fun k => horder k.succ) j
          change tailProduct.ambientVector
              (orthogonalProductLeftIndex (m + 1) j) = _ at htail
          rw [htail]
          rfl

/-- The vectors of the right block occur literally in the second factor
after all vectors of the left block. -/
@[simp]
theorem ambientVector_orthogonalProductRight_right
    (b : BONG V q L n) (c : BONG W r M (m + 1))
    (horder : ∀ i : Fin n, b.order i ≤ c.order 0)
    (j : Fin (m + 1)) :
    (b.orthogonalProductRight c horder).ambientVector
        (orthogonalProductRightIndex n j) =
      (0, c.ambientVector j) := by
  induction b generalizing W with
  | @nil V _ _ q L exhausted =>
      have hindex : orthogonalProductRightIndex 0 j = j := by
        apply Fin.ext
        simp [orthogonalProductRightIndex]
      rw [hindex]
      simp only [orthogonalProductRight,
        BONG.ambientVector_mapLatticeIsometry]
      apply Prod.ext
      · exact exhausted.elim _ _
      · rfl
  | @cons V _ _ q L n x generator anisotropic tail ih =>
      have hindex : orthogonalProductRightIndex (n + 1) j =
          (orthogonalProductRightIndex n j).succ := by
        apply Fin.ext
        simp [orthogonalProductRightIndex]
        omega
      let tailProduct := tail.orthogonalProductRight c
        (fun k => horder k.succ)
      let projected := Lattice.projectedOrthogonalProductIsometry
        (q := q) (r := r) (L := L) (M := M) anisotropic
      rw [hindex]
      simp only [orthogonalProductRight, ambientVector_cons_succ]
      change
        (((tailProduct.mapLatticeIsometry projected.symm).ambientVector
          (orthogonalProductRightIndex n j) :
            (q.orthogonalSum r).vectorOrthogonal (x, 0)) : V × W) = _
      rw [BONG.ambientVector_mapLatticeIsometry]
      have htail := ih c (fun k => horder k.succ)
      change tailProduct.ambientVector (orthogonalProductRightIndex n j) = _
        at htail
      rw [htail]
      rfl

/-- The left order sequence is unchanged by orthogonal concatenation. -/
@[simp]
theorem order_orthogonalProductRight_left
    (b : BONG V q L n) (c : BONG W r M (m + 1))
    (horder : ∀ i : Fin n, b.order i ≤ c.order 0) (i : Fin n) :
    (b.orthogonalProductRight c horder).order
        (orthogonalProductLeftIndex (m + 1) i) =
      b.order i := by
  apply WithTop.coe_injective
  simp only [coe_order, value_orthogonalProductRight_left]

/-- The right order sequence is unchanged by orthogonal concatenation. -/
@[simp]
theorem order_orthogonalProductRight_right
    (b : BONG V q L n) (c : BONG W r M (m + 1))
    (horder : ∀ i : Fin n, b.order i ≤ c.order 0)
    (j : Fin (m + 1)) :
    (b.orthogonalProductRight c horder).order
        (orthogonalProductRightIndex n j) =
      c.order j := by
  apply WithTop.coe_injective
  simp only [coe_order, value_orthogonalProductRight_right]

/-- Exactly the cross-boundary two-step inequalities required for a
left-first concatenation to be good. -/
def OrthogonalProductBoundaryGood
    (b : BONG V q L n) (c : BONG W r M (m + 1)) : Prop :=
  ∀ (i : Fin n) (j : Fin (m + 1)),
    i.val + 2 = n + j.val → b.order i ≤ c.order j

/-- The cross-boundary predicate consists precisely of the comparison from
the penultimate left entry to the right head and, when both exist, the
comparison from the last left entry to the second right entry. -/
theorem orthogonalProductBoundaryGood_of_endpoints
    (b : BONG V q L n) (c : BONG W r M (m + 1))
    (hpenultimate : ∀ hn : 1 < n,
      b.order ⟨n - 2, by omega⟩ ≤ c.order 0)
    (hlastSecond : ∀ (hn : 0 < n) (hm : 1 < m + 1),
      b.order ⟨n - 1, by omega⟩ ≤ c.order ⟨1, hm⟩) :
    OrthogonalProductBoundaryGood b c := by
  intro i j hij
  have hj : j.val ≤ 1 := by omega
  by_cases hjZero : j.val = 0
  · have hn : 1 < n := by omega
    have hiEq : i = (⟨n - 2, by omega⟩ : Fin n) := by
      apply Fin.ext
      change i.val = n - 2
      omega
    have hjEq : j = (0 : Fin (m + 1)) := by
      apply Fin.ext
      exact hjZero
    rw [hiEq, hjEq]
    exact hpenultimate hn
  · have hjOne : j.val = 1 := by omega
    have hn : 0 < n := by omega
    have hm : 1 < m + 1 := by omega
    have hiEq : i = (⟨n - 1, by omega⟩ : Fin n) := by
      apply Fin.ext
      change i.val = n - 1
      omega
    have hjEq : j = (⟨1, hm⟩ : Fin (m + 1)) := by
      apply Fin.ext
      exact hjOne
    rw [hiEq, hjEq]
    exact hlastSecond hn hm

/-- Goodness is preserved by orthogonal concatenation once the (at most two)
cross-boundary two-step inequalities are supplied. -/
theorem isGood_orthogonalProductRight
    (b : BONG V q L n) (c : BONG W r M (m + 1))
    (horder : ∀ i : Fin n, b.order i ≤ c.order 0)
    (hb : b.IsGood) (hc : c.IsGood)
    (hboundary : OrthogonalProductBoundaryGood b c) :
    (b.orthogonalProductRight c horder).IsGood := by
  let d := b.orthogonalProductRight c horder
  intro i hi
  by_cases hiLeft : i.val < n
  · let ib : Fin n := ⟨i.val, hiLeft⟩
    by_cases hiTwoLeft : i.val + 2 < n
    · let jb : Fin n := ⟨i.val + 2, hiTwoLeft⟩
      have hgood := hb ib hiTwoLeft
      have hiEq : i = orthogonalProductLeftIndex (m + 1) ib :=
        Fin.ext (by rfl)
      have hjEq : (⟨i.val + 2, hi⟩ : Fin ((m + 1) + n)) =
          orthogonalProductLeftIndex (m + 1) jb :=
        Fin.ext (by rfl)
      have hiOrder : d.order i = b.order ib := by
        calc
          d.order i = d.order (orthogonalProductLeftIndex (m + 1) ib) :=
            congrArg d.order hiEq
          _ = b.order ib := order_orthogonalProductRight_left b c horder ib
      have hjOrder : d.order ⟨i.val + 2, hi⟩ = b.order jb := by
        calc
          d.order ⟨i.val + 2, hi⟩ =
              d.order (orthogonalProductLeftIndex (m + 1) jb) :=
            congrArg d.order hjEq
          _ = b.order jb := order_orthogonalProductRight_left b c horder jb
      calc
        d.order i = b.order ib := hiOrder
        _ ≤ b.order jb := hgood
        _ = d.order ⟨i.val + 2, hi⟩ := hjOrder.symm
    · let jc : Fin (m + 1) := ⟨i.val + 2 - n, by omega⟩
      have hcross : b.order ib ≤ c.order jc := by
        apply hboundary ib jc
        simp [ib, jc]
        omega
      have hiEq : i = orthogonalProductLeftIndex (m + 1) ib :=
        Fin.ext (by rfl)
      have hjEq : (⟨i.val + 2, hi⟩ : Fin ((m + 1) + n)) =
          orthogonalProductRightIndex n jc := by
        apply Fin.ext
        simp [jc]
        omega
      have hiOrder : d.order i = b.order ib := by
        calc
          d.order i = d.order (orthogonalProductLeftIndex (m + 1) ib) :=
            congrArg d.order hiEq
          _ = b.order ib := order_orthogonalProductRight_left b c horder ib
      have hjOrder : d.order ⟨i.val + 2, hi⟩ = c.order jc := by
        calc
          d.order ⟨i.val + 2, hi⟩ =
              d.order (orthogonalProductRightIndex n jc) :=
            congrArg d.order hjEq
          _ = c.order jc := order_orthogonalProductRight_right b c horder jc
      calc
        d.order i = b.order ib := hiOrder
        _ ≤ c.order jc := hcross
        _ = d.order ⟨i.val + 2, hi⟩ := hjOrder.symm
  · let ic : Fin (m + 1) := ⟨i.val - n, by omega⟩
    let jc : Fin (m + 1) := ⟨i.val + 2 - n, by omega⟩
    have hgood : c.order ic ≤ c.order jc := by
      have hic : ic.val + 2 < m + 1 := by
        simp [ic]
        omega
      have hraw := hc ic hic
      have hindex : (⟨ic.val + 2, hic⟩ : Fin (m + 1)) = jc := by
        apply Fin.ext
        simp [ic, jc]
        omega
      rw [hindex] at hraw
      exact hraw
    have hiEq : i = orthogonalProductRightIndex n ic := by
      apply Fin.ext
      simp [ic]
      omega
    have hjEq : (⟨i.val + 2, hi⟩ : Fin ((m + 1) + n)) =
        orthogonalProductRightIndex n jc := by
      apply Fin.ext
      simp [jc]
      omega
    have hiOrder : d.order i = c.order ic := by
      calc
        d.order i = d.order (orthogonalProductRightIndex n ic) :=
          congrArg d.order hiEq
        _ = c.order ic := order_orthogonalProductRight_right b c horder ic
    have hjOrder : d.order ⟨i.val + 2, hi⟩ = c.order jc := by
      calc
        d.order ⟨i.val + 2, hi⟩ =
            d.order (orthogonalProductRightIndex n jc) :=
          congrArg d.order hjEq
        _ = c.order jc := order_orthogonalProductRight_right b c horder jc
    calc
      d.order i = c.order ic := hiOrder
      _ ≤ c.order jc := hgood
      _ = d.order ⟨i.val + 2, hi⟩ := hjOrder.symm

namespace GoodBONG

/-- The good-BONG form of orthogonal concatenation. -/
noncomputable def orthogonalProductRight
    (b : GoodBONG q L n) (c : GoodBONG r M (m + 1))
    (horder : ∀ i : Fin n, b.order i ≤ c.order 0)
    (hboundary : OrthogonalProductBoundaryGood b.toBONG c.toBONG) :
    GoodBONG (q.orthogonalSum r) (Lattice.product L M)
      ((m + 1) + n) where
  toBONG := b.toBONG.orthogonalProductRight c.toBONG horder
  good := isGood_orthogonalProductRight b.toBONG c.toBONG horder
    b.good c.good hboundary

/-- Paper-facing constructor: all left orders are bounded by the right head,
and the only extra good-BONG boundary comparison is the last-left to
second-right comparison. -/
noncomputable def orthogonalProductRight_of_orderBounds
    (b : GoodBONG q L n) (c : GoodBONG r M (m + 1))
    (horder : ∀ i : Fin n, b.order i ≤ c.order 0)
    (hlastSecond : ∀ (hn : 0 < n) (hm : 1 < m + 1),
      b.order ⟨n - 1, by omega⟩ ≤ c.order ⟨1, hm⟩) :
    GoodBONG (q.orthogonalSum r) (Lattice.product L M)
      ((m + 1) + n) :=
  b.orthogonalProductRight c horder
    (BONG.orthogonalProductBoundaryGood_of_endpoints
      b.toBONG c.toBONG
      (fun _ => horder _)
      hlastSecond)

/-- For a left block of length at least two, the final two head bounds
propagate along its two parity chains and supply all norm-generator bounds
needed by the recursive concatenation. -/
noncomputable def orthogonalProductRight_of_endpointBounds
    (b : GoodBONG q L n) (c : GoodBONG r M (m + 1))
    (hn : 2 ≤ n)
    (hpenultimate : b.order ⟨n - 2, by omega⟩ ≤ c.order 0)
    (hlastHead : b.order ⟨n - 1, by omega⟩ ≤ c.order 0)
    (hlastSecond : ∀ hm : 1 < m + 1,
      b.order ⟨n - 1, by omega⟩ ≤ c.order ⟨1, hm⟩) :
    GoodBONG (q.orthogonalSum r) (Lattice.product L M)
      ((m + 1) + n) := by
  let horder : ∀ i : Fin n, b.order i ≤ c.order 0 := fun i =>
    b.order_le_of_lt_cut_of_last_two_le n hn (by omega)
      (c.order 0) hpenultimate hlastHead i i.isLt
  exact b.orthogonalProductRight_of_orderBounds c horder
    (fun _ hm => hlastSecond hm)

@[simp]
theorem value_orthogonalProductRight_left
    (b : GoodBONG q L n) (c : GoodBONG r M (m + 1))
    (horder : ∀ i : Fin n, b.order i ≤ c.order 0)
    (hboundary : OrthogonalProductBoundaryGood b.toBONG c.toBONG)
    (i : Fin n) :
    (b.orthogonalProductRight c horder hboundary).value
        (BONG.orthogonalProductLeftIndex (m + 1) i) =
      b.value i :=
  BONG.value_orthogonalProductRight_left b.toBONG c.toBONG horder i

@[simp]
theorem value_orthogonalProductRight_right
    (b : GoodBONG q L n) (c : GoodBONG r M (m + 1))
    (horder : ∀ i : Fin n, b.order i ≤ c.order 0)
    (hboundary : OrthogonalProductBoundaryGood b.toBONG c.toBONG)
    (j : Fin (m + 1)) :
    (b.orthogonalProductRight c horder hboundary).value
        (BONG.orthogonalProductRightIndex n j) =
      c.value j :=
  BONG.value_orthogonalProductRight_right b.toBONG c.toBONG horder j

@[simp]
theorem valueUnit_orthogonalProductRight_left
    (b : GoodBONG q L n) (c : GoodBONG r M (m + 1))
    (horder : ∀ i : Fin n, b.order i ≤ c.order 0)
    (hboundary : OrthogonalProductBoundaryGood b.toBONG c.toBONG)
    (i : Fin n) :
    (b.orthogonalProductRight c horder hboundary).valueUnit
        (BONG.orthogonalProductLeftIndex (m + 1) i) =
      b.valueUnit i := by
  apply Units.ext
  exact BONG.value_orthogonalProductRight_left b.toBONG c.toBONG horder i

@[simp]
theorem valueUnit_orthogonalProductRight_right
    (b : GoodBONG q L n) (c : GoodBONG r M (m + 1))
    (horder : ∀ i : Fin n, b.order i ≤ c.order 0)
    (hboundary : OrthogonalProductBoundaryGood b.toBONG c.toBONG)
    (j : Fin (m + 1)) :
    (b.orthogonalProductRight c horder hboundary).valueUnit
        (BONG.orthogonalProductRightIndex n j) =
      c.valueUnit j := by
  apply Units.ext
  exact BONG.value_orthogonalProductRight_right b.toBONG c.toBONG horder j

@[simp]
theorem valueUnit_orthogonalProductRight_of_orderBounds_left
    (b : GoodBONG q L n) (c : GoodBONG r M (m + 1))
    (horder : ∀ i : Fin n, b.order i ≤ c.order 0)
    (hlastSecond : ∀ (hn : 0 < n) (hm : 1 < m + 1),
      b.order ⟨n - 1, by omega⟩ ≤ c.order ⟨1, hm⟩)
    (i : Fin n) :
    (b.orthogonalProductRight_of_orderBounds c horder hlastSecond).valueUnit
        (BONG.orthogonalProductLeftIndex (m + 1) i) = b.valueUnit i := by
  apply valueUnit_orthogonalProductRight_left

@[simp]
theorem valueUnit_orthogonalProductRight_of_orderBounds_right
    (b : GoodBONG q L n) (c : GoodBONG r M (m + 1))
    (horder : ∀ i : Fin n, b.order i ≤ c.order 0)
    (hlastSecond : ∀ (hn : 0 < n) (hm : 1 < m + 1),
      b.order ⟨n - 1, by omega⟩ ≤ c.order ⟨1, hm⟩)
    (j : Fin (m + 1)) :
    (b.orthogonalProductRight_of_orderBounds c horder hlastSecond).valueUnit
        (BONG.orthogonalProductRightIndex n j) = c.valueUnit j := by
  apply valueUnit_orthogonalProductRight_right

@[simp]
theorem valueUnit_orthogonalProductRight_of_endpointBounds_left
    (b : GoodBONG q L n) (c : GoodBONG r M (m + 1))
    (hn : 2 ≤ n)
    (hpenultimate : b.order ⟨n - 2, by omega⟩ ≤ c.order 0)
    (hlastHead : b.order ⟨n - 1, by omega⟩ ≤ c.order 0)
    (hlastSecond : ∀ hm : 1 < m + 1,
      b.order ⟨n - 1, by omega⟩ ≤ c.order ⟨1, hm⟩)
    (i : Fin n) :
    (b.orthogonalProductRight_of_endpointBounds c hn hpenultimate
        hlastHead hlastSecond).valueUnit
        (BONG.orthogonalProductLeftIndex (m + 1) i) = b.valueUnit i := by
  unfold orthogonalProductRight_of_endpointBounds
  apply valueUnit_orthogonalProductRight_of_orderBounds_left

@[simp]
theorem valueUnit_orthogonalProductRight_of_endpointBounds_right
    (b : GoodBONG q L n) (c : GoodBONG r M (m + 1))
    (hn : 2 ≤ n)
    (hpenultimate : b.order ⟨n - 2, by omega⟩ ≤ c.order 0)
    (hlastHead : b.order ⟨n - 1, by omega⟩ ≤ c.order 0)
    (hlastSecond : ∀ hm : 1 < m + 1,
      b.order ⟨n - 1, by omega⟩ ≤ c.order ⟨1, hm⟩)
    (j : Fin (m + 1)) :
    (b.orthogonalProductRight_of_endpointBounds c hn hpenultimate
        hlastHead hlastSecond).valueUnit
        (BONG.orthogonalProductRightIndex n j) = c.valueUnit j := by
  unfold orthogonalProductRight_of_endpointBounds
  apply valueUnit_orthogonalProductRight_of_orderBounds_right

end GoodBONG

end BONG

end Bong
