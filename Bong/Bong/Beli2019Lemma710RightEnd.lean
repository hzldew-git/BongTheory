/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma710PrefixProduct
import Bong.Bong.Segment

/-!
# Beli (2019), Lemma 7.10: the right-end construction

For the case where the replaced block reaches the right endpoint, the paper
starts with a BONG of the replaced tail and then adjoins the unchanged prefix
in decreasing order.  `OrthogonalPrefixSeed` records exactly the stopping
BONG, but deliberately contains no norm-ideal hypotheses.  Its `toData`
construction derives those hypotheses from comparisons with the head of the
fixed right BONG.

The stopping BONG may be imported through an arbitrary lattice isometry.
This is the interface needed to pass from a concrete consecutive-segment
realization to the recursive orthogonal-product model without identifying
different dependent carrier types by hand.
-/

namespace Bong

open Dyadic

namespace BONG

universe u v w z

/-- A replacement BONG placed after exactly `steps` unchanged source heads.
Unlike `OrthogonalPrefixData`, this seed stores no ideal containment proofs;
they are generated uniformly from the paper's order estimates. -/
inductive OrthogonalPrefixSeed
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    {W : Type w} [AddCommGroup W] [Module K W]
    (r : QuadraticSpace K W) (M : Lattice K W) (baseLength : Nat) :
    {V : Type v} → [AddCommGroup V] → [Module K V] →
    {q : QuadraticSpace K V} → {L : Lattice K V} →
    {n steps : Nat} → BONG V q L n →
      Type (max (u + 1) (v + 1) (w + 1))
  | stop
      {V : Type v} [AddCommGroup V] [Module K V]
      {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
      (source : BONG V q L n)
      (base : BONG (V × W) (q.orthogonalSum r)
        (Lattice.product L M) baseLength) :
      OrthogonalPrefixSeed r M baseLength (steps := 0) source
  | cons
      {V : Type v} [AddCommGroup V] [Module K V]
      {q : QuadraticSpace K V} {L : Lattice K V} {n steps : Nat}
      {x : V}
      (generator : Lattice.IsNormGenerator q L x)
      (anisotropic : q.IsAnisotropic x)
      (tail : BONG (q.vectorOrthogonal x)
        (q.orthogonalSpace x anisotropic)
        (L.projectedLattice q x anisotropic) n)
      (tailSeed : OrthogonalPrefixSeed r M baseLength
        (steps := steps) tail) :
      OrthogonalPrefixSeed r M baseLength (steps := steps + 1)
        (BONG.cons x generator anisotropic tail)

namespace OrthogonalPrefixSeed

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}
  {n steps baseLength : Nat} {b : BONG V q L n}

/-- Import the stopping BONG from any isometric lattice model.  In
particular, a replacement block realized by `SegmentWitness` can be used
once its lattice equality is bundled as a lattice isometry. -/
noncomputable def stopOfLatticeIsometry
    {U : Type z} [AddCommGroup U] [Module K U]
    {s : QuadraticSpace K U} {N : Lattice K U}
    (source : BONG V q L n) (base : BONG U s N baseLength)
    (f : Lattice.Isometry s (q.orthogonalSum r) N
      (Lattice.product L M)) :
    OrthogonalPrefixSeed r M baseLength (steps := 0) source :=
  .stop source (base.mapLatticeIsometry f)

/-- Import a concrete consecutive replacement block at the stopping point.
The only geometric datum still required is the lattice isometry expressing
the paper's equality between that block lattice and the relevant orthogonal
product lattice. -/
noncomputable def stopOfSegmentWitness
    {U : Type z} [AddCommGroup U] [Module K U]
    {s : QuadraticSpace K U} {N : Lattice K U} {m start : Nat}
    {target : BONG U s N m} {bound : start + baseLength ≤ m}
    (source : BONG V q L n)
    (replacement : SegmentWitness target start baseLength bound)
    (f : Lattice.Isometry
      (s.restrict replacement.carrier replacement.nondegenerate)
      (q.orthogonalSum r) replacement.lattice
      (Lattice.product L M)) :
    OrthogonalPrefixSeed r M baseLength (steps := 0) source :=
  stopOfLatticeIsometry source replacement.bong f

/-- The number of stored prefix steps is bounded by the source length. -/
theorem steps_le_length
    (S : OrthogonalPrefixSeed r M baseLength (steps := steps) b) :
    steps ≤ n := by
  induction S with
  | stop => simp
  | cons _ _ _ _ ih => omega

/-- The source index corresponding to an unchanged prefix index. -/
def sourceIndex
    (S : OrthogonalPrefixSeed r M baseLength (steps := steps) b)
    (i : Fin steps) : Fin n :=
  ⟨i.val, lt_of_lt_of_le i.isLt S.steps_le_length⟩

@[simp]
theorem sourceIndex_val
    (S : OrthogonalPrefixSeed r M baseLength (steps := steps) b)
    (i : Fin steps) : (S.sourceIndex i).val = i.val :=
  rfl

/-- The head comparison extracted from a uniform comparison for a seed
obtained by adjoining one source head. -/
theorem consHeadOrder
    {rightLength : Nat} {x : V}
    (generator : Lattice.IsNormGenerator q L x)
    (anisotropic : q.IsAnisotropic x)
    (tail : BONG (q.vectorOrthogonal x)
      (q.orthogonalSpace x anisotropic)
      (L.projectedLattice q x anisotropic) n)
    (tailSeed : OrthogonalPrefixSeed r M baseLength
      (steps := steps) tail)
    (right : BONG W r M (rightLength + 1))
    (horder : ∀ i : Fin (steps + 1),
      (BONG.cons x generator anisotropic tail).order
        ((OrthogonalPrefixSeed.cons generator anisotropic tail
          tailSeed).sourceIndex i) ≤ right.order 0) :
    (BONG.cons x generator anisotropic tail).order 0 ≤ right.order 0 := by
  have h := horder (0 : Fin (steps + 1))
  have hindex :
      (OrthogonalPrefixSeed.cons generator anisotropic tail
        tailSeed).sourceIndex (0 : Fin (steps + 1)) =
        (0 : Fin (n + 1)) := by
    apply Fin.ext
    rfl
  rwa [hindex] at h

/-- The comparisons inherited by the tail after adjoining one source
head.  Naming this transformation keeps all later seed recursion free of
proof-term mismatches. -/
theorem consTailOrder
    {rightLength : Nat} {x : V}
    (generator : Lattice.IsNormGenerator q L x)
    (anisotropic : q.IsAnisotropic x)
    (tail : BONG (q.vectorOrthogonal x)
      (q.orthogonalSpace x anisotropic)
      (L.projectedLattice q x anisotropic) n)
    (tailSeed : OrthogonalPrefixSeed r M baseLength
      (steps := steps) tail)
    (right : BONG W r M (rightLength + 1))
    (horder : ∀ i : Fin (steps + 1),
      (BONG.cons x generator anisotropic tail).order
        ((OrthogonalPrefixSeed.cons generator anisotropic tail
          tailSeed).sourceIndex i) ≤ right.order 0) :
    ∀ i : Fin steps,
      tail.order (tailSeed.sourceIndex i) ≤ right.order 0 := by
  intro i
  have h := horder i.succ
  have hindex :
      (OrthogonalPrefixSeed.cons generator anisotropic tail
        tailSeed).sourceIndex i.succ =
        (tailSeed.sourceIndex i).succ := by
    apply Fin.ext
    rfl
  rw [hindex] at h
  have htailOrder :
      tail.order (tailSeed.sourceIndex i) =
        (BONG.cons x generator anisotropic tail).order
          (tailSeed.sourceIndex i).succ := by
    apply WithTop.coe_injective
    simp only [BONG.coe_order, BONG.value_cons_succ]
  rwa [← htailOrder] at h

/-- Generate every norm-ideal comparison required by the decreasing
induction from a uniform comparison with the head of the right BONG. -/
noncomputable def toData
    {rightLength : Nat}
    (S : OrthogonalPrefixSeed r M baseLength (steps := steps) b)
    (right : BONG W r M (rightLength + 1))
    (horder : ∀ i : Fin steps,
      b.order (S.sourceIndex i) ≤ right.order 0) :
    OrthogonalPrefixData r M baseLength (steps := steps) b := by
  induction S with
  | stop source base =>
      exact .stop source base
  | @cons V _ _ q L n steps x generator anisotropic tail tailSeed ih =>
      exact OrthogonalPrefixData.consOfHeadOrder
        generator anisotropic tail right
        (consHeadOrder generator anisotropic tail tailSeed right horder)
        (ih (consTailOrder generator anisotropic tail tailSeed right horder))

/-- The BONG produced by the right-end decreasing induction. -/
noncomputable def result
    {rightLength : Nat}
    (S : OrthogonalPrefixSeed r M baseLength (steps := steps) b)
    (right : BONG W r M (rightLength + 1))
    (horder : ∀ i : Fin steps,
      b.order (S.sourceIndex i) ≤ right.order 0) :
    BONG (V × W) (q.orthogonalSum r) (Lattice.product L M)
      (baseLength + steps) :=
  (S.toData right horder).result

/-- Every unchanged prefix value is retained by the right-end
construction. -/
@[simp]
theorem value_result_left
    {rightLength : Nat}
    (S : OrthogonalPrefixSeed r M baseLength (steps := steps) b)
    (right : BONG W r M (rightLength + 1))
    (horder : ∀ i : Fin steps,
      b.order (S.sourceIndex i) ≤ right.order 0)
    (i : Fin steps) :
    (S.result right horder).value
        (orthogonalProductLeftIndex baseLength i) =
      b.value (S.sourceIndex i) := by
  change (S.toData right horder).result.value
      (orthogonalProductLeftIndex baseLength i) = _
  rw [OrthogonalPrefixData.value_result_left]
  apply congrArg b.value
  apply Fin.ext
  rfl

/-- Every unchanged prefix vector is retained in the left factor of the
right-end construction. -/
@[simp]
theorem ambientVector_result_left
    {rightLength : Nat}
    (S : OrthogonalPrefixSeed r M baseLength (steps := steps) b)
    (right : BONG W r M (rightLength + 1))
    (horder : ∀ i : Fin steps,
      b.order (S.sourceIndex i) ≤ right.order 0)
    (i : Fin steps) :
    (S.result right horder).ambientVector
        (orthogonalProductLeftIndex baseLength i) =
      (b.ambientVector (S.sourceIndex i), 0) := by
  change (S.toData right horder).result.ambientVector
      (orthogonalProductLeftIndex baseLength i) = _
  rw [OrthogonalPrefixData.ambientVector_result_left]
  congr 2

/-- The scalar values of the stopping replacement BONG.  Unlike `toData`,
this datum is independent of all prefix order comparisons. -/
noncomputable def baseValue
    (S : OrthogonalPrefixSeed r M baseLength (steps := steps) b) :
    Fin baseLength → K := by
  induction S with
  | stop _ base => exact base.value
  | cons _ _ _ _ tailValue => exact tailValue

/-- The orders of the stopping replacement BONG, independent of the later
decreasing-induction hypotheses. -/
noncomputable def baseOrder
    (S : OrthogonalPrefixSeed r M baseLength (steps := steps) b) :
    Fin baseLength → Int := by
  induction S with
  | stop _ base => exact base.order
  | cons _ _ _ _ tailOrder => exact tailOrder

/-- The stopping replacement vectors transported back through the stored
prefix projections.  This is intrinsic to the seed and does not mention the
right BONG or any order comparison. -/
noncomputable def baseAmbientVector
    (S : OrthogonalPrefixSeed r M baseLength (steps := steps) b) :
    Fin baseLength → V × W := by
  induction S with
  | stop _ base => exact base.ambientVector
  | @cons V _ _ q L n steps x generator anisotropic tail tailSeed tailBase =>
      exact fun i =>
        (((Lattice.projectedOrthogonalProductIsometry
            (q := q) (r := r) (L := L) (M := M)
            anisotropic).symm.toLinearEquiv (tailBase i) :
              (q.orthogonalSum r).vectorOrthogonal (x, 0)) : V × W)

/-- The transported stopping vectors retain their original quadratic
values. -/
theorem quadratic_baseAmbientVector
    (S : OrthogonalPrefixSeed r M baseLength (steps := steps) b)
    (j : Fin baseLength) :
    (q.orthogonalSum r).quadratic (S.baseAmbientVector j) =
      S.baseValue j := by
  induction S with
  | stop source base =>
      simpa only [baseAmbientVector, baseValue] using
        base.quadratic_ambientVector j
  | @cons V _ _ q L n steps x generator anisotropic tail tailSeed ih =>
      let f := Lattice.projectedOrthogonalProductIsometry
        (q := q) (r := r) (L := L) (M := M) anisotropic
      change (q.orthogonalSum r).quadratic
          (((f.symm.toLinearEquiv (tailSeed.baseAmbientVector j) :
            (q.orthogonalSum r).vectorOrthogonal (x, 0)) : V × W)) =
        tailSeed.baseValue j
      calc
        (q.orthogonalSum r).quadratic
            (((f.symm.toLinearEquiv (tailSeed.baseAmbientVector j) :
              (q.orthogonalSum r).vectorOrthogonal (x, 0)) : V × W)) =
            ((q.orthogonalSum r).orthogonalSpace (x, 0)
              anisotropic.orthogonalSum_inl).quadratic
                (f.symm.toLinearEquiv (tailSeed.baseAmbientVector j)) := rfl
        _ = ((q.orthogonalSpace x anisotropic).orthogonalSum r).quadratic
              (tailSeed.baseAmbientVector j) :=
            f.symm.map_quadratic (tailSeed.baseAmbientVector j)
        _ = tailSeed.baseValue j := ih

/-- The intrinsic stopping order is the valuation of the intrinsic stopping
value. -/
@[simp]
theorem coe_baseOrder
    (S : OrthogonalPrefixSeed r M baseLength (steps := steps) b)
    (j : Fin baseLength) :
    (S.baseOrder j : WithTop Int) = ord K (S.baseValue j) := by
  induction S with
  | stop source base =>
      simpa only [baseOrder, baseValue] using base.coe_order j
  | cons _ _ _ _ ih =>
      simpa only [baseOrder, baseValue] using ih

/-- The external right factor is a sub-ideal of the norm ideal of every
nonempty stopping orthogonal product; hence the stopping head order is at
most the right head order.  This is the formal version of
`S_s ≤ R_(t+1)` in the right-end proof of Lemma 7.10. -/
theorem baseOrder_zero_le_right
    {baseTail rightLength : Nat}
    (S : OrthogonalPrefixSeed r M (baseTail + 1) (steps := steps) b)
    (right : BONG W r M (rightLength + 1)) :
    S.baseOrder 0 ≤ right.order 0 := by
  induction S with
  | stop source base =>
      change base.order 0 ≤ right.order 0
      apply head_order_le_of_normIdeal_le base right
      rw [Lattice.normIdeal_orthogonalProduct]
      exact _root_.le_sup_right
  | cons _ _ _ _ ih =>
      exact ih

/-- Matching a target vector with an intrinsic stopping vector identifies
their BONG orders. -/
theorem order_eq_baseOrder_of_ambientVector_eq
    {targetLength : Nat} {N : Lattice K (V × W)}
    (S : OrthogonalPrefixSeed r M baseLength (steps := steps) b)
    (target : BONG (V × W) (q.orthogonalSum r) N targetLength)
    (i : Fin targetLength) (j : Fin baseLength)
    (hvector : target.ambientVector i = S.baseAmbientVector j) :
    target.order i = S.baseOrder j := by
  apply WithTop.coe_injective
  rw [target.coe_order, ← target.quadratic_ambientVector i, hvector,
    S.quadratic_baseAmbientVector j]
  exact (S.coe_baseOrder j).symm

/-- Passing from a seed to its comparison-bearing data does not change the
stopping values. -/
@[simp]
theorem baseValue_toData
    {rightLength : Nat}
    (S : OrthogonalPrefixSeed r M baseLength (steps := steps) b)
    (right : BONG W r M (rightLength + 1))
    (horder : ∀ i : Fin steps,
      b.order (S.sourceIndex i) ≤ right.order 0)
    (j : Fin baseLength) :
    (S.toData right horder).baseValue j = S.baseValue j := by
  induction S with
  | stop => rfl
  | cons _ _ _ _ ih =>
      simp only [toData, OrthogonalPrefixData.baseValue, baseValue]
      apply ih

/-- Passing from a seed to its comparison-bearing data does not change the
stopping orders. -/
@[simp]
theorem baseOrder_toData
    {rightLength : Nat}
    (S : OrthogonalPrefixSeed r M baseLength (steps := steps) b)
    (right : BONG W r M (rightLength + 1))
    (horder : ∀ i : Fin steps,
      b.order (S.sourceIndex i) ≤ right.order 0)
    (j : Fin baseLength) :
    (S.toData right horder).baseOrder j = S.baseOrder j := by
  induction S with
  | stop => rfl
  | cons _ _ _ _ ih =>
      simp only [toData, OrthogonalPrefixData.baseOrder, baseOrder]
      apply ih

/-- Passing from a seed to its comparison-bearing data does not change the
transported stopping vectors. -/
@[simp]
theorem baseAmbientVector_toData
    {rightLength : Nat}
    (S : OrthogonalPrefixSeed r M baseLength (steps := steps) b)
    (right : BONG W r M (rightLength + 1))
    (horder : ∀ i : Fin steps,
      b.order (S.sourceIndex i) ≤ right.order 0)
    (j : Fin baseLength) :
    (S.toData right horder).baseAmbientVector j =
      S.baseAmbientVector j := by
  induction S with
  | stop => rfl
  | @cons V _ _ q L n steps x generator anisotropic tail tailSeed ih =>
      let htail := consTailOrder generator anisotropic tail tailSeed
        right horder
      have htransport := congrArg
        (fun z =>
          (((Lattice.projectedOrthogonalProductIsometry
              (q := q) (r := r) (L := L) (M := M)
              anisotropic).symm.toLinearEquiv z :
                (q.orthogonalSum r).vectorOrthogonal (x, 0)) : V × W))
        (ih htail)
      simpa only [toData, OrthogonalPrefixData.consOfHeadOrder,
        OrthogonalPrefixData.baseAmbientVector, baseAmbientVector] using
        htransport

/-- The replacement block of the right-end result is exactly the transported
stopping block. -/
@[simp]
theorem ambientVector_result_right
    {rightLength : Nat}
    (S : OrthogonalPrefixSeed r M baseLength (steps := steps) b)
    (right : BONG W r M (rightLength + 1))
    (horder : ∀ i : Fin steps,
      b.order (S.sourceIndex i) ≤ right.order 0)
    (j : Fin baseLength) :
    (S.result right horder).ambientVector
        (orthogonalProductRightIndex steps j) =
      S.baseAmbientVector j := by
  change (S.toData right horder).result.ambientVector
      (orthogonalProductRightIndex steps j) = _
  rw [OrthogonalPrefixData.ambientVector_result_right,
    S.baseAmbientVector_toData right horder]

/-- Final lattice equality for the right-end construction, reduced to the
two literal vector blocks in the statement of Lemma 7.10. -/
theorem lattice_eq_of_matching_vectors
    {rightLength : Nat} {N : Lattice K (V × W)}
    (S : OrthogonalPrefixSeed r M baseLength (steps := steps) b)
    (right : BONG W r M (rightLength + 1))
    (horder : ∀ i : Fin steps,
      b.order (S.sourceIndex i) ≤ right.order 0)
    (target : BONG (V × W) (q.orthogonalSum r) N
      (baseLength + steps))
    (leftVectors : ∀ i : Fin steps,
      target.ambientVector (orthogonalProductLeftIndex baseLength i) =
        (b.ambientVector (S.sourceIndex i), 0))
    (rightVectors : ∀ j : Fin baseLength,
      target.ambientVector (orthogonalProductRightIndex steps j) =
        S.baseAmbientVector j) :
    N = Lattice.product L M :=
  (S.toData right horder).lattice_eq_of_matching_vectors
    target leftVectors (fun j => by
      rw [rightVectors j]
      exact (S.baseAmbientVector_toData right horder j).symm)

/-- Every unchanged prefix order is retained by the right-end
construction. -/
@[simp]
theorem order_result_left
    {rightLength : Nat}
    (S : OrthogonalPrefixSeed r M baseLength (steps := steps) b)
    (right : BONG W r M (rightLength + 1))
    (horder : ∀ i : Fin steps,
      b.order (S.sourceIndex i) ≤ right.order 0)
    (i : Fin steps) :
    (S.result right horder).order
        (orthogonalProductLeftIndex baseLength i) =
      b.order (S.sourceIndex i) := by
  apply WithTop.coe_injective
  simp only [BONG.coe_order, value_result_left]

/-- Bundle the constructed sequence as a good BONG from the explicit
goodness premise in Lemma 7.10. -/
noncomputable def toGoodBONG
    {rightLength : Nat}
    (S : OrthogonalPrefixSeed r M baseLength (steps := steps) b)
    (right : BONG W r M (rightLength + 1))
    (horder : ∀ i : Fin steps,
      b.order (S.sourceIndex i) ≤ right.order 0)
    (good : (S.result right horder).IsGood) :
    GoodBONG (q.orthogonalSum r) (Lattice.product L M)
      (baseLength + steps) :=
  ⟨S.result right horder, good⟩

end OrthogonalPrefixSeed

namespace GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}
  {n rightLength baseLength : Nat}

/-- In the nontrivial right-end case, goodness of the proposed combined
BONG supplies `R_(s-2) ≤ S_s`, while the stopping orthogonal product supplies
`S_s ≤ R_(t+1)`.  Thus the penultimate parity-chain endpoint required by
the decreasing induction is a theorem rather than an extra hypothesis. -/
theorem beli2019Lemma710_previous_order_le_right_of_good
    {baseTail : Nat} {N : Lattice K (V × W)}
    (b : GoodBONG q L n) (s : Nat) (hs : 3 ≤ s)
    (hsRank : s - 1 ≤ n)
    (right : BONG W r M (rightLength + 1))
    (seed : OrthogonalPrefixSeed r M (baseTail + 1)
      (steps := s - 1) b.toBONG)
    (target : BONG (V × W) (q.orthogonalSum r) N
      ((baseTail + 1) + (s - 1)))
    (targetGood : target.IsGood)
    (leftVectors : ∀ i : Fin (s - 1),
      target.ambientVector
          (orthogonalProductLeftIndex (baseTail + 1) i) =
        (b.toBONG.ambientVector (seed.sourceIndex i), 0))
    (rightVectors : ∀ j : Fin (baseTail + 1),
      target.ambientVector (orthogonalProductRightIndex (s - 1) j) =
        seed.baseAmbientVector j) :
    b.order ⟨s - 3, by omega⟩ ≤ right.order 0 := by
  let previous : Fin (s - 1) := ⟨s - 3, by omega⟩
  let previousSource : Fin n := ⟨s - 3, by omega⟩
  let leftIndex : Fin ((baseTail + 1) + (s - 1)) :=
    orthogonalProductLeftIndex (baseTail + 1) previous
  let rightIndex : Fin ((baseTail + 1) + (s - 1)) :=
    orthogonalProductRightIndex (s - 1) (0 : Fin (baseTail + 1))
  have hsource : seed.sourceIndex previous = previousSource := by
    apply Fin.ext
    rfl
  have hleftOrder : target.order leftIndex = b.order previousSource := by
    apply WithTop.coe_injective
    change (target.order leftIndex : WithTop Int) =
      (b.toBONG.order previousSource : WithTop Int)
    rw [target.coe_order, b.toBONG.coe_order]
    rw [← target.quadratic_ambientVector leftIndex]
    change ord K ((q.orthogonalSum r).quadratic
        (target.ambientVector
          (orthogonalProductLeftIndex (baseTail + 1) previous))) = _
    rw [leftVectors previous, hsource,
      QuadraticSpace.orthogonalSum_quadratic_apply,
      r.quadratic_zero, add_zero,
      b.toBONG.quadratic_ambientVector previousSource]
  have hrightOrder :
      target.order rightIndex = seed.baseOrder 0 := by
    apply seed.order_eq_baseOrder_of_ambientVector_eq target
    exact rightVectors 0
  have hleftTwo : leftIndex.val + 2 <
      (baseTail + 1) + (s - 1) := by
    simp only [leftIndex, orthogonalProductLeftIndex_val, previous]
    omega
  have hgood := targetGood leftIndex hleftTwo
  have hnext :
      (⟨leftIndex.val + 2, hleftTwo⟩ :
        Fin ((baseTail + 1) + (s - 1))) = rightIndex := by
    apply Fin.ext
    change s - 3 + 2 = s - 1
    omega
  rw [hnext] at hgood
  change b.order previousSource ≤ right.order 0
  calc
    b.order previousSource = target.order leftIndex := hleftOrder.symm
    _ ≤ target.order rightIndex := hgood
    _ = seed.baseOrder 0 := hrightOrder
    _ ≤ right.order 0 := seed.baseOrder_zero_le_right right

/-- The paper-facing right-end constructor.  The two final orders of the
unchanged prefix imply all head comparisons needed by the decreasing
induction through the parity-chain argument already proved in
`beli2019Lemma710_prefix_order_le`. -/
noncomputable def beli2019Lemma710RightEndData
    (b : GoodBONG q L n) (s : Nat) (hs : 2 ≤ s)
    (hsRank : s - 1 ≤ n)
    (right : BONG W r M (rightLength + 1))
    (seed : OrthogonalPrefixSeed r M baseLength (steps := s - 1)
      b.toBONG)
    (hprevious : 3 ≤ s →
      b.order ⟨s - 3, by omega⟩ ≤ right.order 0)
    (hlast : b.order ⟨s - 2, by omega⟩ ≤ right.order 0) :
    OrthogonalPrefixData r M baseLength (steps := s - 1) b.toBONG :=
  seed.toData right (fun i =>
    b.beli2019Lemma710_prefix_order_le s hs hsRank (right.order 0)
      hprevious hlast (seed.sourceIndex i) (by
        rw [seed.sourceIndex_val]
        exact i.isLt))

/-- The complete right-end conclusion of Lemma 7.10 once the replacement
block is identified through the seed's stopping isometry.  The order inputs
are exactly those consumed by the paper's parity-chain propagation. -/
theorem beli2019Lemma710RightEnd
    {N : Lattice K (V × W)}
    (b : GoodBONG q L n) (s : Nat) (hs : 2 ≤ s)
    (hsRank : s - 1 ≤ n)
    (right : BONG W r M (rightLength + 1))
    (seed : OrthogonalPrefixSeed r M baseLength (steps := s - 1)
      b.toBONG)
    (hprevious : 3 ≤ s →
      b.order ⟨s - 3, by omega⟩ ≤ right.order 0)
    (hlast : b.order ⟨s - 2, by omega⟩ ≤ right.order 0)
    (target : BONG (V × W) (q.orthogonalSum r) N
      (baseLength + (s - 1)))
    (leftVectors : ∀ i : Fin (s - 1),
      target.ambientVector (orthogonalProductLeftIndex baseLength i) =
        (b.toBONG.ambientVector (seed.sourceIndex i), 0))
    (rightVectors : ∀ j : Fin baseLength,
      target.ambientVector (orthogonalProductRightIndex (s - 1) j) =
        seed.baseAmbientVector j) :
    N = Lattice.product L M := by
  apply seed.lattice_eq_of_matching_vectors right
    (fun i => b.beli2019Lemma710_prefix_order_le s hs hsRank
      (right.order 0) hprevious hlast (seed.sourceIndex i) (by
        rw [seed.sourceIndex_val]
        exact i.isLt)) target leftVectors rightVectors

/-- The right-end conclusion in the form used in Beli's proof.  Once the
candidate combined BONG is known to be good, its comparison two places apart
supplies the penultimate endpoint automatically; only the stated last-order
hypothesis remains.  The nonempty stopping block is written as
`baseTail + 1` so that its head norm generator is available. -/
theorem beli2019Lemma710RightEnd_of_good
    {baseTail : Nat} {N : Lattice K (V × W)}
    (b : GoodBONG q L n) (s : Nat) (hs : 2 ≤ s)
    (hsRank : s - 1 ≤ n)
    (right : BONG W r M (rightLength + 1))
    (seed : OrthogonalPrefixSeed r M (baseTail + 1)
      (steps := s - 1) b.toBONG)
    (hlast : b.order ⟨s - 2, by omega⟩ ≤ right.order 0)
    (target : BONG (V × W) (q.orthogonalSum r) N
      ((baseTail + 1) + (s - 1)))
    (targetGood : target.IsGood)
    (leftVectors : ∀ i : Fin (s - 1),
      target.ambientVector
          (orthogonalProductLeftIndex (baseTail + 1) i) =
        (b.toBONG.ambientVector (seed.sourceIndex i), 0))
    (rightVectors : ∀ j : Fin (baseTail + 1),
      target.ambientVector (orthogonalProductRightIndex (s - 1) j) =
        seed.baseAmbientVector j) :
    N = Lattice.product L M := by
  have hprevious : 3 ≤ s →
      b.order ⟨s - 3, by omega⟩ ≤ right.order 0 := by
    intro hsThree
    exact b.beli2019Lemma710_previous_order_le_right_of_good
      s hsThree hsRank right seed target targetGood leftVectors rightVectors
  exact b.beli2019Lemma710RightEnd s hs hsRank right seed
    hprevious hlast target leftVectors rightVectors

/-- Unified right-end form, including the boundary case `s = 1`.  In that
case there is no unchanged prefix and hence no last-order hypothesis; the
conclusion is exactly the stopping-block lattice identification. -/
theorem beli2019Lemma710RightEnd_all_of_good
    {baseTail : Nat} {N : Lattice K (V × W)}
    (b : GoodBONG q L n) (s : Nat) (hs : 1 ≤ s)
    (hsRank : s - 1 ≤ n)
    (right : BONG W r M (rightLength + 1))
    (seed : OrthogonalPrefixSeed r M (baseTail + 1)
      (steps := s - 1) b.toBONG)
    (hlast : ∀ hsTwo : 2 ≤ s,
      b.order ⟨s - 2, by omega⟩ ≤ right.order 0)
    (target : BONG (V × W) (q.orthogonalSum r) N
      ((baseTail + 1) + (s - 1)))
    (targetGood : target.IsGood)
    (leftVectors : ∀ i : Fin (s - 1),
      target.ambientVector
          (orthogonalProductLeftIndex (baseTail + 1) i) =
        (b.toBONG.ambientVector (seed.sourceIndex i), 0))
    (rightVectors : ∀ j : Fin (baseTail + 1),
      target.ambientVector (orthogonalProductRightIndex (s - 1) j) =
        seed.baseAmbientVector j) :
    N = Lattice.product L M := by
  by_cases hsTwo : 2 ≤ s
  · exact b.beli2019Lemma710RightEnd_of_good s hsTwo hsRank right seed
      (hlast hsTwo) target targetGood leftVectors rightVectors
  · have hsEq : s = 1 := by omega
    subst s
    have horder : ∀ i : Fin (1 - 1),
        b.toBONG.order (seed.sourceIndex i) ≤ right.order 0 :=
      fun i => Fin.elim0 i
    exact seed.lattice_eq_of_matching_vectors right horder target
      leftVectors rightVectors

/-- Index-arithmetic form of the unified endpoint theorem.  Here `steps` is
literally the number of unchanged prefix entries, so the only endpoint
condition is conditional on `0 < steps`.  This form is convenient when two
endpoint certificates are assembled in the general case. -/
theorem beli2019Lemma710RightEnd_steps_of_good
    {baseTail steps : Nat} {N : Lattice K (V × W)}
    (b : GoodBONG q L n) (hsteps : steps ≤ n)
    (right : BONG W r M (rightLength + 1))
    (seed : OrthogonalPrefixSeed r M (baseTail + 1)
      (steps := steps) b.toBONG)
    (hlast : ∀ hpos : 0 < steps,
      b.order ⟨steps - 1, by omega⟩ ≤ right.order 0)
    (target : BONG (V × W) (q.orthogonalSum r) N
      ((baseTail + 1) + steps))
    (targetGood : target.IsGood)
    (leftVectors : ∀ i : Fin steps,
      target.ambientVector
          (orthogonalProductLeftIndex (baseTail + 1) i) =
        (b.toBONG.ambientVector (seed.sourceIndex i), 0))
    (rightVectors : ∀ j : Fin (baseTail + 1),
      target.ambientVector (orthogonalProductRightIndex steps j) =
        seed.baseAmbientVector j) :
    N = Lattice.product L M := by
  refine b.beli2019Lemma710RightEnd_all_of_good (steps + 1)
    (by omega) (by simpa using hsteps) right seed ?_ target targetGood
      ?_ ?_
  · intro hsTwo
    have hpos : 0 < steps := by omega
    simpa using hlast hpos
  · exact leftVectors
  · exact rightVectors

end GoodBONG

end BONG

end Bong
