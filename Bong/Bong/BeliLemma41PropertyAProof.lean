/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliCorollary42GoodProof
import Bong.Bong.BeliCorollary44Proof
import Bong.Bong.BeliCorollary44ScaleProof
import Bong.Bong.BeliLemma41ProductModel
import Bong.Lattice.OrthogonalDecompositionCons

/-!
# Beli (2003), Lemma 4.1(ii)

This file constructs the Jordan blocking adapted to an arbitrary BONG of a
property-A lattice.  The construction follows Beli's induction, expressed in
the equivalent order-theoretic form: a strictly increasing first pair splits
off a unary block, while a nonincreasing first pair is a modular binary block.
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

namespace BONG

/-- In any nonempty BONG, the ambient vector at index zero is a norm
generator of the underlying lattice. -/
theorem ambientVector_zero_isNormGenerator (b : BONG V q L n) (hn : 0 < n) :
    Lattice.IsNormGenerator q L (b.ambientVector ⟨0, hn⟩) := by
  cases n with
  | zero => omega
  | succ m =>
      have hindex : (⟨0, hn⟩ : Fin (m + 1)) = 0 := Fin.ext rfl
      rw [hindex]
      rw [b.ambientVector_zero_eq_head]
      exact b.head_isNormGenerator

/-- A one-entry BONG is modular at its unique quadratic value. -/
theorem isModular_valueUnit_zero_unary (b : BONG V q L 1) :
    Lattice.IsModular q L (b.valueUnit 0) := by
  have hmodular : Lattice.IsModular q
      (Lattice.basisLattice b.basis) (b.valueUnit 0) := by
    have hne : ∀ i, q.quadratic (b.basis i) ≠ 0 := by
      intro i
      change q.quadratic (b.ambientVector i) ≠ 0
      rw [b.quadratic_ambientVector]
      exact b.value_ne_zero i
    apply Lattice.isModular_basisLattice_of_iIsOrtho_of_orders_eq
      q b.basis b.ambientVector_iIsOrtho hne (b.valueUnit 0)
    intro i
    have hi : i = 0 := Subsingleton.elim i 0
    subst i
    apply congrArg (ordUnit K)
    apply Units.ext
    exact b.quadratic_ambientVector 0
  have htransport := congrArg
    (fun M : Lattice K V ↦ Lattice.IsModular q M (b.valueUnit 0))
    b.lattice_eq_basisLattice
  exact htransport.mpr hmodular

/-- The whole-segment component has exactly the ambient integral module. -/
theorem SegmentWitness.whole_ambientSubmodule_eq (b : BONG V q L n) :
    (SegmentWitness.whole b).toQuadraticSublattice.ambientSubmodule =
      L.toSubmodule := by
  apply le_antisymm
  · intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    let f := SegmentWitness.wholeLatticeIsometry b
    change y ∈ (SegmentWitness.whole b).lattice at hy
    have hmem : f.toLinearEquiv.symm y ∈ L :=
      (f.map_mem (f.toLinearEquiv.symm y)).2 (by simpa using hy)
    have hcoe : f.toLinearEquiv.symm y = (y : V) := rfl
    rwa [hcoe] at hmem
  · intro x hx
    let f := SegmentWitness.wholeLatticeIsometry b
    refine ⟨f.toLinearEquiv x, (f.map_mem x).1 hx, ?_⟩
    rfl

/-- The singleton orthogonal decomposition attached to the whole segment. -/
noncomputable def singletonSegmentDecomposition (b : BONG V q L n) :
    Lattice.OrthogonalDecomposition q L 1 := by
  let C := (SegmentWitness.whole b).toQuadraticSublattice
  exact {
    component := fun _ ↦ C
    orthogonal := by
      intro i j hij
      exact (hij (Subsingleton.elim i j)).elim
    sum_eq := by
      apply le_antisymm
      · apply iSup_le
        intro i
        rw [show C.ambientSubmodule = L.toSubmodule by
          exact SegmentWitness.whole_ambientSubmodule_eq b]
      · rw [← SegmentWitness.whole_ambientSubmodule_eq b]
        exact le_iSup (fun _ : Fin 1 ↦ C.ambientSubmodule) 0 }

@[simp]
theorem singletonSegmentDecomposition_component (b : BONG V q L n)
    (i : Fin 1) :
    (singletonSegmentDecomposition b).component i =
      (SegmentWitness.whole b).toQuadraticSublattice :=
  rfl

/-- The BONG of the unique component in the singleton decomposition. -/
noncomputable def singletonSegmentBONGFamily (b : BONG V q L n) :
    (singletonSegmentDecomposition b).ComponentBONGFamily := by
  intro i
  have hi : i = 0 := Subsingleton.elim i 0
  subst i
  let w := SegmentWitness.whole b
  exact w.bong.castLength w.bong.length_eq_finrank

/-- A BONG is literally the concatenation of the unique component in its
singleton whole-segment decomposition. -/
theorem singletonSegment_isPutTogether (b : BONG V q L n) :
    b.IsPutTogether (singletonSegmentDecomposition b)
      (singletonSegmentBONGFamily b) := by
  let D := singletonSegmentDecomposition b
  let c := singletonSegmentBONGFamily b
  let ranks : Fin 1 → Nat := D.componentRank
  have hlength : n = ranks 0 := by
    change n = finrank K (SegmentWitness.whole b).carrier
    exact (SegmentWitness.whole b).bong.length_eq_finrank
  have htotal : n = blockTotalRank 0 ranks :=
    hlength.trans (blockTotalRank_zero ranks).symm
  let e : Fin n ≃ Σ i : Fin 1, Fin (ranks i) :=
    (finCongr htotal).trans (blockIndexEquivSingleton ranks)
  have esnd (i : Fin n) : (e i).2.val = i.val := by
    simp [e, blockIndexEquivSingleton]
  refine ⟨{
    indexEquiv := e
    order_iff := ?_
    ambientVector_eq := ?_ }⟩
  · intro i j
    constructor
    · intro hij
      right
      refine ⟨Subsingleton.elim _ _, ?_⟩
      change i.val < j.val at hij
      simpa only [esnd i, esnd j] using hij
    · intro hij
      rcases hij with hcomponent | ⟨_, hlocal⟩
      · have hi : (e i).1 = 0 := Subsingleton.elim _ _
        have hj : (e j).1 = 0 := Subsingleton.elim _ _
        rw [hi, hj] at hcomponent
        exact (lt_irrefl _ hcomponent).elim
      · change i.val < j.val
        simpa only [esnd i, esnd j] using hlocal
  · intro i
    rcases he : e i with ⟨k, z⟩
    have hk : k = 0 := Subsingleton.elim _ _
    subst k
    have hzval : z.val = i.val := by
      have hs := esnd i
      rw [he] at hs
      exact hs
    have hz : z = Fin.cast hlength i := by
      apply Fin.ext
      exact hzval
    subst z
    change b.ambientVector i =
      (((SegmentWitness.whole b).bong.castLength _).ambientVector
        (Fin.cast hlength i) : V)
    rw [BONG.ambientVector_castLength,
      (SegmentWitness.whole b).ambientVector_eq]
    congr 1
    apply Fin.ext
    simp

/-- A Jordan decomposition adapted to a nonempty property-A BONG, together
with the endpoint formulas used by the recursive step. -/
structure PropertyAJordanWitness (b : BONG V q L n) where
  /-- The adapted BONG is nonempty. -/
  length_pos : 0 < n
  /-- One less than the number of Jordan blocks. -/
  blockCount : Nat
  /-- The Jordan decomposition whose blocks are consecutive BONG segments. -/
  jordan : Lattice.JordanDecomposition q L (blockCount + 1)
  /-- The decomposition has Beli's property A. -/
  propertyA : jordan.HasPropertyA
  /-- The selected BONG in each component. -/
  componentBONG : jordan.toOrthogonalDecomposition.ComponentBONGFamily
  /-- The original BONG is their literal ordered concatenation. -/
  putTogether : b.IsPutTogether jordan.toOrthogonalDecomposition componentBONG
  /-- Size of the first block. -/
  firstBlockLength : Nat
  firstBlockLength_pos : 0 < firstBlockLength
  firstBlockLength_le : firstBlockLength ≤ n
  firstBlockLength_one_or_two : firstBlockLength = 1 ∨ firstBlockLength = 2
  firstComponentRank : jordan.componentRank 0 = firstBlockLength
  /-- The first component norm order is the first BONG order. -/
  firstNormOrder :
    ordUnit K (jordan.normGenerator 0) = b.order ⟨0, length_pos⟩
  /-- `2s-u` is the order at the last coordinate of the first block. -/
  firstDualOrder :
    2 * ordUnit K (jordan.scaleGenerator 0) -
        ordUnit K (jordan.normGenerator 0) =
      b.order ⟨firstBlockLength - 1, by omega⟩

/-- A single unary or binary modular block gives the terminal witness in the
property-A recursion. -/
noncomputable def singletonPropertyAJordanWitness
    (b : BONG V q L (n + 1))
    (hsize : n + 1 = 1 ∨ n + 1 = 2)
    (a : Kˣ)
    (hmodular : Lattice.IsModular
      (q.restrict (SegmentWitness.whole b).carrier
        (SegmentWitness.whole b).nondegenerate)
      (SegmentWitness.whole b).lattice a)
    (hdual :
      2 * ordUnit K a -
          ordUnit K ((SegmentWitness.whole b).bong.valueUnit 0) =
        b.order ⟨n, Nat.lt_succ_self n⟩) :
    PropertyAJordanWitness b := by
  let w := SegmentWitness.whole b
  let D := singletonSegmentDecomposition b
  let c := singletonSegmentBONGFamily b
  let norm : Kˣ := w.bong.valueUnit 0
  let scale : Kˣ := a
  let J : Lattice.JordanDecomposition q L 1 := {
    toOrthogonalDecomposition := D
    scaleGenerator := fun _ ↦ scale
    normGenerator := fun _ ↦ norm
    modular := by
      intro i
      have hi : i = 0 := Subsingleton.elim i 0
      subst i
      exact hmodular
    scaleIdeal_eq := by
      intro i
      have hi : i = 0 := Subsingleton.elim i 0
      subst i
      apply hmodular.scaleIdeal_eq_principal
      change 0 < finrank K w.carrier
      have hlen := w.bong.length_eq_finrank
      omega
    normIdeal_eq := by
      intro i
      have hi : i = 0 := Subsingleton.elim i 0
      subst i
      change Lattice.normIdeal
          (q.restrict w.carrier w.nondegenerate) w.lattice =
        Lattice.principalIdeal (K := K) (norm : K)
      simpa [norm, ← w.bong.value_zero_eq_quadratic_head] using
        w.bong.head_isNormGenerator.normIdeal_eq
    scaleOrder_strict := by
      intro i j hij
      exact (ne_of_lt hij (Subsingleton.elim i j)).elim }
  have hproperty : J.HasPropertyA := by
    constructor
    · intro i
      have hi : i = 0 := Subsingleton.elim i 0
      subst i
      change finrank K w.carrier = 1 ∨ finrank K w.carrier = 2
      rw [← w.bong.length_eq_finrank]
      exact hsize
    · intro i j hij
      exact (ne_of_lt hij (Subsingleton.elim i j)).elim
  refine {
    length_pos := Nat.succ_pos n
    blockCount := 0
    jordan := J
    propertyA := hproperty
    componentBONG := c
    putTogether := singletonSegment_isPutTogether b
    firstBlockLength := n + 1
    firstBlockLength_pos := Nat.succ_pos n
    firstBlockLength_le := le_rfl
    firstBlockLength_one_or_two := hsize
    firstComponentRank := ?_
    firstNormOrder := ?_
    firstDualOrder := ?_ }
  · change finrank K w.carrier = n + 1
    exact w.bong.length_eq_finrank.symm
  · change ordUnit K norm = b.order 0
    rw [← w.bong.order_eq_ordUnit]
    simpa [w, SegmentWitness.sourceIndex] using w.order_eq (0 : Fin (n + 1))
  · change 2 * ordUnit K scale - ordUnit K norm =
      b.order ⟨n + 1 - 1, by omega⟩
    simpa [scale, norm] using hdual

/-- Terminal unary block in the adapted Jordan recursion. -/
noncomputable def propertyAJordanWitnessOne (b : BONG V q L 1) :
    PropertyAJordanWitness b := by
  let w := SegmentWitness.whole b
  have hmodular : Lattice.IsModular
      (q.restrict w.carrier w.nondegenerate) w.lattice
      (w.bong.valueUnit 0) :=
    w.bong.isModular_valueUnit_zero_unary
  have hdual :
      2 * ordUnit K (w.bong.valueUnit 0) -
          ordUnit K (w.bong.valueUnit 0) =
        b.order (0 : Fin 1) := by
    rw [two_mul, add_sub_cancel_left]
    rw [← w.bong.order_eq_ordUnit]
    simpa [w, SegmentWitness.sourceIndex] using w.order_eq (0 : Fin 1)
  exact singletonPropertyAJordanWitness b (Or.inl rfl)
    (w.bong.valueUnit 0) hmodular hdual

/-- Terminal modular binary block in the adapted Jordan recursion. -/
noncomputable def propertyAJordanWitnessTwo (b : BONG V q L 2)
    (horder : b.order 1 ≤ b.order 0) : PropertyAJordanWitness b := by
  let w := SegmentWitness.whole b
  have horderW : w.bong.order 1 ≤ w.bong.order 0 := by
    simpa [w, SegmentWitness.sourceIndex] using horder
  let hexists :=
    (w.bong.exists_isModular_iff_order_one_le_order_zero).2 horderW
  let a := Classical.choose hexists
  have hmodular : Lattice.IsModular
      (q.restrict w.carrier w.nondegenerate) w.lattice a :=
    Classical.choose_spec hexists
  have hformula := w.bong.order_one_eq_of_isModular a hmodular
  have hdual :
      2 * ordUnit K a - ordUnit K (w.bong.valueUnit 0) =
        b.order (1 : Fin 2) := by
    rw [← w.bong.order_eq_ordUnit]
    rw [← hformula]
    simpa [w, SegmentWitness.sourceIndex] using w.order_eq (1 : Fin 2)
  exact singletonPropertyAJordanWitness b (Or.inr rfl)
    a hmodular hdual

/-- Transport a BONG across equality of ambient quadratic sublattices. -/
noncomputable def castQuadraticSublattice
    {C D : Lattice.QuadraticSublattice q} {m : Nat}
    (b : BONG C.carrier C.space C.lattice m) (h : C = D) :
    BONG D.carrier D.space D.lattice m := by
  subst D
  exact b

/-- Transport across equality of quadratic sublattices preserves the ambient
vector in the original quadratic space. -/
@[simp]
theorem ambientVector_castQuadraticSublattice
    {C D : Lattice.QuadraticSublattice q} {m : Nat}
    (b : BONG C.carrier C.space C.lattice m) (h : C = D) (i : Fin m) :
    (((b.castQuadraticSublattice h).ambientVector i : D.carrier) : V) =
      ((b.ambientVector i : C.carrier) : V) := by
  subst D
  rfl

@[simp]
theorem prependNestedSegment_component_zero
    {N cut t : Nat} (b : BONG V q L N) (hcut : cut ≤ N)
    (S : TwoBlockSplitWitness b cut hcut)
    (E : Lattice.OrthogonalDecomposition
      (q.restrict S.right.carrier S.right.nondegenerate) S.right.lattice t) :
    (S.decomposition.prependNestedOfEq S.right.toQuadraticSublattice
      S.component_one E).component 0 = S.left.toQuadraticSublattice := by
  rw [Lattice.OrthogonalDecomposition.prependNestedOfEq_zero,
    S.component_zero]

@[simp]
theorem prependNestedSegment_component_succ
    {N cut t : Nat} (b : BONG V q L N) (hcut : cut ≤ N)
    (S : TwoBlockSplitWitness b cut hcut)
    (E : Lattice.OrthogonalDecomposition
      (q.restrict S.right.carrier S.right.nondegenerate) S.right.lattice t)
    (i : Fin t) :
    (S.decomposition.prependNestedOfEq S.right.toQuadraticSublattice
      S.component_one E).component i.succ =
      S.right.toQuadraticSublattice.liftNested (E.component i) := by
  exact Lattice.OrthogonalDecomposition.prependNestedOfEq_succ
    S.decomposition S.right.toQuadraticSublattice S.component_one E i

@[simp]
theorem prependNestedSegment_componentRank_zero
    {N cut t : Nat} (b : BONG V q L N) (hcut : cut ≤ N)
    (S : TwoBlockSplitWitness b cut hcut)
    (E : Lattice.OrthogonalDecomposition
      (q.restrict S.right.carrier S.right.nondegenerate) S.right.lattice t) :
    (S.decomposition.prependNestedOfEq S.right.toQuadraticSublattice
      S.component_one E).componentRank 0 = cut := by
  change finrank K
      ((S.decomposition.prependNestedOfEq S.right.toQuadraticSublattice
        S.component_one E).component 0).carrier = cut
  rw [Lattice.OrthogonalDecomposition.prependNestedOfEq_zero,
    S.component_zero]
  exact S.left.bong.length_eq_finrank.symm

@[simp]
theorem prependNestedSegment_componentRank_succ
    {N cut t : Nat} (b : BONG V q L N) (hcut : cut ≤ N)
    (S : TwoBlockSplitWitness b cut hcut)
    (E : Lattice.OrthogonalDecomposition
      (q.restrict S.right.carrier S.right.nondegenerate) S.right.lattice t)
    (i : Fin t) :
    (S.decomposition.prependNestedOfEq S.right.toQuadraticSublattice
      S.component_one E).componentRank i.succ = E.componentRank i := by
  change finrank K
      ((S.decomposition.prependNestedOfEq S.right.toQuadraticSublattice
        S.component_one E).component i.succ).carrier =
    finrank K (E.component i).carrier
  rw [Lattice.OrthogonalDecomposition.prependNestedOfEq_succ,
    S.right.toQuadraticSublattice.finrank_liftNested]
  rfl

/-- The head BONG in a nested prepend, isolated so its transport is reduced
only once. -/
noncomputable def prependNestedSegmentHeadBONG
    {N cut t : Nat} (b : BONG V q L N) (hcut : cut ≤ N)
    (S : TwoBlockSplitWitness b cut hcut)
    (E : Lattice.OrthogonalDecomposition
      (q.restrict S.right.carrier S.right.nondegenerate) S.right.lattice t) :
    BONG
      ((S.decomposition.prependNestedOfEq S.right.toQuadraticSublattice
        S.component_one E).component 0).carrier
      (q.restrict
        ((S.decomposition.prependNestedOfEq S.right.toQuadraticSublattice
          S.component_one E).component 0).carrier
        ((S.decomposition.prependNestedOfEq S.right.toQuadraticSublattice
          S.component_one E).component 0).nondegenerate)
      ((S.decomposition.prependNestedOfEq S.right.toQuadraticSublattice
        S.component_one E).component 0).lattice
      ((S.decomposition.prependNestedOfEq S.right.toQuadraticSublattice
        S.component_one E).componentRank 0) :=
  (S.left.bong.castQuadraticSublattice
      (prependNestedSegment_component_zero b hcut S E).symm).castLength
    (prependNestedSegment_componentRank_zero b hcut S E).symm

/-- A lifted tail BONG in a nested prepend. -/
noncomputable def prependNestedSegmentTailBONG
    {N cut t : Nat} (b : BONG V q L N) (hcut : cut ≤ N)
    (S : TwoBlockSplitWitness b cut hcut)
    (E : Lattice.OrthogonalDecomposition
      (q.restrict S.right.carrier S.right.nondegenerate) S.right.lattice t)
    (d : E.ComponentBONGFamily) (i : Fin t) :
    BONG
      ((S.decomposition.prependNestedOfEq S.right.toQuadraticSublattice
        S.component_one E).component i.succ).carrier
      (q.restrict
        ((S.decomposition.prependNestedOfEq S.right.toQuadraticSublattice
          S.component_one E).component i.succ).carrier
        ((S.decomposition.prependNestedOfEq S.right.toQuadraticSublattice
          S.component_one E).component i.succ).nondegenerate)
      ((S.decomposition.prependNestedOfEq S.right.toQuadraticSublattice
        S.component_one E).component i.succ).lattice
      ((S.decomposition.prependNestedOfEq S.right.toQuadraticSublattice
        S.component_one E).componentRank i.succ) :=
  (castQuadraticSublattice
    ((d i).mapLatticeIsometry
      (S.right.toQuadraticSublattice.liftNestedIsometry (E.component i)))
    (prependNestedSegment_component_succ b hcut S E i).symm).castLength
    (prependNestedSegment_componentRank_succ b hcut S E i).symm

/-- Prepend the BONG of the left segment to component BONGs living in the
right segment, lifting every nested tail component back to the ambient
quadratic space. -/
noncomputable def prependNestedSegmentBONGFamily
    {N cut t : Nat} (b : BONG V q L N) (hcut : cut ≤ N)
    (S : TwoBlockSplitWitness b cut hcut)
    (E : Lattice.OrthogonalDecomposition
      (q.restrict S.right.carrier S.right.nondegenerate) S.right.lattice t)
    (d : E.ComponentBONGFamily) :
    (S.decomposition.prependNestedOfEq S.right.toQuadraticSublattice
      S.component_one E).ComponentBONGFamily :=
  Fin.cases (prependNestedSegmentHeadBONG b hcut S E)
    (prependNestedSegmentTailBONG b hcut S E d)

@[simp]
theorem prependNestedSegmentBONGFamily_zero
    {N cut t : Nat} (b : BONG V q L N) (hcut : cut ≤ N)
    (S : TwoBlockSplitWitness b cut hcut)
    (E : Lattice.OrthogonalDecomposition
      (q.restrict S.right.carrier S.right.nondegenerate) S.right.lattice t)
    (d : E.ComponentBONGFamily) :
    prependNestedSegmentBONGFamily b hcut S E d 0 =
      prependNestedSegmentHeadBONG b hcut S E := by
  rfl

@[simp]
theorem prependNestedSegmentBONGFamily_succ
    {N cut t : Nat} (b : BONG V q L N) (hcut : cut ≤ N)
    (S : TwoBlockSplitWitness b cut hcut)
    (E : Lattice.OrthogonalDecomposition
      (q.restrict S.right.carrier S.right.nondegenerate) S.right.lattice t)
    (d : E.ComponentBONGFamily) (i : Fin t) :
    prependNestedSegmentBONGFamily b hcut S E d i.succ =
      prependNestedSegmentTailBONG b hcut S E d i := by
  rfl

set_option maxHeartbeats 1000000 in
/-- The first lifted component family retains the left-segment vectors. -/
theorem prependNestedSegmentBONGFamily_ambientVector_zero
    {N cut t : Nat} (b : BONG V q L N) (hcut : cut ≤ N)
    (S : TwoBlockSplitWitness b cut hcut)
    (E : Lattice.OrthogonalDecomposition
      (q.restrict S.right.carrier S.right.nondegenerate) S.right.lattice t)
    (d : E.ComponentBONGFamily) (j : Fin cut) :
    ((((prependNestedSegmentBONGFamily b hcut S E d) 0).ambientVector
        (Fin.cast
          (prependNestedSegment_componentRank_zero b hcut S E).symm j) :
      ((S.decomposition.prependNestedOfEq S.right.toQuadraticSublattice
        S.component_one E).component 0).carrier) : V) =
      b.ambientVector (S.left.sourceIndex j) := by
  rw [prependNestedSegmentBONGFamily_zero]
  rw [prependNestedSegmentHeadBONG, BONG.ambientVector_castLength,
    ambientVector_castQuadraticSublattice]
  let j' : Fin cut :=
    ⟨(Fin.cast
      (prependNestedSegment_componentRank_zero b hcut S E).symm j).val,
      by simpa only [Fin.val_cast] using j.isLt⟩
  change ((S.left.bong.ambientVector j' : S.left.carrier) : V) =
    b.ambientVector (S.left.sourceIndex j)
  have hj : j' = j := by
    apply Fin.ext
    rfl
  subst j'
  exact S.left.ambientVector_eq j

set_option maxHeartbeats 1000000 in
/-- Every lifted tail component retains the corresponding vector of the
tail decomposition. -/
theorem prependNestedSegmentBONGFamily_ambientVector_succ
    {N cut t : Nat} (b : BONG V q L N) (hcut : cut ≤ N)
    (S : TwoBlockSplitWitness b cut hcut)
    (E : Lattice.OrthogonalDecomposition
      (q.restrict S.right.carrier S.right.nondegenerate) S.right.lattice t)
    (d : E.ComponentBONGFamily) (i : Fin t)
    (j : Fin (E.componentRank i)) :
    ((((prependNestedSegmentBONGFamily b hcut S E d) i.succ).ambientVector
        (Fin.cast
          (prependNestedSegment_componentRank_succ b hcut S E i).symm j) :
      ((S.decomposition.prependNestedOfEq S.right.toQuadraticSublattice
        S.component_one E).component i.succ).carrier) : V) =
      ((((d i).ambientVector j : (E.component i).carrier) :
        S.right.carrier) : V) := by
  rw [prependNestedSegmentBONGFamily_succ,
    prependNestedSegmentTailBONG, BONG.ambientVector_castLength,
    ambientVector_castQuadraticSublattice,
    BONG.ambientVector_mapLatticeIsometry]
  let j' : Fin (E.componentRank i) :=
    ⟨(Fin.cast
      (prependNestedSegment_componentRank_succ b hcut S E i).symm j).val,
      by simpa only [Fin.val_cast] using j.isLt⟩
  change ((((d i).ambientVector j' : (E.component i).carrier) :
      S.right.carrier) : V) = _
  have hj : j' = j := by
    apply Fin.ext
    rfl
  subst j'
  rfl

/-- `blockIndexEquivCons` preserves the usual order whenever the recursively
supplied tail equivalence preserves lexicographic block order. -/
theorem blockIndexEquivCons_order_iff_lex
    (k : Nat) (ranks : Fin (k + 2) → Nat)
    (tail : Fin (blockTotalRank k (fun i ↦ ranks i.succ)) ≃
      Σ i : Fin (k + 1), Fin (ranks i.succ))
    (htail : ∀ i j, i < j ↔
      BlockIndexBefore (tail i) (tail j))
    (i j : Fin (blockTotalRank (k + 1) ranks)) :
    i < j ↔ BlockIndexBefore
      (blockIndexEquivCons k ranks tail i)
      (blockIndexEquivCons k ranks tail j) := by
  let tailLength := blockTotalRank k (fun h ↦ ranks h.succ)
  let e := blockIndexEquivCons k ranks tail
  by_cases hi : i.val < ranks 0
  · let ii : Fin (ranks 0) := ⟨i.val, hi⟩
    have hiEq : i = blockLeftIndex k ranks ii := by
      apply Fin.ext
      rfl
    by_cases hj : j.val < ranks 0
    · let jj : Fin (ranks 0) := ⟨j.val, hj⟩
      have hjEq : j = blockLeftIndex k ranks jj := by
        apply Fin.ext
        rfl
      rw [hiEq, hjEq]
      simp only [e, blockIndexEquivCons_left]
      simp [BlockIndexBefore]
      rfl
    · have hjBound : j.val - ranks 0 < tailLength := by
        have hjLt : j.val < ranks 0 + tailLength := by
          calc
            j.val < blockTotalRank (k + 1) ranks := j.isLt
            _ = ranks 0 + tailLength := blockTotalRank_succ k ranks
        omega
      let jj : Fin tailLength := ⟨j.val - ranks 0, hjBound⟩
      have hjEq : j = blockRightIndex k ranks jj := by
        apply Fin.ext
        simp [jj]
        omega
      rw [hiEq, hjEq]
      simp only [e, blockIndexEquivCons_left,
        blockIndexEquivCons_right]
      simp [BlockIndexBefore]
      omega
  · have hiBound : i.val - ranks 0 < tailLength := by
      have hiLt : i.val < ranks 0 + tailLength := by
        calc
          i.val < blockTotalRank (k + 1) ranks := i.isLt
          _ = ranks 0 + tailLength := blockTotalRank_succ k ranks
      omega
    let ii : Fin tailLength := ⟨i.val - ranks 0, hiBound⟩
    have hiEq : i = blockRightIndex k ranks ii := by
      apply Fin.ext
      simp [ii]
      omega
    by_cases hj : j.val < ranks 0
    · let jj : Fin (ranks 0) := ⟨j.val, hj⟩
      have hjEq : j = blockLeftIndex k ranks jj := by
        apply Fin.ext
        rfl
      rw [hiEq, hjEq]
      simp only [e, blockIndexEquivCons_right,
        blockIndexEquivCons_left]
      simp [BlockIndexBefore]
      omega
    · have hjBound : j.val - ranks 0 < tailLength := by
        have hjLt : j.val < ranks 0 + tailLength := by
          calc
            j.val < blockTotalRank (k + 1) ranks := j.isLt
            _ = ranks 0 + tailLength := blockTotalRank_succ k ranks
        omega
      let jj : Fin tailLength := ⟨j.val - ranks 0, hjBound⟩
      have hjEq : j = blockRightIndex k ranks jj := by
        apply Fin.ext
        simp [jj]
        omega
      rw [hiEq, hjEq]
      change ranks 0 + ii.val < ranks 0 + jj.val ↔
        BlockIndexBefore (e (blockRightIndex k ranks ii))
          (e (blockRightIndex k ranks jj))
      rw [Nat.add_lt_add_iff_left]
      change ii < jj ↔
        BlockIndexBefore (e (blockRightIndex k ranks ii))
          (e (blockRightIndex k ranks jj))
      rw [htail]
      simp only [e, blockIndexEquivCons_right]
      simp [BlockIndexBefore]

/-- Pointwise casts of finite fibers induce an equivalence of dependent
sums, without changing either coordinate value. -/
def sigmaFinCastEquiv {t : Nat} (r s : Fin t → Nat)
    (h : ∀ i, r i = s i) :
    (Σ i, Fin (r i)) ≃ Σ i, Fin (s i) where
  toFun z := ⟨z.1, Fin.cast (h z.1) z.2⟩
  invFun z := ⟨z.1, Fin.cast (h z.1).symm z.2⟩
  left_inv z := by
    rcases z with ⟨i, j⟩
    apply Sigma.ext
    · rfl
    · simp
  right_inv z := by
    rcases z with ⟨i, j⟩
    apply Sigma.ext
    · rfl
    · simp

@[simp]
theorem sigmaFinCastEquiv_fst {t : Nat} (r s : Fin t → Nat)
    (h : ∀ i, r i = s i) (z : Σ i, Fin (r i)) :
    (sigmaFinCastEquiv r s h z).1 = z.1 :=
  rfl

@[simp]
theorem sigmaFinCastEquiv_snd_val {t : Nat} (r s : Fin t → Nat)
    (h : ∀ i, r i = s i) (z : Σ i, Fin (r i)) :
    (sigmaFinCastEquiv r s h z).2.val = z.2.val :=
  rfl

set_option maxHeartbeats 1000000 in
/-- Prepending a consecutive segment and lifting a tail concatenation gives a
concatenation for the flattened decomposition. -/
theorem prependNestedSegment_isPutTogether
    {N cut k : Nat} (b : BONG V q L N) (hcut : cut ≤ N)
    (S : TwoBlockSplitWitness b cut hcut)
    (E : Lattice.OrthogonalDecomposition
      (q.restrict S.right.carrier S.right.nondegenerate) S.right.lattice
        (k + 1))
    (d : E.ComponentBONGFamily)
    (htogether : S.right.bong.IsPutTogether E d) :
    b.IsPutTogether
      (S.decomposition.prependNestedOfEq S.right.toQuadraticSublattice
        S.component_one E)
      (prependNestedSegmentBONGFamily b hcut S E d) := by
  rcases htogether with ⟨w⟩
  let D := S.decomposition.prependNestedOfEq
    S.right.toQuadraticSublattice S.component_one E
  let c := prependNestedSegmentBONGFamily b hcut S E d
  let ranks : Fin (k + 2) → Nat := D.componentRank
  have hheadRank : ranks 0 = cut := by
    change finrank K (D.component 0).carrier = cut
    rw [show D = S.decomposition.prependNestedOfEq
      S.right.toQuadraticSublattice S.component_one E by rfl,
      Lattice.OrthogonalDecomposition.prependNestedOfEq_zero,
      S.component_zero]
    exact S.left.bong.length_eq_finrank.symm
  have htailRank (i : Fin (k + 1)) :
      E.componentRank i = ranks i.succ := by
    change finrank K (E.component i).carrier =
      finrank K (D.component i.succ).carrier
    rw [show D = S.decomposition.prependNestedOfEq
      S.right.toQuadraticSublattice S.component_one E by rfl,
      Lattice.OrthogonalDecomposition.prependNestedOfEq_succ,
      S.right.toQuadraticSublattice.finrank_liftNested]
    rfl
  let fiberCast := sigmaFinCastEquiv E.componentRank
    (fun i : Fin (k + 1) ↦ ranks i.succ) htailRank
  let tailE : Fin (N - cut) ≃
      Σ i : Fin (k + 1), Fin (ranks i.succ) :=
    w.indexEquiv.trans fiberCast
  have htailTotal : N - cut =
      blockTotalRank k (fun i ↦ ranks i.succ) := by
    have hcard := Fintype.card_congr tailE
    simpa [blockTotalRank] using hcard
  let tailE' : Fin (blockTotalRank k (fun i ↦ ranks i.succ)) ≃
      Σ i : Fin (k + 1), Fin (ranks i.succ) :=
    (finCongr htailTotal).symm.trans tailE
  have htailOrder : ∀ i j, i < j ↔
      BlockIndexBefore (tailE' i) (tailE' j) := by
    intro i j
    have h := w.order_iff
      ((finCongr htailTotal).symm i)
      ((finCongr htailTotal).symm j)
    simpa [tailE', tailE, fiberCast, BlockIndexBefore,
      ComponentIndexBefore] using h
  have htotal : N = blockTotalRank (k + 1) ranks := by
    rw [blockTotalRank_succ, hheadRank, ← htailTotal]
    omega
  let blockE := blockIndexEquivCons k ranks tailE'
  let e : Fin N ≃ Σ i, Fin (ranks i) :=
    (finCongr htotal).trans blockE
  refine ⟨{
    indexEquiv := e
    order_iff := ?_
    ambientVector_eq := ?_ }⟩
  · intro i j
    have h := blockIndexEquivCons_order_iff_lex k ranks tailE'
      htailOrder (Fin.cast htotal i) (Fin.cast htotal j)
    have hci : (finCongr htotal) i = Fin.cast htotal i := rfl
    have hcj : (finCongr htotal) j = Fin.cast htotal j := rfl
    change i < j ↔ BlockIndexBefore
      (blockE ((finCongr htotal) i))
      (blockE ((finCongr htotal) j))
    rw [hci, hcj]
    exact h
  · intro i
    by_cases hi : i.val < cut
    · let ii : Fin (ranks 0) := ⟨i.val, by rw [hheadRank]; exact hi⟩
      have hig : Fin.cast htotal i = blockLeftIndex k ranks ii := by
        apply Fin.ext
        rfl
      have hei : e i = ⟨0, ii⟩ := by
        change blockE (Fin.cast htotal i) = ⟨0, ii⟩
        rw [hig]
        exact blockIndexEquivCons_left k ranks tailE' ii
      rw [hei]
      change b.ambientVector i =
        ((((prependNestedSegmentBONGFamily b hcut S E d) 0).ambientVector ii :
          ((S.decomposition.prependNestedOfEq
            S.right.toQuadraticSublattice S.component_one E).component
              0).carrier) : V)
      let j : Fin cut := Fin.cast hheadRank ii
      have hlocal :
          Fin.cast
              (prependNestedSegment_componentRank_zero b hcut S E).symm j =
            ii := by
        apply Fin.ext
        rfl
      rw [← hlocal,
        prependNestedSegmentBONGFamily_ambientVector_zero]
      apply congrArg b.ambientVector
      apply Fin.ext
      simp [j, ii, SegmentWitness.sourceIndex]
    · have hright : cut ≤ i.val := Nat.le_of_not_gt hi
      let jj : Fin (N - cut) := ⟨i.val - cut, by omega⟩
      let jj' : Fin (blockTotalRank k (fun h ↦ ranks h.succ)) :=
        Fin.cast htailTotal jj
      have hig : Fin.cast htotal i = blockRightIndex k ranks jj' := by
        apply Fin.ext
        change i.val = ranks 0 + jj'.val
        rw [hheadRank]
        dsimp only [jj']
        simp only [Fin.val_cast]
        dsimp only [jj]
        omega
      have hei : e i =
          ⟨(tailE' jj').1.succ, (tailE' jj').2⟩ := by
        change blockE (Fin.cast htotal i) = _
        rw [hig]
        exact blockIndexEquivCons_right k ranks tailE' jj'
      rw [hei]
      let z := w.indexEquiv jj
      have htailEq : tailE' jj' = fiberCast z := by
        change fiberCast
            (w.indexEquiv ((finCongr htailTotal).symm jj')) = fiberCast z
        congr 2
      rw [htailEq]
      have hfiber : fiberCast z =
          ⟨z.1, Fin.cast (htailRank z.1) z.2⟩ := by
        rfl
      rw [hfiber]
      change b.ambientVector i =
        ((((prependNestedSegmentBONGFamily b hcut S E d) z.1.succ).ambientVector
          (Fin.cast (htailRank z.1) z.2) :
          ((S.decomposition.prependNestedOfEq
            S.right.toQuadraticSublattice S.component_one E).component
              z.1.succ).carrier) : V)
      have hlocal :
          Fin.cast
              (prependNestedSegment_componentRank_succ b hcut S E z.1).symm
              z.2 =
            Fin.cast (htailRank z.1) z.2 := by
        apply Fin.ext
        rfl
      rw [← hlocal,
        prependNestedSegmentBONGFamily_ambientVector_succ,
        ← w.ambientVector_eq jj,
        S.right.ambientVector_eq]
      apply congrArg b.ambientVector
      apply Fin.ext
      dsimp [jj, SegmentWitness.sourceIndex]
      omega

/-- Property A makes the component norm orders strictly increase from the
first Jordan block. -/
theorem PropertyAJordanWitness.firstNormOrder_lt
    {N : Nat} {b : BONG V q L N} (T : PropertyAJordanWitness b)
    (j : Fin (T.blockCount + 1)) (hj : (0 : Fin (T.blockCount + 1)) < j) :
    ordUnit K (T.jordan.normGenerator 0) <
      ordUnit K (T.jordan.normGenerator j) := by
  have h := T.propertyA.2 hj
  omega

/-- The complementary orders `2s-u` also strictly increase between
property-A Jordan blocks. -/
theorem PropertyAJordanWitness.firstDualOrder_lt
    {N : Nat} {b : BONG V q L N} (T : PropertyAJordanWitness b)
    (j : Fin (T.blockCount + 1)) (hj : (0 : Fin (T.blockCount + 1)) < j) :
    2 * ordUnit K (T.jordan.scaleGenerator 0) -
        ordUnit K (T.jordan.normGenerator 0) <
      2 * ordUnit K (T.jordan.scaleGenerator j) -
        ordUnit K (T.jordan.normGenerator j) := by
  have h := T.propertyA.2 hj
  omega

set_option maxHeartbeats 1000000 in
-- The dependent transports through the nested orthogonal decomposition make
-- this constructor substantially more expensive than its arithmetic content.
/-- Prepend one unary or binary modular BONG segment to an adapted
property-A Jordan decomposition of the right segment. -/
noncomputable def PropertyAJordanWitness.prepend
    {N cut : Nat} (b : BONG V q L N) (hcut : cut ≤ N)
    (S : TwoBlockSplitWitness b cut hcut)
    (T : PropertyAJordanWitness S.right.bong)
    (hcutPos : 0 < cut) (hsize : cut = 1 ∨ cut = 2)
    (a : Kˣ)
    (hmodular : Lattice.IsModular
      (q.restrict S.left.carrier S.left.nondegenerate) S.left.lattice a)
    (hdual :
      2 * ordUnit K a -
          ordUnit K (S.left.bong.valueUnit ⟨0, hcutPos⟩) =
        b.order ⟨cut - 1, by omega⟩)
    (hcrossNorm :
      ordUnit K (S.left.bong.valueUnit ⟨0, hcutPos⟩) <
        ordUnit K (T.jordan.normGenerator 0))
    (hcrossDual :
      2 * ordUnit K a -
          ordUnit K (S.left.bong.valueUnit ⟨0, hcutPos⟩) <
        2 * ordUnit K (T.jordan.scaleGenerator 0) -
          ordUnit K (T.jordan.normGenerator 0)) :
    PropertyAJordanWitness b := by
  let E := T.jordan.toOrthogonalDecomposition
  let D := S.decomposition.prependNestedOfEq
    S.right.toQuadraticSublattice S.component_one E
  let headNorm : Kˣ := S.left.bong.valueUnit ⟨0, hcutPos⟩
  let scale : Fin ((T.blockCount + 1) + 1) → Kˣ :=
    Fin.cases a T.jordan.scaleGenerator
  let norm : Fin ((T.blockCount + 1) + 1) → Kˣ :=
    Fin.cases headNorm T.jordan.normGenerator
  have hscaleFirst : ordUnit K a <
      ordUnit K (T.jordan.scaleGenerator 0) := by
    change ordUnit K headNorm < ordUnit K (T.jordan.normGenerator 0)
      at hcrossNorm
    change 2 * ordUnit K a - ordUnit K headNorm <
        2 * ordUnit K (T.jordan.scaleGenerator 0) -
          ordUnit K (T.jordan.normGenerator 0) at hcrossDual
    omega
  let J : Lattice.JordanDecomposition q L ((T.blockCount + 1) + 1) := {
    toOrthogonalDecomposition := D
    scaleGenerator := scale
    normGenerator := norm
    modular := by
      intro i
      cases i using Fin.cases with
      | zero =>
          change Lattice.IsModular (D.component 0).space
            (D.component 0).lattice a
          rw [show D = S.decomposition.prependNestedOfEq
            S.right.toQuadraticSublattice S.component_one E by rfl,
            show E = T.jordan.toOrthogonalDecomposition by rfl,
            prependNestedSegment_component_zero]
          exact hmodular
      | succ i =>
          change Lattice.IsModular (D.component i.succ).space
            (D.component i.succ).lattice (T.jordan.scaleGenerator i)
          rw [show D = S.decomposition.prependNestedOfEq
            S.right.toQuadraticSublattice S.component_one E by rfl,
            show E = T.jordan.toOrthogonalDecomposition by rfl,
            prependNestedSegment_component_succ]
          exact Lattice.QuadraticSublattice.IsModular.liftNested
            S.right.toQuadraticSublattice _ (T.jordan.modular i)
    scaleIdeal_eq := by
      intro i
      cases i using Fin.cases with
      | zero =>
          change Lattice.scaleIdeal (D.component 0).space
              (D.component 0).lattice =
            Lattice.principalIdeal (K := K) (a : K)
          rw [show D = S.decomposition.prependNestedOfEq
            S.right.toQuadraticSublattice S.component_one E by rfl,
            show E = T.jordan.toOrthogonalDecomposition by rfl,
            prependNestedSegment_component_zero]
          exact hmodular.scaleIdeal_eq_principal (by
            rw [← S.left.bong.length_eq_finrank]
            exact hcutPos)
      | succ i =>
          change Lattice.scaleIdeal (D.component i.succ).space
              (D.component i.succ).lattice =
            Lattice.principalIdeal (K := K)
              (T.jordan.scaleGenerator i : K)
          rw [show D = S.decomposition.prependNestedOfEq
            S.right.toQuadraticSublattice S.component_one E by rfl,
            show E = T.jordan.toOrthogonalDecomposition by rfl,
            prependNestedSegment_component_succ]
          apply (Lattice.QuadraticSublattice.IsModular.liftNested
            S.right.toQuadraticSublattice _
              (T.jordan.modular i)).scaleIdeal_eq_principal
          rw [S.right.toQuadraticSublattice.finrank_liftNested]
          change 0 < T.jordan.componentRank i
          rcases T.propertyA.1 i with h | h <;> omega
    normIdeal_eq := by
      intro i
      cases i using Fin.cases with
      | zero =>
          change Lattice.normIdeal (D.component 0).space
              (D.component 0).lattice =
            Lattice.principalIdeal (K := K) (headNorm : K)
          rw [show D = S.decomposition.prependNestedOfEq
            S.right.toQuadraticSublattice S.component_one E by rfl,
            show E = T.jordan.toOrthogonalDecomposition by rfl,
            prependNestedSegment_component_zero]
          have hgen :=
            S.left.bong.ambientVector_zero_isNormGenerator hcutPos
          calc
            Lattice.normIdeal
                (q.restrict S.left.carrier S.left.nondegenerate)
                S.left.lattice =
                Lattice.principalIdeal (K := K)
                  ((q.restrict S.left.carrier S.left.nondegenerate).quadratic
                    (S.left.bong.ambientVector ⟨0, hcutPos⟩)) :=
              hgen.normIdeal_eq
            _ = Lattice.principalIdeal (K := K) (headNorm : K) := by
              congr 1
              exact S.left.bong.quadratic_ambientVector ⟨0, hcutPos⟩
      | succ i =>
          change Lattice.normIdeal (D.component i.succ).space
              (D.component i.succ).lattice =
            Lattice.principalIdeal (K := K)
              (T.jordan.normGenerator i : K)
          rw [show D = S.decomposition.prependNestedOfEq
            S.right.toQuadraticSublattice S.component_one E by rfl,
            show E = T.jordan.toOrthogonalDecomposition by rfl,
            prependNestedSegment_component_succ]
          calc
            Lattice.normIdeal
                (S.right.toQuadraticSublattice.liftNested
                  (T.jordan.component i)).space
                (S.right.toQuadraticSublattice.liftNested
                  (T.jordan.component i)).lattice =
                Lattice.normIdeal (T.jordan.component i).space
                  (T.jordan.component i).lattice :=
              Lattice.normIdeal_map_isometry
                (S.right.toQuadraticSublattice.liftNestedIsometry
                  (T.jordan.component i)).toQuadraticSpaceIsometry
                (T.jordan.component i).lattice
            _ = Lattice.principalIdeal (K := K)
                (T.jordan.normGenerator i : K) :=
              T.jordan.normIdeal_eq i
    scaleOrder_strict := by
      intro i j hij
      cases i using Fin.cases with
      | zero =>
          cases j using Fin.cases with
          | zero => exact (lt_irrefl _ hij).elim
          | succ j =>
              change ordUnit K a <
                ordUnit K (T.jordan.scaleGenerator j)
              by_cases hj : j = 0
              · subst j
                exact hscaleFirst
              · exact hscaleFirst.trans
                  (T.jordan.scaleOrder_strict
                    ((Fin.pos_iff_ne_zero).2 hj))
      | succ i =>
          cases j using Fin.cases with
          | zero => exact (Nat.not_lt_zero i.succ.val hij).elim
          | succ j =>
              change ordUnit K (T.jordan.scaleGenerator i) <
                ordUnit K (T.jordan.scaleGenerator j)
              exact T.jordan.scaleOrder_strict
                (Nat.succ_lt_succ_iff.mp hij) }
  have hproperty : J.HasPropertyA := by
    constructor
    · intro i
      cases i using Fin.cases with
      | zero =>
          change D.componentRank 0 = 1 ∨ D.componentRank 0 = 2
          rw [show D = S.decomposition.prependNestedOfEq
            S.right.toQuadraticSublattice S.component_one E by rfl,
            show E = T.jordan.toOrthogonalDecomposition by rfl,
            prependNestedSegment_componentRank_zero]
          exact hsize
      | succ i =>
          change D.componentRank i.succ = 1 ∨ D.componentRank i.succ = 2
          rw [show D = S.decomposition.prependNestedOfEq
            S.right.toQuadraticSublattice S.component_one E by rfl,
            show E = T.jordan.toOrthogonalDecomposition by rfl,
            prependNestedSegment_componentRank_succ]
          exact T.propertyA.1 i
    · intro i j hij
      cases i using Fin.cases with
      | zero =>
          cases j using Fin.cases with
          | zero => exact (lt_irrefl _ hij).elim
          | succ j =>
              have hnorm : ordUnit K headNorm <
                  ordUnit K (T.jordan.normGenerator j) := by
                by_cases hj : j = 0
                · simpa [hj, headNorm] using hcrossNorm
                · exact (show ordUnit K headNorm <
                      ordUnit K (T.jordan.normGenerator 0) by
                        simpa [headNorm] using hcrossNorm).trans
                    (T.firstNormOrder_lt j ((Fin.pos_iff_ne_zero).2 hj))
              have hdual' : 2 * ordUnit K a - ordUnit K headNorm <
                  2 * ordUnit K (T.jordan.scaleGenerator j) -
                    ordUnit K (T.jordan.normGenerator j) := by
                by_cases hj : j = 0
                · simpa [hj, headNorm] using hcrossDual
                · exact (show 2 * ordUnit K a - ordUnit K headNorm <
                      2 * ordUnit K (T.jordan.scaleGenerator 0) -
                        ordUnit K (T.jordan.normGenerator 0) by
                        simpa [headNorm] using hcrossDual).trans
                    (T.firstDualOrder_lt j ((Fin.pos_iff_ne_zero).2 hj))
              change 0 < ordUnit K (T.jordan.normGenerator j) -
                    ordUnit K headNorm ∧
                ordUnit K (T.jordan.normGenerator j) - ordUnit K headNorm <
                  2 * (ordUnit K (T.jordan.scaleGenerator j) - ordUnit K a)
              constructor <;> omega
      | succ i =>
          cases j using Fin.cases with
          | zero => exact (Nat.not_lt_zero i.succ.val hij).elim
          | succ j =>
              change 0 < ordUnit K (T.jordan.normGenerator j) -
                    ordUnit K (T.jordan.normGenerator i) ∧
                ordUnit K (T.jordan.normGenerator j) -
                    ordUnit K (T.jordan.normGenerator i) <
                  2 * (ordUnit K (T.jordan.scaleGenerator j) -
                    ordUnit K (T.jordan.scaleGenerator i))
              exact T.propertyA.2 (Nat.succ_lt_succ_iff.mp hij)
  refine {
    length_pos := hcutPos.trans_le hcut
    blockCount := T.blockCount + 1
    jordan := J
    propertyA := hproperty
    componentBONG := prependNestedSegmentBONGFamily b hcut S E T.componentBONG
    putTogether := prependNestedSegment_isPutTogether b hcut S E
      T.componentBONG T.putTogether
    firstBlockLength := cut
    firstBlockLength_pos := hcutPos
    firstBlockLength_le := hcut
    firstBlockLength_one_or_two := hsize
    firstComponentRank := ?_
    firstNormOrder := ?_
    firstDualOrder := ?_ }
  · change D.componentRank 0 = cut
    rw [show D = S.decomposition.prependNestedOfEq
      S.right.toQuadraticSublattice S.component_one E by rfl,
      show E = T.jordan.toOrthogonalDecomposition by rfl,
      prependNestedSegment_componentRank_zero]
  · change ordUnit K headNorm = b.order ⟨0, hcutPos.trans_le hcut⟩
    rw [← S.left.bong.order_eq_ordUnit]
    simpa [headNorm, SegmentWitness.sourceIndex] using
      S.left.order_eq ⟨0, hcutPos⟩
  · change 2 * ordUnit K a - ordUnit K headNorm =
      b.order ⟨cut - 1, by omega⟩
    simpa [headNorm] using hdual

set_option maxHeartbeats 2000000 in
/-- A nonempty BONG satisfying the strict two-step inequalities admits the
Jordan blocking used in Beli (2003), Lemma 4.1(ii).  The recursion splits a
unary first block when `R₀ < R₁`; otherwise it splits a modular binary
first block. -/
theorem exists_propertyAJordanWitness_of_hasPropertyA_succ
    {m : Nat} (b : BONG V q L (m + 1)) (hA : b.HasPropertyA) :
    Nonempty (PropertyAJordanWitness b) := by
  induction m using Nat.strong_induction_on generalizing V with
  | h m ih =>
      cases m with
      | zero =>
          exact ⟨propertyAJordanWitnessOne b⟩
      | succ k =>
          have hgood : b.IsGood := hA.isGood
          by_cases hzeroOne : b.order 0 < b.order 1
          · have hsplit : b.HasTwoBlockSplit 1 (by omega) := by
              simpa using b.beliCorollary44_i_unconditional hgood
                (0 : Fin (k + 2)) (by simp) hzeroOne.le
            rcases hsplit with ⟨S⟩
            have hrightA : S.right.bong.HasPropertyA :=
              S.right.hasPropertyA hA
            rcases ih k (by omega) S.right.bong hrightA with ⟨T⟩
            let a : Kˣ := S.left.bong.valueUnit 0
            have hmodular : Lattice.IsModular
                (q.restrict S.left.carrier S.left.nondegenerate)
                S.left.lattice a := by
              simpa [a] using S.left.bong.isModular_valueUnit_zero_unary
            have hdual :
                2 * ordUnit K a -
                    ordUnit K (S.left.bong.valueUnit ⟨0, by omega⟩) =
                  b.order ⟨1 - 1, by omega⟩ := by
              have hindex : (⟨0, by omega⟩ : Fin 1) = 0 := Fin.ext rfl
              rw [hindex, show a = S.left.bong.valueUnit 0 by rfl,
                two_mul, add_sub_cancel_left,
                ← S.left.bong.order_eq_ordUnit]
              simpa [SegmentWitness.sourceIndex] using
                S.left.order_eq (0 : Fin 1)
            have hcrossNorm :
                ordUnit K (S.left.bong.valueUnit ⟨0, by omega⟩) <
                  ordUnit K (T.jordan.normGenerator 0) := by
              have hindex : (⟨0, by omega⟩ : Fin 1) = 0 := Fin.ext rfl
              rw [hindex, ← S.left.bong.order_eq_ordUnit, T.firstNormOrder]
              calc
                S.left.bong.order 0 = b.order 0 := by
                  simpa [SegmentWitness.sourceIndex] using
                    S.left.order_eq (0 : Fin 1)
                _ < b.order 1 := hzeroOne
                _ = S.right.bong.order ⟨0, T.length_pos⟩ := by
                  symm
                  calc
                    S.right.bong.order ⟨0, T.length_pos⟩ =
                        b.order (S.right.sourceIndex ⟨0, T.length_pos⟩) :=
                      S.right.order_eq ⟨0, T.length_pos⟩
                    _ = b.order 1 := by
                      apply congrArg b.order
                      apply Fin.ext
                      simp [SegmentWitness.sourceIndex]
            have hcrossDual :
                2 * ordUnit K a -
                    ordUnit K (S.left.bong.valueUnit ⟨0, by omega⟩) <
                  2 * ordUnit K (T.jordan.scaleGenerator 0) -
                    ordUnit K (T.jordan.normGenerator 0) := by
              rw [hdual, T.firstDualOrder]
              rcases T.firstBlockLength_one_or_two with hfirst | hfirst
              · calc
                  b.order ⟨1 - 1, by omega⟩ = b.order 0 := by
                    apply congrArg b.order
                    apply Fin.ext
                    simp
                  _ < b.order 1 := hzeroOne
                  _ = S.right.bong.order
                      ⟨T.firstBlockLength - 1, by omega⟩ := by
                    symm
                    calc
                      S.right.bong.order
                          ⟨T.firstBlockLength - 1, by omega⟩ =
                          b.order (S.right.sourceIndex
                            ⟨T.firstBlockLength - 1, by omega⟩) :=
                        S.right.order_eq
                          ⟨T.firstBlockLength - 1, by omega⟩
                      _ = b.order 1 := by
                        apply congrArg b.order
                        apply Fin.ext
                        simp [hfirst, SegmentWitness.sourceIndex]
              · have hkpos : 0 < k := by
                  have hle := T.firstBlockLength_le
                  omega
                have hzeroTwo :
                    b.order (⟨0, by omega⟩ : Fin (k + 2)) <
                      b.order ⟨2, by omega⟩ :=
                  hA (⟨0, by omega⟩ : Fin (k + 2)) (by dsimp; omega)
                calc
                  b.order ⟨1 - 1, by omega⟩ =
                      b.order ⟨0, by omega⟩ := by
                    apply congrArg b.order
                    apply Fin.ext
                    rfl
                  _ < b.order ⟨2, by omega⟩ := hzeroTwo
                  _ = S.right.bong.order
                      ⟨T.firstBlockLength - 1, by omega⟩ := by
                    symm
                    calc
                      S.right.bong.order
                          ⟨T.firstBlockLength - 1, by omega⟩ =
                          b.order (S.right.sourceIndex
                            ⟨T.firstBlockLength - 1, by omega⟩) :=
                        S.right.order_eq
                          ⟨T.firstBlockLength - 1, by omega⟩
                      _ = b.order ⟨2, by omega⟩ := by
                        apply congrArg b.order
                        apply Fin.ext
                        simp [hfirst, SegmentWitness.sourceIndex]
            exact ⟨T.prepend b (by omega) S (by omega) (Or.inl rfl) a
              hmodular hdual hcrossNorm hcrossDual⟩
          · have honeZero : b.order 1 ≤ b.order 0 :=
              le_of_not_gt hzeroOne
            by_cases hkzero : k = 0
            · subst k
              exact ⟨propertyAJordanWitnessTwo b honeZero⟩
            · obtain ⟨l, rfl⟩ : ∃ l, k = l + 1 := by
                exact ⟨k - 1, by omega⟩
              have hzeroTwo : b.order 0 < b.order 2 :=
                hA (0 : Fin (l + 3)) (by simp)
              have honeTwo : b.order 1 < b.order 2 :=
                lt_of_le_of_lt honeZero hzeroTwo
              have hsplit : b.HasTwoBlockSplit 2 (by omega) := by
                simpa using b.beliCorollary44_i_unconditional hgood
                  (1 : Fin (l + 3)) (by simp) honeTwo.le
              rcases hsplit with ⟨S⟩
              have hrightA : S.right.bong.HasPropertyA :=
                S.right.hasPropertyA hA
              rcases ih l (by omega) S.right.bong hrightA with ⟨T⟩
              have hleftOrder :
                  S.left.bong.order 1 ≤ S.left.bong.order 0 := by
                simpa [SegmentWitness.sourceIndex] using honeZero
              let hexists :=
                (S.left.bong.exists_isModular_iff_order_one_le_order_zero).2
                  hleftOrder
              let a : Kˣ := Classical.choose hexists
              have hmodular : Lattice.IsModular
                  (q.restrict S.left.carrier S.left.nondegenerate)
                  S.left.lattice a :=
                Classical.choose_spec hexists
              have hformula :=
                S.left.bong.order_one_eq_of_isModular a hmodular
              have hdual :
                  2 * ordUnit K a -
                      ordUnit K (S.left.bong.valueUnit ⟨0, by omega⟩) =
                    b.order ⟨2 - 1, by omega⟩ := by
                have hindex : (⟨0, by omega⟩ : Fin 2) = 0 := Fin.ext rfl
                rw [hindex, ← S.left.bong.order_eq_ordUnit, ← hformula]
                simpa [SegmentWitness.sourceIndex] using
                  S.left.order_eq (1 : Fin 2)
              have hcrossNorm :
                  ordUnit K (S.left.bong.valueUnit ⟨0, by omega⟩) <
                    ordUnit K (T.jordan.normGenerator 0) := by
                have hindex : (⟨0, by omega⟩ : Fin 2) = 0 := Fin.ext rfl
                rw [hindex, ← S.left.bong.order_eq_ordUnit,
                  T.firstNormOrder]
                calc
                  S.left.bong.order 0 = b.order 0 := by
                    simpa [SegmentWitness.sourceIndex] using
                      S.left.order_eq (0 : Fin 2)
                  _ < b.order 2 := hzeroTwo
                  _ = S.right.bong.order ⟨0, T.length_pos⟩ := by
                    symm
                    calc
                      S.right.bong.order ⟨0, T.length_pos⟩ =
                          b.order (S.right.sourceIndex ⟨0, T.length_pos⟩) :=
                        S.right.order_eq ⟨0, T.length_pos⟩
                      _ = b.order 2 := by
                        apply congrArg b.order
                        apply Fin.ext
                        simp [SegmentWitness.sourceIndex,
                          Nat.mod_eq_of_lt (by omega : 2 < l + 3)]
              have hcrossDual :
                  2 * ordUnit K a -
                      ordUnit K (S.left.bong.valueUnit ⟨0, by omega⟩) <
                    2 * ordUnit K (T.jordan.scaleGenerator 0) -
                      ordUnit K (T.jordan.normGenerator 0) := by
                rw [hdual, T.firstDualOrder]
                rcases T.firstBlockLength_one_or_two with hfirst | hfirst
                · calc
                    b.order ⟨2 - 1, by omega⟩ = b.order 1 := by
                      apply congrArg b.order
                      apply Fin.ext
                      simp [Nat.mod_eq_of_lt (by omega : 1 < l + 3)]
                    _ < b.order 2 := honeTwo
                    _ = S.right.bong.order
                        ⟨T.firstBlockLength - 1, by omega⟩ := by
                      symm
                      calc
                        S.right.bong.order
                            ⟨T.firstBlockLength - 1, by omega⟩ =
                            b.order (S.right.sourceIndex
                              ⟨T.firstBlockLength - 1, by omega⟩) :=
                          S.right.order_eq
                            ⟨T.firstBlockLength - 1, by omega⟩
                        _ = b.order 2 := by
                          apply congrArg b.order
                          apply Fin.ext
                          simp [hfirst, SegmentWitness.sourceIndex,
                            Nat.mod_eq_of_lt (by omega : 2 < l + 3)]
                · have hlpos : 0 < l := by
                    have hle := T.firstBlockLength_le
                    omega
                  let oneIndex : Fin (l + 3) := ⟨1, by omega⟩
                  have honeThreeRaw := hA oneIndex (by
                    change 1 + 2 < l + 3
                    omega)
                  have honeThree :
                      b.order (⟨1, by omega⟩ : Fin (l + 3)) <
                        b.order ⟨3, by omega⟩ := by
                    simpa [oneIndex] using honeThreeRaw
                  calc
                    b.order ⟨2 - 1, by omega⟩ =
                        b.order ⟨1, by omega⟩ := by
                      apply congrArg b.order
                      apply Fin.ext
                      rfl
                    _ < b.order ⟨3, by omega⟩ := honeThree
                    _ = S.right.bong.order
                        ⟨T.firstBlockLength - 1, by omega⟩ := by
                      symm
                      calc
                        S.right.bong.order
                            ⟨T.firstBlockLength - 1, by omega⟩ =
                            b.order (S.right.sourceIndex
                              ⟨T.firstBlockLength - 1, by omega⟩) :=
                          S.right.order_eq
                            ⟨T.firstBlockLength - 1, by omega⟩
                        _ = b.order ⟨3, by omega⟩ := by
                          apply congrArg b.order
                          apply Fin.ext
                          simp [hfirst, SegmentWitness.sourceIndex]
              exact ⟨T.prepend b (by omega) S (by omega) (Or.inr rfl) a
                hmodular hdual hcrossNorm hcrossDual⟩

/-- Positive-length form of the adapted Jordan blocking theorem. -/
theorem exists_propertyAJordanWitness_of_hasPropertyA
    (b : BONG V q L n) (hA : b.HasPropertyA) (hn : 0 < n) :
    Nonempty (PropertyAJordanWitness b) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact b.exists_propertyAJordanWitness_of_hasPropertyA_succ hA

/-- The adapted coordinate blocking itself witnesses lattice property A. -/
theorem PropertyAJordanWitness.hasJordanPropertyA
    {b : BONG V q L n} (T : PropertyAJordanWitness b) :
    Lattice.HasJordanPropertyA q L :=
  ⟨T.blockCount + 1, T.jordan, T.propertyA⟩

/-- Positive-rank coordinate Property A implies lattice property A, with no
Jordan-coordinate law instance. -/
theorem hasJordanPropertyA_of_hasPropertyA_of_length_pos
    (b : BONG V q L n) (hA : b.HasPropertyA) (hn : 0 < n) :
    Lattice.HasJordanPropertyA q L := by
  rcases b.exists_propertyAJordanWitness_of_hasPropertyA hA hn with ⟨T⟩
  exact T.hasJordanPropertyA

end BONG

end Bong
