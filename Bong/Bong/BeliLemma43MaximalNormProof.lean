/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma43ConstructionProof

/-!
# Beli (2003), Lemma 4.3(iii)

A good BONG is recursively blocked at its first ascent: a unary block is
removed when `R₀ ≤ R₁`, and an improper modular binary block is removed
when `R₁ < R₀`.  Corollary 4.4 supplies the actual lattice splitting.
The weak two-step inequalities give the two maximal-norm gap inequalities
across every newly created boundary.
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

/-- A maximal-norm splitting adapted to a nonempty good BONG, together with
the endpoint formulas needed by the recursive prepend step. -/
structure GoodMaximalNormWitness (b : BONG V q L n) where
  length_pos : 0 < n
  blockCount : Nat
  splitting : Lattice.MaximalNormSplitting q L (blockCount + 1)
  componentBONG :
    splitting.toOrthogonalDecomposition.ComponentBONGFamily
  putTogether :
    b.IsPutTogether splitting.toOrthogonalDecomposition componentBONG
  allBinaryImproper : AllBinaryComponentsImproper splitting componentBONG
  firstBlockLength : Nat
  firstBlockLength_pos : 0 < firstBlockLength
  firstBlockLength_le : firstBlockLength ≤ n
  firstBlockLength_one_or_two :
    firstBlockLength = 1 ∨ firstBlockLength = 2
  firstComponentRank :
    splitting.componentRank 0 = firstBlockLength
  firstNormOrder :
    ordUnit K (splitting.normGenerator 0) =
      b.order ⟨0, length_pos⟩
  firstDualOrder :
    2 * ordUnit K (splitting.scaleGenerator 0) -
        ordUnit K (splitting.normGenerator 0) =
      b.order ⟨firstBlockLength - 1, by omega⟩

/-- Improper modularity is invariant under a length cast. -/
theorem isImproperModular_castLength_iff
    {W : Type v} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (b : BONG W r M 2) (h : 2 = 2) :
    (b.castLength h).IsImproperModular ↔ b.IsImproperModular := by
  cases h
  rfl

/-- Improper modularity is invariant under an integral isometry. -/
theorem isImproperModular_mapLatticeIsometry_iff
    {W : Type v} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    {W' : Type v} [AddCommGroup W'] [Module K W']
    {r' : QuadraticSpace K W'} {M' : Lattice K W'}
    (f : Lattice.Isometry r r' M M') (b : BONG W r M 2) :
    (b.mapLatticeIsometry f).IsImproperModular ↔ b.IsImproperModular := by
  simp only [IsImproperModular, binaryOrderGap,
    order_mapLatticeIsometry]

/-- Improper modularity depends only on the two integral orders. -/
theorem IsImproperModular.of_orders_eq
    {W W' : Type v} [AddCommGroup W] [Module K W]
    [AddCommGroup W'] [Module K W']
    {r : QuadraticSpace K W} {M : Lattice K W}
    {r' : QuadraticSpace K W'} {M' : Lattice K W'}
    {b : BONG W r M 2} {c : BONG W' r' M' 2}
    (hb : b.IsImproperModular) (horder : ∀ i, c.order i = b.order i) :
    c.IsImproperModular := by
  rw [IsImproperModular, binaryOrderGap] at hb ⊢
  rw [horder 0, horder 1]
  exact hb

/-- Improper modularity is unchanged by transport across equality of
quadratic sublattices. -/
theorem isImproperModular_castQuadraticSublattice_iff
    {C D : Lattice.QuadraticSublattice q}
    (b : BONG C.carrier C.space C.lattice 2) (h : C = D) :
    (b.castQuadraticSublattice h).IsImproperModular ↔
      b.IsImproperModular := by
  subst D
  rfl

@[simp]
theorem order_castQuadraticSublattice
    {C D : Lattice.QuadraticSublattice q} {m : Nat}
    (b : BONG C.carrier C.space C.lattice m) (h : C = D)
    (i : Fin m) :
    (b.castQuadraticSublattice h).order i = b.order i := by
  subst D
  rfl

/-- Later component norm orders are weakly above the first one. -/
theorem GoodMaximalNormWitness.firstNormOrder_le
    {N : Nat} {b : BONG V q L N}
    (T : GoodMaximalNormWitness b)
    (j : Fin (T.blockCount + 1))
    (hj : (0 : Fin (T.blockCount + 1)) < j) :
    ordUnit K (T.splitting.normGenerator 0) ≤
      ordUnit K (T.splitting.normGenerator j) := by
  have h := T.splitting.normGap_bounds hj
  omega

/-- The dual norm orders `2s-u` are weakly increasing across a maximal-norm
splitting. -/
theorem GoodMaximalNormWitness.firstDualOrder_le
    {N : Nat} {b : BONG V q L N}
    (T : GoodMaximalNormWitness b)
    (j : Fin (T.blockCount + 1))
    (hj : (0 : Fin (T.blockCount + 1)) < j) :
    2 * ordUnit K (T.splitting.scaleGenerator 0) -
        ordUnit K (T.splitting.normGenerator 0) ≤
      2 * ordUnit K (T.splitting.scaleGenerator j) -
        ordUnit K (T.splitting.normGenerator j) := by
  have h := T.splitting.normGap_bounds hj
  omega

/-- The terminal unary good BONG gives a one-component maximal-norm
splitting. -/
noncomputable def goodMaximalNormWitnessOne (b : BONG V q L 1) :
    GoodMaximalNormWitness b := by
  let T := propertyAJordanWitnessOne b
  let M := Lattice.MaximalNormSplitting.ofJordanPropertyA
    T.jordan T.propertyA
  refine {
    length_pos := by omega
    blockCount := 0
    splitting := M
    componentBONG := T.componentBONG
    putTogether := T.putTogether
    allBinaryImproper := ?_
    firstBlockLength := T.firstBlockLength
    firstBlockLength_pos := T.firstBlockLength_pos
    firstBlockLength_le := T.firstBlockLength_le
    firstBlockLength_one_or_two := T.firstBlockLength_one_or_two
    firstComponentRank := ?_
    firstNormOrder := T.firstNormOrder
    firstDualOrder := T.firstDualOrder }
  · intro i htwo
    have hi : i = 0 := Fin.ext (by omega)
    subst i
    have hlength : T.firstBlockLength = 1 := by rfl
    have hone : M.componentRank 0 = 1 := by
      change finrank K (T.jordan.component 0).carrier = 1
      exact T.firstComponentRank.trans hlength
    have htwo' : M.componentRank 0 = 2 := by
      exact htwo
    exact (by omega)
  · change finrank K (T.jordan.component 0).carrier =
      T.firstBlockLength
    exact T.firstComponentRank

/-- In a one-component rank-two concatenation, a descending global pair
forces the selected component BONG to be improper modular. -/
theorem singletonComponent_isImproperModular_of_order_one_lt_zero
    {b : BONG V q L 2}
    {D : Lattice.OrthogonalDecomposition q L 1}
    {c : D.ComponentBONGFamily}
    (hput : b.IsPutTogether D c)
    (hrank : D.componentRank 0 = 2)
    (hdesc : b.order 1 < b.order 0) :
    (c 0).castLength hrank |>.IsImproperModular := by
  rcases hput with ⟨w⟩
  let localZero : Fin (D.componentRank 0) :=
    Fin.cast hrank.symm (0 : Fin 2)
  let localOne : Fin (D.componentRank 0) :=
    Fin.cast hrank.symm (1 : Fin 2)
  let globalZero : Fin 2 := w.indexEquiv.symm ⟨0, localZero⟩
  let globalOne : Fin 2 := w.indexEquiv.symm ⟨0, localOne⟩
  have hglobalZeroImage : w.indexEquiv globalZero = ⟨0, localZero⟩ := by
    exact w.indexEquiv.apply_symm_apply ⟨0, localZero⟩
  have hglobalOneImage : w.indexEquiv globalOne = ⟨0, localOne⟩ := by
    exact w.indexEquiv.apply_symm_apply ⟨0, localOne⟩
  have hglobalLt : globalZero < globalOne := by
    apply (w.order_iff globalZero globalOne).mpr
    rw [hglobalZeroImage, hglobalOneImage]
    right
    constructor
    · rfl
    · simp [localZero, localOne]
  have hglobalZeroIndex : globalZero = 0 := by
    apply Fin.ext
    have hz := globalZero.isLt
    have ho := globalOne.isLt
    omega
  have hglobalOneIndex : globalOne = 1 := by
    apply Fin.ext
    have hz := globalZero.isLt
    have ho := globalOne.isLt
    omega
  let componentOrder :
      (Σ i : Fin 1, Fin (D.componentRank i)) → Int :=
    fun z ↦ (c z.1).order z.2
  have hglobalZero : b.order 0 = (c 0).order localZero := by
    calc
      b.order 0 = b.order globalZero :=
        congrArg b.order hglobalZeroIndex.symm
      _ = componentOrder (w.indexEquiv globalZero) := by
        exact w.order_eq globalZero
      _ = componentOrder ⟨0, localZero⟩ :=
        congrArg componentOrder hglobalZeroImage
      _ = (c 0).order localZero := rfl
  have hglobalOne : b.order 1 = (c 0).order localOne := by
    calc
      b.order 1 = b.order globalOne :=
        congrArg b.order hglobalOneIndex.symm
      _ = componentOrder (w.indexEquiv globalOne) := by
        exact w.order_eq globalOne
      _ = componentOrder ⟨0, localOne⟩ :=
        congrArg componentOrder hglobalOneImage
      _ = (c 0).order localOne := rfl
  have hcastZero : ((c 0).castLength hrank).order 0 =
      (c 0).order localZero := by
    rw [order_castLength]
    apply congrArg (c 0).order
    apply Fin.ext
    rfl
  have hcastOne : ((c 0).castLength hrank).order 1 =
      (c 0).order localOne := by
    rw [order_castLength]
    apply congrArg (c 0).order
    apply Fin.ext
    rfl
  rw [IsImproperModular, binaryOrderGap, hcastOne, hcastZero]
  rw [← hglobalOne, ← hglobalZero]
  omega

/-- The terminal descending binary good BONG gives an improper modular
one-component maximal-norm splitting. -/
noncomputable def goodMaximalNormWitnessTwo (b : BONG V q L 2)
    (hdesc : b.order 1 < b.order 0) : GoodMaximalNormWitness b := by
  let T := propertyAJordanWitnessTwo b hdesc.le
  let M := Lattice.MaximalNormSplitting.ofJordanPropertyA
    T.jordan T.propertyA
  refine {
    length_pos := by omega
    blockCount := 0
    splitting := M
    componentBONG := T.componentBONG
    putTogether := T.putTogether
    allBinaryImproper := ?_
    firstBlockLength := T.firstBlockLength
    firstBlockLength_pos := T.firstBlockLength_pos
    firstBlockLength_le := T.firstBlockLength_le
    firstBlockLength_one_or_two := T.firstBlockLength_one_or_two
    firstComponentRank := ?_
    firstNormOrder := T.firstNormOrder
    firstDualOrder := T.firstDualOrder }
  · intro i htwo
    have hi : i = 0 := Fin.ext (by omega)
    subst i
    have hlength : T.firstBlockLength = 2 := by rfl
    exact singletonComponent_isImproperModular_of_order_one_lt_zero
      T.putTogether (by
        change finrank K (T.jordan.component 0).carrier = 2
        exact T.firstComponentRank.trans hlength) hdesc
  · change finrank K (T.jordan.component 0).carrier =
      T.firstBlockLength
    exact T.firstComponentRank

set_option maxHeartbeats 1500000 in
-- Dependent transports through the nested component spaces dominate the
-- elaboration cost of this otherwise elementary prepend construction.
/-- Prepend one unary or improper modular binary segment to an adapted
maximal-norm splitting of the right segment. -/
noncomputable def GoodMaximalNormWitness.prepend
    {N cut : Nat} (b : BONG V q L N) (hcut : cut ≤ N)
    (S : TwoBlockSplitWitness b cut hcut)
    (T : GoodMaximalNormWitness S.right.bong)
    (hcutPos : 0 < cut) (hsize : cut = 1 ∨ cut = 2)
    (a : Kˣ)
    (hmodular : Lattice.IsModular
      (q.restrict S.left.carrier S.left.nondegenerate) S.left.lattice a)
    (hdual :
      2 * ordUnit K a -
          ordUnit K (S.left.bong.valueUnit ⟨0, hcutPos⟩) =
        b.order ⟨cut - 1, by omega⟩)
    (hcrossNorm :
      ordUnit K (S.left.bong.valueUnit ⟨0, hcutPos⟩) ≤
        ordUnit K (T.splitting.normGenerator 0))
    (hcrossDual :
      2 * ordUnit K a -
          ordUnit K (S.left.bong.valueUnit ⟨0, hcutPos⟩) ≤
        2 * ordUnit K (T.splitting.scaleGenerator 0) -
          ordUnit K (T.splitting.normGenerator 0))
    (hheadImproper : ∀ htwo : cut = 2,
      (S.left.bong.castLength htwo).IsImproperModular) :
    GoodMaximalNormWitness b := by
  let E := T.splitting.toOrthogonalDecomposition
  let D := S.decomposition.prependNestedOfEq
    S.right.toQuadraticSublattice S.component_one E
  let headNorm : Kˣ := S.left.bong.valueUnit ⟨0, hcutPos⟩
  let scale : Fin ((T.blockCount + 1) + 1) → Kˣ :=
    Fin.cases a T.splitting.scaleGenerator
  let norm : Fin ((T.blockCount + 1) + 1) → Kˣ :=
    Fin.cases headNorm T.splitting.normGenerator
  have hscaleFirst : ordUnit K a ≤
      ordUnit K (T.splitting.scaleGenerator 0) := by
    change ordUnit K headNorm ≤
        ordUnit K (T.splitting.normGenerator 0) at hcrossNorm
    change 2 * ordUnit K a - ordUnit K headNorm ≤
        2 * ordUnit K (T.splitting.scaleGenerator 0) -
          ordUnit K (T.splitting.normGenerator 0) at hcrossDual
    omega
  let M : Lattice.MaximalNormSplitting q L
      ((T.blockCount + 1) + 1) := {
    toOrthogonalDecomposition := D
    scaleGenerator := scale
    normGenerator := norm
    scaleIdeal_eq := by
      intro i
      cases i using Fin.cases with
      | zero =>
          change Lattice.scaleIdeal (D.component 0).space
              (D.component 0).lattice =
            Lattice.principalIdeal (K := K) (a : K)
          rw [show D = S.decomposition.prependNestedOfEq
            S.right.toQuadraticSublattice S.component_one E by rfl,
            show E = T.splitting.toOrthogonalDecomposition by rfl,
            prependNestedSegment_component_zero]
          exact hmodular.scaleIdeal_eq_principal (by
            rw [← S.left.bong.length_eq_finrank]
            exact hcutPos)
      | succ i =>
          change Lattice.scaleIdeal (D.component i.succ).space
              (D.component i.succ).lattice =
            Lattice.principalIdeal (K := K)
              (T.splitting.scaleGenerator i : K)
          rw [show D = S.decomposition.prependNestedOfEq
            S.right.toQuadraticSublattice S.component_one E by rfl,
            show E = T.splitting.toOrthogonalDecomposition by rfl,
            prependNestedSegment_component_succ]
          calc
            Lattice.scaleIdeal
                (S.right.toQuadraticSublattice.liftNested
                  (T.splitting.component i)).space
                (S.right.toQuadraticSublattice.liftNested
                  (T.splitting.component i)).lattice =
                Lattice.scaleIdeal (T.splitting.component i).space
                  (T.splitting.component i).lattice :=
              Lattice.scaleIdeal_map_isometry
                (S.right.toQuadraticSublattice.liftNestedIsometry
                  (T.splitting.component i)).toQuadraticSpaceIsometry
                (T.splitting.component i).lattice
            _ = Lattice.principalIdeal (K := K)
                (T.splitting.scaleGenerator i : K) :=
              T.splitting.scaleIdeal_eq i
    normIdeal_eq := by
      intro i
      cases i using Fin.cases with
      | zero =>
          change Lattice.normIdeal (D.component 0).space
              (D.component 0).lattice =
            Lattice.principalIdeal (K := K) (headNorm : K)
          rw [show D = S.decomposition.prependNestedOfEq
            S.right.toQuadraticSublattice S.component_one E by rfl,
            show E = T.splitting.toOrthogonalDecomposition by rfl,
            prependNestedSegment_component_zero]
          have hgen := S.left.bong.ambientVector_zero_isNormGenerator
            hcutPos
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
              (T.splitting.normGenerator i : K)
          rw [show D = S.decomposition.prependNestedOfEq
            S.right.toQuadraticSublattice S.component_one E by rfl,
            show E = T.splitting.toOrthogonalDecomposition by rfl,
            prependNestedSegment_component_succ]
          calc
            Lattice.normIdeal
                (S.right.toQuadraticSublattice.liftNested
                  (T.splitting.component i)).space
                (S.right.toQuadraticSublattice.liftNested
                  (T.splitting.component i)).lattice =
                Lattice.normIdeal (T.splitting.component i).space
                  (T.splitting.component i).lattice :=
              Lattice.normIdeal_map_isometry
                (S.right.toQuadraticSublattice.liftNestedIsometry
                  (T.splitting.component i)).toQuadraticSpaceIsometry
                (T.splitting.component i).lattice
            _ = Lattice.principalIdeal (K := K)
                (T.splitting.normGenerator i : K) :=
              T.splitting.normIdeal_eq i
    unary_or_modular_binary := by
      intro i
      cases i using Fin.cases with
      | zero =>
          change D.componentRank 0 = 1 ∨
            (D.componentRank 0 = 2 ∧
              Lattice.IsModular (D.component 0).space
                (D.component 0).lattice a)
          rcases hsize with hsize | hsize
          · left
            rw [show D = S.decomposition.prependNestedOfEq
              S.right.toQuadraticSublattice S.component_one E by rfl,
              show E = T.splitting.toOrthogonalDecomposition by rfl,
              prependNestedSegment_componentRank_zero]
            exact hsize
          · right
            constructor
            · rw [show D = S.decomposition.prependNestedOfEq
                S.right.toQuadraticSublattice S.component_one E by rfl,
                show E = T.splitting.toOrthogonalDecomposition by rfl,
                prependNestedSegment_componentRank_zero]
              exact hsize
            · change Lattice.IsModular (D.component 0).space
                (D.component 0).lattice a
              rw [show D = S.decomposition.prependNestedOfEq
                S.right.toQuadraticSublattice S.component_one E by rfl,
                show E = T.splitting.toOrthogonalDecomposition by rfl,
                prependNestedSegment_component_zero]
              exact hmodular
      | succ i =>
          change D.componentRank i.succ = 1 ∨
            (D.componentRank i.succ = 2 ∧
              Lattice.IsModular (D.component i.succ).space
                (D.component i.succ).lattice
                  (T.splitting.scaleGenerator i))
          rcases T.splitting.unary_or_modular_binary i with hone | htwo
          · left
            rw [show D = S.decomposition.prependNestedOfEq
              S.right.toQuadraticSublattice S.component_one E by rfl,
              show E = T.splitting.toOrthogonalDecomposition by rfl,
              prependNestedSegment_componentRank_succ]
            exact hone
          · right
            constructor
            · rw [show D = S.decomposition.prependNestedOfEq
                S.right.toQuadraticSublattice S.component_one E by rfl,
                show E = T.splitting.toOrthogonalDecomposition by rfl,
                prependNestedSegment_componentRank_succ]
              exact htwo.1
            · rw [show D = S.decomposition.prependNestedOfEq
                S.right.toQuadraticSublattice S.component_one E by rfl,
                show E = T.splitting.toOrthogonalDecomposition by rfl,
                prependNestedSegment_component_succ]
              exact Lattice.QuadraticSublattice.IsModular.liftNested
                S.right.toQuadraticSublattice _ htwo.2
    scaleOrder_mono := by
      intro i j hij
      cases i using Fin.cases with
      | zero =>
          cases j using Fin.cases with
          | zero => exact (lt_irrefl _ hij).elim
          | succ j =>
              change ordUnit K a ≤
                ordUnit K (T.splitting.scaleGenerator j)
              by_cases hj : j = 0
              · subst j
                exact hscaleFirst
              · exact hscaleFirst.trans
                  (T.splitting.scaleOrder_mono
                    ((Fin.pos_iff_ne_zero).2 hj))
      | succ i =>
          cases j using Fin.cases with
          | zero => exact (Nat.not_lt_zero i.succ.val hij).elim
          | succ j =>
              exact T.splitting.scaleOrder_mono
                (Nat.succ_lt_succ_iff.mp hij)
    normGap_bounds := by
      intro i j hij
      cases i using Fin.cases with
      | zero =>
          cases j using Fin.cases with
          | zero => exact (lt_irrefl _ hij).elim
          | succ j =>
              have hnorm : ordUnit K headNorm ≤
                  ordUnit K (T.splitting.normGenerator j) := by
                by_cases hj : j = 0
                · simpa [hj, headNorm] using hcrossNorm
                · exact (show ordUnit K headNorm ≤
                      ordUnit K (T.splitting.normGenerator 0) by
                        simpa [headNorm] using hcrossNorm).trans
                    (T.firstNormOrder_le j
                      ((Fin.pos_iff_ne_zero).2 hj))
              have hdual' : 2 * ordUnit K a - ordUnit K headNorm ≤
                  2 * ordUnit K (T.splitting.scaleGenerator j) -
                    ordUnit K (T.splitting.normGenerator j) := by
                by_cases hj : j = 0
                · simpa [hj, headNorm] using hcrossDual
                · exact (show 2 * ordUnit K a - ordUnit K headNorm ≤
                      2 * ordUnit K (T.splitting.scaleGenerator 0) -
                        ordUnit K (T.splitting.normGenerator 0) by
                        simpa [headNorm] using hcrossDual).trans
                    (T.firstDualOrder_le j
                      ((Fin.pos_iff_ne_zero).2 hj))
              change 0 ≤ ordUnit K (T.splitting.normGenerator j) -
                    ordUnit K headNorm ∧
                ordUnit K (T.splitting.normGenerator j) -
                    ordUnit K headNorm ≤
                  2 * (ordUnit K (T.splitting.scaleGenerator j) -
                    ordUnit K a)
              constructor <;> omega
      | succ i =>
          cases j using Fin.cases with
          | zero => exact (Nat.not_lt_zero i.succ.val hij).elim
          | succ j =>
              exact T.splitting.normGap_bounds
                (Nat.succ_lt_succ_iff.mp hij) }
  let c := prependNestedSegmentBONGFamily b hcut S E T.componentBONG
  refine {
    length_pos := hcutPos.trans_le hcut
    blockCount := T.blockCount + 1
    splitting := M
    componentBONG := c
    putTogether := prependNestedSegment_isPutTogether b hcut S E
      T.componentBONG T.putTogether
    allBinaryImproper := ?_
    firstBlockLength := cut
    firstBlockLength_pos := hcutPos
    firstBlockLength_le := hcut
    firstBlockLength_one_or_two := hsize
    firstComponentRank := ?_
    firstNormOrder := ?_
    firstDualOrder := ?_ }
  · intro i htwo
    cases i using Fin.cases with
    | zero =>
        have hcutTwo : cut = 2 := by
          have hrank := prependNestedSegment_componentRank_zero
            b hcut S E
          change D.componentRank 0 = 2 at htwo
          change D.componentRank 0 = cut at hrank
          omega
        have himproper := hheadImproper hcutTwo
        subst cut
        apply himproper.of_orders_eq
        intro j
        simp only [c, prependNestedSegmentBONGFamily_zero,
          prependNestedSegmentHeadBONG, order_castLength,
          order_castQuadraticSublattice]
        apply congrArg S.left.bong.order
        apply Fin.ext
        rfl
    | succ i =>
        have htailRank :
            T.splitting.toOrthogonalDecomposition.componentRank i = 2 := by
          have hrank := prependNestedSegment_componentRank_succ
            b hcut S E i
          change D.componentRank i.succ = 2 at htwo
          change E.componentRank i = 2
          exact hrank.symm.trans htwo
        have himproper := T.allBinaryImproper i htailRank
        apply himproper.of_orders_eq
        intro j
        simp only [c, prependNestedSegmentBONGFamily_succ,
          prependNestedSegmentTailBONG, order_castLength,
          order_castQuadraticSublattice, order_mapLatticeIsometry]
        apply congrArg (T.componentBONG i).order
        apply Fin.ext
        rfl
  · change D.componentRank 0 = cut
    rw [show D = S.decomposition.prependNestedOfEq
      S.right.toQuadraticSublattice S.component_one E by rfl,
      show E = T.splitting.toOrthogonalDecomposition by rfl,
      prependNestedSegment_componentRank_zero]
  · change ordUnit K headNorm = b.order ⟨0, hcutPos.trans_le hcut⟩
    rw [← S.left.bong.order_eq_ordUnit]
    simpa [headNorm, SegmentWitness.sourceIndex] using
      S.left.order_eq ⟨0, hcutPos⟩
  · change 2 * ordUnit K a - ordUnit K headNorm =
      b.order ⟨cut - 1, by omega⟩
    simpa [headNorm] using hdual

set_option maxHeartbeats 2000000 in
/-- Every nonempty good BONG admits the improper-binary maximal-norm
blocking of Beli (2003), Lemma 4.3(iii). -/
theorem exists_goodMaximalNormWitness_succ
    {m : Nat} (b : BONG V q L (m + 1)) (hgood : b.IsGood) :
    Nonempty (GoodMaximalNormWitness b) := by
  induction m using Nat.strong_induction_on generalizing V with
  | h m ih =>
      cases m with
      | zero =>
          exact ⟨goodMaximalNormWitnessOne b⟩
      | succ k =>
          by_cases hzeroOne : b.order 0 ≤ b.order 1
          · have hsplit : b.HasTwoBlockSplit 1 (by omega) := by
              simpa using b.beliCorollary44_i_unconditional hgood
                (0 : Fin (k + 2)) (by simp) hzeroOne
            rcases hsplit with ⟨S⟩
            have hrightGood : S.right.bong.IsGood :=
              S.right.isGood hgood
            rcases ih k (by omega) S.right.bong hrightGood with ⟨T⟩
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
                ordUnit K (S.left.bong.valueUnit ⟨0, by omega⟩) ≤
                  ordUnit K (T.splitting.normGenerator 0) := by
              have hindex : (⟨0, by omega⟩ : Fin 1) = 0 := Fin.ext rfl
              rw [hindex, ← S.left.bong.order_eq_ordUnit,
                T.firstNormOrder]
              calc
                S.left.bong.order 0 = b.order 0 := by
                  simpa [SegmentWitness.sourceIndex] using
                    S.left.order_eq (0 : Fin 1)
                _ ≤ b.order 1 := hzeroOne
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
                    ordUnit K (S.left.bong.valueUnit ⟨0, by omega⟩) ≤
                  2 * ordUnit K (T.splitting.scaleGenerator 0) -
                    ordUnit K (T.splitting.normGenerator 0) := by
              rw [hdual, T.firstDualOrder]
              rcases T.firstBlockLength_one_or_two with hfirst | hfirst
              · calc
                  b.order ⟨1 - 1, by omega⟩ = b.order 0 := by
                    apply congrArg b.order
                    apply Fin.ext
                    simp
                  _ ≤ b.order 1 := hzeroOne
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
                have hzeroTwo : b.order (0 : Fin (k + 2)) ≤
                    b.order ⟨2, by omega⟩ :=
                  hgood (0 : Fin (k + 2)) (by simp; omega)
                calc
                  b.order ⟨1 - 1, by omega⟩ =
                      b.order (0 : Fin (k + 2)) := by
                    apply congrArg b.order
                    apply Fin.ext
                    rfl
                  _ ≤ b.order ⟨2, by omega⟩ := hzeroTwo
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
            have hheadImproper : ∀ htwo : (1 : Nat) = 2,
                (S.left.bong.castLength htwo).IsImproperModular := by
              intro htwo
              omega
            exact ⟨T.prepend b (by omega) S (by omega) (Or.inl rfl) a
              hmodular hdual hcrossNorm hcrossDual hheadImproper⟩
          · have honeZero : b.order 1 < b.order 0 :=
              lt_of_not_ge hzeroOne
            by_cases hkzero : k = 0
            · subst k
              exact ⟨goodMaximalNormWitnessTwo b honeZero⟩
            · obtain ⟨l, rfl⟩ : ∃ l, k = l + 1 :=
                ⟨k - 1, by omega⟩
              have hzeroTwo : b.order 0 ≤ b.order 2 :=
                hgood (0 : Fin (l + 3)) (by simp)
              have honeTwo : b.order 1 ≤ b.order 2 :=
                honeZero.le.trans hzeroTwo
              have hsplit : b.HasTwoBlockSplit 2 (by omega) := by
                simpa using b.beliCorollary44_i_unconditional hgood
                  (1 : Fin (l + 3)) (by simp) honeTwo
              rcases hsplit with ⟨S⟩
              have hrightGood : S.right.bong.IsGood :=
                S.right.isGood hgood
              rcases ih l (by omega) S.right.bong hrightGood with ⟨T⟩
              have hleftOrder :
                  S.left.bong.order 1 ≤ S.left.bong.order 0 := by
                simpa [SegmentWitness.sourceIndex] using honeZero.le
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
                  ordUnit K (S.left.bong.valueUnit ⟨0, by omega⟩) ≤
                    ordUnit K (T.splitting.normGenerator 0) := by
                have hindex : (⟨0, by omega⟩ : Fin 2) = 0 := Fin.ext rfl
                rw [hindex, ← S.left.bong.order_eq_ordUnit,
                  T.firstNormOrder]
                calc
                  S.left.bong.order 0 = b.order 0 := by
                    simpa [SegmentWitness.sourceIndex] using
                      S.left.order_eq (0 : Fin 2)
                  _ ≤ b.order 2 := hzeroTwo
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
                      ordUnit K (S.left.bong.valueUnit ⟨0, by omega⟩) ≤
                    2 * ordUnit K (T.splitting.scaleGenerator 0) -
                      ordUnit K (T.splitting.normGenerator 0) := by
                rw [hdual, T.firstDualOrder]
                rcases T.firstBlockLength_one_or_two with hfirst | hfirst
                · calc
                    b.order ⟨2 - 1, by omega⟩ = b.order 1 := by
                      apply congrArg b.order
                      apply Fin.ext
                      simp [Nat.mod_eq_of_lt (by omega : 1 < l + 3)]
                    _ ≤ b.order 2 := honeTwo
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
                  have honeThree : b.order (1 : Fin (l + 3)) ≤
                      b.order ⟨3, by omega⟩ :=
                    hgood (1 : Fin (l + 3)) (by simp; omega)
                  calc
                    b.order ⟨2 - 1, by omega⟩ =
                        b.order (1 : Fin (l + 3)) := by
                      apply congrArg b.order
                      apply Fin.ext
                      rfl
                    _ ≤ b.order ⟨3, by omega⟩ := honeThree
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
              have hheadImproper : ∀ htwo : (2 : Nat) = 2,
                  (S.left.bong.castLength htwo).IsImproperModular := by
                intro htwo
                rw [IsImproperModular, binaryOrderGap]
                have hleftZero : S.left.bong.order 0 = b.order 0 := by
                  simpa [SegmentWitness.sourceIndex] using
                    S.left.order_eq (0 : Fin 2)
                have hleftOne : S.left.bong.order 1 = b.order 1 := by
                  simpa [SegmentWitness.sourceIndex] using
                    S.left.order_eq (1 : Fin 2)
                simp only [order_castLength]
                rw [hleftZero, hleftOne]
                omega
              exact ⟨T.prepend b (by omega) S (by omega) (Or.inr rfl) a
                hmodular hdual hcrossNorm hcrossDual hheadImproper⟩

/-- Positive-length wrapper for Lemma 4.3(iii). -/
theorem exists_goodMaximalNormWitness
    (b : BONG V q L n) (hgood : b.IsGood) (hn : 0 < n) :
    Nonempty (GoodMaximalNormWitness b) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact b.exists_goodMaximalNormWitness_succ hgood

/-- Beli (2003), Lemma 4.3(iii), including the zero-rank boundary and the
improper refinement for every binary component. -/
theorem good_has_improper_maximalNormSplitting_proof
    (b : BONG V q L n) (hgood : b.IsGood) :
    ∃ (t : Nat) (M : Lattice.MaximalNormSplitting q L t)
        (c : M.toOrthogonalDecomposition.ComponentBONGFamily),
      b.IsPutTogether M.toOrthogonalDecomposition c ∧
        AllBinaryComponentsImproper M c := by
  by_cases hn : n = 0
  · subst n
    letI : Module.Finite K V := L.moduleFinite
    have hfin : finrank K V = 0 := b.length_eq_finrank.symm
    let J := emptyJordanDecomposition_of_finrank_eq_zero
      (q := q) (L := L) hfin
    have hJ : J.HasPropertyA :=
      emptyJordanDecomposition_of_finrank_eq_zero_hasPropertyA
        (q := q) (L := L) hfin
    let M : Lattice.MaximalNormSplitting q L 0 :=
      Lattice.MaximalNormSplitting.ofJordanPropertyA J hJ
    let c : M.toOrthogonalDecomposition.ComponentBONGFamily := by
      intro i
      exact Fin.elim0 i
    let e : Fin 0 ≃
        Σ i : Fin 0,
          Fin (M.toOrthogonalDecomposition.componentRank i) :=
      { toFun := fun i ↦ Fin.elim0 i
        invFun := fun z ↦ Fin.elim0 z.1
        left_inv := fun i ↦ Fin.elim0 i
        right_inv := fun z ↦ Fin.elim0 z.1 }
    refine ⟨0, M, c, ?_, ?_⟩
    · exact ⟨{
        indexEquiv := e
        order_iff := fun i _ ↦ Fin.elim0 i
        ambientVector_eq := fun i ↦ Fin.elim0 i }⟩
    · intro i
      exact Fin.elim0 i
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    rcases b.exists_goodMaximalNormWitness hgood hnpos with ⟨T⟩
    exact ⟨T.blockCount + 1, T.splitting, T.componentBONG,
      T.putTogether, T.allBinaryImproper⟩

end BONG

/-- The fully proved compatibility bundle for Beli (2003), Lemma 4.3. -/
@[reducible] noncomputable def beliLemma43ConstructionLawsProved
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] :
    BeliLemma43ConstructionLaws.{u, v} K where
  propertyA_of_conditions :=
    BONG.hasPropertyARealization_of_conditions_proof
  good_of_conditions :=
    BONG.hasGoodRealization_of_conditions_proof
  good_has_improper_maximalNormSplitting :=
    BONG.good_has_improper_maximalNormSplitting_proof

noncomputable instance (K : Type u) [Field K] [CharZero K]
    [ValuativeRel K] [TopologicalSpace K] [DyadicContext K] :
    BeliLemma43ConstructionLaws.{u, v} K :=
  beliLemma43ConstructionLawsProved K

end Bong
