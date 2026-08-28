/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OrthogonalDecompositionSuffix
import Bong.Lattice.NestedSublattice

/-!
# Removing the head of an orthogonal decomposition

For a nonempty decomposition, the positive-index components form an exact
orthogonal decomposition of the suffix lattice.  For a decomposition with at
least two components, the original lattice also has an exact two-block
decomposition into its head and this suffix.  These constructions supply the
geometric induction layer used by Beli (2003), Theorem 2.
-/

namespace Bong

open Dyadic

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

namespace OrthogonalDecomposition

noncomputable section

/-- A two-element indexed supremum is an ordinary binary supremum. -/
theorem iSup_fin_two_eq_sup_tail {α : Type*} [CompleteLattice α]
    (f : Fin 2 → α) : (⨆ i, f i) = f 0 ⊔ f 1 := by
  apply le_antisymm
  · apply iSup_le
    intro i
    fin_cases i
    · exact _root_.le_sup_left
    · exact _root_.le_sup_right
  · exact _root_.sup_le (le_iSup f 0) (le_iSup f 1)

section Tail

variable (D : OrthogonalDecomposition q L (n + 1))

/-- The original index corresponding to a tail index. -/
def tailIndex (i : Fin n) : D.SuffixIndex 1 :=
  ⟨i.succ, by simp⟩

/-- Inclusion of an original positive-index component into the suffix
carrier. -/
noncomputable def componentToTailLinearMap (i : Fin n) :
    (D.component i.succ).carrier →ₗ[K]
      (D.suffixQuadraticSublattice 1).carrier where
  toFun x := ⟨x, le_iSup
    (fun j : D.SuffixIndex 1 ↦ (D.component j.1).carrier)
      (D.tailIndex i) x.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The component carrier, viewed as a submodule of the suffix carrier. -/
abbrev tailComponentCarrier (i : Fin n) :
    Submodule K (D.suffixQuadraticSublattice 1).carrier :=
  (D.componentToTailLinearMap i).range

/-- The canonical equivalence from an original positive-index component to
its copy inside the suffix carrier. -/
noncomputable def tailComponentEquiv (i : Fin n) :
    (D.component i.succ).carrier ≃ₗ[K] D.tailComponentCarrier i :=
  LinearEquiv.ofInjective (D.componentToTailLinearMap i) (by
    intro x y hxy
    apply Subtype.ext
    exact congrArg
      (fun z : (D.suffixQuadraticSublattice 1).carrier ↦ (z : V)) hxy)

@[simp]
theorem coe_tailComponentEquiv (i : Fin n)
    (x : (D.component i.succ).carrier) :
    (((D.tailComponentEquiv i x : D.tailComponentCarrier i) :
      (D.suffixQuadraticSublattice 1).carrier) : V) = (x : V) :=
  rfl

/-- A positive-index component as a quadratic sublattice of the suffix. -/
noncomputable def tailComponent (i : Fin n) :
    QuadraticSublattice (D.suffixQuadraticSublattice 1).space where
  carrier := D.tailComponentCarrier i
  nondegenerate := by
    rw [show
      (D.suffixQuadraticSublattice 1).space.bilin.restrict
          (D.tailComponentCarrier i) =
        LinearMap.BilinForm.congr (D.tailComponentEquiv i)
          (D.component i.succ).space.bilin by
      apply LinearMap.BilinForm.ext
      intro x y
      rw [LinearMap.BilinForm.congr_apply]
      have hx :
          (((x : (D.suffixQuadraticSublattice 1).carrier) : V)) =
            (((D.tailComponentEquiv i).symm x :
              (D.component i.succ).carrier) : V) := by
        rw [← D.coe_tailComponentEquiv i
          ((D.tailComponentEquiv i).symm x)]
        exact congrArg
          (fun z : D.tailComponentCarrier i ↦
            (((z : (D.suffixQuadraticSublattice 1).carrier) : V)))
          ((D.tailComponentEquiv i).apply_symm_apply x).symm
      have hy :
          (((y : (D.suffixQuadraticSublattice 1).carrier) : V)) =
            (((D.tailComponentEquiv i).symm y :
              (D.component i.succ).carrier) : V) := by
        rw [← D.coe_tailComponentEquiv i
          ((D.tailComponentEquiv i).symm y)]
        exact congrArg
          (fun z : D.tailComponentCarrier i ↦
            (((z : (D.suffixQuadraticSublattice 1).carrier) : V)))
          ((D.tailComponentEquiv i).apply_symm_apply y).symm
      change q.bilin
        (((x : (D.suffixQuadraticSublattice 1).carrier) : V))
        (((y : (D.suffixQuadraticSublattice 1).carrier) : V)) = _
      rw [hx, hy]
      rfl]
    exact (D.component i.succ).nondegenerate.congr
      (D.tailComponentEquiv i)
  lattice := map (D.tailComponentEquiv i) (D.component i.succ).lattice

/-- Each original positive-index component is integrally isometric to its
copy in the suffix decomposition. -/
noncomputable def tailComponentIsometry (i : Fin n) :
    Isometry (D.component i.succ).space (D.tailComponent i).space
      (D.component i.succ).lattice (D.tailComponent i).lattice where
  toLinearEquiv := D.tailComponentEquiv i
  map_bilin _ _ := rfl
  map_mem x := (map_mem_map_iff (D.tailComponentEquiv i)
    (D.component i.succ).lattice x).symm

/-- Mapping a tail component's ambient integral module back to the original
ambient space recovers the original component lattice. -/
theorem map_tailComponent_ambientSubmodule (i : Fin n) :
    (D.tailComponent i).ambientSubmodule.map
        ((Submodule.subtype
          (D.suffixQuadraticSublattice 1).carrier).restrictScalars
          (IntegerRing K)) =
      (D.component i.succ).ambientSubmodule := by
  ext x
  constructor
  · rintro ⟨z, ⟨w, hw, hwz⟩, hzx⟩
    have hw' : (show D.tailComponentCarrier i from w) ∈
        map (D.tailComponentEquiv i)
          (D.component i.succ).lattice := by
      exact hw
    rw [mem_map_iff] at hw'
    let y : (D.component i.succ).carrier :=
      (D.tailComponentEquiv i).symm w
    refine ⟨y, ?_, ?_⟩
    · simpa [y] using hw'
    · have hyw : D.tailComponentEquiv i y = w := by
        exact (D.tailComponentEquiv i).apply_symm_apply w
      have hcoe := congrArg
        (fun a : D.tailComponentCarrier i ↦
          (((a : (D.suffixQuadraticSublattice 1).carrier) : V))) hyw
      exact (D.coe_tailComponentEquiv i y).symm.trans
        (hcoe.trans (congrArg Subtype.val hwz |>.trans hzx))
  · rintro ⟨y, hy, rfl⟩
    let w : D.tailComponentCarrier i := D.tailComponentEquiv i y
    refine ⟨(w : (D.suffixQuadraticSublattice 1).carrier), ?_, ?_⟩
    · refine ⟨w, ?_, rfl⟩
      change w ∈ map (D.tailComponentEquiv i)
        (D.component i.succ).lattice
      exact (map_mem_map_iff (D.tailComponentEquiv i)
        (D.component i.succ).lattice y).2 hy
    · exact D.coe_tailComponentEquiv i y

/-- The positive-index components form an exact decomposition of the suffix
lattice. -/
noncomputable def tailDecomposition :
    OrthogonalDecomposition (D.suffixQuadraticSublattice 1).space
      (D.suffixQuadraticSublattice 1).lattice n where
  component := D.tailComponent
  orthogonal := by
    intro i j hij x y
    let x' : (D.component i.succ).carrier :=
      (D.tailComponentEquiv i).symm x
    let y' : (D.component j.succ).carrier :=
      (D.tailComponentEquiv j).symm y
    have h := D.orthogonal i.succ j.succ (by
      intro hEq
      apply hij
      apply Fin.ext
      simpa using congrArg Fin.val hEq) x' y'
    have hx : (x' : V) =
        (((show D.tailComponentCarrier i from x) :
          (D.suffixQuadraticSublattice 1).carrier) : V) := by
      rw [← D.coe_tailComponentEquiv i x']
      exact congrArg
        (fun z : D.tailComponentCarrier i ↦
          (((z : (D.suffixQuadraticSublattice 1).carrier) : V)))
        ((D.tailComponentEquiv i).apply_symm_apply x)
    have hy : (y' : V) =
        (((show D.tailComponentCarrier j from y) :
          (D.suffixQuadraticSublattice 1).carrier) : V) := by
      rw [← D.coe_tailComponentEquiv j y']
      exact congrArg
        (fun z : D.tailComponentCarrier j ↦
          (((z : (D.suffixQuadraticSublattice 1).carrier) : V)))
        ((D.tailComponentEquiv j).apply_symm_apply y)
    change q.bilin
      (((show D.tailComponentCarrier i from x) :
        (D.suffixQuadraticSublattice 1).carrier) : V)
      (((show D.tailComponentCarrier j from y) :
        (D.suffixQuadraticSublattice 1).carrier) : V) = 0
    rwa [← hx, ← hy]
  sum_eq := by
    let inclusion :=
      (Submodule.subtype
        (D.suffixQuadraticSublattice 1).carrier).restrictScalars
        (IntegerRing K)
    apply (Submodule.map_injective_of_injective
      (f := inclusion) Subtype.val_injective)
    dsimp only [inclusion]
    rw [Submodule.map_iSup]
    simp_rw [D.map_tailComponent_ambientSubmodule]
    change (⨆ i : Fin n, (D.component i.succ).ambientSubmodule) =
      (D.suffixQuadraticSublattice 1).ambientSubmodule
    rw [D.suffixQuadraticSublattice_ambientSubmodule]
    change (⨆ i : Fin n, (D.component i.succ).ambientSubmodule) =
      D.suffixAmbientSubmodule 1
    unfold suffixAmbientSubmodule
    apply le_antisymm
    · apply iSup_le
      intro i
      exact le_iSup
        (fun j : D.SuffixIndex 1 ↦ (D.component j.1).ambientSubmodule)
        (D.tailIndex i)
    · apply iSup_le
      intro j
      have hjLower : 1 ≤ j.1.val := j.2
      have hjUpper : j.1.val < n + 1 := j.1.isLt
      let i : Fin n := ⟨j.1.val - 1, by omega⟩
      have hij : i.succ = j.1 := by
        apply Fin.ext
        simp [i]
        omega
      simpa [hij] using
        (le_iSup (fun h : Fin n ↦
          (D.component h.succ).ambientSubmodule) i)

end Tail

section HeadTail

variable (D : OrthogonalDecomposition q L (n + 2))

/-- Before the cut at one, the integral prefix is exactly the head
component. -/
theorem prefixAmbientSubmodule_one :
    D.prefixAmbientSubmodule 1 = (D.component 0).ambientSubmodule := by
  unfold prefixAmbientSubmodule
  apply le_antisymm
  · apply iSup_le
    intro i
    have hi : i.1 = (0 : Fin (n + 2)) := by
      apply Fin.ext
      have hlt : i.1.val < 1 := i.2
      exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hlt)
    simpa [hi]
  · exact le_iSup
      (fun i : D.PrefixIndex 1 ↦ (D.component i.1).ambientSubmodule)
      ⟨0, by simp⟩

/-- Split a decomposition with at least two components into its head and
the exact suffix lattice. -/
noncomputable def headTailComponents : Fin 2 → QuadraticSublattice q :=
  Fin.cases (D.component 0) (fun _ ↦ D.suffixQuadraticSublattice 1)

@[simp]
theorem headTailComponents_zero :
    D.headTailComponents 0 = D.component 0 :=
  rfl

@[simp]
theorem headTailComponents_one :
    D.headTailComponents 1 = D.suffixQuadraticSublattice 1 :=
  rfl

/-- Split a decomposition with at least two components into its head and
the exact suffix lattice. -/
noncomputable def headTailDecomposition : OrthogonalDecomposition q L 2 where
  component := D.headTailComponents
  orthogonal := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · intro x y
      apply D.bilin_prefixCarrier_suffixCarrier_eq_zero 1
      · exact le_iSup
          (fun h : D.PrefixIndex 1 ↦ (D.component h.1).carrier)
          ⟨0, by simp⟩ x.property
      · exact y.property
    · intro x y
      exact q.isSymm.eq (x : V) (y : V) |>.trans
        (D.bilin_prefixCarrier_suffixCarrier_eq_zero 1
          (le_iSup
            (fun h : D.PrefixIndex 1 ↦ (D.component h.1).carrier)
            ⟨0, by simp⟩ y.property)
          x.property)
    · exact (hij rfl).elim
  sum_eq := by
    have hpair :
        (D.component 0).ambientSubmodule ⊔
          (D.suffixQuadraticSublattice 1).ambientSubmodule =
            L.toSubmodule := by
      rw [D.suffixQuadraticSublattice_ambientSubmodule,
        ← D.prefixAmbientSubmodule_one]
      exact D.prefixAmbientSubmodule_sup_suffixAmbientSubmodule 1
    rw [iSup_fin_two_eq_sup_tail, D.headTailComponents_zero,
      D.headTailComponents_one]
    exact hpair

@[simp]
theorem headTailDecomposition_zero :
    (D.headTailDecomposition.component 0) = D.component 0 :=
  rfl

@[simp]
theorem headTailDecomposition_one :
    (D.headTailDecomposition.component 1) =
      D.suffixQuadraticSublattice 1 :=
  rfl

end HeadTail

end

end OrthogonalDecomposition

namespace JordanDecomposition

noncomputable section

variable (J : JordanDecomposition q L (n + 1))

/-- Removing the first component of a nonempty Jordan decomposition gives a
Jordan decomposition of the exact integral suffix lattice.  All arithmetic
labels are inherited from the corresponding positive-index components. -/
noncomputable def tail :
    JordanDecomposition
      (J.toOrthogonalDecomposition.suffixQuadraticSublattice 1).space
      (J.toOrthogonalDecomposition.suffixQuadraticSublattice 1).lattice n where
  toOrthogonalDecomposition :=
    J.toOrthogonalDecomposition.tailDecomposition
  scaleGenerator := fun i => J.scaleGenerator i.succ
  normGenerator := fun i => J.normGenerator i.succ
  modular := by
    intro i
    exact (J.modular i.succ).mapLatticeIsometry
      (J.toOrthogonalDecomposition.tailComponentIsometry i)
  scaleIdeal_eq := by
    intro i
    let g := J.toOrthogonalDecomposition.tailComponentIsometry i
    calc
      scaleIdeal
          (J.toOrthogonalDecomposition.tailComponent i).space
          (J.toOrthogonalDecomposition.tailComponent i).lattice =
          scaleIdeal (J.component i.succ).space
            (J.component i.succ).lattice := by
        rw [← g.map_eq]
        exact scaleIdeal_map_isometry g.toQuadraticSpaceIsometry _
      _ = principalIdeal (K := K) (J.scaleGenerator i.succ : K) :=
        J.scaleIdeal_eq i.succ
  normIdeal_eq := by
    intro i
    let g := J.toOrthogonalDecomposition.tailComponentIsometry i
    calc
      normIdeal
          (J.toOrthogonalDecomposition.tailComponent i).space
          (J.toOrthogonalDecomposition.tailComponent i).lattice =
          normIdeal (J.component i.succ).space
            (J.component i.succ).lattice := by
        rw [← g.map_eq]
        exact normIdeal_map_isometry g.toQuadraticSpaceIsometry _
      _ = principalIdeal (K := K) (J.normGenerator i.succ : K) :=
        J.normIdeal_eq i.succ
  scaleOrder_strict := by
    intro i j hij
    exact J.scaleOrder_strict (Fin.succ_lt_succ_iff.mpr hij)

@[simp]
theorem tail_component (i : Fin n) :
    (J.tail.component i) =
      J.toOrthogonalDecomposition.tailComponent i :=
  rfl

@[simp]
theorem tail_scaleGenerator (i : Fin n) :
    J.tail.scaleGenerator i = J.scaleGenerator i.succ :=
  rfl

@[simp]
theorem tail_normGenerator (i : Fin n) :
    J.tail.normGenerator i = J.normGenerator i.succ :=
  rfl

@[simp]
theorem tail_componentRank (i : Fin n) :
    J.tail.componentRank i = J.componentRank i.succ := by
  unfold componentRank
  exact (J.toOrthogonalDecomposition.tailComponentEquiv i).finrank_eq.symm

end

end JordanDecomposition

end Lattice

end Bong
