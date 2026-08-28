/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009ComponentwiseAssembly
import Bong.Lattice.OrthogonalProductDecomposition
import Bong.Lattice.OrthogonalDecompositionCons
import Bong.Lattice.JordanIsometry

/-!
# Orthogonal decompositions of finite block products

The finite dependent product model used for componentwise assembly also has
a canonical integral orthogonal decomposition by its coordinate blocks.  We
construct it recursively from binary orthogonal products and retain an
explicit lattice isometry from every input block to its displayed component.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

private theorem restrictTop_nondegenerate (q : QuadraticSpace K V) :
    (q.bilin.restrict (⊤ : Submodule K V)).Nondegenerate := by
  constructor
  · intro x hx
    apply Subtype.ext
    exact q.nondegenerate.1 (x : V) (fun y ↦ hx ⟨y, trivial⟩)
  · intro y hy
    apply Subtype.ext
    exact q.nondegenerate.2 (y : V) (fun x ↦ hy ⟨x, trivial⟩)

/-- The canonical quadratic-space isometry onto the top restriction. -/
private def restrictTopIsometry (q : QuadraticSpace K V) :
    QuadraticSpace.Isometry q
      (q.restrict (⊤ : Submodule K V) (restrictTop_nondegenerate q)) where
  toLinearEquiv := Submodule.topEquiv.symm
  map_bilin := by intro x y; rfl

/-- The whole ambient lattice, regarded as a quadratic sublattice. -/
noncomputable def wholeQuadraticSublattice
    (q : QuadraticSpace K V) (L : Lattice K V) :
    QuadraticSublattice q := by
  exact {
    carrier := ⊤
    nondegenerate := restrictTop_nondegenerate q
    lattice := map (restrictTopIsometry q).toLinearEquiv L
  }

/-- The ambient lattice is integrally isometric to its whole-sublattice
presentation. -/
noncomputable def wholeQuadraticSublatticeIsometry
    (q : QuadraticSpace K V) (L : Lattice K V) :
    Isometry q (wholeQuadraticSublattice q L).space L
      (wholeQuadraticSublattice q L).lattice := by
  exact {
    toLinearEquiv := (restrictTopIsometry q).toLinearEquiv
    map_bilin := (restrictTopIsometry q).map_bilin
    map_mem := fun x ↦
      (map_mem_map_iff (restrictTopIsometry q).toLinearEquiv L x).symm
  }

/-- The ambient integral module of the whole sublattice is the original
lattice. -/
theorem wholeQuadraticSublattice_ambientSubmodule
    (q : QuadraticSpace K V) (L : Lattice K V) :
    (wholeQuadraticSublattice q L).ambientSubmodule = L.toSubmodule := by
  ext x
  constructor
  · rintro ⟨y, hy, hyx⟩
    change y ∈ map (restrictTopIsometry q).toLinearEquiv L at hy
    have hy' : (restrictTopIsometry q).toLinearEquiv.symm y ∈ L :=
      (mem_map_iff (restrictTopIsometry q).toLinearEquiv L y).1 hy
    change (y : V) = x at hyx
    simpa [restrictTopIsometry] using hyx ▸ hy'
  · intro hx
    let y : (⊤ : Submodule K V) :=
      (restrictTopIsometry q).toLinearEquiv x
    refine ⟨y, ?_, ?_⟩
    · change y ∈ map (restrictTopIsometry q).toLinearEquiv L
      exact (map_mem_map_iff
        (restrictTopIsometry q).toLinearEquiv L x).2 hx
    · change (y : V) = x
      rfl

/-- The one-component integral orthogonal decomposition. -/
noncomputable def singleOrthogonalDecomposition
    (q : QuadraticSpace K V) (L : Lattice K V) :
    OrthogonalDecomposition q L 1 where
  component := fun _ ↦ wholeQuadraticSublattice q L
  orthogonal := by
    intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  sum_eq := by
    rw [show (⨆ _ : Fin 1, (wholeQuadraticSublattice q L).ambientSubmodule) =
        (wholeQuadraticSublattice q L).ambientSubmodule by
      apply le_antisymm
      · apply iSup_le
        intro i
        exact le_rfl
      · exact le_iSup (fun _ : Fin 1 ↦
          (wholeQuadraticSublattice q L).ambientSubmodule) 0]
    exact wholeQuadraticSublattice_ambientSubmodule q L

@[simp]
theorem singleOrthogonalDecomposition_component
    (q : QuadraticSpace K V) (L : Lattice K V) (i : Fin 1) :
    (singleOrthogonalDecomposition q L).component i =
      wholeQuadraticSublattice q L :=
  rfl

end Lattice

namespace BONG

open Lattice

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The canonical coordinate-block decomposition of a nonempty finite
orthogonal product. -/
noncomputable def blockProductOrthogonalDecomposition :
    {n : Nat} →
    (C : Fin (n + 1) → Type v) →
    [(∀ i, AddCommGroup (C i))] → [(∀ i, Module K (C i))] →
    (qs : ∀ i, QuadraticSpace K (C i)) →
    (Ls : ∀ i, Lattice K (C i)) →
    OrthogonalDecomposition (blockOrthogonalForm n C qs)
      (blockProductLattice n C Ls) (n + 1)
  | 0, C, _, _, qs, Ls =>
      (singleOrthogonalDecomposition (qs 0) (Ls 0)).mapIsometry
        (blockOrthogonalSingletonLatticeIsometry C qs Ls).symm
  | n + 1, C, _, _, qs, Ls => by
      let tailC : Fin (n + 1) → Type v := fun i ↦ C i.succ
      let tailQ : ∀ i, QuadraticSpace K (tailC i) := fun i ↦ qs i.succ
      let tailL : ∀ i, Lattice K (tailC i) := fun i ↦ Ls i.succ
      let tailD := blockProductOrthogonalDecomposition tailC tailQ tailL
      let pairD := orthogonalProductDecomposition (qs 0)
        (blockOrthogonalForm n tailC tailQ) (Ls 0)
        (blockProductLattice n tailC tailL)
      let split := blockOrthogonalSplitLatticeIsometry (K := K)
        n C qs Ls
      let tailLift := tailD.mapIsometry
        (orthogonalProductRightComponentIsometry (qs 0)
          (blockOrthogonalForm n tailC tailQ)
          (blockProductLattice n tailC tailL))
      exact (pairD.prependNested tailLift).mapIsometry split.symm

/-- Each input lattice is integrally isometric to its displayed coordinate
component in the block-product decomposition. -/
noncomputable def blockProductComponentIsometry :
    {n : Nat} →
    (C : Fin (n + 1) → Type v) →
    [(∀ i, AddCommGroup (C i))] → [(∀ i, Module K (C i))] →
    (qs : ∀ i, QuadraticSpace K (C i)) →
    (Ls : ∀ i, Lattice K (C i)) →
    (i : Fin (n + 1)) →
    Isometry (qs i)
      ((blockProductOrthogonalDecomposition C qs Ls).component i).space
      (Ls i)
      ((blockProductOrthogonalDecomposition C qs Ls).component i).lattice
  | 0, C, _, _, qs, Ls, i => by
      have hi : i = (0 : Fin 1) := by
        apply Fin.ext
        omega
      subst i
      let D := singleOrthogonalDecomposition (qs 0) (Ls 0)
      let F := blockOrthogonalSingletonLatticeIsometry C qs Ls
      let componentMap := (D.component 0).mapLatticeIsometry F.symm
      exact (wholeQuadraticSublatticeIsometry (qs 0) (Ls 0)).trans
        componentMap
  | n + 1, C, _, _, qs, Ls, i => by
      let tailC : Fin (n + 1) → Type v := fun j ↦ C j.succ
      let tailQ : ∀ j, QuadraticSpace K (tailC j) := fun j ↦ qs j.succ
      let tailL : ∀ j, Lattice K (tailC j) := fun j ↦ Ls j.succ
      let tailD := blockProductOrthogonalDecomposition tailC tailQ tailL
      let tailForm := blockOrthogonalForm n tailC tailQ
      let tailLattice := blockProductLattice n tailC tailL
      let pairD := orthogonalProductDecomposition (qs 0) tailForm
        (Ls 0) tailLattice
      let right := orthogonalProductRightComponentIsometry (qs 0)
        tailForm tailLattice
      let tailLift := tailD.mapIsometry right
      let combined := pairD.prependNested tailLift
      let split := blockOrthogonalSplitLatticeIsometry (K := K)
        n C qs Ls
      let mapped := combined.mapIsometry split.symm
      cases i using Fin.cases with
      | zero =>
          let left := orthogonalProductLeftComponentIsometry
            (qs 0) tailForm (Ls 0)
          let finalMap := (combined.component 0).mapLatticeIsometry split.symm
          change Isometry (qs 0) (mapped.component 0).space (Ls 0)
            (mapped.component 0).lattice
          exact left.trans finalMap
      | succ j =>
          let originalToTail :=
            blockProductComponentIsometry tailC tailQ tailL j
          let tailMap := (tailD.component j).mapLatticeIsometry right
          let lift := (pairD.component 1).liftNestedIsometry
            (tailLift.component j)
          let finalMap := (combined.component j.succ).mapLatticeIsometry
            split.symm
          change Isometry (tailQ j) (mapped.component j.succ).space
            (tailL j) (mapped.component j.succ).lattice
          exact originalToTail.trans <| tailMap.trans <|
            lift.trans finalMap

/-- Assemble a Jordan decomposition from a finite ordered family of modular
lattices with specified scale and norm generators. -/
noncomputable def blockProductJordanDecomposition
    {n : Nat}
    (C : Fin (n + 1) → Type v)
    [∀ i, AddCommGroup (C i)] [∀ i, Module K (C i)]
    (qs : ∀ i, QuadraticSpace K (C i))
    (Ls : ∀ i, Lattice K (C i))
    (scale norm : Fin (n + 1) → Kˣ)
    (hmodular : ∀ i, IsModular (qs i) (Ls i) (scale i))
    (hscale : ∀ i, scaleIdeal (qs i) (Ls i) =
      principalIdeal (K := K) (scale i : K))
    (hnorm : ∀ i, normIdeal (qs i) (Ls i) =
      principalIdeal (K := K) (norm i : K))
    (hstrict : StrictMono (fun i ↦ ordUnit K (scale i))) :
    JordanDecomposition (blockOrthogonalForm n C qs)
      (blockProductLattice n C Ls) (n + 1) := by
  let D := blockProductOrthogonalDecomposition C qs Ls
  refine {
    toOrthogonalDecomposition := D
    scaleGenerator := scale
    normGenerator := norm
    modular := ?_
    scaleIdeal_eq := ?_
    normIdeal_eq := ?_
    scaleOrder_strict := fun hij ↦ hstrict hij
  }
  · intro i
    exact (hmodular i).mapLatticeIsometry
      (blockProductComponentIsometry C qs Ls i)
  · intro i
    let f := blockProductComponentIsometry C qs Ls i
    calc
      scaleIdeal (D.component i).space (D.component i).lattice =
          scaleIdeal (qs i) (Ls i) := by
        rw [← f.map_eq]
        exact scaleIdeal_map_isometry f.toQuadraticSpaceIsometry (Ls i)
      _ = principalIdeal (K := K) (scale i : K) := hscale i
  · intro i
    let f := blockProductComponentIsometry C qs Ls i
    calc
      normIdeal (D.component i).space (D.component i).lattice =
          normIdeal (qs i) (Ls i) := by
        rw [← f.map_eq]
        exact normIdeal_map_isometry f.toQuadraticSpaceIsometry (Ls i)
      _ = principalIdeal (K := K) (norm i : K) := hnorm i

@[simp]
theorem blockProductJordanDecomposition_scaleGenerator
    {n : Nat}
    (C : Fin (n + 1) → Type v)
    [∀ i, AddCommGroup (C i)] [∀ i, Module K (C i)]
    (qs : ∀ i, QuadraticSpace K (C i))
    (Ls : ∀ i, Lattice K (C i))
    (scale norm : Fin (n + 1) → Kˣ)
    (hmodular) (hscale) (hnorm) (hstrict) (i : Fin (n + 1)) :
    (blockProductJordanDecomposition C qs Ls scale norm hmodular
      hscale hnorm hstrict).scaleGenerator i = scale i :=
  rfl

/-- The rank of a displayed block-product Jordan component is the rank of
its source block. -/
theorem blockProductJordanDecomposition_componentRank
    {n : Nat}
    (C : Fin (n + 1) → Type v)
    [∀ i, AddCommGroup (C i)] [∀ i, Module K (C i)]
    (qs : ∀ i, QuadraticSpace K (C i))
    (Ls : ∀ i, Lattice K (C i))
    (scale norm : Fin (n + 1) → Kˣ)
    (hmodular) (hscale) (hnorm) (hstrict) (i : Fin (n + 1)) :
    (blockProductJordanDecomposition C qs Ls scale norm hmodular
      hscale hnorm hstrict).componentRank i = finrank K (C i) := by
  unfold JordanDecomposition.componentRank
  exact (blockProductComponentIsometry C qs Ls i).toLinearEquiv.finrank_eq.symm

end BONG

end Bong
