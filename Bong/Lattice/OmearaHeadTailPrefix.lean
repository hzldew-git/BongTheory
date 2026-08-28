/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OrthogonalSublatticeSum
import Bong.Lattice.OrthogonalDecompositionTail
import Bong.Lattice.OrthogonalDecompositionPrefix
import Bong.Lattice.OrthogonalProductIsometry

/-!
# Splitting a Jordan prefix into its head and tail prefix

The prefix of length `k+1` in a nonempty orthogonal decomposition is the
orthogonal product of the head component and the prefix of length `k` in the
exact suffix decomposition.  Both the quadratic-space and integral-lattice
identifications are concrete.
-/

namespace Bong

open Dyadic Module

namespace Lattice.OrthogonalDecomposition

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

variable (D : OrthogonalDecomposition q L (n + 1))

/-- Mapping a tail component carrier back to the original ambient space
recovers the corresponding positive-index component carrier. -/
theorem map_tailComponent_carrier (i : Fin n) :
    (D.tailComponent i).carrier.map
        (Submodule.subtype
          (D.suffixQuadraticSublattice 1).carrier) =
      (D.component i.succ).carrier := by
  ext x
  constructor
  · rintro ⟨z, hz, hzx⟩
    rcases hz with ⟨y, hy⟩
    have hzy : (z : V) = (y : V) := by
      rw [← hy]
      rfl
    have hxy : x = (y : V) := hzx.symm.trans hzy
    rw [hxy]
    exact y.property
  · intro hx
    let y : (D.component i.succ).carrier := ⟨x, hx⟩
    let z : (D.suffixQuadraticSublattice 1).carrier :=
      D.componentToTailLinearMap i y
    refine ⟨z, ?_, ?_⟩
    · exact ⟨y, rfl⟩
    · rfl

/-- The prefix of the exact suffix, lifted back to the original quadratic
space. -/
noncomputable def tailPrefixLift (k : Nat) : QuadraticSublattice q :=
  (D.suffixQuadraticSublattice 1).liftNested
    (D.tailDecomposition.prefixQuadraticSublattice k)

/-- Its carrier is the sum of the original positive-index component
carriers occurring before the tail cut. -/
theorem tailPrefixLift_carrier (k : Nat) :
    (D.tailPrefixLift k).carrier =
      ⨆ i : D.tailDecomposition.PrefixIndex k,
        (D.component i.1.succ).carrier := by
  rw [tailPrefixLift, QuadraticSublattice.liftNested_carrier]
  unfold QuadraticSublattice.nestedCarrier
  rw [D.tailDecomposition.prefixQuadraticSublattice_carrier]
  unfold prefixCarrier
  rw [Submodule.map_iSup]
  change (⨆ i : D.tailDecomposition.PrefixIndex k,
      (D.tailComponent i.1).carrier.map
        (Submodule.subtype
          (D.suffixQuadraticSublattice 1).carrier)) = _
  simp_rw [D.map_tailComponent_carrier]

/-- The same statement for the embedded integral modules. -/
theorem tailPrefixLift_ambientSubmodule (k : Nat) :
    (D.tailPrefixLift k).ambientSubmodule =
      ⨆ i : D.tailDecomposition.PrefixIndex k,
        (D.component i.1.succ).ambientSubmodule := by
  rw [tailPrefixLift, QuadraticSublattice.ambientSubmodule_liftNested,
    D.tailDecomposition.prefixQuadraticSublattice_ambientSubmodule]
  unfold prefixAmbientSubmodule
  rw [Submodule.map_iSup]
  change (⨆ i : D.tailDecomposition.PrefixIndex k,
      (D.tailComponent i.1).ambientSubmodule.map
        ((Submodule.subtype
          (D.suffixQuadraticSublattice 1).carrier).restrictScalars
            (IntegerRing K))) = _
  simp_rw [D.map_tailComponent_ambientSubmodule]

variable {D}

/-- The head carrier and lifted tail-prefix carrier sum to the next full
prefix carrier. -/
theorem head_sup_tailPrefixLift_carrier
    (D : OrthogonalDecomposition q L (n + 2)) (k : Nat) :
    (D.component 0).carrier ⊔ (D.tailPrefixLift k).carrier =
      (D.prefixQuadraticSublattice (k + 1)).carrier := by
  rw [D.tailPrefixLift_carrier,
    D.prefixQuadraticSublattice_carrier]
  unfold prefixCarrier
  apply le_antisymm
  · apply _root_.sup_le
    · exact le_iSup
        (fun i : D.PrefixIndex (k + 1) => (D.component i.1).carrier)
        ⟨0, by simp⟩
    · apply iSup_le
      intro i
      exact le_iSup
        (fun j : D.PrefixIndex (k + 1) => (D.component j.1).carrier)
        ⟨i.1.succ, by
          change i.1.val + 1 < k + 1
          omega⟩
  · apply iSup_le
    intro i
    by_cases hi : i.1.val = 0
    · have hi0 : i.1 = (0 : Fin (n + 2)) := Fin.ext hi
      simpa only [hi0] using
        (_root_.le_sup_left : (D.component 0).carrier ≤
          (D.component 0).carrier ⊔
            (⨆ j : D.tailDecomposition.PrefixIndex k,
              (D.component j.1.succ).carrier))
    · let j : Fin (n + 1) := ⟨i.1.val - 1, by omega⟩
      have hsucc : j.succ = i.1 := by
        apply Fin.ext
        change j.val + 1 = i.1.val
        dsimp only [j]
        omega
      have hj : j.val < k := by
        dsimp only [j]
        omega
      have hle := le_iSup
        (fun a : D.tailDecomposition.PrefixIndex k =>
          (D.component a.1.succ).carrier) ⟨j, hj⟩
      simpa only [hsucc] using hle.trans
        (_root_.le_sup_right :
          (⨆ a : D.tailDecomposition.PrefixIndex k,
            (D.component a.1.succ).carrier) ≤
          (D.component 0).carrier ⊔
            (⨆ a : D.tailDecomposition.PrefixIndex k,
              (D.component a.1.succ).carrier))

/-- Integral version of `head_sup_tailPrefixLift_carrier`. -/
theorem head_sup_tailPrefixLift_ambientSubmodule
    (D : OrthogonalDecomposition q L (n + 2)) (k : Nat) :
    (D.component 0).ambientSubmodule ⊔
        (D.tailPrefixLift k).ambientSubmodule =
      (D.prefixQuadraticSublattice (k + 1)).ambientSubmodule := by
  rw [D.tailPrefixLift_ambientSubmodule,
    D.prefixQuadraticSublattice_ambientSubmodule]
  unfold prefixAmbientSubmodule
  apply le_antisymm
  · apply _root_.sup_le
    · exact le_iSup
        (fun i : D.PrefixIndex (k + 1) =>
          (D.component i.1).ambientSubmodule) ⟨0, by simp⟩
    · apply iSup_le
      intro i
      exact le_iSup
        (fun j : D.PrefixIndex (k + 1) =>
          (D.component j.1).ambientSubmodule) ⟨i.1.succ, by
            change i.1.val + 1 < k + 1
            omega⟩
  · apply iSup_le
    intro i
    by_cases hi : i.1.val = 0
    · have hi0 : i.1 = (0 : Fin (n + 2)) := Fin.ext hi
      simpa only [hi0] using
        (_root_.le_sup_left : (D.component 0).ambientSubmodule ≤
          (D.component 0).ambientSubmodule ⊔
            (⨆ j : D.tailDecomposition.PrefixIndex k,
              (D.component j.1.succ).ambientSubmodule))
    · let j : Fin (n + 1) := ⟨i.1.val - 1, by omega⟩
      have hsucc : j.succ = i.1 := by
        apply Fin.ext
        change j.val + 1 = i.1.val
        dsimp only [j]
        omega
      have hj : j.val < k := by
        dsimp only [j]
        omega
      have hle := le_iSup
        (fun a : D.tailDecomposition.PrefixIndex k =>
          (D.component a.1.succ).ambientSubmodule) ⟨j, hj⟩
      simpa only [hsucc] using hle.trans
        (_root_.le_sup_right :
          (⨆ a : D.tailDecomposition.PrefixIndex k,
            (D.component a.1.succ).ambientSubmodule) ≤
          (D.component 0).ambientSubmodule ⊔
            (⨆ a : D.tailDecomposition.PrefixIndex k,
              (D.component a.1.succ).ambientSubmodule))

/-- The head is orthogonal to every lifted tail prefix. -/
theorem head_orthogonal_tailPrefixLift
    (D : OrthogonalDecomposition q L (n + 2)) (k : Nat)
    (x : (D.component 0).carrier) (y : (D.tailPrefixLift k).carrier) :
    q.bilin (x : V) (y : V) = 0 := by
  apply D.bilin_prefixCarrier_suffixCarrier_eq_zero 1
  · exact le_iSup
      (fun i : D.PrefixIndex 1 => (D.component i.1).carrier)
      ⟨0, by simp⟩ x.property
  · exact (D.suffixQuadraticSublattice 1).nestedCarrier_le
      (D.tailDecomposition.prefixQuadraticSublattice k) y.property

/-- Concrete integral isometry
`head ⊥ tail-prefix(k) ≅ full-prefix(k+1)`. -/
noncomputable def headTailPrefixLatticeIsometry
    (D : OrthogonalDecomposition q L (n + 2)) (k : Nat) :
    Isometry
      ((D.component 0).space.orthogonalSum
        (D.tailDecomposition.prefixQuadraticSublattice k).space)
      (D.prefixQuadraticSublattice (k + 1)).space
      (product (D.component 0).lattice
        (D.tailDecomposition.prefixQuadraticSublattice k).lattice)
      (D.prefixQuadraticSublattice (k + 1)).lattice := by
  let liftTail :=
    (D.suffixQuadraticSublattice 1).liftNestedIsometry
      (D.tailDecomposition.prefixQuadraticSublattice k)
  let liftProduct :=
    (Isometry.refl (D.component 0).space (D.component 0).lattice).orthogonalProductBasic
      liftTail
  exact liftProduct.trans <|
    QuadraticSublattice.orthogonalSumLatticeIsometry
      (D.component 0) (D.tailPrefixLift k)
      (D.prefixQuadraticSublattice (k + 1))
      (D.head_sup_tailPrefixLift_carrier k)
      (D.head_sup_tailPrefixLift_ambientSubmodule k)
      (D.head_orthogonal_tailPrefixLift k)

end Lattice.OrthogonalDecomposition

end Bong
