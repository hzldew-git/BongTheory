import Bong.Lattice.JordanReplaceFirstPair
import Bong.Lattice.OrthogonalDecompositionPrefix

namespace Bong

open Dyadic Module

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

namespace OrthogonalDecomposition

/-- The carrier of two amalgamated components is their binary supremum. -/
theorem orthogonalSup_carrier_eq_sup
    (D : OrthogonalDecomposition q L (n + 2))
    {i j : Fin (n + 2)} (hij : i ≠ j) :
    (D.orthogonalSup hij).carrier =
      (D.component i).carrier ⊔ (D.component j).carrier := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact Submodule.add_mem _
      ((_root_.le_sup_left : (D.component i).carrier ≤
        (D.component i).carrier ⊔ (D.component j).carrier) z.1.property)
      ((_root_.le_sup_right : (D.component j).carrier ≤
        (D.component i).carrier ⊔ (D.component j).carrier) z.2.property)
  · intro hx
    rw [Submodule.mem_sup] at hx
    rcases hx with ⟨xi, hxi, xj, hxj, rfl⟩
    exact ⟨(⟨xi, hxi⟩, ⟨xj, hxj⟩), rfl⟩

/-- A binary decomposition of a quadratic sublattice recovers its whole
carrier after the two pieces are lifted to the ambient space. -/
theorem liftNested_pair_carrier_sup_eq
    (C : QuadraticSublattice q)
    (P : OrthogonalDecomposition C.space C.lattice 2) :
    (C.liftNested (P.component 0)).carrier ⊔
        (C.liftNested (P.component 1)).carrier = C.carrier := by
  change (P.component 0).carrier.map C.carrier.subtype ⊔
      (P.component 1).carrier.map C.carrier.subtype = C.carrier
  rw [← Submodule.map_sup]
  have htop : (P.component 0).carrier ⊔
      (P.component 1).carrier = ⊤ := by
    rw [← P.carrier_iSup_eq_top]
    apply le_antisymm
    · exact _root_.sup_le
        (le_iSup (fun i : Fin 2 ↦ (P.component i).carrier) 0)
        (le_iSup (fun i : Fin 2 ↦ (P.component i).carrier) 1)
    · apply iSup_le
      rw [Fin.forall_fin_two]
      exact ⟨_root_.le_sup_left, _root_.le_sup_right⟩
  rw [htop, Submodule.map_top]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact y.property
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

/-- Replacing the first two components does not change any prefix containing
both of them. -/
theorem replacePair_first_prefixCarrier_eq
    (D : OrthogonalDecomposition q L (n + 2))
    (P : OrthogonalDecomposition
      (D.orthogonalSup JordanDecomposition.firstIndex_ne_secondIndex).space
      (D.orthogonalSup JordanDecomposition.firstIndex_ne_secondIndex).lattice 2)
    (k : Nat) (hk : 2 ≤ k) :
    (D.replacePair JordanDecomposition.firstIndex_ne_secondIndex P).prefixCarrier k =
      D.prefixCarrier k := by
  classical
  let C := D.orthogonalSup JordanDecomposition.firstIndex_ne_secondIndex
  let E := D.replacePair JordanDecomposition.firstIndex_ne_secondIndex P
  have hOld : (D.component 0).carrier ⊔ (D.component 1).carrier = C.carrier := by
    exact (D.orthogonalSup_carrier_eq_sup
      JordanDecomposition.firstIndex_ne_secondIndex).symm
  have hNew : (E.component 0).carrier ⊔ (E.component 1).carrier = C.carrier := by
    rw [show E.component 0 = C.liftNested (P.component 0) by
      exact D.replacePair_component_left
        JordanDecomposition.firstIndex_ne_secondIndex P]
    rw [show E.component 1 = C.liftNested (P.component 1) by
      exact D.replacePair_component_right
        JordanDecomposition.firstIndex_ne_secondIndex P]
    exact liftNested_pair_carrier_sup_eq C P
  change E.prefixCarrier k = D.prefixCarrier k
  unfold prefixCarrier
  apply le_antisymm
  · apply iSup_le
    intro a
    by_cases ha0 : a.1 = 0
    · rw [ha0]
      have hpair : (E.component 0).carrier ≤
          (E.component 0).carrier ⊔ (E.component 1).carrier :=
        _root_.le_sup_left
      rw [hNew] at hpair
      rw [← hOld] at hpair
      exact hpair.trans <| _root_.sup_le
        (le_iSup (fun b : D.PrefixIndex k ↦ (D.component b.1).carrier)
          ⟨0, by change (0 : Nat) < k; omega⟩)
        (le_iSup (fun b : D.PrefixIndex k ↦ (D.component b.1).carrier)
          ⟨1, by change (1 : Nat) < k; omega⟩)
    · by_cases ha1 : a.1 = 1
      · rw [ha1]
        have hpair : (E.component 1).carrier ≤
            (E.component 0).carrier ⊔ (E.component 1).carrier :=
          _root_.le_sup_right
        rw [hNew] at hpair
        rw [← hOld] at hpair
        exact hpair.trans <| _root_.sup_le
          (le_iSup (fun b : D.PrefixIndex k ↦ (D.component b.1).carrier)
            ⟨0, by change (0 : Nat) < k; omega⟩)
          (le_iSup (fun b : D.PrefixIndex k ↦ (D.component b.1).carrier)
            ⟨1, by change (1 : Nat) < k; omega⟩)
      · rw [show E.component a.1 = D.component a.1 by
          exact D.replacePair_component_other
            JordanDecomposition.firstIndex_ne_secondIndex P a.1 ha0 ha1]
        exact le_iSup (fun b : D.PrefixIndex k ↦
          (D.component b.1).carrier) a
  · apply iSup_le
    intro a
    by_cases ha0 : a.1 = 0
    · rw [ha0]
      have hpair : (D.component 0).carrier ≤
          (D.component 0).carrier ⊔ (D.component 1).carrier :=
        _root_.le_sup_left
      rw [hOld] at hpair
      rw [← hNew] at hpair
      exact hpair.trans <| _root_.sup_le
        (le_iSup (fun b : E.PrefixIndex k ↦ (E.component b.1).carrier)
          ⟨0, by change (0 : Nat) < k; omega⟩)
        (le_iSup (fun b : E.PrefixIndex k ↦ (E.component b.1).carrier)
          ⟨1, by change (1 : Nat) < k; omega⟩)
    · by_cases ha1 : a.1 = 1
      · rw [ha1]
        have hpair : (D.component 1).carrier ≤
            (D.component 0).carrier ⊔ (D.component 1).carrier :=
          _root_.le_sup_right
        rw [hOld] at hpair
        rw [← hNew] at hpair
        exact hpair.trans <| _root_.sup_le
          (le_iSup (fun b : E.PrefixIndex k ↦ (E.component b.1).carrier)
            ⟨0, by change (0 : Nat) < k; omega⟩)
          (le_iSup (fun b : E.PrefixIndex k ↦ (E.component b.1).carrier)
            ⟨1, by change (1 : Nat) < k; omega⟩)
      · rw [← show E.component a.1 = D.component a.1 by
          exact D.replacePair_component_other
            JordanDecomposition.firstIndex_ne_secondIndex P a.1 ha0 ha1]
        exact le_iSup (fun b : E.PrefixIndex k ↦
          (E.component b.1).carrier) a

/-- The integral ambient prefix is likewise unchanged after replacing the
first pair. -/
theorem replacePair_first_prefixAmbientSubmodule_eq
    (D : OrthogonalDecomposition q L (n + 2))
    (P : OrthogonalDecomposition
      (D.orthogonalSup JordanDecomposition.firstIndex_ne_secondIndex).space
      (D.orthogonalSup JordanDecomposition.firstIndex_ne_secondIndex).lattice 2)
    (k : Nat) (hk : 2 ≤ k) :
    (D.replacePair JordanDecomposition.firstIndex_ne_secondIndex P).prefixAmbientSubmodule k =
      D.prefixAmbientSubmodule k := by
  let E := D.replacePair JordanDecomposition.firstIndex_ne_secondIndex P
  have hcarrier : E.prefixCarrier k = D.prefixCarrier k :=
    D.replacePair_first_prefixCarrier_eq P k hk
  ext x
  rw [E.mem_prefixAmbientSubmodule_iff,
    D.mem_prefixAmbientSubmodule_iff, hcarrier]

/-- The identity on ambient vectors is an integral isometry between every
old and new prefix that contains the replaced pair. -/
noncomputable def replacePair_first_prefixLatticeIsometry
    (D : OrthogonalDecomposition q L (n + 2))
    (P : OrthogonalDecomposition
      (D.orthogonalSup JordanDecomposition.firstIndex_ne_secondIndex).space
      (D.orthogonalSup JordanDecomposition.firstIndex_ne_secondIndex).lattice 2)
    (k : Nat) (hk : 2 ≤ k) :
    Isometry (D.prefixQuadraticSublattice k).space
      ((D.replacePair JordanDecomposition.firstIndex_ne_secondIndex P
        ).prefixQuadraticSublattice k).space
      (D.prefixQuadraticSublattice k).lattice
      ((D.replacePair JordanDecomposition.firstIndex_ne_secondIndex P
        ).prefixQuadraticSublattice k).lattice := by
  let E := D.replacePair JordanDecomposition.firstIndex_ne_secondIndex P
  have hcarrier : D.prefixCarrier k = E.prefixCarrier k :=
    (D.replacePair_first_prefixCarrier_eq P k hk).symm
  let e : D.prefixCarrier k ≃ₗ[K] E.prefixCarrier k :=
    LinearEquiv.ofEq _ _ hcarrier
  refine {
    toLinearEquiv := e
    map_bilin := ?_
    map_mem := ?_
  }
  · intro x y
    rfl
  · intro x
    change (show D.prefixCarrier k from x) ∈ D.prefixLattice k ↔
      e (show D.prefixCarrier k from x) ∈ E.prefixLattice k
    rw [D.mem_prefixLattice_iff, E.mem_prefixLattice_iff]
    have hamb : E.prefixAmbientSubmodule k =
        D.prefixAmbientSubmodule k :=
      D.replacePair_first_prefixAmbientSubmodule_eq P k hk
    have hcoe : ((e x : E.prefixCarrier k) : V) = (x : V) := by
      rfl
    rw [hcoe, hamb]

end OrthogonalDecomposition

end Lattice

end Bong
