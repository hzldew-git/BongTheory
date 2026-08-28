/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.NestedSublattice
import Bong.Lattice.OrthogonalSup

/-!
# Replacing two components of an orthogonal decomposition

If two components of an orthogonal decomposition are first amalgamated and
their lattice is then decomposed again into two pieces, the new pair may be
inserted at the original two indices.  This is the bookkeeping operation used
in the terminating argument of Beli (2003), Lemma 4.6.
-/

namespace Bong

open Dyadic

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {t : Nat}

set_option maxHeartbeats 400000

namespace OrthogonalDecomposition

variable (D : OrthogonalDecomposition q L t) {i j : Fin t}

/-- Components obtained by inserting a two-component decomposition of an
explicit intermediate quadratic sublattice at the positions `i,j`. -/
noncomputable def replacePairComponentsIn (i j : Fin t)
    (C : QuadraticSublattice q)
    (P : OrthogonalDecomposition C.space C.lattice 2) :
    Fin t → QuadraticSublattice q := fun k ↦
  if k = i then C.liftNested (P.component 0)
  else if k = j then C.liftNested (P.component 1)
  else D.component k

@[simp]
theorem replacePairComponentsIn_left (hij : i ≠ j)
    (C : QuadraticSublattice q)
    (P : OrthogonalDecomposition C.space C.lattice 2) :
    D.replacePairComponentsIn i j C P i =
      C.liftNested (P.component 0) := by
  simp [replacePairComponentsIn]

@[simp]
theorem replacePairComponentsIn_right (hij : i ≠ j)
    (C : QuadraticSublattice q)
    (P : OrthogonalDecomposition C.space C.lattice 2) :
    D.replacePairComponentsIn i j C P j =
      C.liftNested (P.component 1) := by
  simp [replacePairComponentsIn, hij.symm]

@[simp]
theorem replacePairComponentsIn_other (hij : i ≠ j)
    (C : QuadraticSublattice q)
    (P : OrthogonalDecomposition C.space C.lattice 2)
    (k : Fin t) (hki : k ≠ i) (hkj : k ≠ j) :
    D.replacePairComponentsIn i j C P k = D.component k := by
  simp [replacePairComponentsIn, hki, hkj]

private theorem liftNested_pair_orthogonal
    (C : QuadraticSublattice q)
    (P : OrthogonalDecomposition C.space C.lattice 2)
    {a b : Fin 2} (hab : a ≠ b)
    (x : (C.liftNested (P.component a)).carrier)
    (y : (C.liftNested (P.component b)).carrier) :
    q.bilin (x : V) (y : V) = 0 := by
  let x' : (P.component a).carrier :=
    (C.nestedCarrierEquiv (P.component a)).symm x
  let y' : (P.component b).carrier :=
    (C.nestedCarrierEquiv (P.component b)).symm y
  have h := P.orthogonal a b hab x' y'
  change q.bilin ((x' : C.carrier) : V) ((y' : C.carrier) : V) = 0 at h
  have hx : ((x' : C.carrier) : V) = (x : V) := by
    rw [← C.coe_nestedCarrierEquiv (P.component a) x']
    exact congrArg Subtype.val
      ((C.nestedCarrierEquiv (P.component a)).apply_symm_apply x)
  have hy : ((y' : C.carrier) : V) = (y : V) := by
    rw [← C.coe_nestedCarrierEquiv (P.component b) y']
    exact congrArg Subtype.val
      ((C.nestedCarrierEquiv (P.component b)).apply_symm_apply y)
  rwa [hx, hy] at h

/-- The replacement components still sum to the original lattice when the
intermediate sublattice is exactly the sum of the two old components. -/
theorem iSup_replacePairComponentsIn_eq_lattice (hij : i ≠ j)
    (C : QuadraticSublattice q)
    (P : OrthogonalDecomposition C.space C.lattice 2)
    (hC : C.ambientSubmodule =
      (D.component i).ambientSubmodule ⊔
        (D.component j).ambientSubmodule) :
    (⨆ k, (D.replacePairComponentsIn i j C P k).ambientSubmodule) =
      L.toSubmodule := by
  classical
  have hC_le : C.ambientSubmodule ≤ L.toSubmodule := by
    intro x hx
    rw [hC, Submodule.mem_sup] at hx
    rcases hx with ⟨xi, hxi, xj, hxj, rfl⟩
    exact L.toSubmodule.add_mem
      (D.component_ambientSubmodule_le i hxi)
      (D.component_ambientSubmodule_le j hxj)
  have hC_new : C.ambientSubmodule ≤
      ⨆ k, (D.replacePairComponentsIn i j C P k).ambientSubmodule := by
    rw [← P.iSup_liftNested_ambientSubmodule C]
    apply iSup_le
    intro a
    fin_cases a
    · have hi := le_iSup (fun k ↦
          (D.replacePairComponentsIn i j C P k).ambientSubmodule) i
      rwa [D.replacePairComponentsIn_left hij C P] at hi
    · have hj := le_iSup (fun k ↦
          (D.replacePairComponentsIn i j C P k).ambientSubmodule) j
      rwa [D.replacePairComponentsIn_right hij C P] at hj
  apply le_antisymm
  · apply iSup_le
    intro k
    by_cases hki : k = i
    · subst k
      rw [D.replacePairComponentsIn_left hij C P]
      exact le_trans
        (le_iSup (fun a ↦
          (C.liftNested (P.component a)).ambientSubmodule) 0)
        (by rw [P.iSup_liftNested_ambientSubmodule C]; exact hC_le)
    · by_cases hkj : k = j
      · subst k
        rw [D.replacePairComponentsIn_right hij C P]
        exact le_trans
          (le_iSup (fun a ↦
            (C.liftNested (P.component a)).ambientSubmodule) 1)
          (by rw [P.iSup_liftNested_ambientSubmodule C]; exact hC_le)
      · rw [D.replacePairComponentsIn_other hij C P k hki hkj]
        exact D.component_ambientSubmodule_le k
  · rw [← D.sum_eq]
    apply iSup_le
    intro k
    by_cases hki : k = i
    · subst k
      exact le_trans
        (_root_.le_sup_left : (D.component i).ambientSubmodule ≤
          (D.component i).ambientSubmodule ⊔
            (D.component j).ambientSubmodule)
        (by rw [← hC]; exact hC_new)
    · by_cases hkj : k = j
      · subst k
        exact le_trans
          (_root_.le_sup_right : (D.component j).ambientSubmodule ≤
            (D.component i).ambientSubmodule ⊔
              (D.component j).ambientSubmodule)
          (by rw [← hC]; exact hC_new)
      · have h := le_iSup
            (fun a ↦
              (D.replacePairComponentsIn i j C P a).ambientSubmodule) k
        rwa [D.replacePairComponentsIn_other hij C P k hki hkj] at h

/-- Replace two components through an explicit intermediate sublattice. -/
noncomputable def replacePairIn (hij : i ≠ j)
    (C : QuadraticSublattice q)
    (P : OrthogonalDecomposition C.space C.lattice 2)
    (hC : C.ambientSubmodule =
      (D.component i).ambientSubmodule ⊔
        (D.component j).ambientSubmodule)
    (horth : ∀ (k : Fin t), k ≠ i → k ≠ j →
      ∀ (x : C.carrier) (y : (D.component k).carrier),
        q.bilin (x : V) (y : V) = 0) :
    OrthogonalDecomposition q L t where
  component := D.replacePairComponentsIn i j C P
  orthogonal := by
    classical
    intro a b hab
    by_cases hai : a = i
    · subst a
      have hbi : b ≠ i := fun h ↦ hab h.symm
      by_cases hbj : b = j
      · subst b
        rw [D.replacePairComponentsIn_left hij C P,
          D.replacePairComponentsIn_right hij C P]
        intro x y
        exact liftNested_pair_orthogonal C P (by decide) x y
      · rw [D.replacePairComponentsIn_left hij C P,
          D.replacePairComponentsIn_other hij C P b hbi hbj]
        intro x y
        let xC : C.carrier :=
          ⟨x, C.nestedCarrier_le (P.component 0) x.property⟩
        exact horth b hbi hbj xC y
    · by_cases haj : a = j
      · subst a
        have hbj : b ≠ j := fun h ↦ hab h.symm
        by_cases hbi : b = i
        · subst b
          rw [D.replacePairComponentsIn_right hij C P,
            D.replacePairComponentsIn_left hij C P]
          intro x y
          exact liftNested_pair_orthogonal C P (by decide) x y
        · rw [D.replacePairComponentsIn_right hij C P,
            D.replacePairComponentsIn_other hij C P b hbi hbj]
          intro x y
          let xC : C.carrier :=
            ⟨x, C.nestedCarrier_le (P.component 1) x.property⟩
          exact horth b hbi hbj xC y
      · by_cases hbi : b = i
        · subst b
          rw [D.replacePairComponentsIn_other hij C P a hai haj,
            D.replacePairComponentsIn_left hij C P]
          intro x y
          let yC : C.carrier :=
            ⟨y, C.nestedCarrier_le (P.component 0) y.property⟩
          exact q.isSymm.eq (x : V) (y : V) |>.trans
            (horth a hai haj yC x)
        · by_cases hbj : b = j
          · subst b
            rw [D.replacePairComponentsIn_other hij C P a hai haj,
              D.replacePairComponentsIn_right hij C P]
            intro x y
            let yC : C.carrier :=
              ⟨y, C.nestedCarrier_le (P.component 1) y.property⟩
            exact q.isSymm.eq (x : V) (y : V) |>.trans
              (horth a hai haj yC x)
          · rw [D.replacePairComponentsIn_other hij C P a hai haj,
              D.replacePairComponentsIn_other hij C P b hbi hbj]
            intro x y
            exact D.orthogonal a b hab x y
  sum_eq := D.iSup_replacePairComponentsIn_eq_lattice hij C P hC

@[simp]
theorem replacePairIn_component_left (hij : i ≠ j)
    (C : QuadraticSublattice q)
    (P : OrthogonalDecomposition C.space C.lattice 2)
    (hC) (horth) :
    (D.replacePairIn hij C P hC horth).component i =
      C.liftNested (P.component 0) :=
  D.replacePairComponentsIn_left hij C P

@[simp]
theorem replacePairIn_component_right (hij : i ≠ j)
    (C : QuadraticSublattice q)
    (P : OrthogonalDecomposition C.space C.lattice 2)
    (hC) (horth) :
    (D.replacePairIn hij C P hC horth).component j =
      C.liftNested (P.component 1) :=
  D.replacePairComponentsIn_right hij C P

@[simp]
theorem replacePairIn_component_other (hij : i ≠ j)
    (C : QuadraticSublattice q)
    (P : OrthogonalDecomposition C.space C.lattice 2)
    (hC) (horth) (k : Fin t) (hki : k ≠ i) (hkj : k ≠ j) :
    (D.replacePairIn hij C P hC horth).component k = D.component k :=
  D.replacePairComponentsIn_other hij C P k hki hkj

/-- Canonical specialization: amalgamate the two old components, decompose
that lattice into a new pair, and put the pair back at the old positions. -/
noncomputable def replacePair (hij : i ≠ j)
    (P : OrthogonalDecomposition (D.orthogonalSup hij).space
      (D.orthogonalSup hij).lattice 2) :
    OrthogonalDecomposition q L t :=
  D.replacePairIn hij (D.orthogonalSup hij) P
    (D.orthogonalSup_ambientSubmodule hij)
    (fun k hki hkj x y ↦
      D.orthogonalSup_orthogonal_component hij
        (Ne.symm hki) (Ne.symm hkj) x y)

@[simp]
theorem replacePair_component_left (hij : i ≠ j)
    (P : OrthogonalDecomposition (D.orthogonalSup hij).space
      (D.orthogonalSup hij).lattice 2) :
    (D.replacePair hij P).component i =
      (D.orthogonalSup hij).liftNested (P.component 0) :=
  D.replacePairIn_component_left hij _ _ _ _

@[simp]
theorem replacePair_component_right (hij : i ≠ j)
    (P : OrthogonalDecomposition (D.orthogonalSup hij).space
      (D.orthogonalSup hij).lattice 2) :
    (D.replacePair hij P).component j =
      (D.orthogonalSup hij).liftNested (P.component 1) :=
  D.replacePairIn_component_right hij _ _ _ _

@[simp]
theorem replacePair_component_other (hij : i ≠ j)
    (P : OrthogonalDecomposition (D.orthogonalSup hij).space
      (D.orthogonalSup hij).lattice 2)
    (k : Fin t) (hki : k ≠ i) (hkj : k ≠ j) :
    (D.replacePair hij P).component k = D.component k :=
  D.replacePairIn_component_other hij _ _ _ _ k hki hkj

end OrthogonalDecomposition

end Lattice

end Bong
