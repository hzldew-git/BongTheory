/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.ModularSplitting
import Bong.Lattice.OrthogonalDecompositionPrefix

namespace Bong

open Dyadic Module

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L A : Lattice K V} {t : Nat}

namespace JordanDecomposition

/-- Pairing a displayed Jordan component with the full lattice lies in the
component scale, not merely in the smallest ambient scale. -/
theorem component_pairing
    (J : JordanDecomposition q L t) (i : Fin t)
    (y : (J.component i).carrier) (hy : y ∈ (J.component i).lattice)
    (x : V) (hx : x ∈ L) :
    q.bilin (y : V) x ∈
      principalIdeal (K := K) (J.scaleGenerator i : K) := by
  let D := J.toOrthogonalDecomposition
  have hxSum : x ∈ ⨆ j : Fin t, (D.component j).ambientSubmodule := by
    rw [D.sum_eq]
    exact hx
  rw [← J.scaleIdeal_eq i]
  refine Submodule.iSup_induction
    (p := fun j : Fin t => (D.component j).ambientSubmodule)
    (motive := fun z => q.bilin (y : V) z ∈
      scaleIdeal (J.component i).space (J.component i).lattice)
    hxSum ?_ ?_ ?_
  · intro j z hz
    rcases hz with ⟨z', hz', rfl⟩
    by_cases hji : j = i
    · subst j
      exact bilin_mem_scaleIdeal_of_mem (J.component i).space
        (J.component i).lattice hy hz'
    · have horth := D.orthogonal i j (Ne.symm hji) y z'
      change q.bilin (y : V) (z' : V) ∈
        scaleIdeal (J.component i).space (J.component i).lattice
      rw [horth]
      exact Submodule.zero_mem _
  · simp
  · intro x z hx hz
    rw [LinearMap.BilinForm.add_right]
    exact (scaleIdeal (J.component i).space
      (J.component i).lattice).add_mem hx hz

end JordanDecomposition

namespace OrthogonalDecomposition

variable [FiniteDimensional K V]
  (D : OrthogonalDecomposition q L t)

/-- The sum of the individual orthogonal projections onto the components
strictly before a numerical cut. -/
noncomputable def prefixComponentProjectionSum (k : Nat) (x : V) : V :=
  ∑ j : D.PrefixIndex k,
    ((D.component j.1).carrierProjection x : V)

theorem prefixComponentProjectionSum_mem_carrier
    (k : Nat) (x : V) :
    D.prefixComponentProjectionSum k x ∈ D.prefixCarrier k := by
  classical
  unfold prefixComponentProjectionSum prefixCarrier
  apply Submodule.sum_mem
  intro j _
  exact (le_iSup (fun h : D.PrefixIndex k ↦
    (D.component h.1).carrier) j)
      ((D.component j.1).carrierProjection x).property

theorem prefixComponentProjectionSum_mem_ambient
    (k : Nat) (x : V)
    (hprojection : ∀ j : D.PrefixIndex k,
      (D.component j.1).carrierProjection x ∈
        (D.component j.1).lattice) :
    D.prefixComponentProjectionSum k x ∈ D.prefixAmbientSubmodule k := by
  classical
  unfold prefixComponentProjectionSum prefixAmbientSubmodule
  apply Submodule.sum_mem
  intro j _
  apply le_iSup (fun h : D.PrefixIndex k ↦
    (D.component h.1).ambientSubmodule) j
  exact ⟨(D.component j.1).carrierProjection x, hprojection j, rfl⟩

/-- The projection to a finite orthogonal prefix is the sum of the
projections to its displayed components. -/
theorem prefixCarrierProjection_eq_componentSum
    (k : Nat) (x : V) :
    (D.prefixQuadraticSublattice k).carrierProjection x =
      ⟨D.prefixComponentProjectionSum k x,
        D.prefixComponentProjectionSum_mem_carrier k x⟩ := by
  classical
  let C := D.prefixQuadraticSublattice k
  let s := D.prefixComponentProjectionSum k x
  have hs : s ∈ C.carrier := D.prefixComponentProjectionSum_mem_carrier k x
  have horth : x - s ∈ C.orthogonalCarrier := by
    intro y hy
    change q.bilin y (x - s) = 0
    rw [LinearMap.BilinForm.sub_right]
    have hpairs : q.bilin y s = q.bilin y x := by
      change y ∈ D.prefixCarrier k at hy
      induction hy using Submodule.iSup_induction' with
      | mem l y hyl =>
          have hsum : q.bilin y s =
              q.bilin y
                ((D.component l.1).carrierProjection x : V) := by
            unfold s prefixComponentProjectionSum
            rw [map_sum, Finset.sum_eq_single l]
            · intro j _ hjl
              have hindex : l.1 ≠ j.1 := by
                intro h
                exact hjl (Subtype.ext h.symm)
              exact D.orthogonal l.1 j.1 hindex ⟨y, hyl⟩
                ((D.component j.1).carrierProjection x)
            · simp
          rw [hsum]
          let P := D.component l.1
          have hperp : q.bilin y
              (P.orthogonalProjection x : V) = 0 :=
            (P.orthogonalProjection x).property y hyl
          have hdecomp := P.carrierProjection_add_orthogonalProjection x
          calc
            q.bilin y (P.carrierProjection x : V) =
                q.bilin y ((P.carrierProjection x : V) +
                  (P.orthogonalProjection x : V)) := by
              rw [LinearMap.BilinForm.add_right, hperp, add_zero]
            _ = q.bilin y x := congrArg (q.bilin y) hdecomp
      | zero => simp
      | add y z _ _ hy hz =>
          rw [LinearMap.BilinForm.add_left,
            LinearMap.BilinForm.add_left, hy, hz]
    rw [hpairs, sub_self]
  have hxsplit : x = s + (x - s) := by abel
  apply Subtype.ext
  change ((C.carrierProjection x : C.carrier) : V) = s
  have hleft : C.carrierProjection s = ⟨s, hs⟩ := by
    exact Submodule.projectionOnto_apply_of_mem_left
      C.carrier_isCompl_orthogonalCarrier hs
  have hright : C.carrierProjection (x - s) = 0 := by
    exact Submodule.projectionOnto_apply_of_mem_right
      C.carrier_isCompl_orthogonalCarrier horth
  calc
    ((C.carrierProjection x : C.carrier) : V) =
        ((C.carrierProjection (s + (x - s)) : C.carrier) : V) := by
      exact congrArg (fun z : V =>
        ((C.carrierProjection z : C.carrier) : V)) hxsplit
    _ = ((C.carrierProjection s : C.carrier) : V) +
        ((C.carrierProjection (x - s) : C.carrier) : V) := by
      rw [map_add]
      rfl
    _ = s + 0 := by
      rw [hleft, hright]
      rfl
    _ = s := by simp

/-- If every component projection of an ambient integral vector is
integral, then its projection to the whole prefix is integral. -/
theorem prefixCarrierProjection_mem_lattice
    (k : Nat) (x : V)
    (hprojection : ∀ j : D.PrefixIndex k,
      (D.component j.1).carrierProjection x ∈
        (D.component j.1).lattice) :
    (D.prefixQuadraticSublattice k).carrierProjection x ∈
      (D.prefixQuadraticSublattice k).lattice := by
  let C := D.prefixQuadraticSublattice k
  have hsum := D.prefixComponentProjectionSum_mem_ambient k x hprojection
  change (show D.prefixCarrier k from
    (D.prefixQuadraticSublattice k).carrierProjection x) ∈
      D.prefixLattice k
  rw [D.mem_prefixLattice_iff k]
  have heq := congrArg Subtype.val
    (D.prefixCarrierProjection_eq_componentSum k x)
  change ((C.carrierProjection x : C.carrier) : V) ∈
    D.prefixAmbientSubmodule k
  rw [heq]
  exact hsum

end OrthogonalDecomposition

namespace QuadraticSublattice

variable [FiniteDimensional K V]

theorem orthogonalProjection_mem_lattice_of_integralProjection
    (C : QuadraticSublattice q)
    (hCA : C.ambientSubmodule ≤ A.toSubmodule)
    (hprojection : ∀ x : V, x ∈ A →
      C.carrierProjection x ∈ C.lattice)
    {x : V} (hx : x ∈ A) :
    (C.orthogonalProjection x : V) ∈ A := by
  have hp := hprojection x hx
  have hpA : (C.carrierProjection x : V) ∈ A :=
    hCA ⟨C.carrierProjection x, hp, rfl⟩
  have hdecomp := C.carrierProjection_add_orthogonalProjection x
  have heq : (C.orthogonalProjection x : V) =
      x - (C.carrierProjection x : V) := by
    rw [eq_sub_iff_add_eq, add_comm]
    exact hdecomp
  rw [heq]
  exact A.sub_mem hx hpA

theorem orthogonalCarrier_spans_comap_of_integralProjection
    (C : QuadraticSublattice q)
    (hCA : C.ambientSubmodule ≤ A.toSubmodule)
    (hprojection : ∀ x : V, x ∈ A →
      C.carrierProjection x ∈ C.lattice) :
    Submodule.span K
      ({z : C.orthogonalCarrier | (z : V) ∈ A} : Set C.orthogonalCarrier) =
      ⊤ := by
  apply top_unique
  intro z _
  have hzV : (z : V) ∈ Submodule.span K (A : Set V) := by
    rw [A.spans]
    exact Submodule.mem_top
  have hzProj : C.orthogonalProjection (z : V) ∈
      Submodule.span K (C.orthogonalProjection '' (A : Set V)) :=
    Submodule.apply_mem_span_image_of_mem_span C.orthogonalProjection hzV
  have himage : C.orthogonalProjection '' (A : Set V) ⊆
      {w : C.orthogonalCarrier | (w : V) ∈ A} := by
    rintro _ ⟨x, hx, rfl⟩
    exact C.orthogonalProjection_mem_lattice_of_integralProjection
      hCA hprojection hx
  have hzSpan := Submodule.span_mono himage hzProj
  simpa [orthogonalProjection] using hzSpan

noncomputable def orthogonalLatticeOfIntegralProjection
    (C : QuadraticSublattice q)
    (hCA : C.ambientSubmodule ≤ A.toSubmodule)
    (hprojection : ∀ x : V, x ∈ A →
      C.carrierProjection x ∈ C.lattice) :
    Lattice K C.orthogonalCarrier :=
  comapSubtype A C.orthogonalCarrier
    (C.orthogonalCarrier_spans_comap_of_integralProjection hCA hprojection)

noncomputable def orthogonalSublatticeOfIntegralProjection
    (C : QuadraticSublattice q)
    (hCA : C.ambientSubmodule ≤ A.toSubmodule)
    (hprojection : ∀ x : V, x ∈ A →
      C.carrierProjection x ∈ C.lattice) :
    QuadraticSublattice q where
  carrier := C.orthogonalCarrier
  nondegenerate := C.orthogonalCarrier_nondegenerate
  lattice := C.orthogonalLatticeOfIntegralProjection hCA hprojection

end QuadraticSublattice

/-- O'Meara 82:7 in projection form: any integral nondegenerate sublattice
whose orthogonal projection preserves the ambient lattice splits it. -/
noncomputable def orthogonalSplittingOfIntegralProjection
    [FiniteDimensional K V]
    (C : QuadraticSublattice q)
    (hCA : C.ambientSubmodule ≤ A.toSubmodule)
    (hprojection : ∀ x : V, x ∈ A →
      C.carrierProjection x ∈ C.lattice) :
    OrthogonalDecomposition q A 2 := by
  let R := C.orthogonalSublatticeOfIntegralProjection hCA hprojection
  exact {
    component := pairComponents C R
    orthogonal := by
      intro i j hij x y
      fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · exact y.property (x : V) x.property
      · exact q.isSymm.eq (x : V) (y : V) |>.trans
          (x.property (y : V) y.property)
      · exact (hij rfl).elim
    sum_eq := by
      apply le_antisymm
      · apply iSup_le
        intro i
        fin_cases i
        · exact hCA
        · rintro _ ⟨z, hz, rfl⟩
          exact hz
      · intro x hx
        rw [← C.carrierProjection_add_orthogonalProjection x]
        apply Submodule.add_mem
        · apply le_iSup (fun i : Fin 2 ↦
            (pairComponents C R i).ambientSubmodule) 0
          exact ⟨C.carrierProjection x, hprojection x hx, rfl⟩
        · apply le_iSup (fun i : Fin 2 ↦
            (pairComponents C R i).ambientSubmodule) 1
          exact ⟨C.orthogonalProjection x,
            C.orthogonalProjection_mem_lattice_of_integralProjection
              hCA hprojection hx, rfl⟩ }

namespace JordanDecomposition

/-- O'Meara 82:7 for a Jordan prefix: if each displayed component has the
required mixed pairing with a superlattice, the complete prefix splits that
superlattice simultaneously. -/
noncomputable def prefixSplittingOfComponentPairing
    [FiniteDimensional K V]
    (J : JordanDecomposition q L t) (k : Nat)
    (hLA : L ≤ A)
    (hpair : ∀ j : J.toOrthogonalDecomposition.PrefixIndex k,
      ∀ (y : (J.component j.1).carrier), y ∈ (J.component j.1).lattice →
      ∀ x : V, x ∈ A →
        q.bilin (y : V) x ∈
          principalIdeal (K := K) (J.scaleGenerator j.1 : K)) :
    OrthogonalDecomposition q A 2 := by
  let C := J.toOrthogonalDecomposition.prefixQuadraticSublattice k
  have hCA : C.ambientSubmodule ≤ A.toSubmodule := by
    rw [J.toOrthogonalDecomposition.prefixQuadraticSublattice_ambientSubmodule]
    unfold OrthogonalDecomposition.prefixAmbientSubmodule
    apply iSup_le
    intro j
    exact (J.toOrthogonalDecomposition.component_ambientSubmodule_le j.1).trans
      hLA
  have hprojection : ∀ x : V, x ∈ A →
      C.carrierProjection x ∈ C.lattice := by
    intro x hx
    apply J.toOrthogonalDecomposition.prefixCarrierProjection_mem_lattice
    intro j
    exact (J.component j.1).carrierProjection_mem_lattice_of_pairing
      (J.modular j.1) (hpair j) hx
  exact orthogonalSplittingOfIntegralProjection C hCA hprojection

end JordanDecomposition

end Lattice
end Bong
