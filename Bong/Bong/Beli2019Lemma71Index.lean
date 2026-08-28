/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma71
import Bong.Bong.Beli2019PrimeIndexChain
import Bong.Lattice.AdaptedBasis
import Bong.Lattice.VolumeInclusion
import Mathlib.LinearAlgebra.Transvection.Basic

/-!
# The index calculation in Beli (2019), Lemma 7.1

An index-generator certificate is converted into the literal
`Beli2019IndexPInclusion` used by Section 5.  A basis beginning with the norm
generator is sheared so that every other basis vector lies in the smaller
lattice.  Scaling the head by the uniformizer gives an index-`p` sublattice
inside it.  The even volume-jump formula for nested lattices then forces the
intermediate lattice itself to have volume jump two.
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {N M : Lattice K V}

namespace Lattice.IndexPGeneratorCertificate

variable {x : V} (C : IndexPGeneratorCertificate N M x)

/-- A selected coefficient reducing one integral basis vector modulo `N`. -/
noncomputable def rawCorrection
    (b : Basis (Fin (finrank K V)) (IntegerRing K) M.toSubmodule)
    (j : Fin (finrank K V)) : IntegerRing K :=
  Classical.choose (C.reduce ((b j : M.toSubmodule) : V) (b j).property)

theorem rawCorrection_spec
    (b : Basis (Fin (finrank K V)) (IntegerRing K) M.toSubmodule)
    (j : Fin (finrank K V)) :
    ((b j : M.toSubmodule) : V) - C.rawCorrection b j • x ∈ N :=
  Classical.choose_spec
    (C.reduce ((b j : M.toSubmodule) : V) (b j).property)

/-- The head correction is reset to zero. -/
noncomputable def correction
    (b : Basis (Fin (finrank K V)) (IntegerRing K) M.toSubmodule)
    (i j : Fin (finrank K V)) : IntegerRing K :=
  Function.update (C.rawCorrection b) i 0 j

@[simp]
theorem correction_self
    (b : Basis (Fin (finrank K V)) (IntegerRing K) M.toSubmodule)
    (i : Fin (finrank K V)) : C.correction b i i = 0 := by
  simp [correction]

theorem correction_of_ne
    (b : Basis (Fin (finrank K V)) (IntegerRing K) M.toSubmodule)
    {i j : Fin (finrank K V)} (hji : j ≠ i) :
    C.correction b i j = C.rawCorrection b j := by
  simp [correction, hji]

/-- The linear functional whose transvection performs all reductions at
once. -/
noncomputable def correctionFunctional
    (b : Basis (Fin (finrank K V)) (IntegerRing K) M.toSubmodule)
    (i : Fin (finrank K V)) : Module.Dual (IntegerRing K) M.toSubmodule :=
  b.constr (IntegerRing K) (fun j ↦ -(C.correction b i j))

@[simp]
theorem correctionFunctional_head
    (b : Basis (Fin (finrank K V)) (IntegerRing K) M.toSubmodule)
    (i : Fin (finrank K V)) :
    C.correctionFunctional b i (b i) = 0 := by
  simp [correctionFunctional]

/-- Shear the integral basis while fixing its chosen head. -/
noncomputable def adjustedIntegralBasis
    (b : Basis (Fin (finrank K V)) (IntegerRing K) M.toSubmodule)
    (i : Fin (finrank K V)) :
    Basis (Fin (finrank K V)) (IntegerRing K) M.toSubmodule :=
  b.map (LinearEquiv.transvection (C.correctionFunctional_head b i))

theorem adjustedIntegralBasis_apply
    (b : Basis (Fin (finrank K V)) (IntegerRing K) M.toSubmodule)
    (i j : Fin (finrank K V)) :
    C.adjustedIntegralBasis b i j =
      b j - C.correction b i j • b i := by
  rw [adjustedIntegralBasis, Basis.map_apply,
    LinearEquiv.transvection.apply, correctionFunctional,
    b.constr_basis]
  module

@[simp]
theorem adjustedIntegralBasis_head
    (b : Basis (Fin (finrank K V)) (IntegerRing K) M.toSubmodule)
    (i : Fin (finrank K V)) :
    C.adjustedIntegralBasis b i i = b i := by
  rw [C.adjustedIntegralBasis_apply, C.correction_self]
  simp

theorem adjustedIntegralBasis_mem_of_ne
    (b : Basis (Fin (finrank K V)) (IntegerRing K) M.toSubmodule)
    (i : Fin (finrank K V))
    (hbi : ((b i : M.toSubmodule) : V) = x)
    {j : Fin (finrank K V)} (hji : j ≠ i) :
    ((C.adjustedIntegralBasis b i j : M.toSubmodule) : V) ∈ N := by
  have hadjusted := congrArg (fun z : M.toSubmodule ↦ (z : V))
    (C.adjustedIntegralBasis_apply b i j)
  rw [hadjusted]
  change (((b j : M.toSubmodule) : V) -
    (C.correction b i j : K) • ((b i : M.toSubmodule) : V)) ∈ N
  rw [C.correction_of_ne b hji, hbi]
  exact C.rawCorrection_spec b j

/-- The field basis obtained from the adjusted integral basis. -/
noncomputable def adjustedAmbientBasis
    (b : Basis (Fin (finrank K V)) (IntegerRing K) M.toSubmodule)
    (i : Fin (finrank K V)) : Basis (Fin (finrank K V)) K V :=
  (C.adjustedIntegralBasis b i).extendOfIsLattice K

/-- Scale only the adjusted head coordinate. -/
noncomputable def coordinateSubLattice
    (b : Basis (Fin (finrank K V)) (IntegerRing K) M.toSubmodule)
    (i : Fin (finrank K V)) : Lattice K V :=
  basisLattice (coordinateScaleBasis (C.adjustedAmbientBasis b i) i)

/-- The coordinate-scaled comparison lattice is contained in `N`. -/
theorem coordinateSubLattice_le
    (b : Basis (Fin (finrank K V)) (IntegerRing K) M.toSubmodule)
    (i : Fin (finrank K V))
    (hbi : ((b i : M.toSubmodule) : V) = x) :
    C.coordinateSubLattice b i ≤ N := by
  classical
  rw [coordinateSubLattice]
  change Submodule.span (IntegerRing K)
      (Set.range (coordinateScaleBasis (C.adjustedAmbientBasis b i) i)) ≤
    N.toSubmodule
  rw [Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  by_cases hji : j = i
  · subst j
    rw [coordinateScaleBasis_apply_same, adjustedAmbientBasis,
      Basis.extendOfIsLattice_apply, C.adjustedIntegralBasis_head, hbi]
    exact C.uniformizer_smul_mem
  · rw [coordinateScaleBasis_apply_of_ne _ hji, adjustedAmbientBasis,
      Basis.extendOfIsLattice_apply]
    exact C.adjustedIntegralBasis_mem_of_ne b i hbi hji

/-- The coordinate-scaled comparison lattice has index `p` in `M`. -/
theorem coordinateSubLattice_indexPInclusion
    (b : Basis (Fin (finrank K V)) (IntegerRing K) M.toSubmodule)
    (i : Fin (finrank K V)) :
    Beli2019IndexPInclusion q M (C.coordinateSubLattice b i) := by
  have h := indexPInclusion_coordinateScaleBasis q
    (C.adjustedAmbientBasis b i) i
  have hbasis : basisLattice (C.adjustedAmbientBasis b i) = M := by
    exact basisLattice_extendOfIntegralBasis M (C.adjustedIntegralBasis b i)
  rwa [hbasis] at h

end Lattice.IndexPGeneratorCertificate

namespace Lattice

/-- An index equivalence for the integral basis adapted to a norm
generator. -/
noncomputable def lemma71AdaptedIndexEquivFin
    (q : QuadraticSpace K V) (M : Lattice K V) (x : V)
    (generator : IsNormGenerator q M x) (anisotropic : q.IsAnisotropic x) :
    (Unit ⊕ Fin (finrank K (q.vectorOrthogonal x))) ≃
      Fin (finrank K V) := by
  apply Fintype.equivOfCardEq
  simpa using (Module.finrank_eq_card_basis
    ((adaptedIntegralBasis q M x generator anisotropic).extendOfIsLattice K)).symm

/-- A standard finite integral basis beginning with the chosen norm
generator. -/
noncomputable def lemma71AdaptedIntegralBasis
    (q : QuadraticSpace K V) (M : Lattice K V) (x : V)
    (generator : IsNormGenerator q M x) (anisotropic : q.IsAnisotropic x) :
    Basis (Fin (finrank K V)) (IntegerRing K) M.toSubmodule :=
  (adaptedIntegralBasis q M x generator anisotropic).reindex
    (lemma71AdaptedIndexEquivFin q M x generator anisotropic)

/-- The index occupied by the prescribed norm generator. -/
noncomputable def lemma71HeadIndex
    (q : QuadraticSpace K V) (M : Lattice K V) (x : V)
    (generator : IsNormGenerator q M x) (anisotropic : q.IsAnisotropic x) :
    Fin (finrank K V) :=
  lemma71AdaptedIndexEquivFin q M x generator anisotropic (Sum.inl ())

theorem coe_lemma71AdaptedIntegralBasis_head
    (q : QuadraticSpace K V) (M : Lattice K V) (x : V)
    (generator : IsNormGenerator q M x) (anisotropic : q.IsAnisotropic x) :
    (((lemma71AdaptedIntegralBasis q M x generator anisotropic)
      (lemma71HeadIndex q M x generator anisotropic) : M.toSubmodule) : V) = x := by
  simp [lemma71AdaptedIntegralBasis, lemma71HeadIndex,
    lemma71AdaptedIndexEquivFin, adaptedIntegralBasis_inl]

/-- A generator certificate whose residue direction is a norm generator
has the volume jump required by `Beli2019IndexPInclusion`. -/
theorem IndexPGeneratorCertificate.toBeli2019IndexPInclusion
    {x : V} (C : IndexPGeneratorCertificate N M x)
    (generator : IsNormGenerator q M x) (anisotropic : q.IsAnisotropic x) :
    Beli2019IndexPInclusion q M N := by
  let b := lemma71AdaptedIntegralBasis q M x generator anisotropic
  let i := lemma71HeadIndex q M x generator anisotropic
  have hbi : ((b i : M.toSubmodule) : V) = x :=
    coe_lemma71AdaptedIntegralBasis_head q M x generator anisotropic
  let P := C.coordinateSubLattice b i
  have hPM : Beli2019IndexPInclusion q M P :=
    C.coordinateSubLattice_indexPInclusion b i
  have hPN : P ≤ N := C.coordinateSubLattice_le b i hbi
  rcases exists_volumeOrder_eq_add_two_mul_nat q C.lattice_le with
    ⟨k, hk⟩
  rcases exists_volumeOrder_eq_add_two_mul_nat q hPN with ⟨j, hj⟩
  have hNneM : N ≠ M := by
    intro hNM
    apply C.generator_not_mem
    rw [hNM]
    exact C.generator_mem
  have hkNe : k ≠ 0 := by
    intro hkZero
    have hvolume : volumeOrder q N = volumeOrder q M := by
      rw [hk, hkZero]
      simp
    exact hNneM (eq_of_le_of_volumeOrder_eq q N M C.lattice_le hvolume)
  refine ⟨C.lattice_le, ?_⟩
  have hPVolume := hPM.volumeOrder_eq
  dsimp [P] at hPVolume hj
  omega

end Lattice

namespace BONG.GoodBONG

variable [BeliCorollary44Laws.{u, v} K]

/-- The lattice produced by Lemma 7.1 is literally an index-`p`
sublattice of the original lattice. -/
theorem Beli2019Lemma71Data.indexPInclusion
    {n : Nat} {b : GoodBONG q M (n + 2)}
    (D : Beli2019Lemma71Data b) :
    Beli2019IndexPInclusion q M D.lattice :=
  D.indexP.toBeli2019IndexPInclusion
    b.toBONG.head_isNormGenerator b.toBONG.head_isAnisotropic

end BONG.GoodBONG

end Bong
