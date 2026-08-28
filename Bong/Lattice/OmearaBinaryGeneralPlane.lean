/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.BasisIsometry
import Bong.Lattice.DeterminantBasis
import Bong.Lattice.MixedPairing
import Bong.Lattice.ModularScale
import Bong.Lattice.NormGeneratorValues
import Bong.Lattice.OmearaGeneralPlane
import Bong.Lattice.ScaleGenerator
import Bong.Bong.BinaryShearIsometry

/-!
# Binary modular lattices in O'Meara coordinates

If an integral binary basis `x, y` has mixed pairing equal to a chosen
modular-scale generator `a`, its normalized Gram matrix is exactly
`A(a⁻¹ Q(x), a⁻¹ Q(y))`.  This file records the corresponding
integral lattice isometry and proves that the two displayed coefficients are
integral in an `a`-modular lattice.

This is the presentation layer used in O'Meara 93:18 and 93:19.  The
separate basis-selection argument, which produces such an integral basis
from modularity, is not hidden in this coordinate calculation.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

/-- A scale-generator pairing may be chosen among the pairings of the
standard integral basis, with the two basis indices retained. -/
theorem exists_standardBasis_scaleGenerator_indices
    (q : QuadraticSpace K V) (L : Lattice K V)
    (hfin : 0 < finrank K V) :
    ∃ i j : Fin (finrank K V),
      scaleIdeal q L = principalIdeal (K := K)
        (q.bilin (L.standardAmbientBasis i) (L.standardAmbientBasis j)) ∧
      q.bilin (L.standardAmbientBasis i) (L.standardAmbientBasis j) ≠ 0 := by
  classical
  obtain ⟨m, hm, hmne⟩ :=
    exists_mem_scaleValueCandidates_ne_zero q L hfin
  let S := (scaleValueCandidates q L).filter fun z ↦ z ≠ 0
  have hS : S.Nonempty := ⟨m, by simp [S, hm, hmne]⟩
  obtain ⟨d, hdS, hminimal⟩ :=
    Finset.exists_min_image S (fun z ↦ ord K z) hS
  have hd : d ∈ scaleValueCandidates q L := (Finset.mem_filter.mp hdS).1
  have hdne : d ≠ 0 := (Finset.mem_filter.mp hdS).2
  simp only [scaleValueCandidates, Finset.mem_image] at hd
  obtain ⟨ij, -, rfl⟩ := hd
  refine ⟨ij.1, ij.2, ?_, hdne⟩
  rw [scaleIdeal_eq_span_scaleValueCandidates]
  apply le_antisymm
  · rw [Submodule.span_le]
    intro z hz
    change z ∈ scaleValueCandidates q L at hz
    by_cases hz0 : z = 0
    · subst z
      exact Submodule.zero_mem _
    · apply mem_principalIdeal_of_ord_le hdne
      exact hminimal z (by simp [S, hz, hz0])
  · rw [principalIdeal]
    apply Submodule.span_mono
    simp [scaleValueCandidates]

/-- The elementary integral shear fixing the first coordinate and replacing
the second basis vector by the sum of the two basis vectors. -/
noncomputable def finTwoSecondShearLinearEquiv :
    (Fin 2 → K) ≃ₗ[K] (Fin 2 → K) where
  toFun := fun x ↦ ![x 0 + x 1, x 1]
  invFun := fun x ↦ ![x 0 - x 1, x 1]
  left_inv := by
    intro x
    funext i
    fin_cases i <;> simp
  right_inv := by
    intro x
    funext i
    fin_cases i <;> simp
  map_add' := by
    intro x y
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' := by
    intro c x
    funext i
    fin_cases i <;> simp <;> ring

/-- Shear a binary basis by `b₁ ← b₀ + b₁`. -/
noncomputable def basisSecondShear (b : Basis (Fin 2) K V) :
    Basis (Fin 2) K V :=
  b.map (b.equivFun.trans
    ((finTwoSecondShearLinearEquiv (K := K)).trans b.equivFun.symm))

/-- Shear a binary basis by an arbitrary scalar,
`b₁ ← b₁ + t b₀`. -/
noncomputable def basisSecondShearBy (b : Basis (Fin 2) K V) (t : K) :
    Basis (Fin 2) K V :=
  b.map (b.equivFun.trans
    ((BONG.binaryShearLinearEquiv t).trans b.equivFun.symm))

@[simp]
theorem basisSecondShearBy_zero (b : Basis (Fin 2) K V) (t : K) :
    basisSecondShearBy b t 0 = b 0 := by
  simp [basisSecondShearBy, BONG.binaryShearLinearEquiv]

@[simp]
theorem basisSecondShearBy_one (b : Basis (Fin 2) K V) (t : K) :
    basisSecondShearBy b t 1 = b 1 + t • b 0 := by
  simp [basisSecondShearBy, BONG.binaryShearLinearEquiv, add_comm]

@[simp]
theorem basisSecondShear_zero (b : Basis (Fin 2) K V) :
    basisSecondShear b 0 = b 0 := by
  simp [basisSecondShear, finTwoSecondShearLinearEquiv]

@[simp]
theorem basisSecondShear_one (b : Basis (Fin 2) K V) :
    basisSecondShear b 1 = b 0 + b 1 := by
  simp [basisSecondShear, finTwoSecondShearLinearEquiv]

/-- The binary shear is unimodular over the valuation ring, hence leaves the
integral basis lattice unchanged. -/
theorem basisLattice_basisSecondShear (b : Basis (Fin 2) K V) :
    basisLattice (basisSecondShear b) = basisLattice b := by
  apply Lattice.ext
  change Submodule.span (IntegerRing K) (Set.range (basisSecondShear b)) =
    Submodule.span (IntegerRing K) (Set.range b)
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hi : i = 0 ∨ i = 1 := by
      have hval : i.val = 0 ∨ i.val = 1 := by omega
      rcases hval with hval | hval
      · exact Or.inl (Fin.ext hval)
      · exact Or.inr (Fin.ext hval)
    rcases hi with rfl | rfl
    · simp only [basisSecondShear_zero]
      exact Submodule.subset_span ⟨0, rfl⟩
    · simp only [basisSecondShear_one]
      exact (Submodule.span (IntegerRing K) (Set.range b)).add_mem
        (Submodule.subset_span ⟨0, rfl⟩)
        (Submodule.subset_span ⟨1, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hi : i = 0 ∨ i = 1 := by
      have hval : i.val = 0 ∨ i.val = 1 := by omega
      rcases hval with hval | hval
      · exact Or.inl (Fin.ext hval)
      · exact Or.inr (Fin.ext hval)
    rcases hi with rfl | rfl
    · rw [← basisSecondShear_zero b]
      exact Submodule.subset_span ⟨0, rfl⟩
    · have hsum : b 0 + b 1 ∈
          Submodule.span (IntegerRing K) (Set.range (basisSecondShear b)) := by
        rw [← basisSecondShear_one b]
        exact Submodule.subset_span ⟨1, rfl⟩
      have hzero : b 0 ∈
          Submodule.span (IntegerRing K) (Set.range (basisSecondShear b)) := by
        rw [← basisSecondShear_zero b]
        exact Submodule.subset_span ⟨0, rfl⟩
      have := (Submodule.span (IntegerRing K)
        (Set.range (basisSecondShear b))).sub_mem hsum hzero
      simpa using this

/-- An integral shear by an arbitrary valuation-ring scalar preserves the
binary basis lattice. -/
theorem basisLattice_basisSecondShearBy
    (b : Basis (Fin 2) K V) (t : IntegerRing K) :
    basisLattice (basisSecondShearBy b (t : K)) = basisLattice b := by
  apply Lattice.ext
  change Submodule.span (IntegerRing K)
      (Set.range (basisSecondShearBy b (t : K))) =
    Submodule.span (IntegerRing K) (Set.range b)
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hi : i = 0 ∨ i = 1 := by
      have hval : i.val = 0 ∨ i.val = 1 := by omega
      rcases hval with hval | hval
      · exact Or.inl (Fin.ext hval)
      · exact Or.inr (Fin.ext hval)
    rcases hi with rfl | rfl
    · simp only [basisSecondShearBy_zero]
      exact Submodule.subset_span ⟨0, rfl⟩
    · simp only [basisSecondShearBy_one]
      exact (Submodule.span (IntegerRing K) (Set.range b)).add_mem
        (Submodule.subset_span ⟨1, rfl⟩)
        ((Submodule.span (IntegerRing K) (Set.range b)).smul_mem t
          (Submodule.subset_span ⟨0, rfl⟩))
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hi : i = 0 ∨ i = 1 := by
      have hval : i.val = 0 ∨ i.val = 1 := by omega
      rcases hval with hval | hval
      · exact Or.inl (Fin.ext hval)
      · exact Or.inr (Fin.ext hval)
    rcases hi with rfl | rfl
    · rw [← basisSecondShearBy_zero b (t : K)]
      exact Submodule.subset_span ⟨0, rfl⟩
    · have hsum : b 1 + (t : K) • b 0 ∈
          Submodule.span (IntegerRing K)
            (Set.range (basisSecondShearBy b (t : K))) := by
        rw [← basisSecondShearBy_one b (t : K)]
        exact Submodule.subset_span ⟨1, rfl⟩
      have hzero : (t : K) • b 0 ∈
          Submodule.span (IntegerRing K)
            (Set.range (basisSecondShearBy b (t : K))) := by
        have hbzero : b 0 ∈ Submodule.span (IntegerRing K)
            (Set.range (basisSecondShearBy b (t : K))) := by
          rw [← basisSecondShearBy_zero b (t : K)]
          exact Submodule.subset_span ⟨0, rfl⟩
        exact (Submodule.span (IntegerRing K)
          (Set.range (basisSecondShearBy b (t : K)))).smul_mem t hbzero
      have := (Submodule.span (IntegerRing K)
        (Set.range (basisSecondShearBy b (t : K)))).sub_mem hsum hzero
      simpa using this

/-- A binary integral basis normalized so that its mixed pairing is exactly
the chosen modular-scale generator. -/
structure NormalizedBinaryBasisData
    (q : QuadraticSpace K V) (L : Lattice K V) (a : Kˣ) where
  basis : Basis (Fin 2) K V
  basis_lattice : basisLattice basis = L
  pairing_eq : q.bilin (basis 0) (basis 1) = (a : K)

namespace NormalizedBinaryBasisData

/-- Normalize a nonzero mixed scale generator by multiplying the second
basis vector by a valuation-ring unit. -/
noncomputable def ofScalePair
    (q : QuadraticSpace K V) (L : Lattice K V) (a : Kˣ)
    (b : Basis (Fin 2) K V) (hb : basisLattice b = L)
    (hpairne : q.bilin (b 0) (b 1) ≠ 0)
    (hideal : principalIdeal (K := K) (q.bilin (b 0) (b 1)) =
      principalIdeal (K := K) (a : K)) :
    NormalizedBinaryBasisData q L a := by
  let p : Kˣ := Units.mk0 (q.bilin (b 0) (b 1)) hpairne
  let hexists := exists_valuationUnit_mul_eq_of_principalIdeal_eq p a (by
    change principalIdeal (K := K) (q.bilin (b 0) (b 1)) =
      principalIdeal (K := K) (a : K)
    exact hideal)
  let u := Classical.choose hexists
  have hu : IsValuationUnit K (u : K) :=
    (Classical.choose_spec hexists).1
  have hup : u * p = a := (Classical.choose_spec hexists).2
  let weights : Fin 2 → Kˣ := fun i ↦ if i = 1 then u else 1
  let c := b.unitsSMul weights
  have hweights : ∀ i, IsValuationUnit K (weights i : K) := by
    intro i
    by_cases hi : i = 1
    · simp [weights, hi, hu]
    · simp [weights, hi, IsValuationUnit]
  have hcL : basisLattice c = L := by
    rw [show basisLattice c = basisLattice b from
      basisLattice_unitsSMul_eq b weights hweights, hb]
  have hpair : q.bilin (c 0) (c 1) = (a : K) := by
    have hupField := congrArg (fun z : Kˣ ↦ (z : K)) hup
    simp only [c, Basis.unitsSMul_apply]
    have hzero : weights 0 = 1 := by simp [weights]
    have hone : weights 1 = u := by simp [weights]
    rw [hzero, hone]
    simp only [Units.val_one, one_smul, Units.smul_def,
      LinearMap.BilinForm.smul_right]
    simpa only [p, Units.val_mul, Units.val_mk0] using hupField
  exact ⟨c, hcL, hpair⟩

end NormalizedBinaryBasisData

/-- If a diagonal Gram entry generates the scale but the mixed entry does
not, the integral shear makes their sum into a mixed scale generator. -/
theorem principalIdeal_pairing_after_secondShear_eq_scale
    (q : QuadraticSpace K V) (b : Basis (Fin 2) K V)
    (hdiag : scaleIdeal q (basisLattice b) =
      principalIdeal (K := K) (q.quadratic (b 0)))
    (hdiag_ne : q.quadratic (b 0) ≠ 0)
    (hcross : principalIdeal (K := K) (q.bilin (b 0) (b 1)) ≠
      scaleIdeal q (basisLattice b)) :
    principalIdeal (K := K)
        (q.bilin (basisSecondShear b 0) (basisSecondShear b 1)) =
      scaleIdeal q (basisLattice b) := by
  let d := q.quadratic (b 0)
  let p := q.bilin (b 0) (b 1)
  have hb0 : b 0 ∈ basisLattice b :=
    Submodule.subset_span ⟨0, rfl⟩
  have hb1 : b 1 ∈ basisLattice b :=
    Submodule.subset_span ⟨1, rfl⟩
  have hpScale : p ∈ scaleIdeal q (basisLattice b) :=
    bilin_mem_scaleIdeal_of_mem q (basisLattice b) hb0 hb1
  have hpDiag : p ∈ principalIdeal (K := K) d := by
    rw [← hdiag]
    exact hpScale
  have hle : ord K d ≤ ord K p :=
    ord_le_of_mem_principalIdeal hdiag_ne hpDiag
  have hstrict : ord K d < ord K p := by
    apply lt_of_le_of_ne hle
    intro heq
    apply hcross
    rw [hdiag]
    by_cases hp0 : p = 0
    · exfalso
      apply hdiag_ne
      apply (ord_eq_top_iff K).mp
      rw [heq, hp0, ord_zero]
    · let pu : Kˣ := Units.mk0 p hp0
      let du : Kˣ := Units.mk0 d hdiag_ne
      apply (principalIdeal_eq_iff_ordUnit_eq pu du).2
      apply WithTop.coe_injective
      rw [coe_ordUnit, coe_ordUnit]
      exact heq.symm
  have hord : ord K (d + p) = ord K d :=
    (ord K).map_add_eq_of_lt_left hstrict
  have hsum_ne : d + p ≠ 0 := by
    intro hzero
    rw [hzero, ord_zero] at hord
    exact (ord_eq_top_iff K).not.mpr hdiag_ne hord.symm
  have hsumIdeal : principalIdeal (K := K) (d + p) =
      principalIdeal (K := K) d := by
    let su : Kˣ := Units.mk0 (d + p) hsum_ne
    let du : Kˣ := Units.mk0 d hdiag_ne
    apply (principalIdeal_eq_iff_ordUnit_eq su du).2
    apply WithTop.coe_injective
    rw [coe_ordUnit, coe_ordUnit]
    exact hord
  rw [basisSecondShear_zero, basisSecondShear_one,
    LinearMap.BilinForm.add_right]
  change principalIdeal (K := K) (d + p) = _
  exact hsumIdeal.trans hdiag.symm

namespace NormalizedBinaryBasisData

/-- Construct a normalized binary basis when the first diagonal entry is a
scale generator.  If the original mixed entry is not a generator, use the
preceding integral shear. -/
noncomputable def ofFirstDiagonalScale
    (q : QuadraticSpace K V) (L : Lattice K V) (a : Kˣ)
    (b : Basis (Fin 2) K V) (hb : basisLattice b = L)
    (hscale : scaleIdeal q L = principalIdeal (K := K) (a : K))
    (hdiag : scaleIdeal q L =
      principalIdeal (K := K) (q.quadratic (b 0)))
    (hdiag_ne : q.quadratic (b 0) ≠ 0) :
    NormalizedBinaryBasisData q L a := by
  let p := q.bilin (b 0) (b 1)
  by_cases hcross : principalIdeal (K := K) p = scaleIdeal q L
  · have hpne : p ≠ 0 := by
      intro hp0
      have haMem := generator_mem_principalIdeal (K := K) (a : K)
      rw [← hscale, ← hcross, hp0, principalIdeal] at haMem
      exact Units.ne_zero a (by simpa using haMem)
    exact ofScalePair q L a b hb hpne (hcross.trans hscale)
  · let c := basisSecondShear b
    have hcL : basisLattice c = L := by
      rw [basisLattice_basisSecondShear, hb]
    have hdiag' : scaleIdeal q (basisLattice b) =
        principalIdeal (K := K) (q.quadratic (b 0)) := by
      simpa only [hb] using hdiag
    have hcross' : principalIdeal (K := K) p ≠
        scaleIdeal q (basisLattice b) := by
      simpa only [hb] using hcross
    have hpairIdeal : principalIdeal (K := K) (q.bilin (c 0) (c 1)) =
        principalIdeal (K := K) (a : K) := by
      exact (principalIdeal_pairing_after_secondShear_eq_scale
        q b hdiag' hdiag_ne hcross').trans (by simpa only [hb] using hscale)
    have hpairne : q.bilin (c 0) (c 1) ≠ 0 := by
      intro hzero
      have haMem := generator_mem_principalIdeal (K := K) (a : K)
      rw [← hpairIdeal, hzero, principalIdeal] at haMem
      exact Units.ne_zero a (by simpa using haMem)
    exact ofScalePair q L a c hcL hpairne hpairIdeal

/-- Every binary `a`-modular lattice admits an integral basis whose mixed
pairing is the chosen generator `a`.  A standard-basis scale generator is
either mixed, or diagonal; the latter case is converted to a mixed generator
by the integral shear above. -/
noncomputable def ofModular
    (q : QuadraticSpace K V) (L : Lattice K V) (a : Kˣ)
    (hmodular : IsModular q L a) (hrank : finrank K V = 2) :
    NormalizedBinaryBasisData q L a := by
  let e : Fin (finrank K V) ≃ Fin 2 := finCongr hrank
  let b : Basis (Fin 2) K V := L.standardAmbientBasis.reindex e
  have hb : basisLattice b = L := by
    exact (basisLattice_reindex L.standardAmbientBasis e).trans
      (basisLattice_standardAmbientBasis L)
  have hscale : scaleIdeal q L = principalIdeal (K := K) (a : K) :=
    hmodular.scaleIdeal_eq_principal (by omega)
  let hexists := exists_standardBasis_scaleGenerator_indices q L (by omega)
  let i := Classical.choose hexists
  let hjExists := Classical.choose_spec hexists
  let j := Classical.choose hjExists
  have hgenerator : scaleIdeal q L = principalIdeal (K := K)
      (q.bilin (L.standardAmbientBasis i) (L.standardAmbientBasis j)) :=
    (Classical.choose_spec hjExists).1
  have hgenerator_ne :
      q.bilin (L.standardAmbientBasis i) (L.standardAmbientBasis j) ≠ 0 :=
    (Classical.choose_spec hjExists).2
  let i' : Fin 2 := e i
  let j' : Fin 2 := e j
  have hgenerator' : scaleIdeal q L = principalIdeal (K := K)
      (q.bilin (b i') (b j')) := by
    simpa only [b, i', j', Basis.coe_reindex, Function.comp_apply,
      Equiv.symm_apply_apply] using hgenerator
  have hgenerator_ne' : q.bilin (b i') (b j') ≠ 0 := by
    simpa only [b, i', j', Basis.coe_reindex, Function.comp_apply,
      Equiv.symm_apply_apply] using hgenerator_ne
  by_cases hi : i' = 0
  · by_cases hj : j' = 0
    · have hgen00 := hgenerator'
      have hne00 := hgenerator_ne'
      rw [hi, hj] at hgen00 hne00
      exact ofFirstDiagonalScale q L a b hb hscale (by
        simpa only [QuadraticSpace.quadratic] using hgen00) (by
        simpa only [QuadraticSpace.quadratic] using hne00)
    · have hjOne : j' = 1 := by
        apply Fin.ext
        omega
      have hgen01 := hgenerator'
      have hne01 := hgenerator_ne'
      rw [hi, hjOne] at hgen01 hne01
      exact ofScalePair q L a b hb hne01
        (hgen01.symm.trans hscale)
  · have hiOne : i' = 1 := by
      apply Fin.ext
      omega
    by_cases hj : j' = 0
    · have hgen10 := hgenerator'
      have hne10 := hgenerator_ne'
      rw [hiOne, hj] at hgen10 hne10
      have hcrossGenerator : scaleIdeal q L = principalIdeal (K := K)
          (q.bilin (b 0) (b 1)) := by
        simpa only [q.isSymm.eq (b 1) (b 0)] using hgen10
      have hcrossNe : q.bilin (b 0) (b 1) ≠ 0 := by
        simpa only [q.isSymm.eq (b 1) (b 0)] using hne10
      exact ofScalePair q L a b hb hcrossNe
        (hcrossGenerator.symm.trans hscale)
    · have hjOne : j' = 1 := by
        apply Fin.ext
        omega
      have hgen11 := hgenerator'
      have hne11 := hgenerator_ne'
      rw [hiOne, hjOne] at hgen11 hne11
      let swap : Fin 2 ≃ Fin 2 := Equiv.swap 0 1
      let c : Basis (Fin 2) K V := b.reindex swap
      have hc0 : c 0 = b 1 := by
        simp only [c, Basis.coe_reindex, Function.comp_apply]
        rw [show swap.symm 0 = 1 by simp [swap]]
      have hcL : basisLattice c = L :=
        (basisLattice_reindex b swap).trans hb
      have hdiagC : scaleIdeal q L =
          principalIdeal (K := K) (q.quadratic (c 0)) := by
        rw [hc0]
        simpa only [QuadraticSpace.quadratic] using hgen11
      have hdiagCNe : q.quadratic (c 0) ≠ 0 := by
        rw [hc0]
        simpa only [QuadraticSpace.quadratic] using hne11
      exact ofFirstDiagonalScale q L a c hcL hscale hdiagC hdiagCNe

end NormalizedBinaryBasisData

/-- The two normalized diagonal coefficients attached to a binary basis
whose mixed pairing is the chosen scale generator. -/
noncomputable def omearaLeftCoefficient
    (q : QuadraticSpace K V) (a : Kˣ) (b : Basis (Fin 2) K V) : K :=
  ((a⁻¹ : Kˣ) : K) * q.quadratic (b 0)

noncomputable def omearaRightCoefficient
    (q : QuadraticSpace K V) (a : Kˣ) (b : Basis (Fin 2) K V) : K :=
  ((a⁻¹ : Kˣ) : K) * q.quadratic (b 1)

/-- Nondegeneracy of the ambient binary form gives nondegeneracy of its
normalized O'Meara matrix. -/
theorem omearaCoefficients_mul_ne_one
    (q : QuadraticSpace K V) (a : Kˣ) (b : Basis (Fin 2) K V)
    (hpair : q.bilin (b 0) (b 1) = (a : K)) :
    omearaLeftCoefficient q a b * omearaRightCoefficient q a b ≠ 1 := by
  intro hone
  have hdet :=
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp q.nondegenerate
  have ha : (a : K) ≠ 0 := Units.ne_zero a
  unfold omearaLeftCoefficient omearaRightCoefficient at hone
  rw [Units.val_inv_eq_inv_val] at hone
  have hprod : q.quadratic (b 0) * q.quadratic (b 1) = (a : K) ^ 2 := by
    calc
      q.quadratic (b 0) * q.quadratic (b 1) =
          (a : K) ^ 2 *
            (((a : K)⁻¹ * q.quadratic (b 0)) *
              ((a : K)⁻¹ * q.quadratic (b 1))) := by
                field_simp [ha]
                <;> ring
      _ = (a : K) ^ 2 := by rw [hone, mul_one]
  apply hdet
  change (LinearMap.BilinForm.toMatrix b q.bilin).det = 0
  rw [Matrix.det_fin_two]
  simp only [LinearMap.BilinForm.toMatrix_apply]
  change q.quadratic (b 0) * q.quadratic (b 1) -
    q.bilin (b 0) (b 1) * q.bilin (b 1) (b 0) = 0
  rw [q.isSymm.eq (b 1) (b 0), hpair, hprod]
  ring

/-- An integral binary basis with mixed pairing `a` identifies its lattice
with the scaled general plane `a A(alpha,beta)`. -/
noncomputable def binaryGeneralPlaneIsometryOfPairingEq
    (q : QuadraticSpace K V) (a : Kˣ) (b : Basis (Fin 2) K V)
    (hpair : q.bilin (b 0) (b 1) = (a : K)) :
    Isometry q
      ((QuadraticSpace.omearaGeneralPlane
        (omearaLeftCoefficient q a b) (omearaRightCoefficient q a b)
        (omearaCoefficients_mul_ne_one q a b hpair)).rescaleUnit a)
      (basisLattice b) (hyperbolicPlaneLattice (K := K)) := by
  let c : Basis (Fin 2) K (Fin 2 → K) := Pi.basisFun K (Fin 2)
  let model := (QuadraticSpace.omearaGeneralPlane
    (omearaLeftCoefficient q a b) (omearaRightCoefficient q a b)
    (omearaCoefficients_mul_ne_one q a b hpair)).rescaleUnit a
  have hgram : ∀ i j, model.bilin (c i) (c j) = q.bilin (b i) (b j) := by
    intro i j
    fin_cases i <;> fin_cases j
    all_goals
      simp [model, c, QuadraticSpace.rescaleUnit_bilin_apply,
        QuadraticSpace.omearaGeneralPlane_bilin_apply]
    · unfold omearaLeftCoefficient
      rw [Units.val_inv_eq_inv_val]
      change (a : K) * ((a : K)⁻¹ * q.quadratic (b 0)) =
        q.bilin (b 0) (b 0)
      rw [← QuadraticSpace.quadratic]
      field_simp [Units.ne_zero a]
    · exact hpair.symm
    · rw [q.isSymm.eq (b 1) (b 0)]
      exact hpair.symm
    · unfold omearaRightCoefficient
      rw [Units.val_inv_eq_inv_val]
      change (a : K) * ((a : K)⁻¹ * q.quadratic (b 1)) =
        q.bilin (b 1) (b 1)
      rw [← QuadraticSpace.quadratic]
      field_simp [Units.ne_zero a]
  exact Classical.choice
    (basisLattice_isIsometric_of_gram_eq q model b c hgram)

/-- Concrete O'Meara coordinates for a binary modular lattice once a
scale-normalized integral basis has been selected. -/
structure BinaryModularGeneralPlaneData
    (q : QuadraticSpace K V) (L : Lattice K V) (a : Kˣ) where
  basis : Basis (Fin 2) K V
  basis_lattice : basisLattice basis = L
  pairing_eq : q.bilin (basis 0) (basis 1) = (a : K)
  leftCoefficient : K
  rightCoefficient : K
  leftCoefficient_eq : leftCoefficient = omearaLeftCoefficient q a basis
  rightCoefficient_eq : rightCoefficient = omearaRightCoefficient q a basis
  left_integral : leftCoefficient ∈ IntegerRing K
  right_integral : rightCoefficient ∈ IntegerRing K
  nondegenerate : leftCoefficient * rightCoefficient ≠ 1
  isometry : Isometry q
    ((QuadraticSpace.omearaGeneralPlane leftCoefficient rightCoefficient
      nondegenerate).rescaleUnit a)
    L (hyperbolicPlaneLattice (K := K))

namespace BinaryModularGeneralPlaneData

/-- Package the coordinate calculation for a supplied normalized integral
basis of an `a`-modular lattice. -/
noncomputable def ofBasis
    (q : QuadraticSpace K V) (L : Lattice K V) (a : Kˣ)
    (hmodular : IsModular q L a) (b : Basis (Fin 2) K V)
    (hb : basisLattice b = L)
    (hpair : q.bilin (b 0) (b 1) = (a : K)) :
    BinaryModularGeneralPlaneData q L a := by
  let alpha := omearaLeftCoefficient q a b
  let beta := omearaRightCoefficient q a b
  have hbmem (i : Fin 2) : b i ∈ basisLattice b := by
    exact Submodule.subset_span ⟨i, rfl⟩
  have hq0 : q.quadratic (b 0) ∈ principalIdeal (K := K) (a : K) := by
    apply hmodular.scaleIdeal_le_principal
    rw [← hb]
    exact bilin_mem_scaleIdeal_of_mem q (basisLattice b)
      (hbmem 0) (hbmem 0)
  have hq1 : q.quadratic (b 1) ∈ principalIdeal (K := K) (a : K) := by
    apply hmodular.scaleIdeal_le_principal
    rw [← hb]
    exact bilin_mem_scaleIdeal_of_mem q (basisLattice b)
      (hbmem 1) (hbmem 1)
  have halpha : alpha ∈ IntegerRing K := by
    apply mem_integerRing_of_mul_mem_principalIdeal (Units.ne_zero a)
    have hmul : (a : K) * alpha = q.quadratic (b 0) := by
      dsimp only [alpha, omearaLeftCoefficient]
      rw [Units.val_inv_eq_inv_val]
      field_simp [Units.ne_zero a]
    rw [hmul]
    exact hq0
  have hbeta : beta ∈ IntegerRing K := by
    apply mem_integerRing_of_mul_mem_principalIdeal (Units.ne_zero a)
    have hmul : (a : K) * beta = q.quadratic (b 1) := by
      dsimp only [beta, omearaRightCoefficient]
      rw [Units.val_inv_eq_inv_val]
      field_simp [Units.ne_zero a]
    rw [hmul]
    exact hq1
  have hnondeg : alpha * beta ≠ 1 :=
    omearaCoefficients_mul_ne_one q a b hpair
  let raw := binaryGeneralPlaneIsometryOfPairingEq q a b hpair
  let transported : Isometry q
      ((QuadraticSpace.omearaGeneralPlane alpha beta hnondeg).rescaleUnit a)
      L (hyperbolicPlaneLattice (K := K)) := by
    rw [← hb]
    simpa only [alpha, beta] using raw
  exact
    { basis := b
      basis_lattice := hb
      pairing_eq := hpair
      leftCoefficient := alpha
      rightCoefficient := beta
      leftCoefficient_eq := rfl
      rightCoefficient_eq := rfl
      left_integral := halpha
      right_integral := hbeta
      nondegenerate := hnondeg
      isometry := transported }

/-- O'Meara general-plane presentation of every binary modular lattice,
with no basis-selection hypothesis left in the public constructor. -/
noncomputable def ofModular
    (q : QuadraticSpace K V) (L : Lattice K V) (a : Kˣ)
    (hmodular : IsModular q L a) (hrank : finrank K V = 2) :
    BinaryModularGeneralPlaneData q L a := by
  let B := NormalizedBinaryBasisData.ofModular q L a hmodular hrank
  exact ofBasis q L a hmodular B.basis B.basis_lattice B.pairing_eq

end BinaryModularGeneralPlaneData

end Lattice

end Bong
