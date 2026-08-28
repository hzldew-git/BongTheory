/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaHyperbolicTransvection
import Bong.Lattice.OrthogonalProductIsometry
import Bong.Lattice.Reflection
import Bong.QuadraticSpace.Rescale

/-!
# O'Meara 93:14: hyperbolic cancellation

This file proves the common-isotropic-vector step in O'Meara's dyadic
hyperbolic cancellation theorem.  It is step 2 of the proof of Theorem
93:14: when two unimodular hyperbolic summands have the same first
isotropic basis vector, projection to the other factor is already an exact
integral isometry of their complements.

The remaining steps of 93:14 reduce arbitrary pairs of hyperbolic summands
to this situation.
-/

namespace Bong

open Dyadic

namespace Lattice

universe u v w x y

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

/-- The first isotropic vector in the standard unimodular hyperbolic
plane. -/
def omearaHyperbolicFirst : Fin 2 → K :=
  ![1, 0]

/-- The second isotropic vector in the standard unimodular hyperbolic
plane. -/
def omearaHyperbolicSecond : Fin 2 → K :=
  ![0, 1]

@[simp]
theorem omearaHyperbolicFirst_zero :
    (omearaHyperbolicFirst (K := K)) 0 = 1 :=
  rfl

@[simp]
theorem omearaHyperbolicFirst_one :
    (omearaHyperbolicFirst (K := K)) 1 = 0 :=
  rfl

@[simp]
theorem omearaHyperbolicSecond_zero :
    (omearaHyperbolicSecond (K := K)) 0 = 0 :=
  rfl

@[simp]
theorem omearaHyperbolicSecond_one :
    (omearaHyperbolicSecond (K := K)) 1 = 1 :=
  rfl

/-- Projection of an ambient hyperbolic-sum isometry to the second
factor. -/
noncomputable def hyperbolicComplementLinearMap
    (f : Isometry
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum q)
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r)
      (product (hyperbolicPlaneLattice (K := K)) L)
      (product (hyperbolicPlaneLattice (K := K)) M)) :
    V →ₗ[K] W where
  toFun x := (f.toLinearEquiv (0, x)).2
  map_add' x y := by
    have h := congrArg Prod.snd
      (map_add f.toLinearEquiv (0, x) (0, y))
    simpa using h
  map_smul' c x := by
    have h := congrArg Prod.snd
      (map_smul f.toLinearEquiv c (0, x))
    simpa using h

/-- If an isometry fixes the first hyperbolic vector, the image of every
complement vector has zero second hyperbolic coordinate. -/
theorem hyperbolicComplementImage_first_one_eq_zero
    (f : Isometry
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum q)
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r)
      (product (hyperbolicPlaneLattice (K := K)) L)
      (product (hyperbolicPlaneLattice (K := K)) M))
    (hfix : f.toLinearEquiv (omearaHyperbolicFirst (K := K), 0) =
      (omearaHyperbolicFirst (K := K), 0)) (x : V) :
    (f.toLinearEquiv (0, x)).1 1 = 0 := by
  have h := f.map_bilin
    (omearaHyperbolicFirst (K := K), 0) (0, x)
  rw [hfix] at h
  simpa [QuadraticSpace.orthogonalSum_bilin_apply,
    QuadraticSpace.hyperbolicPlane_bilin_apply,
    omearaHyperbolicFirst] using h

/-- Consequently the whole first coordinate of a complement image is a
multiple of the fixed isotropic vector. -/
theorem hyperbolicComplementImage_first_eq_smul
    (f : Isometry
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum q)
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r)
      (product (hyperbolicPlaneLattice (K := K)) L)
      (product (hyperbolicPlaneLattice (K := K)) M))
    (hfix : f.toLinearEquiv (omearaHyperbolicFirst (K := K), 0) =
      (omearaHyperbolicFirst (K := K), 0)) (x : V) :
    (f.toLinearEquiv (0, x)).1 =
      (f.toLinearEquiv (0, x)).1 0 •
        omearaHyperbolicFirst (K := K) := by
  funext i
  fin_cases i
  · simp
  · simp [hyperbolicComplementImage_first_one_eq_zero f hfix x]

/-- The inverse ambient isometry fixes the same hyperbolic vector. -/
theorem Isometry.symm_fix_omearaHyperbolicFirst
    (f : Isometry
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum q)
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r)
      (product (hyperbolicPlaneLattice (K := K)) L)
      (product (hyperbolicPlaneLattice (K := K)) M))
    (hfix : f.toLinearEquiv (omearaHyperbolicFirst (K := K), 0) =
      (omearaHyperbolicFirst (K := K), 0)) :
    f.symm.toLinearEquiv (omearaHyperbolicFirst (K := K), 0) =
      (omearaHyperbolicFirst (K := K), 0) := by
  change f.toLinearEquiv.symm (omearaHyperbolicFirst (K := K), 0) = _
  rw [← hfix]
  exact f.toLinearEquiv.symm_apply_apply _

/-- Projection to the two complement factors is inverse when the ambient
isometry fixes the common isotropic vector. -/
theorem hyperbolicComplementLinearMap_symm_apply_apply
    (f : Isometry
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum q)
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r)
      (product (hyperbolicPlaneLattice (K := K)) L)
      (product (hyperbolicPlaneLattice (K := K)) M))
    (hfix : f.toLinearEquiv (omearaHyperbolicFirst (K := K), 0) =
      (omearaHyperbolicFirst (K := K), 0)) (x : V) :
    hyperbolicComplementLinearMap f.symm
        (hyperbolicComplementLinearMap f x) = x := by
  let y := f.toLinearEquiv (0, x)
  let a : K := y.1 0
  have hyFirst : y.1 = a • omearaHyperbolicFirst (K := K) := by
    simpa [y, a] using
      hyperbolicComplementImage_first_eq_smul f hfix x
  have hyPair : (y.1, 0) = a •
      (omearaHyperbolicFirst (K := K), (0 : W)) := by
    apply Prod.ext
    · exact hyFirst
    · simp
  have hzeroPair : ((0 : Fin 2 → K), y.2) = y - (y.1, 0) := by
    apply Prod.ext
    · simp [hyFirst]
    · simp
  change (f.toLinearEquiv.symm
    (0, (f.toLinearEquiv (0, x)).2)).2 = x
  change (f.toLinearEquiv.symm (0, y.2)).2 = x
  have hfixInv : f.toLinearEquiv.symm
      (omearaHyperbolicFirst (K := K), (0 : W)) =
      (omearaHyperbolicFirst (K := K), (0 : V)) :=
    f.symm_fix_omearaHyperbolicFirst hfix
  rw [hzeroPair, map_sub, hyPair, map_smul,
    hfixInv]
  simp [y]

/-- The exact field-linear equivalence between the two complements. -/
noncomputable def hyperbolicComplementLinearEquiv
    (f : Isometry
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum q)
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r)
      (product (hyperbolicPlaneLattice (K := K)) L)
      (product (hyperbolicPlaneLattice (K := K)) M))
    (hfix : f.toLinearEquiv (omearaHyperbolicFirst (K := K), 0) =
      (omearaHyperbolicFirst (K := K), 0)) : V ≃ₗ[K] W :=
  LinearEquiv.ofLinear (hyperbolicComplementLinearMap f)
    (hyperbolicComplementLinearMap f.symm)
    (by
      ext x
      exact hyperbolicComplementLinearMap_symm_apply_apply f.symm
        (f.symm_fix_omearaHyperbolicFirst hfix) x)
    (by
      ext x
      exact hyperbolicComplementLinearMap_symm_apply_apply f hfix x)

/-- The complement equivalence preserves the bilinear forms. -/
theorem hyperbolicComplementLinearEquiv_map_bilin
    (f : Isometry
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum q)
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r)
      (product (hyperbolicPlaneLattice (K := K)) L)
      (product (hyperbolicPlaneLattice (K := K)) M))
    (hfix : f.toLinearEquiv (omearaHyperbolicFirst (K := K), 0) =
      (omearaHyperbolicFirst (K := K), 0)) (x y : V) :
    r.bilin (hyperbolicComplementLinearEquiv f hfix x)
        (hyperbolicComplementLinearEquiv f hfix y) = q.bilin x y := by
  have h := f.map_bilin (0, x) (0, y)
  have hxFirst := hyperbolicComplementImage_first_eq_smul f hfix x
  have hyFirst := hyperbolicComplementImage_first_eq_smul f hfix y
  change r.bilin (f.toLinearEquiv (0, x)).2
      (f.toLinearEquiv (0, y)).2 = q.bilin x y
  rw [QuadraticSpace.orthogonalSum_bilin_apply,
    QuadraticSpace.orthogonalSum_bilin_apply] at h
  rw [hxFirst, hyFirst,
    QuadraticSpace.hyperbolicPlane_bilin_apply] at h
  simpa [omearaHyperbolicFirst] using h

/-- O'Meara 93:14, common-isotropic-vector case: cancellation is integral,
not merely an isometry of the ambient quadratic spaces. -/
noncomputable def omeara9314_commonIsotropicVector
    (f : Isometry
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum q)
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r)
      (product (hyperbolicPlaneLattice (K := K)) L)
      (product (hyperbolicPlaneLattice (K := K)) M))
    (hfix : f.toLinearEquiv (omearaHyperbolicFirst (K := K), 0) =
      (omearaHyperbolicFirst (K := K), 0)) :
    Isometry q r L M where
  toLinearEquiv := hyperbolicComplementLinearEquiv f hfix
  map_bilin := hyperbolicComplementLinearEquiv_map_bilin f hfix
  map_mem x := by
    constructor
    · intro hx
      have hproduct : ((0 : Fin 2 → K), x) ∈
          product (hyperbolicPlaneLattice (K := K)) L := by
        simp [mem_product_iff, hx]
      have himage := (f.map_mem (0, x)).mp hproduct
      exact (mem_product_iff.mp himage).2
    · intro hx
      have hproduct : ((0 : Fin 2 → K),
          hyperbolicComplementLinearEquiv f hfix x) ∈
          product (hyperbolicPlaneLattice (K := K)) M := by
        simp [mem_product_iff, hx]
      have hpreimage := (f.symm.map_mem
        (0, hyperbolicComplementLinearEquiv f hfix x)).mp hproduct
      have hsnd := (mem_product_iff.mp hpreimage).2
      change hyperbolicComplementLinearMap f.symm
        (hyperbolicComplementLinearMap f x) ∈ L at hsnd
      rw [hyperbolicComplementLinearMap_symm_apply_apply f hfix x] at hsnd
      exact hsnd

/-! ## The unit cross-pairing reduction -/

/-- The diagonal automorphism `(x,y) ↦ (tx,t⁻¹y)` of a hyperbolic
plane. -/
noncomputable def omearaHyperbolicDiagonalLinearEquiv (t : Kˣ) :
    (Fin 2 → K) ≃ₗ[K] (Fin 2 → K) where
  toFun x := ![(t : K) * x 0, ((t⁻¹ : Kˣ) : K) * x 1]
  invFun x := ![((t⁻¹ : Kˣ) : K) * x 0, (t : K) * x 1]
  left_inv x := by
    funext i
    fin_cases i <;> simp [Units.ne_zero]
  right_inv x := by
    funext i
    fin_cases i <;> simp [Units.ne_zero]
  map_add' x y := by
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' c x := by
    funext i
    fin_cases i <;> simp <;> ring

@[simp]
theorem omearaHyperbolicDiagonalLinearEquiv_zero
    (t : Kˣ) (x : Fin 2 → K) :
    omearaHyperbolicDiagonalLinearEquiv t x 0 = (t : K) * x 0 :=
  rfl

@[simp]
theorem omearaHyperbolicDiagonalLinearEquiv_one
    (t : Kˣ) (x : Fin 2 → K) :
    omearaHyperbolicDiagonalLinearEquiv t x 1 =
      ((t⁻¹ : Kˣ) : K) * x 1 :=
  rfl

/-- Diagonal scaling preserves the standard hyperbolic form. -/
noncomputable def omearaHyperbolicDiagonalSpaceIsometry (t : Kˣ) :
    QuadraticSpace.Isometry
      (QuadraticSpace.hyperbolicPlane (1 : Kˣ))
      (QuadraticSpace.hyperbolicPlane (1 : Kˣ)) where
  toLinearEquiv := omearaHyperbolicDiagonalLinearEquiv t
  map_bilin x y := by
    rw [QuadraticSpace.hyperbolicPlane_bilin_apply,
      QuadraticSpace.hyperbolicPlane_bilin_apply]
    simp only [omearaHyperbolicDiagonalLinearEquiv_zero,
      omearaHyperbolicDiagonalLinearEquiv_one, Units.val_one, one_mul]
    change
      (((t : K) * x 0) * (((t⁻¹ : Kˣ) : K) * y 1) +
        (((t⁻¹ : Kˣ) : K) * x 1) * ((t : K) * y 0)) = _
    simp only [Units.val_inv_eq_inv_val]
    field_simp [Units.ne_zero t]

/-- Hyperbolic diagonal scaling by a valuation unit is an integral lattice
isometry of the standard unimodular plane. -/
noncomputable def hyperbolicDiagonalLatticeIsometry
    (t : Kˣ) (ht : IsValuationUnit K (t : K)) :
    Isometry (QuadraticSpace.hyperbolicPlane (1 : Kˣ))
      (QuadraticSpace.hyperbolicPlane (1 : Kˣ))
      (hyperbolicPlaneLattice (K := K))
      (hyperbolicPlaneLattice (K := K)) where
  toLinearEquiv := omearaHyperbolicDiagonalLinearEquiv t
  map_bilin := (omearaHyperbolicDiagonalSpaceIsometry t).map_bilin
  map_mem x := by
    rw [mem_omearaPlaneLattice_iff, mem_omearaPlaneLattice_iff]
    have htMem : (t : K) ∈ IntegerRing K :=
      (mem_integerRing_iff K).2 (by
        rw [Dyadic.IsIntegral]
        exact ht.ge)
    have htInvVal : IsValuationUnit K ((t⁻¹ : Kˣ) : K) := by
      simpa [IsValuationUnit, AddValuation.map_inv, ht]
    have htInvMem : ((t⁻¹ : Kˣ) : K) ∈ IntegerRing K :=
      (mem_integerRing_iff K).2 (by
        rw [Dyadic.IsIntegral]
        exact htInvVal.ge)
    constructor
    · rintro ⟨hzero, hone⟩
      exact ⟨(IntegerRing K).toSubring.mul_mem htMem hzero,
        (IntegerRing K).toSubring.mul_mem htInvMem hone⟩
    · rintro ⟨hzero, hone⟩
      constructor
      · have h := (IntegerRing K).toSubring.mul_mem htInvMem hzero
        change ((t⁻¹ : Kˣ) : K) * ((t : K) * x 0) ∈
          (IntegerRing K).toSubring at h
        simpa [Units.ne_zero] using h
      · have h := (IntegerRing K).toSubring.mul_mem htMem hone
        change (t : K) * (((t⁻¹ : Kˣ) : K) * x 1) ∈
          (IntegerRing K).toSubring at h
        simpa [Units.ne_zero] using h

/-- A valuation unit, regarded as a field element, is nonzero. -/
theorem ne_zero_of_isValuationUnit {c : K}
    (hc : IsValuationUnit K c) : c ≠ 0 := by
  intro hzero
  subst c
  simp [IsValuationUnit] at hc

/-- Adding an element of the maximal ideal to one gives a valuation unit. -/
theorem isValuationUnit_one_add_of_isInMaximalIdeal {c : K}
    (hc : IsInMaximalIdeal K c) : IsValuationUnit K (1 + c) := by
  rw [IsValuationUnit]
  have hlt : ord K (1 : K) < ord K c := by
    change 0 < ord K c at hc
    simpa only [ord_one] using hc
  simpa only [ord_one] using (ord K).map_add_eq_of_lt_left hlt

/-- The maximal ideal is stable under negation. -/
theorem isInMaximalIdeal_neg {c : K}
    (hc : IsInMaximalIdeal K c) : IsInMaximalIdeal K (-c) := by
  simpa [IsInMaximalIdeal] using hc

/-- The maximal ideal is stable under subtraction. -/
theorem isInMaximalIdeal_sub {c d : K}
    (hc : IsInMaximalIdeal K c) (hd : IsInMaximalIdeal K d) :
    IsInMaximalIdeal K (c - d) := by
  simpa only [sub_eq_add_neg] using
    isInMaximalIdeal_add K hc (isInMaximalIdeal_neg hd)

/-- A product of valuation units is a valuation unit. -/
theorem isValuationUnit_mul {c d : K}
    (hc : IsValuationUnit K c) (hd : IsValuationUnit K d) :
    IsValuationUnit K (c * d) := by
  rw [IsValuationUnit, ord_mul, hc, hd, add_zero]

/-- An integral nonunit belongs to the maximal ideal. -/
theorem isInMaximalIdeal_of_mem_integerRing_of_not_isValuationUnit
    {c : K} (hc : c ∈ IntegerRing K)
    (hnot : ¬ IsValuationUnit K c) : IsInMaximalIdeal K c := by
  change 0 < ord K c
  have hge : 0 ≤ ord K c := (mem_integerRing_iff K).1 hc
  have hne : ord K c ≠ 0 := by
    intro hzero
    exact hnot hzero
  exact lt_of_le_of_ne hge hne.symm

/-- The image of the first source hyperbolic vector. -/
noncomputable def hyperbolicFirstImage
    (f : Isometry
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum q)
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r)
      (product (hyperbolicPlaneLattice (K := K)) L)
      (product (hyperbolicPlaneLattice (K := K)) M)) :
    (Fin 2 → K) × W :=
  f.toLinearEquiv (omearaHyperbolicFirst (K := K), 0)

/-- The image of the second source hyperbolic vector. -/
noncomputable def hyperbolicSecondImage
    (f : Isometry
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum q)
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r)
      (product (hyperbolicPlaneLattice (K := K)) L)
      (product (hyperbolicPlaneLattice (K := K)) M)) :
    (Fin 2 → K) × W :=
  f.toLinearEquiv (omearaHyperbolicSecond (K := K), 0)

/-- Its pairing with the first target hyperbolic vector. -/
noncomputable def hyperbolicFirstCrossPairing
    (f : Isometry
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum q)
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r)
      (product (hyperbolicPlaneLattice (K := K)) L)
      (product (hyperbolicPlaneLattice (K := K)) M)) : K :=
  (hyperbolicFirstImage f).1 1

/-- The cross-pairing is literally the ambient bilinear pairing with the
first target vector. -/
theorem hyperbolicFirstCrossPairing_eq_bilin
    (f : Isometry
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum q)
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r)
      (product (hyperbolicPlaneLattice (K := K)) L)
      (product (hyperbolicPlaneLattice (K := K)) M)) :
    hyperbolicFirstCrossPairing f =
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r).bilin
        (omearaHyperbolicFirst (K := K), 0)
        (hyperbolicFirstImage f) := by
  simp [hyperbolicFirstCrossPairing, hyperbolicFirstImage,
    QuadraticSpace.orthogonalSum_bilin_apply,
    QuadraticSpace.hyperbolicPlane_bilin_apply,
    omearaHyperbolicFirst]

/-- The residual vector used by O'Meara's unit-pairing reduction. -/
noncomputable def hyperbolicFirstResidual
    (f : Isometry
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum q)
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r)
      (product (hyperbolicPlaneLattice (K := K)) L)
      (product (hyperbolicPlaneLattice (K := K)) M)) :
    (Fin 2 → K) × W :=
  hyperbolicFirstImage f - hyperbolicFirstCrossPairing f •
    (omearaHyperbolicFirst (K := K), 0)

/-- The residual has quadratic value `-2c²`. -/
theorem hyperbolicFirstResidual_quadratic
    (f : Isometry
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum q)
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r)
      (product (hyperbolicPlaneLattice (K := K)) L)
      (product (hyperbolicPlaneLattice (K := K)) M)) :
    ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r).quadratic
        (hyperbolicFirstResidual f) =
      -2 * hyperbolicFirstCrossPairing f ^ 2 := by
  let Q := (QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r
  let E : (Fin 2 → K) × W :=
    (omearaHyperbolicFirst (K := K), 0)
  let X := hyperbolicFirstImage f
  let c := hyperbolicFirstCrossPairing f
  have hE : Q.quadratic E = 0 := by
    simp [Q, E, QuadraticSpace.orthogonalSum_quadratic_apply,
      QuadraticSpace.hyperbolicPlane_quadratic_apply,
      omearaHyperbolicFirst]
  have hX : Q.quadratic X = 0 := by
    have h := f.map_quadratic
      (omearaHyperbolicFirst (K := K), (0 : V))
    simpa [Q, X, hyperbolicFirstImage,
      QuadraticSpace.orthogonalSum_quadratic_apply,
      QuadraticSpace.hyperbolicPlane_quadratic_apply,
      omearaHyperbolicFirst] using h
  have hEX : Q.bilin E X = c := by
    simpa [Q, E, X, c] using
      (hyperbolicFirstCrossPairing_eq_bilin f).symm
  have hXE : Q.bilin X E = c := by
    rw [Q.isSymm.eq]
    exact hEX
  change Q.quadratic (X - c • E) = -2 * c ^ 2
  change Q.bilin (X - c • E) (X - c • E) = _
  simp only [LinearMap.BilinForm.sub_left,
    LinearMap.BilinForm.sub_right,
    LinearMap.BilinForm.smul_left,
    LinearMap.BilinForm.smul_right]
  change Q.quadratic X - c * Q.bilin E X -
      c * (Q.bilin X E - c * Q.quadratic E) = _
  rw [hX, hXE, hEX, hE]
  ring

/-- Under a unit cross-pairing, the residual is anisotropic. -/
theorem hyperbolicFirstResidual_isAnisotropic
    (f : Isometry
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum q)
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r)
      (product (hyperbolicPlaneLattice (K := K)) L)
      (product (hyperbolicPlaneLattice (K := K)) M))
    (hcross : IsValuationUnit K (hyperbolicFirstCrossPairing f)) :
    ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r).IsAnisotropic
      (hyperbolicFirstResidual f) := by
  rw [QuadraticSpace.IsAnisotropic,
    hyperbolicFirstResidual_quadratic]
  exact mul_ne_zero (by norm_num)
    (pow_ne_zero 2 (ne_zero_of_isValuationUnit hcross))

/-- The residual lies in the target lattice. -/
theorem hyperbolicFirstResidual_mem
    (f : Isometry
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum q)
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r)
      (product (hyperbolicPlaneLattice (K := K)) L)
      (product (hyperbolicPlaneLattice (K := K)) M))
    (hcross : IsValuationUnit K (hyperbolicFirstCrossPairing f)) :
    hyperbolicFirstResidual f ∈
      product (hyperbolicPlaneLattice (K := K)) M := by
  have hsource : (omearaHyperbolicFirst (K := K), (0 : V)) ∈
      product (hyperbolicPlaneLattice (K := K)) L := by
    rw [mem_product_iff, mem_omearaPlaneLattice_iff]
    simp [omearaHyperbolicFirst]
  have himage : hyperbolicFirstImage f ∈
      product (hyperbolicPlaneLattice (K := K)) M := by
    exact (f.map_mem _).mp hsource
  have htarget : (omearaHyperbolicFirst (K := K), (0 : W)) ∈
      product (hyperbolicPlaneLattice (K := K)) M := by
    rw [mem_product_iff, mem_omearaPlaneLattice_iff]
    simp [omearaHyperbolicFirst]
  have hcrossMem : hyperbolicFirstCrossPairing f ∈ IntegerRing K :=
    (mem_integerRing_iff K).2 (by
      rw [Dyadic.IsIntegral]
      exact hcross.ge)
  exact (product (hyperbolicPlaneLattice (K := K)) M).sub_mem
    himage ((product (hyperbolicPlaneLattice (K := K)) M).smul_mem
      ⟨hyperbolicFirstCrossPairing f, hcrossMem⟩ htarget)

/-- The residual pairs integrally with every target-lattice vector. -/
theorem hyperbolicFirstResidual_pairing_mem_integerRing
    (f : Isometry
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum q)
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r)
      (product (hyperbolicPlaneLattice (K := K)) L)
      (product (hyperbolicPlaneLattice (K := K)) M))
    (hcross : IsValuationUnit K (hyperbolicFirstCrossPairing f))
    (y : (Fin 2 → K) × W)
    (hy : y ∈ product (hyperbolicPlaneLattice (K := K)) M) :
    ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r).bilin
        (hyperbolicFirstResidual f) y ∈ IntegerRing K := by
  let Q := (QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r
  let E : (Fin 2 → K) × W :=
    (omearaHyperbolicFirst (K := K), 0)
  have hpre : f.toLinearEquiv.symm y ∈
      product (hyperbolicPlaneLattice (K := K)) L :=
    (f.symm.map_mem y).mp hy
  have hprePlane := (mem_product_iff.mp hpre).1
  have hpreOne : (f.toLinearEquiv.symm y).1 1 ∈ IntegerRing K :=
    (mem_omearaPlaneLattice_iff _).mp hprePlane |>.2
  have himage : Q.bilin (hyperbolicFirstImage f) y ∈ IntegerRing K := by
    have hmap := f.map_bilin
      (omearaHyperbolicFirst (K := K), (0 : V))
      (f.toLinearEquiv.symm y)
    rw [f.toLinearEquiv.apply_symm_apply] at hmap
    change
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r).bilin
        (f.toLinearEquiv
          (omearaHyperbolicFirst (K := K), (0 : V))) y ∈
        IntegerRing K
    rw [hmap]
    simpa [Q, QuadraticSpace.orthogonalSum_bilin_apply,
      QuadraticSpace.hyperbolicPlane_bilin_apply,
      omearaHyperbolicFirst] using hpreOne
  have hyPlane := (mem_product_iff.mp hy).1
  have hyOne : y.1 1 ∈ IntegerRing K :=
    (mem_omearaPlaneLattice_iff _).mp hyPlane |>.2
  have hE : Q.bilin E y ∈ IntegerRing K := by
    simpa [Q, E, QuadraticSpace.orthogonalSum_bilin_apply,
      QuadraticSpace.hyperbolicPlane_bilin_apply,
      omearaHyperbolicFirst] using hyOne
  have hcrossMem : hyperbolicFirstCrossPairing f ∈ IntegerRing K :=
    (mem_integerRing_iff K).2 (by
      rw [Dyadic.IsIntegral]
      exact hcross.ge)
  change Q.bilin (hyperbolicFirstImage f -
      hyperbolicFirstCrossPairing f • E) y ∈ IntegerRing K
  rw [LinearMap.BilinForm.sub_left,
    LinearMap.BilinForm.smul_left]
  exact (IntegerRing K).toSubring.sub_mem himage
    ((IntegerRing K).toSubring.mul_mem hcrossMem hE)

/-- Reflection in the residual is integral. -/
theorem hyperbolicFirstResidual_isIntegralReflection
    (f : Isometry
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum q)
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r)
      (product (hyperbolicPlaneLattice (K := K)) L)
      (product (hyperbolicPlaneLattice (K := K)) M))
    (hcross : IsValuationUnit K (hyperbolicFirstCrossPairing f)) :
    IsIntegralReflection
      (q := (QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r)
      (L := product (hyperbolicPlaneLattice (K := K)) M)
      (hyperbolicFirstResidual_isAnisotropic f hcross) := by
  let c := hyperbolicFirstCrossPairing f
  have hc0 : c ≠ 0 := ne_zero_of_isValuationUnit hcross
  have hcInvVal : IsValuationUnit K c⁻¹ := by
    simpa [IsValuationUnit, AddValuation.map_inv, hcross]
  have hcInvMem : c⁻¹ ∈ IntegerRing K :=
    (mem_integerRing_iff K).2 (by
      rw [Dyadic.IsIntegral]
      exact hcInvVal.ge)
  apply isIntegralReflection_of_coefficient_mem_integerRing
    (hyperbolicFirstResidual_isAnisotropic f hcross)
    (hyperbolicFirstResidual_mem f hcross)
  intro y hy
  have hpair := hyperbolicFirstResidual_pairing_mem_integerRing
    f hcross y hy
  have hinvSq : c⁻¹ * c⁻¹ ∈ IntegerRing K :=
    (IntegerRing K).toSubring.mul_mem hcInvMem hcInvMem
  have hproduct : -(c⁻¹ * c⁻¹) *
      (((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r).bilin
        (hyperbolicFirstResidual f) y) ∈ IntegerRing K :=
    (IntegerRing K).toSubring.mul_mem
      ((IntegerRing K).toSubring.neg_mem hinvSq) hpair
  rw [hyperbolicFirstResidual_quadratic]
  have heq :
      2 * (((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r).bilin
          (hyperbolicFirstResidual f) y) /
          (-2 * c ^ 2) =
        -(c⁻¹ * c⁻¹) *
          (((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r).bilin
            (hyperbolicFirstResidual f) y) := by
    field_simp [hc0]
    <;> ring
  rw [heq]
  exact hproduct

/-- The integral reflection sends the image of the first source vector to
the cross-pairing multiple of the first target vector. -/
theorem hyperbolicFirstResidual_reflection_apply_image
    (f : Isometry
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum q)
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r)
      (product (hyperbolicPlaneLattice (K := K)) L)
      (product (hyperbolicPlaneLattice (K := K)) M))
    (hcross : IsValuationUnit K (hyperbolicFirstCrossPairing f)) :
    (QuadraticSpace.reflectionLinearEquiv
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r)
      (hyperbolicFirstResidual f)
      (hyperbolicFirstResidual_isAnisotropic f hcross))
      (hyperbolicFirstImage f) =
        hyperbolicFirstCrossPairing f •
          (omearaHyperbolicFirst (K := K), (0 : W)) := by
  apply QuadraticSpace.reflectionLinearEquiv_sub_apply_left_of_equalValue
  have hleft :
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r).quadratic
        (hyperbolicFirstImage f) = 0 := by
    have h := f.map_quadratic
      (omearaHyperbolicFirst (K := K), (0 : V))
    simpa [hyperbolicFirstImage,
      QuadraticSpace.orthogonalSum_quadratic_apply,
      QuadraticSpace.hyperbolicPlane_quadratic_apply,
      omearaHyperbolicFirst] using h
  rw [hleft]
  simp [QuadraticSpace.orthogonalSum_quadratic_apply,
    QuadraticSpace.hyperbolicPlane_quadratic_apply,
    omearaHyperbolicFirst]

/-- O'Meara 93:14 in the unit cross-pairing case. -/
noncomputable def omeara9314_unitCrossPairing
    (f : Isometry
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum q)
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r)
      (product (hyperbolicPlaneLattice (K := K)) L)
      (product (hyperbolicPlaneLattice (K := K)) M))
    (hcross : IsValuationUnit K (hyperbolicFirstCrossPairing f)) :
    Isometry q r L M := by
  let Q := (QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r
  let N := product (hyperbolicPlaneLattice (K := K)) M
  let hres := hyperbolicFirstResidual_isAnisotropic f hcross
  let hrefl : Isometry Q Q N N := integralReflection hres
    (hyperbolicFirstResidual_isIntegralReflection f hcross)
  let c : K := hyperbolicFirstCrossPairing f
  have hc0 : c ≠ 0 := ne_zero_of_isValuationUnit hcross
  let cu : Kˣ := Units.mk0 c hc0
  have hcu : IsValuationUnit K (cu : K) := by
    simpa [cu, c] using hcross
  have hcuInv : IsValuationUnit K ((cu⁻¹ : Kˣ) : K) := by
    simpa [IsValuationUnit, AddValuation.map_inv, hcu]
  let hdiag := Isometry.orthogonalProductBasic
    (hyperbolicDiagonalLatticeIsometry cu⁻¹ hcuInv)
    (Isometry.refl r M)
  let normalized := (f.trans hrefl).trans hdiag
  have hreflImage : hrefl.toLinearEquiv (hyperbolicFirstImage f) =
      c • (omearaHyperbolicFirst (K := K), (0 : W)) := by
    change Q.reflectionLinearEquiv (hyperbolicFirstResidual f) hres
      (hyperbolicFirstImage f) = _
    simpa [Q, c] using
      hyperbolicFirstResidual_reflection_apply_image f hcross
  have hnormalized : normalized.toLinearEquiv
      (omearaHyperbolicFirst (K := K), (0 : V)) =
        (omearaHyperbolicFirst (K := K), (0 : W)) := by
    change hdiag.toLinearEquiv
      (hrefl.toLinearEquiv (hyperbolicFirstImage f)) = _
    rw [hreflImage]
    apply Prod.ext
    · change omearaHyperbolicDiagonalLinearEquiv cu⁻¹
        (c • omearaHyperbolicFirst (K := K)) =
          omearaHyperbolicFirst (K := K)
      funext i
      fin_cases i <;>
        simp [omearaHyperbolicDiagonalLinearEquiv,
          omearaHyperbolicFirst, cu, c, hc0]
    · simp [hdiag]
  exact omeara9314_commonIsotropicVector normalized hnormalized

/-- Hyperbolic cancellation when the first source vector pairs by a unit
with the second target vector. -/
noncomputable def omeara9314_unitCrossPairing_firstSecond
    (f : Isometry
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum q)
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r)
      (product (hyperbolicPlaneLattice (K := K)) L)
      (product (hyperbolicPlaneLattice (K := K)) M))
    (hcross : IsValuationUnit K ((hyperbolicFirstImage f).1 0)) :
    Isometry q r L M := by
  let swapTarget := omearaHyperbolicProductSwap r M
  let g := f.trans swapTarget
  apply omeara9314_unitCrossPairing g
  change IsValuationUnit K
    ((swapTarget.toLinearEquiv (hyperbolicFirstImage f)).1 1)
  simpa [swapTarget] using hcross

/-- Hyperbolic cancellation when the second source vector pairs by a unit
with the first target vector. -/
noncomputable def omeara9314_unitCrossPairing_secondFirst
    (f : Isometry
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum q)
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r)
      (product (hyperbolicPlaneLattice (K := K)) L)
      (product (hyperbolicPlaneLattice (K := K)) M))
    (hcross : IsValuationUnit K ((hyperbolicSecondImage f).1 1)) :
    Isometry q r L M := by
  let swapSource := omearaHyperbolicProductSwap q L
  let g := swapSource.trans f
  apply omeara9314_unitCrossPairing g
  change IsValuationUnit K
    ((f.toLinearEquiv
      (swapSource.toLinearEquiv
        (omearaHyperbolicFirst (K := K), (0 : V)))).1 1)
  simpa [swapSource, hyperbolicSecondImage,
    omearaHyperbolicFirst, omearaHyperbolicSecond] using hcross

/-- Hyperbolic cancellation when the second source vector pairs by a unit
with the second target vector. -/
noncomputable def omeara9314_unitCrossPairing_secondSecond
    (f : Isometry
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum q)
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r)
      (product (hyperbolicPlaneLattice (K := K)) L)
      (product (hyperbolicPlaneLattice (K := K)) M))
    (hcross : IsValuationUnit K ((hyperbolicSecondImage f).1 0)) :
    Isometry q r L M := by
  let swapSource := omearaHyperbolicProductSwap q L
  let swapTarget := omearaHyperbolicProductSwap r M
  let g := (swapSource.trans f).trans swapTarget
  apply omeara9314_unitCrossPairing g
  change IsValuationUnit K
    ((swapTarget.toLinearEquiv
      (f.toLinearEquiv
        (swapSource.toLinearEquiv
          (omearaHyperbolicFirst (K := K), (0 : V))))).1 1)
  simpa [swapSource, swapTarget, hyperbolicSecondImage,
    omearaHyperbolicFirst, omearaHyperbolicSecond] using hcross

/-- The last branch of O'Meara 93:14: if all four cross-pairings of the
two hyperbolic planes lie in the maximal ideal, an explicit integral Eichler
transformation creates a unit cross-pairing. -/
noncomputable def omeara9314_smallCrossPairings
    (f : Isometry
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum q)
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r)
      (product (hyperbolicPlaneLattice (K := K)) L)
      (product (hyperbolicPlaneLattice (K := K)) M))
    (hX0 : IsInMaximalIdeal K ((hyperbolicFirstImage f).1 0))
    (hX1 : IsInMaximalIdeal K ((hyperbolicFirstImage f).1 1))
    (hY0 : IsInMaximalIdeal K ((hyperbolicSecondImage f).1 0))
    (hY1 : IsInMaximalIdeal K ((hyperbolicSecondImage f).1 1)) :
    Isometry q r L M := by
  let E : Fin 2 → K := omearaHyperbolicFirst (K := K)
  let F : Fin 2 → K := omearaHyperbolicSecond (K := K)
  let P : (Fin 2 → K) × V := f.toLinearEquiv.symm (F, 0)
  let a : K := P.1 0
  let b : K := P.1 1
  let z : V := P.2
  have hfP : f.toLinearEquiv P = (F, (0 : W)) := by
    simpa [P] using f.toLinearEquiv.apply_symm_apply (F, (0 : W))
  have htargetSecond : (F, (0 : W)) ∈
      product (hyperbolicPlaneLattice (K := K)) M := by
    rw [mem_product_iff, mem_omearaPlaneLattice_iff]
    simp [F, omearaHyperbolicSecond]
  have hPmem : P ∈ product (hyperbolicPlaneLattice (K := K)) L := by
    exact (f.symm.map_mem (F, (0 : W))).mp htargetSecond
  have hzL : z ∈ L := by
    exact (mem_product_iff.mp hPmem).2
  have haEq : a = (hyperbolicSecondImage f).1 0 := by
    have h := f.map_bilin (F, (0 : V)) P
    rw [hfP] at h
    simpa [a, F, hyperbolicSecondImage,
      QuadraticSpace.orthogonalSum_bilin_apply,
      QuadraticSpace.hyperbolicPlane_bilin_apply,
      omearaHyperbolicSecond] using h.symm
  have hbEq : b = (hyperbolicFirstImage f).1 0 := by
    have h := f.map_bilin (E, (0 : V)) P
    rw [hfP] at h
    simpa [b, E, F, hyperbolicFirstImage,
      QuadraticSpace.orthogonalSum_bilin_apply,
      QuadraticSpace.hyperbolicPlane_bilin_apply,
      omearaHyperbolicFirst, omearaHyperbolicSecond] using h.symm
  have haMax : IsInMaximalIdeal K a := by
    rw [haEq]
    exact hY0
  have hbMax : IsInMaximalIdeal K b := by
    rw [hbEq]
    exact hX0
  have haMem : a ∈ IntegerRing K :=
    (mem_integerRing_iff K).2 (le_of_lt haMax)
  have hbMem : b ∈ IntegerRing K :=
    (mem_integerRing_iff K).2 (le_of_lt hbMax)
  have hqz : q.quadratic z = -2 * a * b := by
    have h := f.map_quadratic P
    rw [hfP] at h
    have h' : 0 = 2 * a * b + q.quadratic z := by
      calc
        0 = 2 * (a * b) + q.quadratic z := by
          simpa [F, a, b, z,
            QuadraticSpace.orthogonalSum_quadratic_apply,
            QuadraticSpace.hyperbolicPlane_quadratic_apply,
            omearaHyperbolicSecond] using h
        _ = 2 * a * b + q.quadratic z := by ring
    linear_combination -h'
  have hzDual : z ∈ dualLattice q L := by
    rw [mem_dualLattice_iff q L z]
    intro v hv
    let fv := f.toLinearEquiv ((0 : Fin 2 → K), v)
    have hsource : ((0 : Fin 2 → K), v) ∈
        product (hyperbolicPlaneLattice (K := K)) L := by
      rw [mem_product_iff, mem_omearaPlaneLattice_iff]
      simp [hv]
    have hfvMem : fv ∈ product (hyperbolicPlaneLattice (K := K)) M :=
      (f.map_mem _).mp hsource
    have hcoord : fv.1 0 ∈ IntegerRing K :=
      (mem_omearaPlaneLattice_iff fv.1).mp
        (mem_product_iff.mp hfvMem).1 |>.1
    have hbilin := f.map_bilin P ((0 : Fin 2 → K), v)
    rw [hfP] at hbilin
    have heq : fv.1 0 = q.bilin z v := by
      simpa [fv, F, z,
        QuadraticSpace.orthogonalSum_bilin_apply,
        QuadraticSpace.hyperbolicPlane_bilin_apply,
        omearaHyperbolicSecond] using hbilin
    rw [← heq]
    exact hcoord
  let u : K := 1 + b
  have hu : IsValuationUnit K u := by
    simpa [u] using isValuationUnit_one_add_of_isInMaximalIdeal hbMax
  have hu0 : u ≠ 0 := ne_zero_of_isValuationUnit hu
  let uu : Kˣ := Units.mk0 u hu0
  let uinv : K := ((uu⁻¹ : Kˣ) : K)
  have huinv_eq : uinv = u⁻¹ := by
    simp [uinv, uu]
  have huinv : IsValuationUnit K uinv := by
    simpa [uinv, IsValuationUnit, AddValuation.map_inv, hu]
  have huinvMem : uinv ∈ IntegerRing K :=
    (mem_integerRing_iff K).2 (by
      rw [Dyadic.IsIntegral]
      exact huinv.ge)
  let z' : V := uinv • z
  have hz'L : z' ∈ L := by
    exact L.smul_mem ⟨uinv, huinvMem⟩ hzL
  have hz'Dual : z' ∈ dualLattice q L := by
    exact (dualLattice q L).smul_mem ⟨uinv, huinvMem⟩ hzDual
  let s : K := -(a * b * uinv ^ 2)
  have hsMem : s ∈ IntegerRing K := by
    change s ∈ (IntegerRing K).toSubring
    exact (IntegerRing K).toSubring.neg_mem
      ((IntegerRing K).toSubring.mul_mem
        ((IntegerRing K).toSubring.mul_mem haMem hbMem)
        ((IntegerRing K).toSubring.pow_mem huinvMem 2))
  have hquadratic : q.quadratic z' = 2 * s := by
    rw [show q.quadratic z' = uinv ^ 2 * q.quadratic z by
      change q.quadratic (uinv • z) = uinv ^ 2 * q.quadratic z
      exact q.quadratic_smul uinv z]
    rw [hqz]
    simp only [s]
    ring
  let T := hyperbolicEichlerLatticeIsometry
    q L z' hz'L hz'Dual s hquadratic hsMem
  let swapSource := omearaHyperbolicProductSwap q L
  let g := (swapSource.trans T).trans f
  apply omeara9314_unitCrossPairing g
  let X0 : K := (hyperbolicFirstImage f).1 0
  let X1 : K := (hyperbolicFirstImage f).1 1
  let Y0 : K := (hyperbolicSecondImage f).1 0
  let Y1 : K := (hyperbolicSecondImage f).1 1
  have hPdecomp : P =
      a • (E, (0 : V)) + b • (F, (0 : V)) +
        ((0 : Fin 2 → K), z) := by
    apply Prod.ext
    · funext i
      fin_cases i <;> simp [a, b, E, F, P,
        omearaHyperbolicFirst, omearaHyperbolicSecond]
    · simp [z, P]
  have hfzOne :
      (f.toLinearEquiv ((0 : Fin 2 → K), z)).1 1 =
        1 - a * X1 - b * Y1 := by
    have hmap := congrArg f.toLinearEquiv hPdecomp
    rw [hfP, map_add, map_add, map_smul, map_smul] at hmap
    have hcoord := congrArg (fun x : (Fin 2 → K) × W => x.1 1) hmap
    change 1 = a * X1 + b * Y1 +
      (f.toLinearEquiv ((0 : Fin 2 → K), z)).1 1 at hcoord
    calc
      (f.toLinearEquiv ((0 : Fin 2 → K), z)).1 1 =
          (a * X1 + b * Y1 +
            (f.toLinearEquiv ((0 : Fin 2 → K), z)).1 1) -
              a * X1 - b * Y1 := by ring
      _ = 1 - a * X1 - b * Y1 := by rw [← hcoord]
  have hTSecond : T.toLinearEquiv (F, (0 : V)) =
      (![-s, 1], z') := by
    apply Prod.ext
    · funext i
      fin_cases i <;> simp [T, F, omearaHyperbolicSecond]
    · simp [T, F, omearaHyperbolicSecond]
  have hcrossFormula : hyperbolicFirstCrossPairing g =
      uinv * (1 + Y1 - a * uinv * X1) := by
    change
      (f.toLinearEquiv
        (T.toLinearEquiv
          (swapSource.toLinearEquiv
            (omearaHyperbolicFirst (K := K), (0 : V))))).1 1 = _
    rw [show swapSource.toLinearEquiv
        (omearaHyperbolicFirst (K := K), (0 : V)) = (F, (0 : V)) by
      simp [swapSource, F, omearaHyperbolicFirst,
        omearaHyperbolicSecond]]
    rw [hTSecond]
    have hvector : (![-s, 1], z') =
        (-s) • (E, (0 : V)) + (F, (0 : V)) +
          ((0 : Fin 2 → K), z') := by
      apply Prod.ext
      · funext i
        fin_cases i <;> simp [E, F, omearaHyperbolicFirst,
          omearaHyperbolicSecond]
      · simp
    rw [hvector, map_add, map_add, map_smul]
    have hz'Image : f.toLinearEquiv ((0 : Fin 2 → K), z') =
        uinv • f.toLinearEquiv ((0 : Fin 2 → K), z) := by
      rw [show ((0 : Fin 2 → K), z') =
          uinv • ((0 : Fin 2 → K), z) by simp [z']]
      exact map_smul f.toLinearEquiv uinv _
    rw [hz'Image]
    change -s * X1 + Y1 + uinv *
      (f.toLinearEquiv ((0 : Fin 2 → K), z)).1 1 = _
    rw [hfzOne]
    simp only [s, huinv_eq, u]
    have hu0' : 1 + b ≠ 0 := by simpa [u] using hu0
    field_simp [hu0']
    ring
  have hX1Int : Dyadic.IsIntegral K X1 := by
    exact le_of_lt hX1
  have huinvInt : Dyadic.IsIntegral K uinv := by
    exact huinv.ge
  have haUinvMax : IsInMaximalIdeal K (a * uinv) :=
    isInMaximalIdeal_mul_isIntegral K haMax huinvInt
  have haUinvX1Max : IsInMaximalIdeal K (a * uinv * X1) :=
    isInMaximalIdeal_mul_isIntegral K haUinvMax hX1Int
  have hm : IsInMaximalIdeal K (Y1 - a * uinv * X1) := by
    exact isInMaximalIdeal_sub hY1 haUinvX1Max
  have hd : IsValuationUnit K (1 + Y1 - a * uinv * X1) := by
    have := isValuationUnit_one_add_of_isInMaximalIdeal hm
    simpa only [add_sub_assoc] using this
  rw [hcrossFormula]
  exact isValuationUnit_mul huinv hd

/-- O'Meara 93:14 for one standard unimodular hyperbolic adjunction.
Every possible cross-pairing configuration is discharged explicitly; no
cancellation law remains as a hypothesis. -/
noncomputable def omeara9314
    (f : Isometry
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum q)
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum r)
      (product (hyperbolicPlaneLattice (K := K)) L)
      (product (hyperbolicPlaneLattice (K := K)) M)) :
    Isometry q r L M := by
  let E : Fin 2 → K := omearaHyperbolicFirst (K := K)
  let F : Fin 2 → K := omearaHyperbolicSecond (K := K)
  have hEsource : (E, (0 : V)) ∈
      product (hyperbolicPlaneLattice (K := K)) L := by
    rw [mem_product_iff, mem_omearaPlaneLattice_iff]
    simp [E, omearaHyperbolicFirst]
  have hFsource : (F, (0 : V)) ∈
      product (hyperbolicPlaneLattice (K := K)) L := by
    rw [mem_product_iff, mem_omearaPlaneLattice_iff]
    simp [F, omearaHyperbolicSecond]
  have hXmem : hyperbolicFirstImage f ∈
      product (hyperbolicPlaneLattice (K := K)) M := by
    simpa [hyperbolicFirstImage, E] using (f.map_mem (E, (0 : V))).mp hEsource
  have hYmem : hyperbolicSecondImage f ∈
      product (hyperbolicPlaneLattice (K := K)) M := by
    simpa [hyperbolicSecondImage, F] using (f.map_mem (F, (0 : V))).mp hFsource
  have hXplane := (mem_product_iff.mp hXmem).1
  have hYplane := (mem_product_iff.mp hYmem).1
  have hX0mem : (hyperbolicFirstImage f).1 0 ∈ IntegerRing K :=
    (mem_omearaPlaneLattice_iff _).mp hXplane |>.1
  have hX1mem : (hyperbolicFirstImage f).1 1 ∈ IntegerRing K :=
    (mem_omearaPlaneLattice_iff _).mp hXplane |>.2
  have hY0mem : (hyperbolicSecondImage f).1 0 ∈ IntegerRing K :=
    (mem_omearaPlaneLattice_iff _).mp hYplane |>.1
  have hY1mem : (hyperbolicSecondImage f).1 1 ∈ IntegerRing K :=
    (mem_omearaPlaneLattice_iff _).mp hYplane |>.2
  by_cases hX1 : IsValuationUnit K ((hyperbolicFirstImage f).1 1)
  · exact omeara9314_unitCrossPairing f hX1
  by_cases hX0 : IsValuationUnit K ((hyperbolicFirstImage f).1 0)
  · exact omeara9314_unitCrossPairing_firstSecond f hX0
  by_cases hY1 : IsValuationUnit K ((hyperbolicSecondImage f).1 1)
  · exact omeara9314_unitCrossPairing_secondFirst f hY1
  by_cases hY0 : IsValuationUnit K ((hyperbolicSecondImage f).1 0)
  · exact omeara9314_unitCrossPairing_secondSecond f hY0
  exact omeara9314_smallCrossPairings f
    (isInMaximalIdeal_of_mem_integerRing_of_not_isValuationUnit hX0mem hX0)
    (isInMaximalIdeal_of_mem_integerRing_of_not_isValuationUnit hX1mem hX1)
    (isInMaximalIdeal_of_mem_integerRing_of_not_isValuationUnit hY0mem hY0)
    (isInMaximalIdeal_of_mem_integerRing_of_not_isValuationUnit hY1mem hY1)

/-- O'Meara 93:14 after an arbitrary common form scaling.  This is the
version needed to cancel one summand `s A(0,0)` in a modular hyperbolic
adjunction.  The proof rescales both ambient forms by `s⁻¹`, applies the
unimodular theorem, and cancels the nonzero scalar on the complements. -/
noncomputable def omeara9314_scaled (s : Kˣ)
    (f : Isometry
      ((QuadraticSpace.hyperbolicPlane s).orthogonalSum q)
      ((QuadraticSpace.hyperbolicPlane s).orthogonalSum r)
      (product (hyperbolicPlaneLattice (K := K)) L)
      (product (hyperbolicPlaneLattice (K := K)) M)) :
    Isometry q r L M := by
  let fScaled : Isometry
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum
        (q.rescaleUnit s⁻¹))
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).orthogonalSum
        (r.rescaleUnit s⁻¹))
      (product (hyperbolicPlaneLattice (K := K)) L)
      (product (hyperbolicPlaneLattice (K := K)) M) :=
    {
    toLinearEquiv := f.toLinearEquiv
    map_bilin x y := by
      have h := f.map_bilin x y
      simp only [QuadraticSpace.orthogonalSum_bilin_apply,
        QuadraticSpace.hyperbolicPlane_bilin_apply,
        QuadraticSpace.rescaleUnit_bilin_apply, Units.val_one, one_mul] at h ⊢
      have hs : (s : K) ≠ 0 := Units.ne_zero s
      have hsInv : ((s⁻¹ : Kˣ) : K) = (s : K)⁻¹ := by
        simpa only [Units.val_inv_eq_inv_val]
      rw [hsInv]
      field_simp [hs]
      simpa only [mul_comm] using h
    map_mem := f.map_mem }
  let g : Isometry (q.rescaleUnit s⁻¹) (r.rescaleUnit s⁻¹) L M :=
    omeara9314 fScaled
  exact
    { toLinearEquiv := g.toLinearEquiv
      map_bilin := by
        intro x y
        have h := g.map_bilin x y
        simp only [QuadraticSpace.rescaleUnit_bilin_apply] at h
        exact mul_left_cancel₀ (Units.ne_zero (s⁻¹ : Kˣ)) h
      map_mem := g.map_mem }

/-- Cancellation after identifying the two displayed summands with the
same scaled hyperbolic plane.  This conjugation form is what is iterated in
the proof of O'Meara 93:14a. -/
noncomputable def omeara9314_scaled_of_isometric_summand
    {U : Type x} [AddCommGroup U] [Module K U]
    {U' : Type y} [AddCommGroup U'] [Module K U']
    {p : QuadraticSpace K U} {p' : QuadraticSpace K U'}
    {J : Lattice K U} {J' : Lattice K U'}
    (s : Kˣ)
    (sourceSummand : Isometry p
      (QuadraticSpace.hyperbolicPlane s) J
      (hyperbolicPlaneLattice (K := K)))
    (targetSummand : Isometry p'
      (QuadraticSpace.hyperbolicPlane s) J'
      (hyperbolicPlaneLattice (K := K)))
    (f : Isometry (p.orthogonalSum q) (p'.orthogonalSum r)
      (product J L) (product J' M)) :
    Isometry q r L M := by
  let sourceToDisplayed : Isometry
      ((QuadraticSpace.hyperbolicPlane s).orthogonalSum q)
      (p.orthogonalSum q)
      (product (hyperbolicPlaneLattice (K := K)) L)
      (product J L) :=
    sourceSummand.symm.orthogonalProductBasic (Isometry.refl q L)
  let displayedToTarget : Isometry
      (p'.orthogonalSum r)
      ((QuadraticSpace.hyperbolicPlane s).orthogonalSum r)
      (product J' M)
      (product (hyperbolicPlaneLattice (K := K)) M) :=
    targetSummand.orthogonalProductBasic (Isometry.refl r M)
  exact omeara9314_scaled s
    (sourceToDisplayed.trans (f.trans displayedToTarget))

end Lattice

end Bong
