/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryPrimitiveCoordinates
import Bong.Dyadic.QuadraticDefectHensel
import Bong.Lattice.OmearaGeneralPlane
import Bong.Lattice.OmearaHyperbolicCancellation
import Bong.Lattice.PrimitiveVector

/-!
# O'Meara 93:11: isotropic even unimodular binary planes

This file proves the isotropic branch of O'Meara 93:11 in the exact
coordinate form used in 93:18.  If the two diagonal entries of
`A(2 * eta, 2 * zeta)` are even and its ambient binary space is isotropic,
then its standard integral lattice is the hyperbolic plane `A(0,0)`.

The proof is integral.  We first choose a primitive lattice representative
on an isotropic line.  One of its two coordinates is a valuation unit.  An
explicit second isotropic vector then has pairing one with the first, and
the resulting change-of-basis determinant is a valuation unit.  Thus both
the change of basis and its inverse preserve the standard lattice.
-/

namespace Bong

open Dyadic

namespace Lattice

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-! ## Integral binary changes of basis -/

/-- Determinant of the matrix whose columns are the two displayed binary
vectors. -/
def binaryColumnDeterminant (x y : Fin 2 → K) : K :=
  x 0 * y 1 - x 1 * y 0

/-- The linear equivalence whose columns are `x` and `y`. -/
noncomputable def binaryColumnLinearEquiv (x y : Fin 2 → K)
    (hdet : binaryColumnDeterminant x y ≠ 0) :
    (Fin 2 → K) ≃ₗ[K] (Fin 2 → K) where
  toFun z := fun i ↦ z 0 * x i + z 1 * y i
  invFun z := ![
    (y 1 * z 0 - y 0 * z 1) / binaryColumnDeterminant x y,
    (-x 1 * z 0 + x 0 * z 1) / binaryColumnDeterminant x y]
  left_inv z := by
    have hdet' : y 1 * x 0 - y 0 * x 1 ≠ 0 := by
      simpa [binaryColumnDeterminant, mul_comm] using hdet
    have hdet'' : -(x 1 * y 0) + x 0 * y 1 ≠ 0 := by
      simpa [binaryColumnDeterminant, sub_eq_add_neg, add_comm] using hdet
    funext i
    fin_cases i
    · simp [binaryColumnDeterminant]
      field_simp [hdet, hdet', hdet''] <;> ring
    · simp [binaryColumnDeterminant]
      apply (div_eq_iff hdet).2
      dsimp [binaryColumnDeterminant]
      ring
  right_inv z := by
    have hdet' : y 1 * x 0 - y 0 * x 1 ≠ 0 := by
      simpa [binaryColumnDeterminant, mul_comm] using hdet
    have hdet'' : -(x 1 * y 0) + x 0 * y 1 ≠ 0 := by
      simpa [binaryColumnDeterminant, sub_eq_add_neg, add_comm] using hdet
    funext i
    fin_cases i <;>
      simp [binaryColumnDeterminant] <;>
      field_simp [hdet, hdet', hdet''] <;> ring
  map_add' z w := by
    funext i
    simp
    ring
  map_smul' c z := by
    funext i
    simp [smul_eq_mul]
    ring

@[simp]
theorem binaryColumnLinearEquiv_apply
    (x y z : Fin 2 → K) (hdet : binaryColumnDeterminant x y ≠ 0)
    (i : Fin 2) :
    binaryColumnLinearEquiv x y hdet z i = z 0 * x i + z 1 * y i :=
  rfl

/-- Integral columns give an integral forward binary change of basis. -/
theorem binaryColumnLinearEquiv_integral
    (x y : Fin 2 → K)
    (hx : ∀ i, x i ∈ IntegerRing K)
    (hy : ∀ i, y i ∈ IntegerRing K)
    (hdet : binaryColumnDeterminant x y ≠ 0)
    {z : Fin 2 → K} (hz : ∀ i, z i ∈ IntegerRing K) :
    ∀ i, binaryColumnLinearEquiv x y hdet z i ∈ IntegerRing K := by
  intro i
  rw [binaryColumnLinearEquiv_apply]
  exact (IntegerRing K).toSubring.add_mem
    ((IntegerRing K).toSubring.mul_mem (hz 0) (hx i))
    ((IntegerRing K).toSubring.mul_mem (hz 1) (hy i))

/-- A valuation-unit determinant also makes the inverse binary change of
basis integral. -/
theorem binaryColumnLinearEquiv_symm_integral
    (x y : Fin 2 → K)
    (hx : ∀ i, x i ∈ IntegerRing K)
    (hy : ∀ i, y i ∈ IntegerRing K)
    (hdetUnit : IsValuationUnit K (binaryColumnDeterminant x y))
    {z : Fin 2 → K} (hz : ∀ i, z i ∈ IntegerRing K) :
    ∀ i,
      (binaryColumnLinearEquiv x y
        (ne_zero_of_isValuationUnit hdetUnit)).symm z i ∈ IntegerRing K := by
  let d := binaryColumnDeterminant x y
  have hdInvUnit : IsValuationUnit K d⁻¹ := by
    simpa [d, IsValuationUnit, AddValuation.map_inv, hdetUnit]
  have hdInv : d⁻¹ ∈ IntegerRing K :=
    (mem_integerRing_iff K).2 hdInvUnit.ge
  intro i
  fin_cases i
  · change (y 1 * z 0 - y 0 * z 1) / d ∈ IntegerRing K
    rw [div_eq_mul_inv]
    exact (IntegerRing K).toSubring.mul_mem
      ((IntegerRing K).toSubring.sub_mem
        ((IntegerRing K).toSubring.mul_mem (hy 1) (hz 0))
        ((IntegerRing K).toSubring.mul_mem (hy 0) (hz 1))) hdInv
  · change (-x 1 * z 0 + x 0 * z 1) / d ∈ IntegerRing K
    rw [div_eq_mul_inv]
    exact (IntegerRing K).toSubring.mul_mem
      ((IntegerRing K).toSubring.add_mem
        ((IntegerRing K).toSubring.mul_mem
          ((IntegerRing K).toSubring.neg_mem (hx 1)) (hz 0))
        ((IntegerRing K).toSubring.mul_mem (hx 0) (hz 1))) hdInv

/-- Two integral vectors with hyperbolic Gram matrix and unit determinant
give an integral isometry from the standard hyperbolic plane. -/
noncomputable def hyperbolicLatticeIsometryOfIntegralBinaryBasis
    (q : QuadraticSpace K (Fin 2 → K)) (x y : Fin 2 → K)
    (hx : ∀ i, x i ∈ IntegerRing K)
    (hy : ∀ i, y i ∈ IntegerRing K)
    (hdetUnit : IsValuationUnit K (binaryColumnDeterminant x y))
    (hxx : q.bilin x x = 0) (hxy : q.bilin x y = 1)
    (hyy : q.bilin y y = 0) :
    Isometry (QuadraticSpace.hyperbolicPlane (1 : Kˣ)) q
      (hyperbolicPlaneLattice (K := K))
      (hyperbolicPlaneLattice (K := K)) where
  toLinearEquiv := binaryColumnLinearEquiv x y
    (ne_zero_of_isValuationUnit hdetUnit)
  map_bilin z w := by
    rw [QuadraticSpace.hyperbolicPlane_bilin_apply]
    change q.bilin (z 0 • x + z 1 • y)
        (w 0 • x + w 1 • y) = _
    simp only [Units.val_one, one_mul,
      LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right,
      smul_eq_mul]
    rw [hxx, hxy, q.isSymm.eq y x, hxy, hyy]
    ring
  map_mem z := by
    rw [mem_omearaPlaneLattice_iff, mem_omearaPlaneLattice_iff]
    constructor
    · rintro ⟨hz0, hz1⟩
      have hz : ∀ i, z i ∈ IntegerRing K := by
        intro i
        fin_cases i <;> assumption
      exact ⟨
        binaryColumnLinearEquiv_integral x y hx hy
          (ne_zero_of_isValuationUnit hdetUnit) hz 0,
        binaryColumnLinearEquiv_integral x y hx hy
          (ne_zero_of_isValuationUnit hdetUnit) hz 1⟩
    · rintro ⟨hz0, hz1⟩
      let e := binaryColumnLinearEquiv x y
        (ne_zero_of_isValuationUnit hdetUnit)
      have hz : ∀ i, e z i ∈ IntegerRing K := by
        intro i
        fin_cases i <;> assumption
      have hinv := binaryColumnLinearEquiv_symm_integral x y hx hy
        hdetUnit hz
      have hzero := hinv 0
      have hone := hinv 1
      simpa [e] using And.intro hzero hone

/-! ## Normalizing an even isotropic plane -/

/-- If the first coordinate of an integral isotropic vector is a valuation
unit, it can be completed integrally to a hyperbolic basis of
`A(2*eta,2*zeta)`. -/
noncomputable def evenGeneralPlaneHyperbolicIsometryOfFirstUnit
    (eta zeta : K) (heta : eta ∈ IntegerRing K)
    (hzeta : zeta ∈ IntegerRing K)
    (hnondegenerate : ((2 : K) * eta) * ((2 : K) * zeta) ≠ 1)
    (x : Fin 2 → K) (hx : ∀ i, x i ∈ IntegerRing K)
    (hisotropic :
      (QuadraticSpace.omearaGeneralPlane
        ((2 : K) * eta) ((2 : K) * zeta) hnondegenerate).quadratic x = 0)
    (hxzeroUnit : IsValuationUnit K (x 0)) :
    Isometry (QuadraticSpace.hyperbolicPlane (1 : Kˣ))
      (QuadraticSpace.omearaGeneralPlane
        ((2 : K) * eta) ((2 : K) * zeta) hnondegenerate)
      (hyperbolicPlaneLattice (K := K))
      (hyperbolicPlaneLattice (K := K)) := by
  let q := QuadraticSpace.omearaGeneralPlane
    ((2 : K) * eta) ((2 : K) * zeta) hnondegenerate
  let e₁ : Fin 2 → K := ![0, 1]
  let c : K := x 0 + (2 : K) * zeta * x 1
  have hxzeroNe : x 0 ≠ 0 := ne_zero_of_isValuationUnit hxzeroUnit
  have hxzeroInvUnit : IsValuationUnit K (x 0)⁻¹ := by
    simpa [IsValuationUnit, AddValuation.map_inv, hxzeroUnit]
  have hxzeroInv : (x 0)⁻¹ ∈ IntegerRing K :=
    (mem_integerRing_iff K).2 hxzeroInvUnit.ge
  have htailIntegral : zeta * x 1 * (x 0)⁻¹ ∈ IntegerRing K :=
    (IntegerRing K).toSubring.mul_mem
      ((IntegerRing K).toSubring.mul_mem hzeta (hx 1)) hxzeroInv
  have htailMax :
      IsInMaximalIdeal K ((2 : K) * (zeta * x 1 * (x 0)⁻¹)) :=
    isInMaximalIdeal_mul_isIntegral K (two_isInMaximalIdeal K)
      ((mem_integerRing_iff K).1 htailIntegral)
  have honeTailUnit :
      IsValuationUnit K (1 + (2 : K) * (zeta * x 1 * (x 0)⁻¹)) :=
    isValuationUnit_one_add_of_isInMaximalIdeal htailMax
  have hcFactor :
      c = x 0 * (1 + (2 : K) * (zeta * x 1 * (x 0)⁻¹)) := by
    dsimp [c]
    field_simp [hxzeroNe] <;> ring
  have hcUnit : IsValuationUnit K c := by
    rw [hcFactor]
    exact isValuationUnit_mul hxzeroUnit honeTailUnit
  have hcNe : c ≠ 0 := ne_zero_of_isValuationUnit hcUnit
  have hcInvUnit : IsValuationUnit K c⁻¹ := by
    simpa [IsValuationUnit, AddValuation.map_inv, hcUnit]
  have hcInv : c⁻¹ ∈ IntegerRing K :=
    (mem_integerRing_iff K).2 hcInvUnit.ge
  let y : Fin 2 → K :=
    c⁻¹ • (e₁ - (zeta * c⁻¹) • x)
  have he₁Integral : ∀ i, e₁ i ∈ IntegerRing K := by
    intro i
    fin_cases i <;> simp [e₁]
  have hy : ∀ i, y i ∈ IntegerRing K := by
    intro i
    dsimp [y]
    change c⁻¹ * (e₁ i - (zeta * c⁻¹) * x i) ∈ IntegerRing K
    exact (IntegerRing K).toSubring.mul_mem hcInv
      ((IntegerRing K).toSubring.sub_mem (he₁Integral i)
        ((IntegerRing K).toSubring.mul_mem
          ((IntegerRing K).toSubring.mul_mem hzeta hcInv) (hx i)))
  have hxx : q.bilin x x = 0 := by
    exact hisotropic
  have hxe₁ : q.bilin x e₁ = c := by
    rw [QuadraticSpace.omearaGeneralPlane_bilin_apply]
    simp [e₁, c] <;> ring
  have hxy : q.bilin x y = 1 := by
    dsimp [y]
    rw [LinearMap.BilinForm.smul_right,
      LinearMap.BilinForm.sub_right,
      LinearMap.BilinForm.smul_right, hxe₁, hxx]
    simp [smul_eq_mul, hcNe]
  have hyy : q.bilin y y = 0 := by
    have he₁e₁ : q.bilin e₁ e₁ = (2 : K) * zeta := by
      rw [QuadraticSpace.omearaGeneralPlane_bilin_apply]
      simp [e₁]
    have he₁x : q.bilin e₁ x = c := by
      rw [q.isSymm.eq e₁ x]
      exact hxe₁
    dsimp [y, e₁]
    simp only [LinearMap.BilinForm.smul_left,
      LinearMap.BilinForm.smul_right,
      LinearMap.BilinForm.sub_left,
      LinearMap.BilinForm.sub_right, smul_eq_mul]
    rw [he₁e₁, he₁x, hxe₁, hxx]
    field_simp [hcNe] <;> ring
  have hdetEq : binaryColumnDeterminant x y = x 0 * c⁻¹ := by
    dsimp [binaryColumnDeterminant, y, e₁]
    ring
  have hdetUnit : IsValuationUnit K (binaryColumnDeterminant x y) := by
    rw [hdetEq]
    exact isValuationUnit_mul hxzeroUnit hcInvUnit
  exact hyperbolicLatticeIsometryOfIntegralBinaryBasis
    q x y hx hy hdetUnit hxx hxy hyy

/-- O'Meara 93:11, isotropic branch.  An even unimodular binary plane
`A(2*eta,2*zeta)` is integrally hyperbolic whenever its ambient space is
isotropic. -/
theorem omeara9311_isotropic_even_plane_isIsometric
    (eta zeta : K) (heta : eta ∈ IntegerRing K)
    (hzeta : zeta ∈ IntegerRing K)
    (hnondegenerate : ((2 : K) * eta) * ((2 : K) * zeta) ≠ 1)
    (hisotropic : ∃ z : Fin 2 → K, z ≠ 0 ∧
      (QuadraticSpace.omearaGeneralPlane
        ((2 : K) * eta) ((2 : K) * zeta) hnondegenerate).quadratic z = 0) :
    IsIsometric
      (QuadraticSpace.omearaGeneralPlane
        ((2 : K) * eta) ((2 : K) * zeta) hnondegenerate)
      (QuadraticSpace.hyperbolicPlane (1 : Kˣ))
      (hyperbolicPlaneLattice (K := K))
      (hyperbolicPlaneLattice (K := K)) := by
  let q := QuadraticSpace.omearaGeneralPlane
    ((2 : K) * eta) ((2 : K) * zeta) hnondegenerate
  let z : Fin 2 → K := Classical.choose hisotropic
  have hzSpec := Classical.choose_spec hisotropic
  have hzNe : z ≠ 0 := hzSpec.1
  have hzIso : q.quadratic z = 0 := hzSpec.2
  let htExists :=
    exists_unit_smul_mem_not_mem_uniformizer_rescale
      (hyperbolicPlaneLattice (K := K)) hzNe
  let t : Kˣ := Classical.choose htExists
  have htSpec := Classical.choose_spec htExists
  have hxMem : (t : K) • z ∈ hyperbolicPlaneLattice (K := K) := by
    simpa [t] using htSpec.1
  have hxPrimitive :
      (t : K) • z ∉ rescale (uniformizerUnit K)
        (hyperbolicPlaneLattice (K := K)) := by
    simpa [t] using htSpec.2
  let x : Fin 2 → K := (t : K) • z
  have hxMem' : x ∈ hyperbolicPlaneLattice (K := K) := by
    exact hxMem
  have hx : ∀ i, x i ∈ IntegerRing K := by
    have h := (mem_omearaPlaneLattice_iff x).1 hxMem'
    intro i
    fin_cases i
    · exact h.1
    · exact h.2
  have hxIso : q.quadratic x = 0 := by
    change q.bilin ((t : K) • z) ((t : K) • z) = 0
    rw [LinearMap.BilinForm.smul_left,
      LinearMap.BilinForm.smul_right]
    change (t : K) * ((t : K) * q.bilin z z) = 0
    change q.bilin z z = 0 at hzIso
    rw [hzIso]
    ring
  have hxPrimitive' :
      x ∉ rescale (uniformizerUnit K)
        (BONG.binaryModelLattice (K := K)) := by
    simpa [x, BONG.binaryModelLattice, BONG.binaryModelBasis,
      hyperbolicPlaneLattice] using hxPrimitive
  have hxBinary : x ∈ BONG.binaryModelLattice (K := K) := by
    simpa [BONG.binaryModelLattice, BONG.binaryModelBasis,
      hyperbolicPlaneLattice] using hxMem'
  have hcoordinateUnit :
      IsValuationUnit K (x 0) ∨ IsValuationUnit K (x 1) :=
    (BONG.primitive_binaryModelLattice_iff_coordinate_unit
      x hxBinary).1 hxPrimitive'
  rcases hcoordinateUnit with hxzeroUnit | hxoneUnit
  · exact ⟨(evenGeneralPlaneHyperbolicIsometryOfFirstUnit
      eta zeta heta hzeta hnondegenerate x hx hxIso hxzeroUnit).symm⟩
  · let hnondegenerate' :
        ((2 : K) * zeta) * ((2 : K) * eta) ≠ 1 := by
        rwa [mul_comm]
    let swap := omearaGeneralPlaneSwapLatticeIsometry
        ((2 : K) * eta) ((2 : K) * zeta) hnondegenerate
    let x' : Fin 2 → K := ![x 1, x 0]
    have hx'eq : x' = swap.toLinearEquiv x := by
      rfl
    have hx' : ∀ i, x' i ∈ IntegerRing K := by
      intro i
      fin_cases i
      · simpa [x'] using hx 1
      · simpa [x'] using hx 0
    have hx'Iso :
        (QuadraticSpace.omearaGeneralPlane
          ((2 : K) * zeta) ((2 : K) * eta)
            hnondegenerate').quadratic x' = 0 := by
      calc
        _ = q.quadratic x := by
          rw [hx'eq]
          exact swap.map_quadratic x
        _ = 0 := hxIso
    have hx'zeroUnit : IsValuationUnit K (x' 0) := by
      simpa [x'] using hxoneUnit
    exact ⟨swap.trans
      (evenGeneralPlaneHyperbolicIsometryOfFirstUnit
        zeta eta hzeta heta hnondegenerate' x' hx' hx'Iso
          hx'zeroUnit).symm⟩

/-- The directly applicable form of O'Meara 93:11 used in 93:18(ii).
If one diagonal coefficient is in `2 * p` and the other is in `2 * o`,
then the discriminant unit `1 - alpha * beta` is a square by the local
square theorem.  Hence the binary space is isotropic and the integral
plane is hyperbolic. -/
theorem omeara9311_deep_even_plane_isIsometric
    (eta zeta : K)
    (heta : eta ∈ IntegerRing K)
    (hetaDeep : IsInMaximalIdeal K eta)
    (hzeta : zeta ∈ IntegerRing K)
    (hnondegenerate : ((2 : K) * eta) * ((2 : K) * zeta) ≠ 1) :
    IsIsometric
      (QuadraticSpace.omearaGeneralPlane
        ((2 : K) * eta) ((2 : K) * zeta) hnondegenerate)
      (QuadraticSpace.hyperbolicPlane (1 : Kˣ))
      (hyperbolicPlaneLattice (K := K))
      (hyperbolicPlaneLattice (K := K)) := by
  let alpha : K := (2 : K) * eta
  let beta : K := (2 : K) * zeta
  have hdiscNe : 1 - alpha * beta ≠ 0 := by
    intro hzero
    apply hnondegenerate
    change alpha * beta = 1
    exact (sub_eq_zero.mp hzero).symm
  let disc : Kˣ := Units.mk0 (1 - alpha * beta) hdiscNe
  have htwoE :
      (((2 * ramificationIndex K : ℕ) : ℤ) : WithTop ℤ) =
        ord K (2 : K) + ord K (2 : K) := by
    rw [show 2 * ramificationIndex K =
        ramificationIndex K + ramificationIndex K by omega]
    calc
      ((((ramificationIndex K + ramificationIndex K : ℕ) : ℤ) :
          WithTop ℤ)) =
          (((ramificationIndex K : ℕ) : ℤ) : WithTop ℤ) +
            (((ramificationIndex K : ℕ) : ℤ) : WithTop ℤ) := by
              norm_cast
      _ = ord K (2 : K) + ord K (2 : K) := by
        rw [ramificationIndex_spec]
  have hetaOrd : 0 < ord K eta := hetaDeep
  have hzetaOrd : 0 ≤ ord K zeta :=
    (mem_integerRing_iff K).1 hzeta
  have hproductDeep :
      ord K (2 : K) + ord K (2 : K) <
        (ord K (2 : K) + ord K eta) +
          (ord K (2 : K) + ord K zeta) := by
    rw [← ramificationIndex_spec]
    cases hetaValue : ord K eta with
    | top => simp [hetaValue]
    | coe etaOrder =>
        cases hzetaValue : ord K zeta with
        | top => simp [hzetaValue]
        | coe zetaOrder =>
            rw [hetaValue] at hetaOrd
            rw [hzetaValue] at hzetaOrd
            have hetaOrderPos : 0 < etaOrder := by
              exact_mod_cast hetaOrd
            have hzetaOrderNonneg : 0 ≤ zetaOrder := by
              exact_mod_cast hzetaOrd
            norm_cast
            omega
  have hdeep :
      (((2 * ramificationIndex K : ℕ) : ℤ) : WithTop ℤ) <
        ord K ((disc : K) - 1) := by
    rw [htwoE]
    change ord K (2 : K) + ord K (2 : K) <
      ord K ((1 - alpha * beta) - 1)
    rw [show (1 - alpha * beta) - 1 = -(alpha * beta) by ring,
      ord_neg, ord_mul]
    dsimp [alpha, beta]
    rw [ord_mul, ord_mul]
    exact hproductDeep
  have hdiscSquare : IsSquare disc :=
    isSquare_of_ord_sub_one_gt_two_mul_e K disc hdeep
  rcases hdiscSquare with ⟨s, hs⟩
  have hsField : (s : K) ^ 2 = 1 - alpha * beta := by
    have h := congrArg (fun z : Kˣ ↦ (z : K)) hs
    simpa [disc, pow_two] using h.symm
  have hisotropic : ∃ z : Fin 2 → K, z ≠ 0 ∧
      (QuadraticSpace.omearaGeneralPlane
        ((2 : K) * eta) ((2 : K) * zeta) hnondegenerate).quadratic z = 0 := by
    by_cases hbeta : beta = 0
    · let z : Fin 2 → K := ![0, 1]
      refine ⟨z, ?_, ?_⟩
      · intro hz
        have hone := congrFun hz 1
        simp [z] at hone
      · rw [QuadraticSpace.quadratic,
          QuadraticSpace.omearaGeneralPlane_bilin_apply]
        simp [z, beta] at hbeta ⊢
        exact hbeta
    · let t : K := ((s : K) - 1) / beta
      let z : Fin 2 → K := ![1, t]
      refine ⟨z, ?_, ?_⟩
      · intro hz
        have hone := congrFun hz 0
        simp [z] at hone
      · rw [QuadraticSpace.quadratic,
          QuadraticSpace.omearaGeneralPlane_bilin_apply]
        change alpha * z 0 * z 0 + z 0 * z 1 + z 1 * z 0 +
          beta * z 1 * z 1 = 0
        simp only [z, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, one_mul, t]
        field_simp [hbeta]
        have hcalc :
            alpha * beta + ((s : K) - 1) + ((s : K) - 1) +
                ((s : K) - 1) ^ 2 = 0 := by
          calc
            _ = alpha * beta + (s : K) ^ 2 - 1 := by ring
            _ = 0 := by rw [hsField]; ring
        simpa using hcalc
  exact omeara9311_isotropic_even_plane_isIsometric
    eta zeta heta hzeta hnondegenerate hisotropic

/-- A chosen integral isometry in the isotropic branch of O'Meara 93:11. -/
noncomputable def omeara9311_isotropic_even_plane
    (eta zeta : K) (heta : eta ∈ IntegerRing K)
    (hzeta : zeta ∈ IntegerRing K)
    (hnondegenerate : ((2 : K) * eta) * ((2 : K) * zeta) ≠ 1)
    (hisotropic : ∃ z : Fin 2 → K, z ≠ 0 ∧
      (QuadraticSpace.omearaGeneralPlane
        ((2 : K) * eta) ((2 : K) * zeta) hnondegenerate).quadratic z = 0) :
    Isometry
      (QuadraticSpace.omearaGeneralPlane
        ((2 : K) * eta) ((2 : K) * zeta) hnondegenerate)
      (QuadraticSpace.hyperbolicPlane (1 : Kˣ))
      (hyperbolicPlaneLattice (K := K))
      (hyperbolicPlaneLattice (K := K)) :=
  Classical.choice
    (omeara9311_isotropic_even_plane_isIsometric
      eta zeta heta hzeta hnondegenerate hisotropic)

end Lattice

end Bong
