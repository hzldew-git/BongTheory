/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009WeightIdealIsometry
import Bong.Bong.Beli2009OrthogonalIdealProof
import Bong.Bong.BeliLemma45Proof
import Bong.Lattice.DeterminantIsometry
import Bong.Lattice.NormGeneratorIsometry
import Bong.Lattice.OmearaBinaryGeneralPlane
import Bong.Lattice.OmearaEvenPlaneNormalization
import Bong.Lattice.OrthogonalDecompositionVolume

/-!
# O'Meara 93:10 with the weight coefficient displayed

For a binary unimodular lattice, start with an actual norm-generator vector.
It is primitive, hence in integral coordinates one of its two coordinates is
a valuation unit.  We complete it to an integral basis.  O'Meara 93:4 then
allows an integral shear which puts the second norm in the weight ideal.
When the weight is `2s`, the new second norm is even; the unimodular Gram
determinant forces the mixed pairing to be a unit, so it can be normalized to
one.  The result is the exact `A(a, 2*zeta)` presentation used in 93:18(ii).
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

/-! ## Integral binary bases -/

/-- A primitive integral binary vector together with a chosen integral
partner whose column determinant is a valuation unit. -/
structure PrimitiveBinaryPartnerData (x : Fin 2 → K) where
  partner : Fin 2 → K
  partner_integral : ∀ i, partner i ∈ IntegerRing K
  determinant_unit : IsValuationUnit K (binaryColumnDeterminant x partner)

/-- A primitive vector of the standard binary lattice can be completed to
an integral basis. -/
noncomputable def primitiveBinaryPartnerData
    (x : Fin 2 → K) (hx : x ∈ hyperbolicPlaneLattice (K := K))
    (hprimitive : x ∉ rescale (uniformizerUnit K)
      (hyperbolicPlaneLattice (K := K))) :
    PrimitiveBinaryPartnerData x := by
  have hxBinary : x ∈ BONG.binaryModelLattice (K := K) := by
    simpa [BONG.binaryModelLattice, BONG.binaryModelBasis,
      hyperbolicPlaneLattice] using hx
  have hprimitiveBinary : x ∉ rescale (uniformizerUnit K)
      (BONG.binaryModelLattice (K := K)) := by
    simpa [BONG.binaryModelLattice, BONG.binaryModelBasis,
      hyperbolicPlaneLattice] using hprimitive
  have hcoordinateUnit :
      IsValuationUnit K (x 0) ∨ IsValuationUnit K (x 1) :=
    (BONG.primitive_binaryModelLattice_iff_coordinate_unit
      x hxBinary).1 hprimitiveBinary
  by_cases hzero : IsValuationUnit K (x 0)
  · let y : Fin 2 → K := ![0, (x 0)⁻¹]
    have hinvUnit : IsValuationUnit K (x 0)⁻¹ := by
      simpa [IsValuationUnit, AddValuation.map_inv, hzero]
    have hy : ∀ i, y i ∈ IntegerRing K := by
      intro i
      fin_cases i
      · simp [y]
      · exact (mem_integerRing_iff K).2 hinvUnit.ge
    have hdet : binaryColumnDeterminant x y = 1 := by
      dsimp [binaryColumnDeterminant, y]
      field_simp [ne_zero_of_isValuationUnit hzero]
      ring
    exact ⟨y, hy, by rw [hdet]; simp [IsValuationUnit]⟩
  · have hone : IsValuationUnit K (x 1) :=
      hcoordinateUnit.resolve_left hzero
    let y : Fin 2 → K := ![(x 1)⁻¹, 0]
    have hinvUnit : IsValuationUnit K (x 1)⁻¹ := by
      simpa [IsValuationUnit, AddValuation.map_inv, hone]
    have hy : ∀ i, y i ∈ IntegerRing K := by
      intro i
      fin_cases i
      · exact (mem_integerRing_iff K).2 hinvUnit.ge
      · simp [y]
    have hdet : binaryColumnDeterminant x y = -1 := by
      dsimp [binaryColumnDeterminant, y]
      field_simp [ne_zero_of_isValuationUnit hone]
      ring
    exact ⟨y, hy, by rw [hdet]; simp [IsValuationUnit]⟩

/-- A binary column transformation with integral columns and unit
determinant preserves the standard integral lattice in both directions. -/
theorem binaryColumnLinearEquiv_mem_iff
    (x y : Fin 2 → K)
    (hx : ∀ i, x i ∈ IntegerRing K)
    (hy : ∀ i, y i ∈ IntegerRing K)
    (hdetUnit : IsValuationUnit K (binaryColumnDeterminant x y))
    (z : Fin 2 → K) :
    z ∈ hyperbolicPlaneLattice (K := K) ↔
      binaryColumnLinearEquiv x y
        (ne_zero_of_isValuationUnit hdetUnit) z ∈
          hyperbolicPlaneLattice (K := K) := by
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
    have hinv := binaryColumnLinearEquiv_symm_integral
      x y hx hy hdetUnit hz
    have hzero := hinv 0
    have hone := hinv 1
    simpa [e] using And.intro hzero hone

/-- The basis whose columns are an integral unit-determinant pair generates
the standard binary lattice. -/
theorem basisLattice_binaryColumn_eq
    (x y : Fin 2 → K)
    (hx : ∀ i, x i ∈ IntegerRing K)
    (hy : ∀ i, y i ∈ IntegerRing K)
    (hdetUnit : IsValuationUnit K (binaryColumnDeterminant x y)) :
    basisLattice ((Pi.basisFun K (Fin 2)).map
      (binaryColumnLinearEquiv x y
        (ne_zero_of_isValuationUnit hdetUnit))) =
      hyperbolicPlaneLattice (K := K) := by
  let e := binaryColumnLinearEquiv x y
    (ne_zero_of_isValuationUnit hdetUnit)
  calc
    basisLattice ((Pi.basisFun K (Fin 2)).map e) =
        map e (basisLattice (Pi.basisFun K (Fin 2))) :=
      (map_basisLattice_eq_basisLattice_map
        (Pi.basisFun K (Fin 2)) e).symm
    _ = hyperbolicPlaneLattice (K := K) := by
      apply Lattice.ext
      ext z
      change z ∈ map e (basisLattice (Pi.basisFun K (Fin 2))) ↔
        z ∈ hyperbolicPlaneLattice (K := K)
      rw [mem_map_iff]
      change e.symm z ∈ hyperbolicPlaneLattice (K := K) ↔
        z ∈ hyperbolicPlaneLattice (K := K)
      have h := binaryColumnLinearEquiv_mem_iff
        x y hx hy hdetUnit (e.symm z)
      simpa [e] using h

/-- Equal Gram entries in an integral unit-determinant binary basis give an
integral isometry from the corresponding general O'Meara plane. -/
noncomputable def generalPlaneLatticeIsometryOfIntegralBinaryBasis
    (q : QuadraticSpace K (Fin 2 → K))
    (x y : Fin 2 → K)
    (hx : ∀ i, x i ∈ IntegerRing K)
    (hy : ∀ i, y i ∈ IntegerRing K)
    (hdetUnit : IsValuationUnit K (binaryColumnDeterminant x y))
    (alpha beta : K) (hnondegenerate : alpha * beta ≠ 1)
    (hxx : q.bilin x x = alpha)
    (hxy : q.bilin x y = 1)
    (hyy : q.bilin y y = beta) :
    Isometry
      (QuadraticSpace.omearaGeneralPlane alpha beta hnondegenerate) q
      (hyperbolicPlaneLattice (K := K))
      (hyperbolicPlaneLattice (K := K)) where
  toLinearEquiv := binaryColumnLinearEquiv x y
    (ne_zero_of_isValuationUnit hdetUnit)
  map_bilin z w := by
    rw [QuadraticSpace.omearaGeneralPlane_bilin_apply]
    change q.bilin (z 0 • x + z 1 • y)
      (w 0 • x + w 1 • y) = _
    simp only [LinearMap.BilinForm.add_left,
      LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.smul_left,
      LinearMap.BilinForm.smul_right, smul_eq_mul]
    rw [hxx, hxy, q.isSymm.eq y x, hxy, hyy]
    ring
  map_mem z :=
    binaryColumnLinearEquiv_mem_iff x y hx hy hdetUnit z

/-! ## Weight-adapted coordinates on the standard lattice -/

/-- Exact output of O'Meara 93:10 in the `wL = 2sL` branch. -/
structure Omeara9310WeightCoordinatesData
    (q : QuadraticSpace K (Fin 2 → K)) (x : Fin 2 → K) where
  zeta : K
  zeta_integral : zeta ∈ IntegerRing K
  nondegenerate : q.quadratic x * ((2 : K) * zeta) ≠ 1
  isometry : Isometry q
    (QuadraticSpace.omearaGeneralPlane
      (q.quadratic x) ((2 : K) * zeta) nondegenerate)
    (hyperbolicPlaneLattice (K := K))
    (hyperbolicPlaneLattice (K := K))

/-- O'Meara 93:10 for a standard binary unimodular lattice whose weight is
`2s`, with a prescribed actual norm-generator vector as first vector. -/
noncomputable def omeara9310WeightCoordinatesStandard
    (q : QuadraticSpace K (Fin 2 → K))
    (x : Fin 2 → K)
    (hmodular : IsModular q (hyperbolicPlaneLattice (K := K)) (1 : Kˣ))
    (hgenerator : IsNormGenerator q
      (hyperbolicPlaneLattice (K := K)) x)
    (hweight : weightIdeal q (hyperbolicPlaneLattice (K := K)) =
      twoScaleIdeal q (hyperbolicPlaneLattice (K := K))) :
    Omeara9310WeightCoordinatesData q x := by
  let H := hyperbolicPlaneLattice (K := K)
  have hfin : 0 < finrank K (Fin 2 → K) := by simp
  have hxAnisotropic : q.IsAnisotropic x :=
    hgenerator.isAnisotropic_of_finrank_pos hfin
  have hxPrimitive : x ∉ rescale (uniformizerUnit K) H :=
    hgenerator.not_mem_uniformizer_rescale hxAnisotropic
  have hxCoordinates : ∀ i, x i ∈ IntegerRing K := by
    have h := (mem_omearaPlaneLattice_iff x).1 hgenerator.mem
    intro i
    fin_cases i
    · exact h.1
    · exact h.2
  let P := primitiveBinaryPartnerData x hgenerator.mem hxPrimitive
  let y₀ := P.partner
  have hy₀Mem : y₀ ∈ H := by
    rw [mem_omearaPlaneLattice_iff]
    exact ⟨P.partner_integral 0, P.partner_integral 1⟩
  let a : Kˣ := Units.mk0 (q.quadratic x) hxAnisotropic
  have ha : IsNormGeneratorValue q H a :=
    hgenerator.isNormGeneratorValue hxAnisotropic
  have hy₀Group : q.quadratic y₀ ∈ normGroupSet q H := by
    refine ⟨y₀, hy₀Mem, 0, Submodule.zero_mem _, ?_⟩
    simp
  rw [normGroupSet_eq_integralSquareCoset_weightIdeal a ha] at hy₀Group
  let c : IntegerRing K := Classical.choose hy₀Group
  have hcSpec := Classical.choose_spec hy₀Group
  let eta : K := Classical.choose hcSpec
  have hetaSpec := Classical.choose_spec hcSpec
  have heta : eta ∈ weightIdeal q H := hetaSpec.1
  have hqeta : q.quadratic y₀ = (a : K) * (c : K) ^ 2 + eta :=
    hetaSpec.2
  let y : Fin 2 → K := y₀ + (c : K) • x
  have hyMem : y ∈ H :=
    H.add_mem hy₀Mem (H.smul_mem c hgenerator.mem)
  have hyCoordinates : ∀ i, y i ∈ IntegerRing K := by
    have h := (mem_omearaPlaneLattice_iff y).1 hyMem
    intro i
    fin_cases i
    · exact h.1
    · exact h.2
  have hqyWeight : q.quadratic y ∈ weightIdeal q H := by
    have hxScale : q.quadratic x ∈ scaleIdeal q H :=
      bilin_mem_scaleIdeal_of_mem q H hgenerator.mem hgenerator.mem
    have hxy₀Scale : q.bilin x y₀ ∈ scaleIdeal q H :=
      bilin_mem_scaleIdeal_of_mem q H hgenerator.mem hy₀Mem
    have hheadTwo : (2 : K) * (c : K) ^ 2 * q.quadratic x ∈
        twoScaleIdeal q H := by
      refine ⟨(c ^ 2) • q.quadratic x,
        (scaleIdeal q H).smul_mem (c ^ 2) hxScale, ?_⟩
      change (2 : K) * ((c : K) ^ 2 * q.quadratic x) = _
      ring
    have hmixedTwo : (2 : K) * (c : K) * q.bilin x y₀ ∈
        twoScaleIdeal q H := by
      refine ⟨c • q.bilin x y₀,
        (scaleIdeal q H).smul_mem c hxy₀Scale, ?_⟩
      change (2 : K) * ((c : K) * q.bilin x y₀) = _
      ring
    have hheadWeight := twoScaleIdeal_le_weightIdeal q H hheadTwo
    have hmixedWeight := twoScaleIdeal_le_weightIdeal q H hmixedTwo
    have hsum := (weightIdeal q H).add_mem
      ((weightIdeal q H).add_mem hheadWeight heta) hmixedWeight
    rw [q.quadratic_add, q.quadratic_smul,
      LinearMap.BilinForm.smul_right, q.isSymm.eq y₀ x, hqeta]
    have hqx : q.quadratic x = (a : K) := rfl
    rw [hqx]
    rw [hqx] at hsum
    convert hsum using 1 <;> ring
  have hqyTwo : q.quadratic y ∈ twoScaleIdeal q H := by
    rw [← hweight]
    exact hqyWeight
  have hscale : scaleIdeal q H = principalIdeal (K := K) (1 : K) :=
    hmodular.scaleIdeal_eq_principal (by simp)
  have htwoScale : twoScaleIdeal q H =
      principalIdeal (K := K) (2 : K) := by
    rw [twoScaleIdeal, hscale, twiceIdeal_principalIdeal]
    simp
  rw [htwoScale, principalIdeal, Submodule.mem_span_singleton] at hqyTwo
  let zetaO : IntegerRing K := Classical.choose hqyTwo
  have hzetaEq := Classical.choose_spec hqyTwo
  let zeta : K := zetaO
  have hzeta : zeta ∈ IntegerRing K := zetaO.property
  have hqy : q.quadratic y = (2 : K) * zeta := by
    have hzetaEqField : (zetaO : K) * (2 : K) = q.quadratic y := by
      change (zetaO : K) * (2 : K) = q.quadratic y at hzetaEq
      exact hzetaEq
    calc
      q.quadratic y = (zetaO : K) * (2 : K) := hzetaEqField.symm
      _ = (2 : K) * zeta := by dsimp [zeta]; ring
  have hdetY : binaryColumnDeterminant x y =
      binaryColumnDeterminant x y₀ := by
    dsimp [binaryColumnDeterminant, y]
    ring
  have hdetYUnit : IsValuationUnit K (binaryColumnDeterminant x y) := by
    rw [hdetY]
    exact P.determinant_unit
  let e := binaryColumnLinearEquiv x y
    (ne_zero_of_isValuationUnit hdetYUnit)
  let b : Basis (Fin 2) K (Fin 2 → K) :=
    (Pi.basisFun K (Fin 2)).map e
  have hbzero : b 0 = x := by
    funext i
    fin_cases i <;> simp [b, e, binaryColumnLinearEquiv]
  have hbone : b 1 = y := by
    funext i
    fin_cases i <;> simp [b, e, binaryColumnLinearEquiv]
  have hbLattice : basisLattice b = H := by
    exact basisLattice_binaryColumn_eq x y hxCoordinates hyCoordinates hdetYUnit
  have hvolumeZero : volumeOrder q (basisLattice b) = 0 := by
    rw [hbLattice, hmodular.volumeOrder_eq]
    simp [ordUnit]
  have hgramOrder : ord K
      (LinearMap.BilinForm.toMatrix b q.bilin).det = 0 := by
    rw [← coe_volumeOrder_basisLattice_eq_ord_det_toMatrix q b,
      hvolumeZero]
    rfl
  have hgram :
      (LinearMap.BilinForm.toMatrix b q.bilin).det =
        q.quadratic x * q.quadratic y - (q.bilin x y) ^ 2 := by
    rw [Matrix.det_fin_two]
    simp only [LinearMap.BilinForm.toMatrix_apply, hbzero, hbone]
    change q.quadratic x * q.quadratic y -
      q.bilin x y * q.bilin y x = _
    rw [q.isSymm.eq y x, pow_two]
  have hgramUnit : IsValuationUnit K
      (q.quadratic x * q.quadratic y - (q.bilin x y) ^ 2) := by
    rw [← hgram]
    exact hgramOrder
  have hqxIntegral : q.quadratic x ∈ IntegerRing K := by
    change q.bilin x x ∈ IntegerRing K
    apply mem_integerRing_of_mul_mem_principalIdeal (one_ne_zero : (1 : K) ≠ 0)
    simpa only [one_mul, ← hscale] using
      (bilin_mem_scaleIdeal_of_mem q H hgenerator.mem hgenerator.mem)
  have hcrossIntegral : q.bilin x y ∈ IntegerRing K := by
    apply mem_integerRing_of_mul_mem_principalIdeal (one_ne_zero : (1 : K) ≠ 0)
    simpa only [one_mul, ← hscale] using
      (bilin_mem_scaleIdeal_of_mem q H hgenerator.mem hyMem)
  have hqyMax : IsInMaximalIdeal K (q.quadratic y) := by
    rw [hqy]
    exact isInMaximalIdeal_mul_isIntegral K (two_isInMaximalIdeal K)
      ((mem_integerRing_iff K).1 hzeta)
  have hproductMax : IsInMaximalIdeal K
      (q.quadratic x * q.quadratic y) := by
    rw [mul_comm]
    exact isInMaximalIdeal_mul_isIntegral K hqyMax
      ((mem_integerRing_iff K).1 hqxIntegral)
  have hcrossUnit : IsValuationUnit K (q.bilin x y) := by
    by_contra hnot
    have hcrossNonneg : (0 : WithTop Int) ≤ ord K (q.bilin x y) :=
      (mem_integerRing_iff K).1 hcrossIntegral
    have hcrossMax : IsInMaximalIdeal K (q.bilin x y) := by
      rw [IsInMaximalIdeal]
      exact lt_of_le_of_ne hcrossNonneg (Ne.symm hnot)
    have hcrossSqMax : IsInMaximalIdeal K ((q.bilin x y) ^ 2) := by
      rw [pow_two]
      exact isInMaximalIdeal_mul_isIntegral K hcrossMax
        ((mem_integerRing_iff K).1 hcrossIntegral)
    have hdetMax := isInMaximalIdeal_sub hproductMax hcrossSqMax
    rw [IsInMaximalIdeal, hgramUnit] at hdetMax
    exact (lt_irrefl 0 hdetMax)
  have hcrossNe : q.bilin x y ≠ 0 :=
    ne_zero_of_isValuationUnit hcrossUnit
  have hcrossInvUnit : IsValuationUnit K (q.bilin x y)⁻¹ := by
    simpa [IsValuationUnit, AddValuation.map_inv, hcrossUnit]
  have hcrossInvIntegral : (q.bilin x y)⁻¹ ∈ IntegerRing K :=
    (mem_integerRing_iff K).2 hcrossInvUnit.ge
  let y' : Fin 2 → K := (q.bilin x y)⁻¹ • y
  have hy'Coordinates : ∀ i, y' i ∈ IntegerRing K := by
    intro i
    change (q.bilin x y)⁻¹ * y i ∈ IntegerRing K
    exact (IntegerRing K).toSubring.mul_mem hcrossInvIntegral
      (hyCoordinates i)
  have hdetY' : binaryColumnDeterminant x y' =
      (q.bilin x y)⁻¹ * binaryColumnDeterminant x y := by
    dsimp [binaryColumnDeterminant, y']
    ring
  have hdetY'Unit : IsValuationUnit K (binaryColumnDeterminant x y') := by
    rw [hdetY']
    exact isValuationUnit_mul hcrossInvUnit hdetYUnit
  let zeta' : K := (q.bilin x y)⁻¹ ^ 2 * zeta
  have hzeta' : zeta' ∈ IntegerRing K := by
    exact (IntegerRing K).toSubring.mul_mem
      ((IntegerRing K).toSubring.pow_mem hcrossInvIntegral 2) hzeta
  have hxy' : q.bilin x y' = 1 := by
    dsimp [y']
    rw [LinearMap.BilinForm.smul_right]
    change (q.bilin x y)⁻¹ * q.bilin x y = 1
    exact inv_mul_cancel₀ hcrossNe
  have hqy' : q.quadratic y' = (2 : K) * zeta' := by
    dsimp [y', zeta']
    rw [q.quadratic_smul, hqy]
    ring
  have hnondegenerate : q.quadratic x * ((2 : K) * zeta') ≠ 1 := by
    let e' := binaryColumnLinearEquiv x y'
      (ne_zero_of_isValuationUnit hdetY'Unit)
    let b' : Basis (Fin 2) K (Fin 2 → K) :=
      (Pi.basisFun K (Fin 2)).map e'
    have hb'zero : b' 0 = x := by
      funext i
      fin_cases i <;> simp [b', e', binaryColumnLinearEquiv]
    have hb'one : b' 1 = y' := by
      funext i
      fin_cases i <;> simp [b', e', binaryColumnLinearEquiv]
    have hdetNe :=
      (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b').mp
        q.nondegenerate
    intro hone
    apply hdetNe
    rw [Matrix.det_fin_two]
    simp only [LinearMap.BilinForm.toMatrix_apply, hb'zero, hb'one]
    change q.quadratic x * q.quadratic y' -
      q.bilin x y' * q.bilin y' x = 0
    rw [q.isSymm.eq y' x, hxy', hqy', hone]
    ring
  let forward := generalPlaneLatticeIsometryOfIntegralBinaryBasis
    q x y' hxCoordinates hy'Coordinates hdetY'Unit
      (q.quadratic x) ((2 : K) * zeta') hnondegenerate
      rfl hxy' hqy'
  exact
    { zeta := zeta'
      zeta_integral := hzeta'
      nondegenerate := hnondegenerate
      isometry := forward.symm }

/-! ## Transport back to an arbitrary binary modular lattice -/

/-- Coordinate output of 93:10 on an arbitrary binary lattice. -/
structure Omeara9310BinaryWeightData
    (q : QuadraticSpace K V) (L : Lattice K V) (x : V) where
  zeta : K
  zeta_integral : zeta ∈ IntegerRing K
  nondegenerate : q.quadratic x * ((2 : K) * zeta) ≠ 1
  isometry : Isometry q
    (QuadraticSpace.omearaGeneralPlane
      (q.quadratic x) ((2 : K) * zeta) nondegenerate)
    L (hyperbolicPlaneLattice (K := K))

/-- O'Meara 93:10, transported from the standard coordinate calculation.
No basis-selection assumption remains in the result. -/
noncomputable def omeara9310BinaryWeightData
    (q : QuadraticSpace K V) (L : Lattice K V) (x : V)
    (hmodular : IsModular q L (1 : Kˣ))
    (hrank : finrank K V = 2)
    (hgenerator : IsNormGenerator q L x)
    (hweight : weightIdeal q L = twoScaleIdeal q L) :
    Omeara9310BinaryWeightData q L x := by
  let C := BinaryModularGeneralPlaneData.ofModular
    q L (1 : Kˣ) hmodular hrank
  let model := QuadraticSpace.omearaGeneralPlane
    C.leftCoefficient C.rightCoefficient C.nondegenerate
  let displayed : Isometry q model L
      (hyperbolicPlaneLattice (K := K)) :=
    C.isometry.trans
      (Isometry.rescaleUnitOne model
        (hyperbolicPlaneLattice (K := K)))
  let x' := displayed.toLinearEquiv x
  have hgenerator' : IsNormGenerator model
      (hyperbolicPlaneLattice (K := K)) x' :=
    hgenerator.mapLatticeIsometry displayed
  have hmodelModular : IsModular model
      (hyperbolicPlaneLattice (K := K)) (1 : Kˣ) :=
    hmodular.mapLatticeIsometry displayed
  have hscaleTransport : scaleIdeal model
      (hyperbolicPlaneLattice (K := K)) = scaleIdeal q L := by
    rw [← displayed.map_eq]
    exact scaleIdeal_map_isometry displayed.toQuadraticSpaceIsometry L
  have hweightTransport : weightIdeal model
      (hyperbolicPlaneLattice (K := K)) = weightIdeal q L :=
    weightIdeal_eq_of_isometry displayed (by omega)
  have hmodelWeight : weightIdeal model
      (hyperbolicPlaneLattice (K := K)) =
        twoScaleIdeal model (hyperbolicPlaneLattice (K := K)) := by
    calc
      weightIdeal model (hyperbolicPlaneLattice (K := K)) =
          weightIdeal q L := hweightTransport
      _ = twoScaleIdeal q L := hweight
      _ = twoScaleIdeal model (hyperbolicPlaneLattice (K := K)) := by
        unfold twoScaleIdeal
        rw [hscaleTransport]
  let D := omeara9310WeightCoordinatesStandard
    model x' hmodelModular hgenerator' hmodelWeight
  have hquad : model.quadratic x' = q.quadratic x :=
    displayed.map_quadratic x
  have hnondegenerate : q.quadratic x * ((2 : K) * D.zeta) ≠ 1 := by
    simpa only [hquad] using D.nondegenerate
  let adjusted : Isometry model
      (QuadraticSpace.omearaGeneralPlane
        (q.quadratic x) ((2 : K) * D.zeta) hnondegenerate)
      (hyperbolicPlaneLattice (K := K))
      (hyperbolicPlaneLattice (K := K)) := by
    exact
      { toLinearEquiv := D.isometry.toLinearEquiv
        map_bilin := by
          intro z w
          have h := D.isometry.map_bilin z w
          rw [QuadraticSpace.omearaGeneralPlane_bilin_apply] at h ⊢
          simpa only [hquad] using h
        map_mem := D.isometry.map_mem }
  exact
    { zeta := D.zeta
      zeta_integral := D.zeta_integral
      nondegenerate := hnondegenerate
      isometry := displayed.trans adjusted }

end Lattice

end Bong
