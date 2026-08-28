/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009BinaryWeightProof
import Bong.Lattice.OmearaBinaryGeneralPlane
import Bong.Lattice.AsymmetricBinaryModular
import Bong.Lattice.ModularPrimitivePairing
import Bong.Lattice.ModularSplitting
import Bong.Lattice.OrthogonalDecompositionProduct
import Bong.Lattice.OrthogonalProductIsometry

/-!
# Weight-adapted binary planes in the odd branch of O'Meara 93:18

Below the terminal ideal `2sL`, the canonical weight is witnessed by an
actual quadratic value.  Its defining minimality forces the witnessing
vector to be primitive: otherwise division by one uniformizer would give a
smaller norm-group value of the same opposite parity.  In a unimodular
lattice that primitive vector extends to a scale-generating binary basis and
therefore splits a displayed plane whose first coefficient has exactly the
weight order.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- A norm-group value whose parity is opposite to the norm order cannot
occur below the canonical weight order. -/
theorem weightIdealOrder_le_ordUnit_of_mem_normGroupSet_of_odd
    (a z : Kˣ) (ha : IsNormGeneratorValue q L a)
    (hz : (z : K) ∈ normGroupSet q L)
    (hodd : Odd (ordUnit K a + ordUnit K z)) :
    weightIdealOrder q L ≤ ordUnit K z := by
  have hnormLe : canonicalNormOrder q L ≤ ordUnit K z :=
    canonicalNormOrder_le_ordUnit_of_mem_normGroupSet ha hz
  have haOrder : ordUnit K a = canonicalNormOrder q L :=
    ordUnit_eq_canonicalNormOrder ha
  let n : Nat := Int.toNat (ordUnit K z - canonicalNormOrder q L)
  have hdiffNonneg : 0 ≤ ordUnit K z - canonicalNormOrder q L := by
    omega
  have hnCast : (n : Int) =
      ordUnit K z - canonicalNormOrder q L := by
    exact Int.toNat_of_nonneg hdiffNonneg
  have hdiffOdd : Odd (ordUnit K z - canonicalNormOrder q L) := by
    rcases hodd with ⟨k, hk⟩
    refine ⟨k - canonicalNormOrder q L, ?_⟩
    rw [haOrder] at hk
    omega
  have hnOddInt : Odd (n : Int) := by
    rw [hnCast]
    exact hdiffOdd
  have hnOdd : Odd n := (Int.odd_coe_nat n).mp hnOddInt
  have hnOrder : ordUnit K z =
      canonicalNormOrder q L + (n : Int) := by
    omega
  have hoffset : canonicalWeightOffset q L ≤ n :=
    canonicalWeightOffset_le_of_oppositeParityOrder
      ⟨hnOdd, z, hz, hnOrder⟩
  rw [weightIdealOrder_eq_canonicalWeightOrder a ha,
    canonicalWeightOrder_eq ha]
  exact_mod_cast (show
    canonicalNormOrder q L + (canonicalWeightOffset q L : Int) ≤
      ordUnit K z by omega)

/-- A vector realizing the nonterminal odd weight order is primitive. -/
theorem primitive_of_quadratic_order_eq_weightIdealOrder
    (hmodular : IsModular q L (1 : Kˣ))
    (a : Kˣ) (ha : IsNormGeneratorValue q L a)
    {x : V} (hx : x ∈ L) (hxne : q.quadratic x ≠ 0)
    (hxOrder : ord K (q.quadratic x) =
      ((weightIdealOrder q L : Int) : WithTop Int))
    (hodd : Odd (ordUnit K a + weightIdealOrder q L)) :
    x ∉ rescale (uniformizerUnit K) L := by
  intro hxScaled
  rw [mem_rescale_iff] at hxScaled
  rcases hxScaled with ⟨y, hy, hxy⟩
  have hqyNe : q.quadratic y ≠ 0 := by
    intro hzero
    apply hxne
    rw [← hxy, q.quadratic_smul, hzero, mul_zero]
  let xu : Kˣ := Units.mk0 (q.quadratic x) hxne
  let yu : Kˣ := Units.mk0 (q.quadratic y) hqyNe
  have hpiOrder : ordUnit K (uniformizerUnit K) = 1 := by
    simpa [uniformizerPowerUnit] using
      (ordUnit_uniformizerPowerUnit (K := K) (1 : Int))
  have hunitEq : xu = uniformizerUnit K ^ 2 * yu := by
    apply Units.ext
    change q.quadratic x =
      (uniformizerUnit K : K) ^ 2 * q.quadratic y
    rw [← hxy, q.quadratic_smul]
  have hxuOrder : ordUnit K xu = weightIdealOrder q L := by
    apply WithTop.coe_injective
    rw [coe_ordUnit]
    simpa only [xu, Units.val_mk0] using hxOrder
  have hyuOrder : ordUnit K yu = weightIdealOrder q L - 2 := by
    have h := congrArg (ordUnit K) hunitEq
    rw [ordUnit_mul, ordUnit_pow, hpiOrder, hxuOrder] at h
    omega
  have hyGroup : (yu : K) ∈ normGroupSet q L := by
    refine ⟨y, hy, 0, Submodule.zero_mem _, ?_⟩
    simp [yu]
  have hyOdd : Odd (ordUnit K a + ordUnit K yu) := by
    rcases hodd with ⟨k, hk⟩
    refine ⟨k - 1, ?_⟩
    rw [hyuOrder]
    omega
  have hlower := weightIdealOrder_le_ordUnit_of_mem_normGroupSet_of_odd
    a yu ha hyGroup hyOdd
  rw [hyuOrder] at hlower
  omega

/-- A binary summand whose first basis vector realizes the canonical weight
order.  The basis is normalized so that its mixed pairing is exactly one. -/
structure WeightAdaptedBinarySplittingData
    (q : QuadraticSpace K V) (L : Lattice K V) where
  decomposition : OrthogonalDecomposition q L 2
  first_rank : finrank K (decomposition.component 0).carrier = 2
  first_modular : IsModular
    (decomposition.component 0).space
    (decomposition.component 0).lattice (1 : Kˣ)
  complement_modular : IsModular
    (decomposition.component 1).space
    (decomposition.component 1).lattice (1 : Kˣ)
  basis : Basis (Fin 2) K (decomposition.component 0).carrier
  basis_lattice : basisLattice basis =
    (decomposition.component 0).lattice
  pairing_eq : (decomposition.component 0).space.bilin
    (basis 0) (basis 1) = (1 : K)
  first_ne : (decomposition.component 0).space.quadratic (basis 0) ≠ 0
  first_order : ord K
      ((decomposition.component 0).space.quadratic (basis 0)) =
    ((weightIdealOrder q L : Int) : WithTop Int)

namespace WeightAdaptedBinarySplittingData

variable (D : WeightAdaptedBinarySplittingData q L)

/-- O'Meara coordinates of the displayed binary summand. -/
noncomputable def coordinates : BinaryModularGeneralPlaneData
    (D.decomposition.component 0).space
    (D.decomposition.component 0).lattice (1 : Kˣ) :=
  BinaryModularGeneralPlaneData.ofBasis
    (D.decomposition.component 0).space
    (D.decomposition.component 0).lattice (1 : Kˣ)
    D.first_modular D.basis D.basis_lattice D.pairing_eq

/-- The first O'Meara coefficient is exactly the value of the selected
weight vector. -/
theorem coordinates_leftCoefficient_eq :
    D.coordinates.leftCoefficient =
      (D.decomposition.component 0).space.quadratic (D.basis 0) := by
  rw [D.coordinates.leftCoefficient_eq]
  have hbasis : D.coordinates.basis = D.basis := rfl
  rw [hbasis]
  simp [omearaLeftCoefficient]

theorem coordinates_leftCoefficient_ne :
    D.coordinates.leftCoefficient ≠ 0 := by
  rw [D.coordinates_leftCoefficient_eq]
  exact D.first_ne

/-- Unit packaging of the first displayed coefficient. -/
noncomputable def coefficientUnit : Kˣ :=
  Units.mk0 D.coordinates.leftCoefficient
    D.coordinates_leftCoefficient_ne

theorem coefficientUnit_order :
    ordUnit K D.coefficientUnit = weightIdealOrder q L := by
  apply WithTop.coe_injective
  rw [coe_ordUnit]
  simpa only [coefficientUnit, Units.val_mk0,
    D.coordinates_leftCoefficient_eq] using D.first_order

/-- Display the whole lattice as the weight-adapted general plane followed
by its unimodular orthogonal complement. -/
noncomputable def displayedIsometry : Isometry q
    ((QuadraticSpace.omearaGeneralPlane
      D.coordinates.leftCoefficient D.coordinates.rightCoefficient
      D.coordinates.nondegenerate).orthogonalSum
        (D.decomposition.component 1).space)
    L (product (hyperbolicPlaneLattice (K := K))
      (D.decomposition.component 1).lattice) :=
  let model := QuadraticSpace.omearaGeneralPlane
    D.coordinates.leftCoefficient D.coordinates.rightCoefficient
      D.coordinates.nondegenerate
  let identify : Isometry
      (model.rescaleUnit (1 : Kˣ)) model
      (hyperbolicPlaneLattice (K := K))
      (hyperbolicPlaneLattice (K := K)) :=
    Isometry.rescaleUnitOne model (hyperbolicPlaneLattice (K := K))
  D.decomposition.pairProductLatticeIsometry.symm |>.trans
    ((D.coordinates.isometry.trans identify).orthogonalProductBasic
      (Isometry.refl (D.decomposition.component 1).space
        (D.decomposition.component 1).lattice))

end WeightAdaptedBinarySplittingData

/-- Construct the weight-adapted binary splitting in the strict
nonterminal odd branch. -/
noncomputable def weightAdaptedBinarySplittingData
    (hmodular : IsModular q L (1 : Kˣ))
    (a : Kˣ) (ha : IsNormGeneratorValue q L a)
    (hlt : weightIdealOrder q L < canonicalTwoScaleOrder q L) :
    WeightAdaptedBinarySplittingData q L := by
  letI : Module.Finite K V := L.moduleFinite
  let hex := exists_quadratic_order_eq_weightIdealOrder_of_lt_twoScale
    a ha hlt
  let x : V := Classical.choose hex
  have hxAll := Classical.choose_spec hex
  have hx : x ∈ L := hxAll.1
  have hxne : q.quadratic x ≠ 0 := hxAll.2.1
  have hxOrder : ord K (q.quadratic x) =
      ((weightIdealOrder q L : Int) : WithTop Int) := hxAll.2.2.1
  have hodd : Odd (ordUnit K a + weightIdealOrder q L) :=
    hxAll.2.2.2
  have hxPrimitive := primitive_of_quadratic_order_eq_weightIdealOrder
    hmodular a ha hx hxne hxOrder hodd
  let hey := hmodular.exists_pairing_eq_of_not_mem_rescale hx hxPrimitive
  let y : V := Classical.choose hey
  have hyAll := Classical.choose_spec hey
  have hy : y ∈ L := hyAll.1
  have hpair : q.bilin x y = (1 : K) := hyAll.2
  have hpairNe : q.bilin x y ≠ 0 := by
    rw [hpair]
    norm_num
  have hleft : ord K (q.bilin x y) < ord K (q.quadratic x) := by
    rw [hpair, ord_one, hxOrder]
    exact_mod_cast (show 0 < weightIdealOrder q L by
      have hnormLeWeight := normGeneratorOrder_le_weightIdealOrder a ha
      have hnormNonneg : 0 ≤ ordUnit K a := by
        have hnormScale := normIdeal_le_scaleIdeal q L
        rw [ha.2, hmodular.scaleIdeal_eq_principal (by
          exact finrank_pos_of_isNormGeneratorValue ha)] at hnormScale
        have hord : ord K (1 : K) ≤ ord K (a : K) :=
          (principalIdeal_le_iff_ord_ge
            (Units.ne_zero a) (one_ne_zero : (1 : K) ≠ 0)).1 hnormScale
        rw [ord_one, ← coe_ordUnit K a] at hord
        exact WithTop.coe_le_coe.mp hord
      by_contra hnot
      have hweightZero : weightIdealOrder q L = 0 := by omega
      have hnormZero : ordUnit K a = 0 := by omega
      rw [hweightZero, hnormZero] at hodd
      exact Int.not_odd_zero hodd)
  have hright : ord K (q.bilin x y) ≤ ord K (q.quadratic y) := by
    rw [hpair, ord_one]
    have hyScale : q.quadratic y ∈ principalIdeal (K := K) (1 : K) := by
      apply hmodular.scaleIdeal_le_principal
      change q.bilin y y ∈ scaleIdeal q L
      exact bilin_mem_scaleIdeal_of_mem q L hy hy
    have hyIntegral : q.quadratic y ∈ IntegerRing K :=
      mem_integerRing_of_mul_mem_principalIdeal
        (one_ne_zero : (1 : K) ≠ 0) (by simpa using hyScale)
    exact (mem_integerRing_iff K).1 hyIntegral
  let C := asymmetricBinaryScaleComponent (q := q)
    hpairNe hleft hright
  have hCL : C.ambientSubmodule ≤ L.toSubmodule :=
    asymmetricBinaryScaleComponent_ambientSubmodule_le
      hpairNe hleft hright hx hy
  have hCmodular : IsModular C.space C.lattice (1 : Kˣ) := by
    have hraw := asymmetricBinaryScaleComponent_isModular
      hpairNe hleft hright
    have hu : Units.mk0 (q.bilin x y) hpairNe = (1 : Kˣ) := by
      apply Units.ext
      exact hpair
    simpa only [hu] using hraw
  let S : OrthogonalDecomposition q L 2 :=
    omearaModularSplittingOfScaleIdealLe C hCL hCmodular
      hmodular.scaleIdeal_le_principal
  let b : Basis (Fin 2) K C.carrier :=
    BONG.binaryPairBasis (K := K) x y
      (binaryPair_linearIndependent_of_left_strict
        hpairNe hleft hright)
  have hb0 : (b 0 : V) = x := by
    rw [show (b 0 : V) = BONG.binaryPairFamily x y 0 by
      exact BONG.coe_binaryPairBasis x y
        (binaryPair_linearIndependent_of_left_strict
          hpairNe hleft hright) 0]
    exact BONG.binaryPairFamily_zero x y
  have hb1 : (b 1 : V) = y := by
    rw [show (b 1 : V) = BONG.binaryPairFamily x y 1 by
      exact BONG.coe_binaryPairBasis x y
        (binaryPair_linearIndependent_of_left_strict
          hpairNe hleft hright) 1]
    exact BONG.binaryPairFamily_one x y
  have hfirstRank : finrank K (S.component 0).carrier = 2 := by
    change finrank K C.carrier = 2
    simpa using Module.finrank_eq_card_basis b
  exact
    { decomposition := S
      first_rank := hfirstRank
      first_modular := by
        change IsModular C.space C.lattice (1 : Kˣ)
        exact hCmodular
      complement_modular := S.component_modular_of_ambient hmodular 1
      basis := b
      basis_lattice := rfl
      pairing_eq := by
        change q.bilin (b 0 : V) (b 1 : V) = 1
        rw [hb0, hb1, hpair]
      first_ne := by
        change q.quadratic (b 0 : V) ≠ 0
        rw [hb0]
        exact hxne
      first_order := by
        change ord K (q.quadratic (b 0 : V)) = _
        rw [hb0]
        exact hxOrder }

end Lattice

end Bong
