/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.UnaryBinaryModel
import Bong.Lattice.Omeara9318EvenParity
import Bong.Lattice.OmearaOddRankProper
import Bong.Lattice.OmearaUnimodularNormClassification

/-!
# Adjoining a represented unit line

This is the invariant calculation used in O'Meara 93:18(iv).  If an
unimodular lattice represents a valuation unit `epsilon`, adjoining the
standard line `<epsilon>` preserves its norm group, two-scale ideal, and
weight ideal.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The standard integral line `<epsilon>` is unimodular whenever its
coefficient is a valuation unit. -/
theorem unaryModelLattice_isModular_scaledLine_of_isValuationUnit
    (epsilon : Kˣ) (hepsilon : IsValuationUnit K (epsilon : K)) :
    IsModular (QuadraticSpace.scaledLine epsilon)
      (BONG.unaryModelLattice (K := K)) (1 : Kˣ) := by
  let b := Basis.singleton Unit K
  have horth : (QuadraticSpace.scaledLine epsilon).bilin.iIsOrtho b := by
    rw [LinearMap.BilinForm.iIsOrtho_def]
    intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  have hne : ∀ i,
      (QuadraticSpace.scaledLine epsilon).quadratic (b i) ≠ 0 := by
    intro i
    have hi : i = Unit.unit := Subsingleton.elim i Unit.unit
    subst i
    simp [b]
  apply isModular_basisLattice_of_iIsOrtho_of_orders_eq
    (QuadraticSpace.scaledLine epsilon) b horth hne (1 : Kˣ)
  intro i
  have hi : i = Unit.unit := Subsingleton.elim i Unit.unit
  subst i
  have hvalue : Units.mk0
      ((QuadraticSpace.scaledLine epsilon).quadratic (b Unit.unit))
        (hne Unit.unit) = epsilon := by
    apply Units.ext
    simp [b]
  rw [hvalue]
  have hepsilonOrder : ordUnit K epsilon = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K epsilon).mp hepsilon
  have hone : ordUnit K (1 : Kˣ) = 0 := by
    have h := ordUnit_mul K (1 : Kˣ) 1
    simp only [mul_one] at h
    omega
  rw [hepsilonOrder, hone]

namespace OddRankUnimodularUnitValueData

variable {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- The represented unit selected in an odd-rank unimodular lattice is a
norm-generator value of that lattice. -/
theorem isNormGeneratorValue
    (D : OddRankUnimodularUnitValueData q L)
    (hmodular : IsModular q L (1 : Kˣ))
    (hrankOdd : Odd (finrank K V)) :
    IsNormGeneratorValue q L D.valueUnit := by
  have hpos : 0 < finrank K V := by
    rcases hrankOdd with ⟨k, hk⟩
    omega
  have hprincipal : principalIdeal (K := K) (D.valueUnit : K) =
      principalIdeal (K := K) (1 : K) := by
    apply (principalIdeal_eq_iff_ordUnit_eq D.valueUnit (1 : Kˣ)).mpr
    have hDorder : ordUnit K D.valueUnit = 0 :=
      (isValuationUnit_iff_ordUnit_eq_zero K D.valueUnit).mp
        D.value_isValuationUnit
    have hone : ordUnit K (1 : Kˣ) = 0 := by
      have h := ordUnit_mul K (1 : Kˣ) 1
      simp only [mul_one] at h
      omega
    rw [hDorder, hone]
  constructor
  · exact ⟨D.vector, D.vector_mem, 0, Submodule.zero_mem _, by
      rw [D.valueUnit_eq]
      simp⟩
  · calc
      normIdeal q L = scaleIdeal q L :=
        normIdeal_eq_scaleIdeal_of_modular_of_odd_rank
          q L (1 : Kˣ) hmodular hrankOdd
      _ = principalIdeal (K := K) (1 : K) :=
        hmodular.scaleIdeal_eq_principal hpos
      _ = principalIdeal (K := K) (D.valueUnit : K) :=
        hprincipal.symm

/-- Every norm value of the adjoined unit line already belongs to the norm
group of the original lattice. -/
theorem line_normGroupSet_subset
    (D : OddRankUnimodularUnitValueData q L)
    (hmodular : IsModular q L (1 : Kˣ))
    (hrankOdd : Odd (finrank K V)) :
    normGroupSet (QuadraticSpace.scaledLine D.valueUnit)
        (BONG.unaryModelLattice (K := K)) ⊆
      normGroupSet q L := by
  let line := QuadraticSpace.scaledLine D.valueUnit
  let lineLattice := BONG.unaryModelLattice (K := K)
  have hline : IsModular line lineLattice (1 : Kˣ) :=
    unaryModelLattice_isModular_scaledLine_of_isValuationUnit
      D.valueUnit D.value_isValuationUnit
  have hpos : 0 < finrank K V := by
    rcases hrankOdd with ⟨k, hk⟩
    omega
  have htwo : twoScaleIdeal line lineLattice = twoScaleIdeal q L := by
    rw [twoScaleIdeal_eq_principalIdeal_two_of_unimodular hline (by simp),
      twoScaleIdeal_eq_principalIdeal_two_of_unimodular hmodular hpos]
  rintro z ⟨c, hc, y, hy, rfl⟩
  have hcIntegral : c ∈ IntegerRing K := by
    exact (BONG.mem_unaryModelLattice_iff c).mp hc
  let cO : IntegerRing K := ⟨c, hcIntegral⟩
  have hcVector : c • D.vector ∈ L := by
    change (cO : K) • D.vector ∈ L
    exact L.smul_mem cO D.vector_mem
  refine ⟨c • D.vector, hcVector, y, ?_, ?_⟩
  · rw [← htwo]
    exact hy
  · rw [q.quadratic_smul, QuadraticSpace.scaledLine_quadratic_apply,
      D.valueUnit_eq]
    ring

/-- Adjoining the represented unit line does not change the norm group. -/
theorem orthogonalProduct_line_normGroupSet_eq
    (D : OddRankUnimodularUnitValueData q L)
    (hmodular : IsModular q L (1 : Kˣ))
    (hrankOdd : Odd (finrank K V)) :
    normGroupSet
        ((QuadraticSpace.scaledLine D.valueUnit).orthogonalSum q)
        (product (BONG.unaryModelLattice (K := K)) L) =
      normGroupSet q L := by
  ext z
  rw [mem_normGroupSet_orthogonalProduct_iff]
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact add_mem_normGroupSet q L
      (D.line_normGroupSet_subset hmodular hrankOdd hx) hy
  · intro hz
    exact ⟨0, zero_mem_normGroupSet _ _, z, hz, by simp⟩

end OddRankUnimodularUnitValueData

/-- Equality of norm groups and two-scale ideals transports O'Meara's
uniquely characterized weight ideal. -/
theorem weightIdeal_eq_of_commonNormGenerator_and_twoScaleIdeal_eq
    {V : Type v} {W : Type w} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W}
    (a : Kˣ) (ha : IsNormGeneratorValue q L a)
    (ha' : IsNormGeneratorValue r M a)
    (hgroup : normGroupSet q L = normGroupSet r M)
    (htwo : twoScaleIdeal q L = twoScaleIdeal r M) :
    weightIdeal q L = weightIdeal r M := by
  let w := Beli2009WeightIdealData.weight q L
  have hw : twoScaleIdeal r M ≤ w.carrier := by
    rw [← htwo]
    exact twoScaleIdeal_le_weightIdeal q L
  have hconditions : SatisfiesWeightIdealConditions r M a w := by
    have hsource := (beli2009Lemma210 a ha w
      (twoScaleIdeal_le_weightIdeal q L)).mp rfl
    rcases hsource with ⟨hcoset, hterminal⟩
    constructor
    · exact hgroup.symm.trans hcoset
    · rcases hterminal with hterminal | hodd
      · exact Or.inl (hterminal.trans htwo)
      · exact Or.inr hodd
  exact (beli2009Lemma210 a ha' w hw).mpr hconditions

/-- Complete invariant package for adjoining the represented unit line. -/
structure UnitLineAdjunctionData
    {V : Type v} [AddCommGroup V] [Module K V]
    (q : QuadraticSpace K V) (L : Lattice K V) where
  unitData : OddRankUnimodularUnitValueData q L
  space : QuadraticSpace K (K × V) :=
    (QuadraticSpace.scaledLine unitData.valueUnit).orthogonalSum q
  lattice : Lattice K (K × V) :=
    product (BONG.unaryModelLattice (K := K)) L
  modular : IsModular space lattice (1 : Kˣ)
  normGenerator : IsNormGeneratorValue space lattice unitData.valueUnit
  normGroupSet_eq : normGroupSet space lattice = normGroupSet q L
  twoScaleIdeal_eq : twoScaleIdeal space lattice = twoScaleIdeal q L
  weightIdeal_eq : weightIdeal space lattice = weightIdeal q L
  weightIdealOrder_eq : weightIdealOrder space lattice = weightIdealOrder q L

set_option maxHeartbeats 3000000 in
-- The norm/weight transport below unfolds both orthogonal-product ideals.
/-- Construct the rank-one adjunction used to reduce 93:18(iv) to the
quaternary case. -/
noncomputable def unitLineAdjunctionData
    {V : Type v} [AddCommGroup V] [Module K V]
    (q : QuadraticSpace K V) (L : Lattice K V)
    (hmodular : IsModular q L (1 : Kˣ))
    (hrankOdd : Odd (finrank K V)) :
    UnitLineAdjunctionData.{u, v} q L := by
  letI : Module.Finite K V := L.moduleFinite
  let D := oddRankUnimodularUnitValueData q L hmodular hrankOdd
  let line := QuadraticSpace.scaledLine D.valueUnit
  let lineLattice := BONG.unaryModelLattice (K := K)
  have hline : IsModular line lineLattice (1 : Kˣ) :=
    unaryModelLattice_isModular_scaledLine_of_isValuationUnit
      D.valueUnit D.value_isValuationUnit
  have hadjoined : IsModular (line.orthogonalSum q)
      (product lineLattice L) (1 : Kˣ) :=
    hline.orthogonalProduct hmodular
  have hgroup := D.orthogonalProduct_line_normGroupSet_eq
    hmodular hrankOdd
  have hpos : 0 < finrank K V := by
    rcases hrankOdd with ⟨k, hk⟩
    omega
  have hadjoinedPos : 0 < finrank K (K × V) := by
    rw [Module.finrank_prod]
    simp
  have htwo : twoScaleIdeal (line.orthogonalSum q)
      (product lineLattice L) = twoScaleIdeal q L := by
    rw [twoScaleIdeal_eq_principalIdeal_two_of_unimodular
      hadjoined hadjoinedPos,
      twoScaleIdeal_eq_principalIdeal_two_of_unimodular hmodular hpos]
  have hnormOriginal := D.isNormGeneratorValue hmodular hrankOdd
  have hnormAdjoined : IsNormGeneratorValue (line.orthogonalSum q)
      (product lineLattice L) D.valueUnit := by
    constructor
    · rw [hgroup]
      exact hnormOriginal.1
    · rw [normIdeal_orthogonalProduct,
        normIdeal_eq_scaleIdeal_of_finrank_eq_one line lineLattice (by simp),
        hline.scaleIdeal_eq_principal (by simp), hnormOriginal.2]
      have hprincipal : principalIdeal (K := K) (D.valueUnit : K) =
          principalIdeal (K := K) (1 : K) := by
        apply (principalIdeal_eq_iff_ordUnit_eq D.valueUnit (1 : Kˣ)).mpr
        have hDorder :=
          (isValuationUnit_iff_ordUnit_eq_zero K D.valueUnit).mp
            D.value_isValuationUnit
        have hone : ordUnit K (1 : Kˣ) = 0 := by
          have h := ordUnit_mul K (1 : Kˣ) 1
          simp only [mul_one] at h
          omega
        rw [hDorder, hone]
      rw [hprincipal]
      simpa using sup_idem (principalIdeal (K := K) (1 : K))
  have hweight : weightIdeal (line.orthogonalSum q)
      (product lineLattice L) = weightIdeal q L :=
    weightIdeal_eq_of_commonNormGenerator_and_twoScaleIdeal_eq
      D.valueUnit hnormAdjoined hnormOriginal hgroup htwo
  have hweightOrder : weightIdealOrder (line.orthogonalSum q)
      (product lineLattice L) = weightIdealOrder q L := by
    apply powerIdeal_order_eq_of_eq (K := K)
    calc
      powerIdeal (K := K)
          (weightIdealOrder (line.orthogonalSum q)
            (product lineLattice L)) =
          weightIdeal (line.orthogonalSum q) (product lineLattice L) :=
        (weightIdeal_eq_powerIdeal _ _).symm
      _ = weightIdeal q L := hweight
      _ = powerIdeal (K := K) (weightIdealOrder q L) :=
        weightIdeal_eq_powerIdeal q L
  exact
    { unitData := D
      modular := hadjoined
      normGenerator := hnormAdjoined
      normGroupSet_eq := hgroup
      twoScaleIdeal_eq := htwo
      weightIdeal_eq := hweight
      weightIdealOrder_eq := hweightOrder }

/-- The adjoined space is definitionally the represented unit line followed
by the original quadratic space.  This named equation avoids unfolding the
invariant proof package in later cancellation arguments. -/
@[simp]
theorem unitLineAdjunctionData_space
    {V : Type v} [AddCommGroup V] [Module K V]
    (q : QuadraticSpace K V) (L : Lattice K V)
    (hmodular : IsModular q L (1 : Kˣ))
    (hrankOdd : Odd (finrank K V)) :
    (unitLineAdjunctionData q L hmodular hrankOdd).space =
      (QuadraticSpace.scaledLine
        (unitLineAdjunctionData q L hmodular hrankOdd).unitData.valueUnit).orthogonalSum q := by
  rfl

/-- The lattice underlying the unit-line adjunction is the corresponding
product lattice. -/
@[simp]
theorem unitLineAdjunctionData_lattice
    {V : Type v} [AddCommGroup V] [Module K V]
    (q : QuadraticSpace K V) (L : Lattice K V)
    (hmodular : IsModular q L (1 : Kˣ))
    (hrankOdd : Odd (finrank K V)) :
    (unitLineAdjunctionData q L hmodular hrankOdd).lattice =
      product (BONG.unaryModelLattice (K := K)) L := by
  rfl

end Lattice

end Bong
