/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaFundamentalIdeals
import Bong.Lattice.OmearaModularNormClassification
import Bong.Lattice.OmearaSaturationCriterion
import Bong.Lattice.OmearaIntegralReflection
import Bong.Lattice.OmearaComponentwiseFundamentalTransfer

/-!
# O'Meara 93:25 for fundamental norm groups and weights

The two lattice inclusions behind 93:25 are proved directly from the
pairing definition `L^r = L ∩ π^r L♯`.  They imply both the ordinary
and the quadratically rescaled inclusions of fundamental norm groups.
For the even norm-order gaps needed in 93:27, O'Meara's intrinsic
characterization of the weight then gives the corresponding two weight
inequalities.  No duality or local-classification law is assumed.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V}

/-- Larger truncation exponents give smaller intrinsic lattices. -/
theorem scaleTruncation_anti {a b : Int} (hab : a ≤ b) :
    scaleTruncation q L b ≤ scaleTruncation q L a := by
  intro x hx
  change x ∈ scaleTruncation q L b at hx
  change x ∈ scaleTruncation q L a
  rw [mem_scaleTruncation_iff_ord_bilin_ge] at hx ⊢
  refine ⟨hx.1, ?_⟩
  intro y hy
  have hab' : (a : WithTop Int) ≤ (b : WithTop Int) := by
    exact_mod_cast hab
  exact hab'.trans (hx.2 y hy)

/-- Multiplying `L^a` by `π^(b-a)` lands in `L^b`. -/
theorem rescale_scaleTruncation_le {a b : Int} (hab : a ≤ b) :
    rescale (uniformizerPowerUnit K (b - a))
        (scaleTruncation q L a) ≤
      scaleTruncation q L b := by
  intro x hx
  change x ∈ rescale (uniformizerPowerUnit K (b - a))
    (scaleTruncation q L a) at hx
  change x ∈ scaleTruncation q L b
  rw [mem_rescale_iff] at hx
  rcases hx with ⟨z, hz, rfl⟩
  rw [mem_scaleTruncation_iff_ord_bilin_ge] at hz ⊢
  have hcIntegral :
      (uniformizerPowerUnit K (b - a) : K) ∈ IntegerRing K := by
    rw [mem_integerRing_iff]
    change (0 : WithTop Int) ≤
      ord K (uniformizerPowerUnit K (b - a) : K)
    rw [← coe_ordUnit,
      ordUnit_uniformizerPowerUnit]
    exact_mod_cast sub_nonneg.mpr hab
  let cO : IntegerRing K :=
    ⟨(uniformizerPowerUnit K (b - a) : K), hcIntegral⟩
  refine ⟨L.smul_mem cO hz.1, ?_⟩
  intro y hy
  have hpair := hz.2 y hy
  rw [LinearMap.BilinForm.smul_left]
  change (b : WithTop Int) ≤ ord K
    ((uniformizerPowerUnit K (b - a) : K) * q.bilin z y)
  rw [ord_mul,
    ← coe_ordUnit, ordUnit_uniformizerPowerUnit]
  have hsum : (b : WithTop Int) =
      ((b - a : Int) : WithTop Int) + (a : WithTop Int) := by
    norm_cast
    omega
  rw [hsum]
  simpa [add_comm] using
    (add_le_add_left hpair ((b - a : Int) : WithTop Int))

/-- Doubled scale ideals are monotone with the underlying lattice. -/
theorem twoScaleIdeal_mono (hLM : L ≤ M) :
    twoScaleIdeal q L ≤ twoScaleIdeal q M := by
  unfold twoScaleIdeal twiceIdeal
  exact Submodule.map_mono (scaleIdeal_mono q hLM)

/-- Scalar norm groups are monotone with the underlying lattice. -/
theorem normGroupSet_mono (hLM : L ≤ M) :
    normGroupSet q L ⊆ normGroupSet q M := by
  rintro z ⟨x, hx, y, hy, rfl⟩
  exact ⟨x, hLM hx, y, twoScaleIdeal_mono hLM hy, rfl⟩

/-- The ideal-theoretic core of O'Meara 93:25: inclusion of norm groups and
doubled scale ideals forces inclusion of weights.  The source and target may
live in different quadratic spaces. -/
theorem weightIdeal_mono_of_normGroupSet_subset_of_twoScaleIdeal_le
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {N : Lattice K W}
    (a b : Kˣ)
    (ha : IsNormGeneratorValue q L a)
    (hb : IsNormGeneratorValue r N b)
    (htwo : twoScaleIdeal q L ≤ twoScaleIdeal r N)
    (hgroup : normGroupSet q L ⊆ normGroupSet r N) :
    weightIdeal q L ≤ weightIdeal r N := by
  rcases weightIdeal_eq_twoScale_or_odd a ha with hterminal | hodd
  · rw [hterminal]
    exact htwo.trans (twoScaleIdeal_le_weightIdeal r N)
  · rw [weightIdeal_eq_powerIdeal, weightIdeal_eq_powerIdeal,
      powerIdeal_le_iff]
    let z : Kˣ := weightIdealGenerator q L
    have hzL : (z : K) ∈ normGroupSet q L :=
      weightIdealGenerator_mem_normGroupSet q L a ha
    have hzN : (z : K) ∈ normGroupSet r N := hgroup hzL
    have haN : (a : K) ∈ normGroupSet r N := hgroup ha.1
    have hnormSource : ordUnit K a ≤ weightIdealOrder q L := by
      have hbound := canonicalNormOrder_le_ordUnit_of_mem_normGroupSet ha hzL
      rw [← ordUnit_eq_canonicalNormOrder ha] at hbound
      simpa only [z, ordUnit_weightIdealGenerator] using hbound
    have hsourceOdd : Odd (ordUnit K a + ordUnit K z) := by
      simpa only [z, ordUnit_weightIdealGenerator] using hodd
    rcases Int.even_or_odd (ordUnit K b + ordUnit K a) with heven | hbaOdd
    · have htargetOdd : Odd (ordUnit K b + ordUnit K z) := by
        rcases heven with ⟨d, hd⟩
        rcases hsourceOdd with ⟨e, he⟩
        refine ⟨d + e - ordUnit K a, ?_⟩
        omega
      have hbound := weightIdealOrder_le_ordUnit_of_mem_normGroupSet_of_odd
        b z hb hzN htargetOdd
      simpa only [z, ordUnit_weightIdealGenerator] using hbound
    · exact (weightIdealOrder_le_ordUnit_of_mem_normGroupSet_of_odd
        b a hb haN hbaOdd).trans hnormSource

/-- O'Meara 93:25 for weights in its unscaled lattice form. -/
theorem weightIdeal_mono_of_lattice_le
    (hLM : L ≤ M) (a b : Kˣ)
    (ha : IsNormGeneratorValue q L a)
    (hb : IsNormGeneratorValue q M b) :
    weightIdeal q L ≤ weightIdeal q M :=
  weightIdeal_mono_of_normGroupSet_subset_of_twoScaleIdeal_le
    a b ha hb (twoScaleIdeal_mono hLM) (normGroupSet_mono hLM)

/-- Quadratic values and doubled scales both acquire the square of a
lattice-rescaling factor. -/
theorem sq_mul_mem_normGroupSet_rescale
    (c : Kˣ) {z : K} (hz : z ∈ normGroupSet q L) :
    (c ^ 2 : Kˣ) * z ∈ normGroupSet q (rescale c L) := by
  let f := scalarMultiplicationRescaleLatticeIsometry q L c
  rw [normGroupSet_eq_of_latticeIsometry f,
    mem_normGroupSet_rescaleQuadraticUnit_iff]
  rw [← mul_assoc]
  have hunit : (((c ^ 2)⁻¹ : Kˣ) : K) * ((c ^ 2 : Kˣ) : K) = 1 := by
    simp
  rw [hunit, one_mul]
  exact hz

namespace JordanDecomposition

variable {t : Nat} (J : JordanDecomposition q L t)

private theorem fundamentalScaleOrder_mono {i j : Fin t} (hij : i ≤ j) :
    J.fundamentalScaleOrder i ≤ J.fundamentalScaleOrder j := by
  unfold fundamentalScaleOrder
  by_cases hEq : i = j
  · subst j
    exact le_rfl
  · exact (J.scaleOrder_strict (lt_of_le_of_ne hij hEq)).le

/-- The later fundamental norm group is contained in the earlier one. -/
theorem fundamentalNormGroup_anti {i j : Fin t} (hij : i ≤ j) :
    J.fundamentalNormGroup j ⊆ J.fundamentalNormGroup i := by
  unfold fundamentalNormGroup fundamentalLattice
  exact normGroupSet_mono
    (scaleTruncation_anti (J.fundamentalScaleOrder_mono hij))

/-- The square-scaled earlier fundamental norm group is contained in the
later one, which is the first displayed inclusion of O'Meara 93:25. -/
theorem fundamentalNormGroup_sq_scale_subset
    {i j : Fin t} (hij : i ≤ j) {z : K}
    (hz : z ∈ J.fundamentalNormGroup i) :
    let c := uniformizerPowerUnit K
      (J.fundamentalScaleOrder j - J.fundamentalScaleOrder i)
    (c ^ 2 : Kˣ) * z ∈ J.fundamentalNormGroup j := by
  let c := uniformizerPowerUnit K
    (J.fundamentalScaleOrder j - J.fundamentalScaleOrder i)
  change (c ^ 2 : Kˣ) * z ∈ J.fundamentalNormGroup j
  have hrescaled : (c ^ 2 : Kˣ) * z ∈
      normGroupSet q (rescale c (J.fundamentalLattice i)) :=
    sq_mul_mem_normGroupSet_rescale c hz
  exact normGroupSet_mono
    (rescale_scaleTruncation_le (J.fundamentalScaleOrder_mono hij))
      hrescaled

/-- Every fundamental weight is contained in the doubled fundamental scale. -/
theorem fundamentalWeightOrder_le_twoScaleOrder (i : Fin t) :
    J.fundamentalWeightOrder i ≤
      J.fundamentalScaleOrder i + ramificationIndex K := by
  have h := twoScaleIdeal_le_weightIdeal q (J.fundamentalLattice i)
  rw [J.fundamentalTwoScaleIdeal_eq_powerIdeal,
    weightIdeal_eq_powerIdeal, powerIdeal_le_iff] at h
  exact h

/-- The direct weight inequality of 93:25 for the even norm-order gaps
used in 93:27. -/
theorem fundamentalWeightOrder_mono_of_even_normOrderGap
    {i j : Fin t} (hij : i ≤ j)
    (hgap : Even (ordUnit K (J.fundamentalNormGenerator j) -
      ordUnit K (J.fundamentalNormGenerator i))) :
    J.fundamentalWeightOrder i ≤ J.fundamentalWeightOrder j := by
  let ai := J.fundamentalNormGenerator i
  let aj := J.fundamentalNormGenerator j
  rcases weightIdeal_eq_twoScale_or_odd aj
      (J.fundamentalNormGenerator_spec j) with htwo | hodd
  · have hwj : J.fundamentalWeightOrder j =
        J.fundamentalScaleOrder j + ramificationIndex K := by
      unfold fundamentalWeightOrder
      apply powerIdeal_order_eq_of_eq (K := K)
      rw [← weightIdeal_eq_powerIdeal, htwo,
        J.fundamentalTwoScaleIdeal_eq_powerIdeal]
    rw [hwj]
    exact (J.fundamentalWeightOrder_le_twoScaleOrder i).trans
      (by
        have hscale := J.fundamentalScaleOrder_mono hij
        omega)
  · let z := J.fundamentalWeightGenerator j
    have hz : (z : K) ∈ J.fundamentalNormGroup i :=
      J.fundamentalNormGroup_anti hij (J.fundamentalWeightGenerator_mem j)
    have hodd' : Odd (ordUnit K ai + ordUnit K z) := by
      rw [J.fundamentalWeightGenerator_order]
      change Odd (ordUnit K ai +
        weightIdealOrder q (J.fundamentalLattice j))
      dsimp only [ai, aj] at hgap hodd ⊢
      rcases hgap with ⟨d, hd⟩
      rcases hodd with ⟨e, he⟩
      refine ⟨e - d, ?_⟩
      omega
    have hbound := weightIdealOrder_le_ordUnit_of_mem_normGroupSet_of_odd
      ai z (J.fundamentalNormGenerator_spec i) hz hodd'
    have hzOrder : ordUnit K z = J.fundamentalWeightOrder j := by
      simpa only [z] using J.fundamentalWeightGenerator_order j
    rw [hzOrder] at hbound
    simpa only [fundamentalWeightOrder] using hbound

/-- The dual weight inequality of 93:25 for even norm-order gaps. -/
theorem fundamentalWeightOrder_sub_two_scale_anti_of_even_normOrderGap
    {i j : Fin t} (hij : i ≤ j)
    (hgap : Even (ordUnit K (J.fundamentalNormGenerator j) -
      ordUnit K (J.fundamentalNormGenerator i))) :
    J.fundamentalWeightOrder j - 2 * J.fundamentalScaleOrder j ≤
      J.fundamentalWeightOrder i - 2 * J.fundamentalScaleOrder i := by
  let ai := J.fundamentalNormGenerator i
  let aj := J.fundamentalNormGenerator j
  let d := J.fundamentalScaleOrder j - J.fundamentalScaleOrder i
  let c := uniformizerPowerUnit K d
  rcases weightIdeal_eq_twoScale_or_odd ai
      (J.fundamentalNormGenerator_spec i) with htwo | hodd
  · have hwi : J.fundamentalWeightOrder i =
        J.fundamentalScaleOrder i + ramificationIndex K := by
      unfold fundamentalWeightOrder
      apply powerIdeal_order_eq_of_eq (K := K)
      rw [← weightIdeal_eq_powerIdeal, htwo,
        J.fundamentalTwoScaleIdeal_eq_powerIdeal]
    have hwj := J.fundamentalWeightOrder_le_twoScaleOrder j
    have hscale := J.fundamentalScaleOrder_mono hij
    rw [hwi]
    omega
  · let z : Kˣ := c ^ 2 * J.fundamentalWeightGenerator i
    have hz : (z : K) ∈ J.fundamentalNormGroup j := by
      exact J.fundamentalNormGroup_sq_scale_subset hij
        (J.fundamentalWeightGenerator_mem i)
    have hzOrder : ordUnit K z =
        2 * d + J.fundamentalWeightOrder i := by
      simp only [z, c, ordUnit_mul, ordUnit_pow,
        ordUnit_uniformizerPowerUnit,
        J.fundamentalWeightGenerator_order]
      norm_num
    have hodd' : Odd (ordUnit K aj + ordUnit K z) := by
      rw [hzOrder]
      change Odd (ordUnit K aj +
        (2 * d + weightIdealOrder q (J.fundamentalLattice i)))
      dsimp only [ai, aj] at hgap hodd ⊢
      rcases hgap with ⟨g, hg⟩
      rcases hodd with ⟨e, he⟩
      refine ⟨e + g + d, ?_⟩
      omega
    have hbound := weightIdealOrder_le_ordUnit_of_mem_normGroupSet_of_odd
      aj z (J.fundamentalNormGenerator_spec j) hz hodd'
    rw [hzOrder] at hbound
    dsimp only [d] at hbound ⊢
    unfold fundamentalWeightOrder at hbound ⊢
    omega

end JordanDecomposition

end Lattice

end Bong
