/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OMaximal
import Bong.Lattice.AdjoinVector
import Bong.Dyadic.QuadraticDefectHensel
import Bong.Lattice.OmearaEvenPlaneNormalization
import Bong.Lattice.OmearaTwoPlaneCombination
import Bong.Lattice.OrthogonalSumRescale

/-!
# Uniqueness and hyperbolic splitting of maximal integral lattices

This file proves the local maximal-lattice inputs used in Beli's Section 4.
The anisotropic argument is O'Meara 91:1: the local square theorem shows
that integral quadratic vectors are closed under addition.  The isotropic
argument applies O'Meara 82:20 to the form `2q`, normalizes its even
unimodular plane by 93:11, and then uses Witt cancellation inductively.
The resulting endpoint is O'Meara 91:2, with no maximal-lattice axiom.
-/

open Bong Bong.Dyadic
namespace Bong.Dyadic

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

theorem isIntegral_one_add_square_mul {c C : K}
    (hC : IsIntegral K C) (hc : IsIntegral K (c ^ 2 * C)) :
    IsIntegral K ((c + 1) ^ 2 * C) := by
  rw [IsIntegral, ord_mul, ord_pow] at hc ⊢
  have hadd : min (ord K c) 0 ≤ ord K (c + 1) := by
    simpa only [ord_one] using min_ord_le_ord_add K c 1
  rcases le_total 0 (ord K c) with hcNonneg | hcNonpos
  · have hsumNonneg : 0 ≤ ord K (c + 1) := by
      exact (by simpa [min_eq_right hcNonneg] using hadd)
    exact add_nonneg (nsmul_nonneg hsumNonneg 2) hC
  · have hbound : 2 • ord K c + ord K C ≤
        2 • ord K (c + 1) + ord K C := by
      have hsingle : ord K c ≤ ord K (c + 1) := by
        simpa [min_eq_left hcNonpos] using hadd
      have hdouble := add_le_add hsingle hsingle
      have hboundRaw := add_le_add_right hdouble (ord K C)
      simpa [two_nsmul, add_comm] using hboundRaw
    exact hc.trans hbound

end Bong.Dyadic

namespace Bong.QuadraticSpace

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

/-- Every zero of an anisotropic quadratic space is the zero vector. -/
def IsAnisotropicSpace (q : QuadraticSpace K V) : Prop :=
  ∀ x : V, q.quadratic x = 0 → x = 0

theorem two_bilin_integral_of_anisotropicSpace
    {q : QuadraticSpace K V} (hq : q.IsAnisotropicSpace)
    {x y : V} (hx : Dyadic.IsIntegral K (q.quadratic x))
    (hy : Dyadic.IsIntegral K (q.quadratic y)) :
    Dyadic.IsIntegral K (2 * q.bilin x y) := by
  by_contra hcross
  have hcrossNeg : ord K (2 * q.bilin x y) < 0 := by
    exact lt_of_not_ge hcross
  have hbilinNe : q.bilin x y ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero, ord_zero] at hcrossNeg
    exact (not_lt_of_ge le_top) hcrossNeg
  have hxqNe : q.quadratic x ≠ 0 := by
    intro hzero
    have hxzero := hq x hzero
    subst x
    simp at hbilinNe
  have hyqNe : q.quadratic y ≠ 0 := by
    intro hzero
    have hyzero := hq y hzero
    subst y
    simp at hbilinNe
  let A : Kˣ := Units.mk0 (q.quadratic x) hxqNe
  let C : Kˣ := Units.mk0 (q.quadratic y) hyqNe
  let b : Kˣ := Units.mk0 (q.bilin x y) hbilinNe
  have hAord : 0 ≤ ordUnit K A := by
    apply WithTop.coe_le_coe.mp
    rw [coe_ordUnit]
    change 0 ≤ ord K (q.quadratic x)
    exact hx
  have hCord : 0 ≤ ordUnit K C := by
    apply WithTop.coe_le_coe.mp
    rw [coe_ordUnit]
    change 0 ≤ ord K (q.quadratic y)
    exact hy
  have hborder : (ramificationIndex K : Int) + ordUnit K b < 0 := by
    apply WithTop.coe_lt_coe.mp
    rw [WithTop.coe_add, ramificationIndex_spec, coe_ordUnit]
    change ord K (2 : K) + ord K (q.bilin x y) < 0
    rwa [← ord_mul]
  let u : K := 1 - (A : K) * (C : K) / (b : K) ^ 2
  have husquare : IsSquare u := by
    by_cases hu : u = 0
    · exact ⟨0, by simpa [hu]⟩
    · let uu : Kˣ := Units.mk0 u hu
      have hdeep :
          (((2 * ramificationIndex K : Nat) : Int) : WithTop Int) <
            ord K ((uu : K) - 1) := by
        have hint : (2 * ramificationIndex K : Int) <
            ordUnit K A + ordUnit K C - 2 * ordUnit K b := by
          omega
        have hfield : (uu : K) - 1 =
            -(((A * C / b ^ 2 : Kˣ) : K)) := by
          change u - 1 = -(((A * C / b ^ 2 : Kˣ) : K))
          have hcoe : (((A * C / b ^ 2 : Kˣ) : K)) =
              (A : K) * (C : K) / (b : K) ^ 2 := by simp
          rw [hcoe]
          dsimp only [u]
          ring
        rw [hfield, ord_neg, ← coe_ordUnit]
        simpa [div_eq_mul_inv, sub_eq_add_neg] using
          (show (((2 * ramificationIndex K : Int) : WithTop Int) <
              ((ordUnit K A + ordUnit K C - 2 * ordUnit K b : Int) :
                WithTop Int)) by exact_mod_cast hint)
      have huu : IsSquare uu :=
        Dyadic.isSquare_of_ord_sub_one_gt_two_mul_e K uu hdeep
      change IsSquare (uu : K)
      exact huu.map (Units.coeHom K)
  rcases husquare with ⟨t, ht⟩
  let lambda : K := (b : K) * (t - 1) / (C : K)
  have hzq : q.quadratic (x + lambda • y) = 0 := by
    rw [q.quadratic_add, q.quadratic_smul,
      LinearMap.BilinForm.smul_right]
    change (A : K) + lambda ^ 2 * (C : K) +
      2 * (lambda * (b : K)) = 0
    have ht' : t ^ 2 = u := by simpa [pow_two] using ht.symm
    dsimp only [lambda, u] at ht' ⊢
    field_simp [Units.ne_zero b] at ht'
    field_simp [Units.ne_zero C]
    calc
      (A : K) * (C : K) + (b : K) ^ 2 * (t - 1) ^ 2 +
          (b : K) ^ 2 * (t - 1) * 2 =
          (A : K) * (C : K) + (b : K) ^ 2 * (t ^ 2 - 1) := by ring
      _ = (C : K) * 0 := by linear_combination ht'
  have hzzero : x + lambda • y = 0 := hq _ hzq
  have hxdep : x = (-lambda) • y := by
    have := eq_neg_of_add_eq_zero_left hzzero
    simpa using this
  have hscaled : Dyadic.IsIntegral K ((-lambda) ^ 2 * q.quadratic y) := by
    rw [← q.quadratic_smul, ← hxdep]
    exact hx
  have honeAdd := Dyadic.isIntegral_one_add_square_mul hy hscaled
  have hsumIntegral : Dyadic.IsIntegral K (q.quadratic (x + y)) := by
    rw [hxdep]
    have hvec : (-lambda) • y + y = (-lambda + 1) • y := by
      module
    rw [hvec, q.quadratic_smul]
    simpa [add_comm] using honeAdd
  have hcrossIntegral : Dyadic.IsIntegral K (2 * q.bilin x y) := by
    have hxy := Dyadic.isIntegral_sub K
      (Dyadic.isIntegral_sub K hsumIntegral hx) hy
    have heq : (q.quadratic (x + y) - q.quadratic x) -
        q.quadratic y = 2 * q.bilin x y := by
      rw [q.quadratic_add]
      ring
    rwa [heq] at hxy
  exact hcross hcrossIntegral

theorem quadratic_add_integral_of_anisotropicSpace
    {q : QuadraticSpace K V} (hq : q.IsAnisotropicSpace)
    {x y : V} (hx : Dyadic.IsIntegral K (q.quadratic x))
    (hy : Dyadic.IsIntegral K (q.quadratic y)) :
    Dyadic.IsIntegral K (q.quadratic (x + y)) := by
  rw [q.quadratic_add]
  exact Dyadic.isIntegral_add K (Dyadic.isIntegral_add K hx hy)
    (two_bilin_integral_of_anisotropicSpace hq hx hy)

end Bong.QuadraticSpace

namespace Bong.Lattice

universe u v

open Dyadic

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

noncomputable def dyadicTwoUnit : Kˣ := Units.mk0 (2 : K) (by norm_num)

noncomputable def dyadicHalfUnit : Kˣ := (dyadicTwoUnit (K := K))⁻¹

noncomputable def hyperbolicOneRescaleHalfIsometry :
    Isometry
      ((QuadraticSpace.hyperbolicPlane (1 : Kˣ)).rescaleUnit
        (dyadicHalfUnit (K := K)))
      (QuadraticSpace.hyperbolicPlane (dyadicHalfUnit (K := K)))
      (hyperbolicPlaneLattice (K := K))
      (hyperbolicPlaneLattice (K := K)) where
  toLinearEquiv := LinearEquiv.refl K (Fin 2 → K)
  map_bilin := by
    intro x y
    simp only [QuadraticSpace.rescaleUnit_bilin_apply,
      QuadraticSpace.hyperbolicPlane_bilin_apply,
      LinearEquiv.refl_apply, Units.val_one, one_mul]
  map_mem := by intro x; rfl

noncomputable def rescaleTwoHalfIsometry
    (q : QuadraticSpace K V) (L : Lattice K V) :
    Isometry
      ((q.rescaleUnit (dyadicTwoUnit (K := K))).rescaleUnit
        (dyadicHalfUnit (K := K))) q L L where
  toLinearEquiv := LinearEquiv.refl K V
  map_bilin := by
    intro x y
    simp only [QuadraticSpace.rescaleUnit_bilin_apply,
      LinearEquiv.refl_apply]
    rw [← mul_assoc, ← Units.val_mul]
    have hmul : dyadicHalfUnit (K := K) * dyadicTwoUnit (K := K) = 1 := by
      simp [dyadicHalfUnit]
    rw [hmul]
    simp
  map_mem := by intro x; rfl

theorem adjoinVector_isIntegral_of_anisotropicSpace
    (hq : q.IsAnisotropicSpace) (hL : IsIntegral q L)
    {x : V} (hx : Dyadic.IsIntegral K (q.quadratic x)) :
    IsIntegral q (adjoinVector L x) := by
  rw [isIntegral_iff_forall]
  intro z hz
  rcases mem_adjoinVector_iff.mp hz with ⟨y, hy, c, rfl⟩
  have hyIntegral : Dyadic.IsIntegral K (q.quadratic y) :=
    (isIntegral_iff_forall q L).mp hL y hy
  have hcIntegral : Dyadic.IsIntegral K (c : K) :=
    (mem_integerRing_iff K).mpr c.property
  have hcxIntegral : Dyadic.IsIntegral K (q.quadratic (c • x)) := by
    rw [show c • x = (c : K) • x by rfl, q.quadratic_smul]
    exact Dyadic.isIntegral_mul K
      (by simpa [pow_two] using
        (Dyadic.isIntegral_mul K hcIntegral hcIntegral)) hx
  exact q.quadratic_add_integral_of_anisotropicSpace
    hq hyIntegral hcxIntegral

theorem IsOMaximal.mem_of_anisotropicSpace
    (hL : IsOMaximal q L) (hq : q.IsAnisotropicSpace)
    {x : V} (hx : Dyadic.IsIntegral K (q.quadratic x)) : x ∈ L := by
  have hadjoin : IsIntegral q (adjoinVector L x) :=
    adjoinVector_isIntegral_of_anisotropicSpace hq hL.isIntegral hx
  have heq := hL.eq_of_le (adjoinVector L x) (le_adjoinVector L x) hadjoin
  have hxmem : x ∈ adjoinVector L x := mem_adjoinVector L x
  rw [heq] at hxmem
  exact hxmem

theorem oMaximal_eq_of_anisotropicSpace
    (hL : IsOMaximal q L) (hq : q.IsAnisotropicSpace)
    {M : Lattice K V} (hM : IsOMaximal q M) : M = L := by
  apply Lattice.ext
  apply le_antisymm
  · intro x hx
    apply hL.mem_of_anisotropicSpace hq
    exact (isIntegral_iff_forall q M).mp hM.isIntegral x hx
  · intro x hx
    apply hM.mem_of_anisotropicSpace hq
    exact (isIntegral_iff_forall q L).mp hL.isIntegral x hx

theorem IsOMaximal.of_latticeIsometry
    {W : Type*} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (hL : IsOMaximal q L) (f : Isometry q r L M) : IsOMaximal r M := by
  refine ⟨(isIntegral_iff_of_latticeIsometry f).mp hL.isIntegral, ?_⟩
  intro N hMN hN
  let pre : Lattice K V := map f.toLinearEquiv.symm N
  have hLpre : L ≤ pre := by
    intro x hx
    change x ∈ pre
    rw [show pre = map f.toLinearEquiv.symm N by rfl, mem_map_iff]
    simpa using hMN ((f.map_mem x).mp hx)
  let preIso : Isometry r q N pre :=
    Isometry.toMap r f.symm.toQuadraticSpaceIsometry N
  have hpreIntegral : IsIntegral q pre :=
    (isIntegral_iff_of_latticeIsometry preIso).mp hN
  have hpreEq : pre = L := hL.eq_of_le pre hLpre hpreIntegral
  apply Lattice.ext
  ext y
  calc
    y ∈ N ↔ f.toLinearEquiv.symm y ∈ pre := by
      simpa only [pre] using
        (map_mem_map_iff f.toLinearEquiv.symm N y).symm
    _ ↔ f.toLinearEquiv.symm y ∈ L := by rw [hpreEq]
    _ ↔ y ∈ M := by
      simpa using f.map_mem (f.toLinearEquiv.symm y)

theorem isOMaximal_iff_of_latticeIsometry
    {W : Type*} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (f : Isometry q r L M) : IsOMaximal q L ↔ IsOMaximal r M := by
  constructor
  · intro hL
    exact hL.of_latticeIsometry f
  · intro hM
    exact hM.of_latticeIsometry f.symm

theorem orthogonalProduct_isIntegral
    {W : Type*} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (hL : IsIntegral q L) (hM : IsIntegral r M) :
    IsIntegral (q.orthogonalSum r) (product L M) := by
  rw [isIntegral_iff_forall]
  intro z hz
  rw [QuadraticSpace.orthogonalSum_quadratic_apply]
  exact Dyadic.isIntegral_add K
    ((isIntegral_iff_forall q L).mp hL z.1 hz.1)
    ((isIntegral_iff_forall r M).mp hM z.2 hz.2)

/-- Integrality of an orthogonal product restricts to its right factor. -/
theorem IsIntegral.right_of_orthogonalProduct
    {W : Type*} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (h : IsIntegral (q.orthogonalSum r) (product L M)) :
    IsIntegral r M := by
  rw [isIntegral_iff_forall]
  intro y hy
  have hpair : (0, y) ∈ product L M := by
    exact ⟨L.zero_mem, hy⟩
  have hvalue := (isIntegral_iff_forall (q.orthogonalSum r)
    (product L M)).mp h (0, y) hpair
  simpa using hvalue

/-- Integrality of an orthogonal product restricts to its left factor. -/
theorem IsIntegral.left_of_orthogonalProduct
    {W : Type*} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (h : IsIntegral (q.orthogonalSum r) (product L M)) :
    IsIntegral q L := by
  rw [isIntegral_iff_forall]
  intro x hx
  have hpair : (x, 0) ∈ product L M := by
    exact ⟨hx, M.zero_mem⟩
  have hvalue := (isIntegral_iff_forall (q.orthogonalSum r)
    (product L M)).mp h (x, 0) hpair
  simpa using hvalue

theorem IsOMaximal.right_of_orthogonalProduct
    {W : Type*} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (h : IsOMaximal (q.orthogonalSum r) (product L M)) :
    IsOMaximal r M := by
  refine ⟨?_, ?_⟩
  · rw [isIntegral_iff_forall]
    intro y hy
    have hpair : (0, y) ∈ product L M := by simp [hy]
    have := (isIntegral_iff_forall (q.orthogonalSum r)
      (product L M)).mp h.isIntegral (0, y) hpair
    simpa using this
  · intro N hMN hN
    have hleft : IsIntegral q L := by
      rw [isIntegral_iff_forall]
      intro x hx
      have hpair : (x, 0) ∈ product L M := by simp [hx]
      have := (isIntegral_iff_forall (q.orthogonalSum r)
        (product L M)).mp h.isIntegral (x, 0) hpair
      simpa using this
    have hprodIntegral :
        IsIntegral (q.orthogonalSum r) (product L N) :=
      orthogonalProduct_isIntegral hleft hN
    have hprodLe : product L M ≤ product L N := by
      intro z hz
      exact ⟨hz.1, hMN hz.2⟩
    have heq := h.eq_of_le (product L N) hprodLe hprodIntegral
    apply Lattice.ext
    ext y
    constructor
    · intro hy
      have hpair : (0, y) ∈ product L N := ⟨L.zero_mem, hy⟩
      rw [heq] at hpair
      exact hpair.2
    · intro hy
      exact hMN hy

theorem IsOMaximal.isotropic_mem_rescaleTwoDual
    (hL : IsOMaximal q L) {z : V}
    (hzdual : z ∈ dualLattice
      (q.rescaleUnit (Units.mk0 (2 : K) (by norm_num))) L)
    (hziso : (q.rescaleUnit (Units.mk0 (2 : K) (by norm_num))).quadratic z = 0) :
    z ∈ L := by
  let two : Kˣ := Units.mk0 (2 : K) (by norm_num)
  have hzq : q.quadratic z = 0 := by
    change (two : K) * q.quadratic z = 0 at hziso
    exact (mul_eq_zero.mp hziso).resolve_left (Units.ne_zero two)
  have hzpair : ∀ y : V, y ∈ L →
      2 * q.bilin z y ∈ IntegerRing K := by
    intro y hy
    have h := (mem_dualLattice_iff (q.rescaleUnit two) L z).mp
      (by simpa only [two] using hzdual) y hy
    change (2 : K) * q.bilin z y ∈ IntegerRing K at h
    exact h
  have hadjoin : IsIntegral q (adjoinVector L z) := by
    rw [isIntegral_iff_forall]
    intro x hx
    rcases mem_adjoinVector_iff.mp hx with ⟨y, hy, c, rfl⟩
    have hyq : Dyadic.IsIntegral K (q.quadratic y) :=
      (isIntegral_iff_forall q L).mp hL.isIntegral y hy
    have hcross : Dyadic.IsIntegral K
        (2 * q.bilin y ((c : K) • z)) := by
      have hzy := hzpair y hy
      have hmul : (c : K) * (2 * q.bilin z y) ∈ IntegerRing K :=
        (IntegerRing K).toSubring.mul_mem c.property hzy
      apply (mem_integerRing_iff K).mp
      rw [LinearMap.BilinForm.smul_right, q.isSymm.eq y z]
      convert hmul using 1 <;> ring
    change Dyadic.IsIntegral K (q.quadratic (y + (c : K) • z))
    rw [q.quadratic_add, q.quadratic_smul, hzq, mul_zero]
    simpa only [add_zero] using Dyadic.isIntegral_add K hyq hcross
  have heq := hL.eq_of_le (adjoinVector L z) (le_adjoinVector L z) hadjoin
  have hzmem : z ∈ adjoinVector L z := mem_adjoinVector L z
  rwa [heq] at hzmem

noncomputable def oMaximalRescaledTwoDecomposition
    (hL : IsOMaximal q L) {z : V} (hzNe : z ≠ 0)
    (hziso : q.quadratic z = 0) :
    OrthogonalDecomposition
      (q.rescaleUnit (Units.mk0 (2 : K) (by norm_num))) L 2 := by
  let two : Kˣ := Units.mk0 (2 : K) (by norm_num)
  let q2 := q.rescaleUnit two
  have hscale : scaleIdeal q2 L ≤ unitIdeal (K := K) := by
    exact scaleIdeal_rescaleTwo_le_unitIdeal hL.isIntegral
  have hclosed : ∀ {w : V}, w ∈ dualLattice q2 L →
      q2.quadratic w = 0 → w ∈ L := by
    intro w hw hwiso
    exact hL.isotropic_mem_rescaleTwoDual
      (by simpa only [q2, two] using hw)
      (by simpa only [q2, two] using hwiso)
  let E := exists_unit_smul_mem_not_mem_uniformizer_rescale L hzNe
  let t : Kˣ := Classical.choose E
  have hx : (t : K) • z ∈ L := (Classical.choose_spec E).1
  have hprimitive : (t : K) • z ∉
      rescale (uniformizerUnit K) L := (Classical.choose_spec E).2
  let x : V := (t : K) • z
  have hxisotropic : q2.quadratic x = 0 := by
    dsimp only [q2, x]
    rw [QuadraticSpace.rescaleUnit_quadratic, q.quadratic_smul,
      hziso, mul_zero, mul_zero]
  let P := omeara933PlaneData (q := q2) hscale hclosed
    (x := x) hx hprimitive hxisotropic
  exact P.splitting hscale hxisotropic hx

noncomputable def oMaximalRescaledTwoHeadIsometry
    (hL : IsOMaximal q L) {z : V} (hzNe : z ≠ 0)
    (hziso : q.quadratic z = 0) :
    let D := oMaximalRescaledTwoDecomposition hL hzNe hziso
    Isometry (D.component 0).space
      (QuadraticSpace.hyperbolicPlane (1 : Kˣ))
      (D.component 0).lattice (hyperbolicPlaneLattice (K := K)) := by
  let two : Kˣ := Units.mk0 (2 : K) (by norm_num)
  let q2 := q.rescaleUnit two
  have hscale : scaleIdeal q2 L ≤ unitIdeal (K := K) := by
    exact scaleIdeal_rescaleTwo_le_unitIdeal hL.isIntegral
  have hclosed : ∀ {w : V}, w ∈ dualLattice q2 L →
      q2.quadratic w = 0 → w ∈ L := by
    intro w hw hwiso
    exact hL.isotropic_mem_rescaleTwoDual
      (by simpa only [q2, two] using hw)
      (by simpa only [q2, two] using hwiso)
  let E := exists_unit_smul_mem_not_mem_uniformizer_rescale L hzNe
  let t : Kˣ := Classical.choose E
  have hx : (t : K) • z ∈ L := (Classical.choose_spec E).1
  have hprimitive : (t : K) • z ∉
      rescale (uniformizerUnit K) L := (Classical.choose_spec E).2
  let x : V := (t : K) • z
  have hxisotropic : q2.quadratic x = 0 := by
    dsimp only [q2, x]
    rw [QuadraticSpace.rescaleUnit_quadratic, q.quadratic_smul,
      hziso, mul_zero, mul_zero]
  let P := omeara933PlaneData (q := q2) hscale hclosed
    (x := x) hx hprimitive hxisotropic
  let raw := omeara933PlaneComponentIsometry
    P.pairing_eq hxisotropic P.partner_quadratic_integral
  let eta : K := q.quadratic P.partner
  have heta : eta ∈ IntegerRing K := by
    exact (mem_integerRing_iff K).mpr
      ((isIntegral_iff_forall q L).mp hL.isIntegral
        P.partner P.partner_mem)
  have hzero : (0 : K) ∈ IntegerRing K := (IntegerRing K).zero_mem
  have hnondeg : ((2 : K) * eta) * ((2 : K) * 0) ≠ 1 := by simp
  let e1 : Fin 2 → K := ![0, 1]
  have he1ne : e1 ≠ 0 := by
    intro heq
    have h := congrFun heq 1
    simp [e1] at h
  have he1iso :
      (QuadraticSpace.omearaGeneralPlane
        ((2 : K) * eta) ((2 : K) * 0) hnondeg).quadratic e1 = 0 := by
    rw [QuadraticSpace.quadratic,
      QuadraticSpace.omearaGeneralPlane_bilin_apply]
    simp [e1]
  let evenIso := Classical.choice
    (omeara9311_isotropic_even_plane_isIsometric
      eta 0 heta hzero hnondeg ⟨e1, he1ne, he1iso⟩)
  let evenIso' : Isometry
      (QuadraticSpace.omearaGeneralPlane ((2 : K) * eta) 0 (by simp))
      (QuadraticSpace.hyperbolicPlane (1 : Kˣ))
      (hyperbolicPlaneLattice (K := K))
      (hyperbolicPlaneLattice (K := K)) := by
    simpa only [mul_zero] using evenIso
  let identify := omearaGeneralPlaneZeroRightLatticeIsometry
    (K := K) ((2 : K) * eta)
  let result := raw.symm.trans identify.symm |>.trans evenIso'
  change Isometry (P.component hxisotropic).space
    (QuadraticSpace.hyperbolicPlane (1 : Kˣ))
    (P.component hxisotropic).lattice
    (hyperbolicPlaneLattice (K := K))
  exact result

noncomputable def oMaximalHyperbolicSplitIsometry
    (hL : IsOMaximal q L) {z : V} (hzNe : z ≠ 0)
    (hziso : q.quadratic z = 0) :
    let D := oMaximalRescaledTwoDecomposition hL hzNe hziso
    Isometry
      ((QuadraticSpace.hyperbolicPlane (dyadicHalfUnit (K := K))).orthogonalSum
        ((D.component 1).space.rescaleUnit (dyadicHalfUnit (K := K))))
      q
      (product (hyperbolicPlaneLattice (K := K))
        (D.component 1).lattice) L := by
  let D := oMaximalRescaledTwoDecomposition hL hzNe hziso
  let half : Kˣ := dyadicHalfUnit (K := K)
  let head := oMaximalRescaledTwoHeadIsometry hL hzNe hziso
  let headHalf := (head.rescaleUnitBoth half).trans
    (hyperbolicOneRescaleHalfIsometry (K := K))
  let tailForm := (D.component 1).space.rescaleUnit half
  let tailIdentity := Isometry.refl tailForm (D.component 1).lattice
  let separate := headHalf.symm.orthogonalProductBasic tailIdentity
  let distribute := rescaleUnitOrthogonalProductIsometry
    (D.component 0).space (D.component 1).space
    (D.component 0).lattice (D.component 1).lattice half
  let pair := D.pairProductLatticeIsometry.rescaleUnitBoth half
  let restore := rescaleTwoHalfIsometry q L
  exact separate.trans distribute.symm |>.trans pair |>.trans restore

theorem oMaximalHyperbolicSplit_residual_isOMaximal
    (hL : IsOMaximal q L) {z : V} (hzNe : z ≠ 0)
    (hziso : q.quadratic z = 0) :
    let D := oMaximalRescaledTwoDecomposition hL hzNe hziso
    IsOMaximal
      ((D.component 1).space.rescaleUnit (dyadicHalfUnit (K := K)))
      (D.component 1).lattice := by
  let D := oMaximalRescaledTwoDecomposition hL hzNe hziso
  let f := oMaximalHyperbolicSplitIsometry hL hzNe hziso
  have hproduct : IsOMaximal
      ((QuadraticSpace.hyperbolicPlane
        (dyadicHalfUnit (K := K))).orthogonalSum
        ((D.component 1).space.rescaleUnit (dyadicHalfUnit (K := K))))
      (product (hyperbolicPlaneLattice (K := K))
        (D.component 1).lattice) :=
    (isOMaximal_iff_of_latticeIsometry f).mpr hL
  exact hproduct.right_of_orthogonalProduct

theorem oMaximal_isIsometric_of_isometric
    {W : Type*} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (hL : IsOMaximal q L) (hM : IsOMaximal r M)
    (ambient : q.IsIsometric r) : IsIsometric q r L M := by
  letI : Module.Finite K V := L.moduleFinite
  letI : Module.Finite K W := M.moduleFinite
  generalize hn : Module.finrank K V = n
  induction n using Nat.strong_induction_on generalizing V W with
  | h n ih =>
      rcases ambient with ⟨g⟩
      by_cases han : q.IsAnisotropicSpace
      · let pre : Lattice K V := map g.toLinearEquiv.symm M
        let preIso : Isometry r q M pre :=
          Isometry.toMap r g.symm M
        have hpre : IsOMaximal q pre :=
          hM.of_latticeIsometry preIso
        have heq : pre = L :=
          oMaximal_eq_of_anisotropicSpace hL han hpre
        have f := preIso.symm
        rw [heq] at f
        exact ⟨f⟩
      · rw [QuadraticSpace.IsAnisotropicSpace] at han
        push Not at han
        obtain ⟨z, hziso, hzNe⟩ := han
        let z' : W := g.toLinearEquiv z
        have hz'Ne : z' ≠ 0 := by
          simpa [z'] using g.toLinearEquiv.injective.ne hzNe
        have hz'iso : r.quadratic z' = 0 := by
          exact (g.map_quadratic z).trans hziso
        let D := oMaximalRescaledTwoDecomposition hL hzNe hziso
        let E := oMaximalRescaledTwoDecomposition hM hz'Ne hz'iso
        let fL := oMaximalHyperbolicSplitIsometry hL hzNe hziso
        let fM := oMaximalHyperbolicSplitIsometry hM hz'Ne hz'iso
        let qTail :=
          (D.component 1).space.rescaleUnit (dyadicHalfUnit (K := K))
        let rTail :=
          (E.component 1).space.rescaleUnit (dyadicHalfUnit (K := K))
        let LTail := (D.component 1).lattice
        let MTail := (E.component 1).lattice
        letI : Module.Finite K (D.component 1).carrier := LTail.moduleFinite
        letI : Module.Finite K (E.component 1).carrier := MTail.moduleFinite
        have htotal : QuadraticSpace.Isometry
            ((QuadraticSpace.hyperbolicPlane
              (dyadicHalfUnit (K := K))).orthogonalSum qTail)
            ((QuadraticSpace.hyperbolicPlane
              (dyadicHalfUnit (K := K))).orthogonalSum rTail) :=
          fL.toQuadraticSpaceIsometry.trans g |>.trans
            fM.symm.toQuadraticSpaceIsometry
        let htailAmbient : QuadraticSpace.Isometry qTail rTail :=
          QuadraticSpace.orthogonalSumCancel
            (QuadraticSpace.hyperbolicPlane (dyadicHalfUnit (K := K)))
            (QuadraticSpace.hyperbolicPlane (dyadicHalfUnit (K := K)))
            qTail rTail
            (QuadraticSpace.Isometry.refl _)
            htotal
        have htailRank : Module.finrank K (D.component 1).carrier < n := by
          have hrank := fL.toLinearEquiv.finrank_eq
          change Module.finrank K
              ((Fin 2 → K) × (D.component 1).carrier) =
            Module.finrank K V at hrank
          rw [Module.finrank_prod, Module.finrank_fin_fun] at hrank
          omega
        have hLTail : IsOMaximal qTail LTail :=
          oMaximalHyperbolicSplit_residual_isOMaximal hL hzNe hziso
        have hMTail : IsOMaximal rTail MTail :=
          oMaximalHyperbolicSplit_residual_isOMaximal hM hz'Ne hz'iso
        have htailIso : IsIsometric qTail rTail LTail MTail :=
          ih (Module.finrank K (D.component 1).carrier) htailRank
            hLTail hMTail ⟨htailAmbient⟩ rfl
        let tailIso := Classical.choice htailIso
        let headIso := Isometry.refl
          (QuadraticSpace.hyperbolicPlane (dyadicHalfUnit (K := K)))
          (hyperbolicPlaneLattice (K := K))
        exact ⟨fL.symm.trans (headIso.orthogonalProductBasic tailIso) |>.trans fM⟩

end Bong.Lattice
