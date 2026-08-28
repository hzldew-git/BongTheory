/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Projection

/-!
# Mixed pairings controlled by a norm generator

This file proves the dyadic mixed-pairing estimate in Beli's Lemma 2.2.
If `x` is a norm generator of `M`, `nN ≤ nM`, and the projection of `N`
is contained in the projection of `M`, then

`2 B(M, N) ⊆ nM`.

The proof follows Beli's argument without normalizing `Q(x)` to one.  Its key
valuation-ring step is that `b² - g²` and `2g` integral imply `b - g`
integral.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

namespace Lattice

/-- In a valuation ring, integrality of `b² - g²` and `2g` implies that of `b - g`. -/
theorem sub_mem_integerRing_of_sq_sub_sq_mem
    {b g : K} (hsq : b ^ 2 - g ^ 2 ∈ IntegerRing K)
    (htwo : (2 : K) * g ∈ IntegerRing K) : b - g ∈ IntegerRing K := by
  change b - g ∈ (IntegerRing K).toSubring
  have hfac : (b - g) * (b + g) ∈ IntegerRing K := by
    convert hsq using 1
    ring
  rcases (IntegerRing K).mem_or_inv_mem (b - g) with h | hinv
  · exact h
  · by_cases hzero : b - g = 0
    · rw [hzero]
      exact (IntegerRing K).zero_mem
    · have hplus : b + g ∈ (IntegerRing K).toSubring := by
        have hmul := (IntegerRing K).toSubring.mul_mem hinv hfac
        convert hmul using 1
        field_simp
      have hsub := (IntegerRing K).toSubring.sub_mem hplus htwo
      convert hsub using 1
      ring

omit [ValuativeRel K] [TopologicalSpace K] [DyadicContext K] in
/-- Orthogonal projection separates the quadratic value into line and tail terms. -/
theorem quadratic_projection_decomposition (q : QuadraticSpace K V)
    (x : V) (anisotropic : q.IsAnisotropic x) (y : V) :
    q.quadratic y =
      (q.bilin x y / q.quadratic x) ^ 2 * q.quadratic x +
        q.quadratic (q.orthogonalProjection x y) := by
  let a := q.bilin x y / q.quadratic x
  have hy : y = a • x + q.orthogonalProjection x y := by
    rw [q.orthogonalProjection_apply]
    dsimp [a]
    abel
  have horth := q.bilin_orthogonalProjection_eq_zero anisotropic y
  calc
    q.quadratic y = q.quadratic (a • x + q.orthogonalProjection x y) :=
      congrArg q.quadratic hy
    _ = a ^ 2 * q.quadratic x +
        q.quadratic (q.orthogonalProjection x y) := by
      rw [q.quadratic_add, q.quadratic_smul]
      simp only [LinearMap.BilinForm.smul_left, horth, mul_zero]
      ring

theorem mem_integerRing_of_mul_mem_principalIdeal
    {a c : K} (ha : a ≠ 0)
    (h : a * c ∈ principalIdeal (K := K) a) : c ∈ IntegerRing K := by
  rw [principalIdeal, Submodule.mem_span_singleton] at h
  rcases h with ⟨d, hd⟩
  have hdc : (d : K) = c := by
    apply mul_right_cancel₀ ha
    calc
      (d : K) * a = a * c := by simpa [Algebra.smul_def] using hd
      _ = c * a := mul_comm _ _
  rw [← hdc]
  exact d.property

theorem mul_mem_principalIdeal_of_mem_integerRing
    (a c : K) (hc : c ∈ IntegerRing K) :
    a * c ∈ principalIdeal (K := K) a := by
  rw [principalIdeal, Submodule.mem_span_singleton]
  refine ⟨⟨c, hc⟩, ?_⟩
  simp [Algebra.smul_def, mul_comm]

/-- Twice the coefficient of a lattice vector along a norm generator is integral. -/
theorem two_projectionCoefficient_mem_integerRing
    (q : QuadraticSpace K V) (L : Lattice K V) (x y : V)
    (generator : IsNormGenerator q L x) (anisotropic : q.IsAnisotropic x)
    (hy : y ∈ L) :
    (2 : K) * (q.bilin x y / q.quadratic x) ∈ IntegerRing K := by
  have hpair :
      (2 : IntegerRing K) • q.bilin x y ∈ normIdeal q L :=
    two_smul_mem_normIdeal q L
      (bilin_mem_scaleIdeal_of_mem q L generator.mem hy)
  rw [generator.normIdeal_eq] at hpair
  apply mem_integerRing_of_mul_mem_principalIdeal anisotropic
  have heq :
      q.quadratic x * (2 * (q.bilin x y / q.quadratic x)) =
        (2 : IntegerRing K) • q.bilin x y := by
    change q.quadratic x * (2 * (q.bilin x y / q.quadratic x)) =
      (2 : K) * q.bilin x y
    calc
      q.quadratic x * (2 * (q.bilin x y / q.quadratic x)) =
          2 * ((q.bilin x y / q.quadratic x) * q.quadratic x) := by ring
      _ = 2 * q.bilin x y := by rw [div_mul_cancel₀ _ anisotropic]
  rw [heq]
  exact hpair

/-- The mixed-pairing estimate used in Beli's proof of Lemma 2.2. -/
theorem two_bilin_mem_normIdeal_of_normGenerator
    (q : QuadraticSpace K V) (M N : Lattice K V) (x : V)
    (generator : IsNormGenerator q M x) (anisotropic : q.IsAnisotropic x)
    (norm_le : normIdeal q N ≤ normIdeal q M)
    (projection_le :
      projectedLattice q N x anisotropic ≤ projectedLattice q M x anisotropic)
    (y z : V) (hy : y ∈ M) (hz : z ∈ N) :
    (2 : IntegerRing K) • q.bilin y z ∈ normIdeal q M := by
  have hpzN :
      q.projectionToOrthogonal x anisotropic z ∈
        projectedLattice q N x anisotropic :=
    projection_mem_projectedLattice q N x anisotropic hz
  have hpzM := projection_le hpzN
  rcases (mem_projectedLattice_iff q M x anisotropic
    (q.projectionToOrthogonal x anisotropic z)).mp hpzM with
      ⟨w, hw, hwp⟩
  let a := q.bilin x y / q.quadratic x
  let b := q.bilin x z / q.quadratic x
  let g := q.bilin x w / q.quadratic x
  have hproj : q.orthogonalProjection x w = q.orthogonalProjection x z :=
    congrArg Subtype.val hwp
  have hqdiff : q.quadratic z - q.quadratic w ∈ normIdeal q M :=
    (normIdeal q M).sub_mem
      (norm_le (quadratic_mem_normIdeal_of_mem q N hz))
      (quadratic_mem_normIdeal_of_mem q M hw)
  have hquad :
      q.quadratic z - q.quadratic w =
        (b ^ 2 - g ^ 2) * q.quadratic x := by
    rw [quadratic_projection_decomposition q x anisotropic z,
      quadratic_projection_decomposition q x anisotropic w]
    change
      b ^ 2 * q.quadratic x + q.quadratic (q.orthogonalProjection x z) -
          (g ^ 2 * q.quadratic x +
            q.quadratic (q.orthogonalProjection x w)) =
        (b ^ 2 - g ^ 2) * q.quadratic x
    rw [hproj]
    ring
  have hsq : b ^ 2 - g ^ 2 ∈ IntegerRing K := by
    apply mem_integerRing_of_mul_mem_principalIdeal anisotropic
    rw [mul_comm, ← hquad, ← generator.normIdeal_eq]
    exact hqdiff
  have htwoG : (2 : K) * g ∈ IntegerRing K :=
    two_projectionCoefficient_mem_integerRing
      q M x w generator anisotropic hw
  have hbg : b - g ∈ IntegerRing K :=
    sub_mem_integerRing_of_sq_sub_sq_mem hsq htwoG
  have htwoA : (2 : K) * a ∈ IntegerRing K :=
    two_projectionCoefficient_mem_integerRing
      q M x y generator anisotropic hy
  have hcoefficient : ((2 : K) * a) * (b - g) ∈ IntegerRing K :=
    (IntegerRing K).toSubring.mul_mem htwoA hbg
  have hterm :
      (((2 : K) * a) * (b - g)) * q.quadratic x ∈ normIdeal q M := by
    rw [generator.normIdeal_eq, mul_comm]
    exact mul_mem_principalIdeal_of_mem_integerRing
      (q.quadratic x) (((2 : K) * a) * (b - g)) hcoefficient
  have hpairYW :
      (2 : IntegerRing K) • q.bilin y w ∈ normIdeal q M :=
    two_smul_mem_normIdeal q M (bilin_mem_scaleIdeal_of_mem q M hy hw)
  have hzdecomp : z = b • x + q.orthogonalProjection x z := by
    rw [q.orthogonalProjection_apply]
    dsimp [b]
    abel
  have hwdecomp : w = g • x + q.orthogonalProjection x w := by
    rw [q.orthogonalProjection_apply]
    dsimp [g]
    abel
  have hzw : z - w = (b - g) • x := by
    rw [hzdecomp, hwdecomp, hproj]
    module
  have hbzw :
      q.bilin y z - q.bilin y w = (b - g) * q.bilin y x := by
    calc
      q.bilin y z - q.bilin y w = q.bilin y (z - w) := by
        rw [LinearMap.BilinForm.sub_right]
      _ = q.bilin y ((b - g) • x) := congrArg (q.bilin y) hzw
      _ = (b - g) * q.bilin y x := by
        rw [LinearMap.BilinForm.smul_right]
  have hbilinYX : q.bilin y x = a * q.quadratic x := by
    rw [q.isSymm.eq]
    dsimp [a]
    exact (div_mul_cancel₀ _ anisotropic).symm
  have hpair :
      (2 : K) * q.bilin y z =
        (2 : K) * q.bilin y w +
          (((2 : K) * a) * (b - g)) * q.quadratic x := by
    rw [hbilinYX] at hbzw
    calc
      (2 : K) * q.bilin y z =
          2 * q.bilin y w + 2 * (q.bilin y z - q.bilin y w) := by ring
      _ = 2 * q.bilin y w + 2 * ((b - g) * (a * q.quadratic x)) := by
        rw [hbzw]
      _ = 2 * q.bilin y w + ((2 * a) * (b - g)) * q.quadratic x := by
        ring
  have hsum := (normIdeal q M).add_mem hpairYW hterm
  convert hsum using 1
  simpa only [Algebra.smul_def, map_ofNat] using hpair

end Lattice

end Bong
