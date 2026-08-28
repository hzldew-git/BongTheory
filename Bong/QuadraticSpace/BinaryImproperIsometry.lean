/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.QuadraticSpace.ReflectionGeneration
import Bong.QuadraticSpace.OrthogonalExtension

/-!
# Improper isometries of a binary quadratic space

An isometry of a nondegenerate binary quadratic space with determinant
`-1` is a single reflection.  This is the rank-two geometric reduction used
in the local spinor-norm calculations of Hsia and Xu.
-/

namespace Bong

namespace QuadraticSpace

universe u v

variable {K : Type u} [Field K] [CharZero K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V}

/-- In a one-dimensional nondegenerate quadratic space every nonzero vector
is anisotropic. -/
theorem isAnisotropic_of_ne_zero_of_finrank_eq_one
    [FiniteDimensional K V] (hfin : Module.finrank K V = 1)
    {x : V} (hx : x ≠ 0) : q.IsAnisotropic x := by
  intro hquadratic
  apply hx
  apply q.nondegenerate.1
  intro y
  rcases (finrank_eq_one_iff_of_nonzero' x hx).1 hfin y with
    ⟨c, rfl⟩
  rw [LinearMap.BilinForm.smul_right]
  change c * q.quadratic x = 0
  rw [hquadratic, mul_zero]

/-- On a one-dimensional vector space, the determinant determines a linear
equivalence. -/
theorem linearEquiv_eq_of_finrank_eq_one_of_det_eq
    [FiniteDimensional K V] (hfin : Module.finrank K V = 1)
    (f g : V ≃ₗ[K] V) (hdet : LinearEquiv.det f = LinearEquiv.det g) :
    f = g := by
  obtain ⟨a, ha, _⟩ :=
    LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hfin f.toLinearMap
  obtain ⟨b, hb, _⟩ :=
    LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hfin g.toLinearMap
  have hdetA : LinearMap.det f.toLinearMap = a := by
    rw [ha, LinearMap.det_smul, hfin]
    simp
  have hdetB : LinearMap.det g.toLinearMap = b := by
    rw [hb, LinearMap.det_smul, hfin]
    simp
  have hab : a = b := by
    have hcoe := congrArg Units.val hdet
    rw [LinearEquiv.coe_det, LinearEquiv.coe_det, hdetA, hdetB] at hcoe
    exact hcoe
  apply LinearEquiv.ext
  intro x
  have hmaps : f.toLinearMap = g.toLinearMap := by
    rw [ha, hb, hab]
  exact DFunLike.congr_fun hmaps x

/-- A determinant-one isometry of a binary quadratic space which fixes an
anisotropic vector is the identity. -/
theorem Isometry.eq_refl_of_fix_of_det_one_of_finrank_eq_two
    [FiniteDimensional K V] (f : Isometry q q) {x : V}
    (hx : q.IsAnisotropic x)
    (hfin : Module.finrank K V = 2)
    (hfix : f.toLinearEquiv x = x)
    (hdet : LinearEquiv.det f.toLinearEquiv = 1) :
    f = Isometry.refl q := by
  let r := restrictFixingVector (hx := hx) f hfix
  have hperpFin : Module.finrank K (q.vectorOrthogonal x) = 1 := by
    have h := q.finrank_vectorOrthogonal hx
    rw [hfin] at h
    omega
  have hdetR : LinearEquiv.det r.toLinearEquiv = 1 := by
    have hext := det_orthogonalExtensionLinearEquiv r
    have hrecover := orthogonalExtensionIsometry_restrictFixingVector
      (hx := hx) f hfix
    have hlinear := congrArg Isometry.toLinearEquiv hrecover
    change orthogonalExtensionLinearEquiv r = f.toLinearEquiv at hlinear
    rw [hlinear] at hext
    exact hext.symm.trans hdet
  have hr : r.toLinearEquiv = LinearEquiv.refl K (q.vectorOrthogonal x) := by
    apply linearEquiv_eq_of_finrank_eq_one_of_det_eq hperpFin
    simpa using hdetR
  rw [← orthogonalExtensionIsometry_restrictFixingVector
    (hx := hx) f hfix]
  have hrIso : r = Isometry.refl (q.orthogonalSpace x hx) := by
    apply Isometry.ext
    intro z
    exact DFunLike.congr_fun hr z
  change orthogonalExtensionIsometry r = Isometry.refl q
  rw [hrIso]
  exact orthogonalExtensionIsometry_refl

/-- Equal-valued anisotropic vectors in a binary quadratic space cannot
differ by a nonzero isotropic vector. -/
theorem eq_of_equalValue_of_not_isAnisotropic_sub_of_finrank_eq_two
    [FiniteDimensional K V] {x y : V}
    (hx : q.IsAnisotropic x)
    (hfin : Module.finrank K V = 2)
    (heq : q.quadratic x = q.quadratic y)
    (hsub : ¬q.IsAnisotropic (x - y)) :
    x = y := by
  have hsubQuadratic : q.quadratic (x - y) = 0 := by
    simpa [IsAnisotropic] using hsub
  have horth : q.bilin x (x - y) = 0 := by
    have hsubExpanded :
        q.quadratic (x - y) =
          q.quadratic x + q.quadratic y - 2 * q.bilin x y := by
      rw [show x - y = x + (-y) by abel, q.quadratic_add,
        q.quadratic_neg, LinearMap.BilinForm.neg_right]
      ring
    have hxy : q.bilin x y = q.quadratic x := by
      have hsum : 2 * q.bilin x y =
          q.quadratic x + q.quadratic y := by
        rw [hsubQuadratic] at hsubExpanded
        linear_combination hsubExpanded
      have htwice : (2 : K) * q.bilin x y =
          (2 : K) * q.quadratic x := by
        rw [hsum, ← heq]
        ring
      exact mul_left_cancel₀ (by norm_num : (2 : K) ≠ 0) htwice
    rw [LinearMap.BilinForm.sub_right]
    change q.quadratic x - q.bilin x y = 0
    rw [hxy, sub_self]
  let z : q.vectorOrthogonal x := ⟨x - y,
    (q.mem_vectorOrthogonal_iff x (x - y)).2 horth⟩
  have hperpFin : Module.finrank K (q.vectorOrthogonal x) = 1 := by
    have h := q.finrank_vectorOrthogonal hx
    rw [hfin] at h
    omega
  have hzZero : z = 0 := by
    by_contra hz
    have hzAnisotropic :=
      isAnisotropic_of_ne_zero_of_finrank_eq_one
        (q := q.orthogonalSpace x hx) hperpFin hz
    exact hzAnisotropic hsubQuadratic
  have hxyZero : x - y = 0 := by
    exact congrArg Subtype.val hzZero
  exact sub_eq_zero.mp hxyZero

/-- Every determinant-`-1` isometry of a nondegenerate binary quadratic
space is reflection in an anisotropic vector. -/
theorem Isometry.exists_eq_reflection_of_det_neg_one_of_finrank_eq_two
    [FiniteDimensional K V] (f : Isometry q q)
    (hfin : Module.finrank K V = 2)
    (hdet : LinearEquiv.det f.toLinearEquiv = (-1 : Kˣ)) :
    ∃ (x : V) (hx : q.IsAnisotropic x),
      f = q.reflectionIsometry x hx := by
  have hpos : 0 < Module.finrank K V := by omega
  obtain ⟨x, hx⟩ := q.exists_isAnisotropic_of_finrank_pos hpos
  let y : V := f.toLinearEquiv x
  have hy : q.IsAnisotropic y := by
    change q.quadratic (f.toLinearEquiv x) ≠ 0
    rw [f.map_quadratic]
    exact hx
  have heq : q.quadratic x = q.quadratic y := by
    exact (f.map_quadratic x).symm
  by_cases hsub : q.IsAnisotropic (x - y)
  · let r := q.reflectionIsometry (x - y) hsub
    have hrx : r.toLinearEquiv x = y :=
      q.reflectionLinearEquiv_sub_apply_left_of_equalValue x y hsub heq
    have hfix : (f.trans r).toLinearEquiv x = x := by
      change r.toLinearEquiv y = x
      rw [← hrx]
      exact q.reflectionLinearEquiv_involutive (x - y) hsub x
    have hdetProduct :
        LinearEquiv.det (f.trans r).toLinearEquiv = 1 := by
      change LinearEquiv.det (f.toLinearEquiv.trans r.toLinearEquiv) = 1
      have hdetR : LinearEquiv.det r.toLinearEquiv = (-1 : Kˣ) :=
        q.det_reflectionLinearEquiv hsub
      rw [LinearEquiv.det_trans, hdetR, hdet]
      norm_num
    have hid := Isometry.eq_refl_of_fix_of_det_one_of_finrank_eq_two
      (f.trans r) hx hfin hfix hdetProduct
    refine ⟨x - y, hsub, ?_⟩
    apply Isometry.ext
    intro z
    have happ := congrArg
      (fun g : Isometry q q => g.toLinearEquiv z) hid
    change r.toLinearEquiv (f.toLinearEquiv z) = z at happ
    apply r.toLinearEquiv.injective
    change r.toLinearEquiv (f.toLinearEquiv z) =
      r.toLinearEquiv (r.toLinearEquiv z)
    dsimp only [r] at happ ⊢
    change q.reflectionLinearEquiv (x - y) hsub (f.toLinearEquiv z) =
      q.reflectionLinearEquiv (x - y) hsub
        (q.reflectionLinearEquiv (x - y) hsub z)
    change q.reflectionLinearEquiv (x - y) hsub (f.toLinearEquiv z) = z
      at happ
    rw [q.reflectionLinearEquiv_involutive (x - y) hsub]
    exact happ
  · have hxy : x = y :=
      eq_of_equalValue_of_not_isAnisotropic_sub_of_finrank_eq_two
        hx hfin heq hsub
    have hfix : f.toLinearEquiv x = x := by simpa [y] using hxy.symm
    let r := restrictFixingVector (hx := hx) f hfix
    have hperpFin : Module.finrank K (q.vectorOrthogonal x) = 1 := by
      have h := q.finrank_vectorOrthogonal hx
      rw [hfin] at h
      omega
    have hperpPos : 0 < Module.finrank K (q.vectorOrthogonal x) := by
      omega
    obtain ⟨z, hz⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hperpPos
    have hzAnisotropic :
        (q.orthogonalSpace x hx).IsAnisotropic z :=
      isAnisotropic_of_ne_zero_of_finrank_eq_one hperpFin hz
    let s := (q.orthogonalSpace x hx).reflectionIsometry z hzAnisotropic
    have hdetR : LinearEquiv.det r.toLinearEquiv = (-1 : Kˣ) := by
      have hext := det_orthogonalExtensionLinearEquiv r
      have hrecover := orthogonalExtensionIsometry_restrictFixingVector
        (hx := hx) f hfix
      have hlinear := congrArg Isometry.toLinearEquiv hrecover
      change orthogonalExtensionLinearEquiv r = f.toLinearEquiv at hlinear
      rw [hlinear] at hext
      exact hext.symm.trans hdet
    have hrs : r.toLinearEquiv = s.toLinearEquiv := by
      apply linearEquiv_eq_of_finrank_eq_one_of_det_eq hperpFin
      rw [hdetR]
      exact ((q.orthogonalSpace x hx).det_reflectionLinearEquiv
        hzAnisotropic).symm
    refine ⟨(z : V), hzAnisotropic, ?_⟩
    rw [← orthogonalExtensionIsometry_restrictFixingVector
      (hx := hx) f hfix]
    rw [← q.orthogonalExtensionIsometry_reflection
      x hx z hzAnisotropic]
    have hrsIso : r = s := by
      apply Isometry.ext
      intro t
      exact DFunLike.congr_fun hrs t
    change orthogonalExtensionIsometry r = orthogonalExtensionIsometry s
    rw [hrsIso]

end QuadraticSpace

end Bong
