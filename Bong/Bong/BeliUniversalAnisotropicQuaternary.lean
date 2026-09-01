/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.DiagonalQuaternaryUniversalityProof
import Bong.Bong.DiagonalLocalClassificationProof
import Bong.Lattice.OMaximalUniqueness

/-!
# The anisotropic quaternary space in Beli's Corollary 4.5(ii)

This file proves, rather than assumes, the dyadic local fact used in
Corollary 4.5(ii): every anisotropic quaternary quadratic space is isometric
to the paper's diagonal model `[1, -Δ, π, -Δπ]`.  The proof diagonalizes
the space, writes a square-determinant quaternary form as a scalar multiple
of a quaternion norm, removes that scalar by explicit quaternion
multiplication, and applies O'Meara 63:11b.
-/

namespace Bong

open Dyadic Module BONG.GoodBONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- A scalar multiple of the reduced norm form of the quaternion symbol
`(a,b)`. -/
def scaledQuaternionNormCoefficients (c a b : Kˣ) : Fin 4 → K :=
  fun i => (c : K) * quaternionNormCoefficients a b i

/-- A zero of a binary norm form is trivial when its defining parameter is
nonsquare. -/
theorem quadraticNorm_zero_of_not_isSquare
    (a : Kˣ) (ha : ¬ IsSquare a) {x y : K}
    (hxy : x ^ 2 - (a : K) * y ^ 2 = 0) : x = 0 ∧ y = 0 := by
  by_cases hy : y = 0
  · subst y
    have hxSq : x ^ 2 = 0 := by simpa using hxy
    exact ⟨sq_eq_zero_iff.mp hxSq, rfl⟩
  · have hx : x ≠ 0 := by
      intro hx
      subst x
      have : (a : K) * y ^ 2 = 0 := by simpa using hxy.symm
      exact (mul_ne_zero (Units.ne_zero a) (pow_ne_zero 2 hy)) this
    apply False.elim
    apply ha
    let s : Kˣ := Units.mk0 (x / y) (div_ne_zero hx hy)
    refine ⟨s, ?_⟩
    apply Units.ext
    change (a : K) = (x / y) * (x / y)
    have haField : (a : K) * y ^ 2 = x ^ 2 := by
      linear_combination -hxy
    field_simp [hy]
    simpa [pow_two] using haField

/-- The quaternion norm form is anisotropic exactly when the second
parameter is not a norm from the first quadratic algebra. -/
theorem quaternionNorm_anisotropic_iff_nonnorm (a b : Kˣ) :
    DiagonalAnisotropic (quaternionNormCoefficients a b) ↔
      ¬ IsQuadraticNorm K a b := by
  constructor
  · intro han hnorm
    rcases hnorm with ⟨x, y, hxy⟩
    let z : Fin 4 → K := ![x, y, 1, 0]
    have hzNe : z ≠ 0 := by
      intro hz
      have := congrFun hz (2 : Fin 4)
      simp [z] at this
    apply hzNe
    apply han z
    simp [quaternionNormCoefficients, diagonalQuadratic,
      Fin.sum_univ_four, z]
    linear_combination hxy
  · intro hnorm z hz
    have ha : ¬ IsSquare a := by
      intro ha
      exact hnorm (isQuadraticNorm_of_isSquare_left K ha)
    let p : K := z 0 ^ 2 - (a : K) * z 1 ^ 2
    let q : K := z 2 ^ 2 - (a : K) * z 3 ^ 2
    have hpq : p = (b : K) * q := by
      simp [quaternionNormCoefficients, diagonalQuadratic,
        Fin.sum_univ_four] at hz
      dsimp only [p, q]
      linear_combination hz
    by_cases hq : q = 0
    · have hp : p = 0 := by rw [hpq, hq, mul_zero]
      have hzero := quadraticNorm_zero_of_not_isSquare a ha
        (x := z 0) (y := z 1) (by simpa only [p] using hp)
      have htwo := quadraticNorm_zero_of_not_isSquare a ha
        (x := z 2) (y := z 3) (by simpa only [q] using hq)
      funext i
      fin_cases i
      · exact hzero.1
      · exact hzero.2
      · exact htwo.1
      · exact htwo.2
    · have hp : p ≠ 0 := by
        rw [hpq]
        exact mul_ne_zero (Units.ne_zero b) hq
      let pu : Kˣ := Units.mk0 p hp
      let qu : Kˣ := Units.mk0 q hq
      have hpNorm : IsQuadraticNorm K a pu := by
        refine ⟨z 0, z 1, ?_⟩
        rfl
      have hqNorm : IsQuadraticNorm K a qu := by
        refine ⟨z 2, z 3, ?_⟩
        rfl
      have hb : b = pu * qu⁻¹ := by
        apply Units.ext
        change (b : K) = p * q⁻¹
        rw [hpq]
        field_simp [hq]
      apply False.elim
      apply hnorm
      rw [hb]
      exact hpNorm.mul K hqNorm.inv

/-- Left multiplication by a quaternion of norm `c` gives the standard
similitude from `c N_{a,b}` to `N_{a,b}`. -/
theorem scaledQuaternionNorm_represents_quaternionNorm
    (c a b : Kˣ) :
    DiagonalRepresents (scaledQuaternionNormCoefficients c a b)
      (quaternionNormCoefficients a b) := by
  obtain ⟨t, ht⟩ := quaternionNorm_exists_value a b c
  have ht' :
      t 0 ^ 2 - (a : K) * t 1 ^ 2 - (b : K) * t 2 ^ 2 +
          ((a : K) * (b : K)) * t 3 ^ 2 = (c : K) := by
    simp [quaternionNormCoefficients, diagonalQuadratic,
      Fin.sum_univ_four] at ht
    linear_combination ht
  let f : (Fin 4 → K) →ₗ[K] (Fin 4 → K) :=
    { toFun := fun z => ![
          t 0 * z 0 + (a : K) * t 1 * z 1 +
            (b : K) * t 2 * z 2 - (a : K) * (b : K) * t 3 * z 3,
          t 0 * z 1 + t 1 * z 0 - (b : K) * t 2 * z 3 +
            (b : K) * t 3 * z 2,
          t 0 * z 2 + t 2 * z 0 + (a : K) * t 1 * z 3 -
            (a : K) * t 3 * z 1,
          t 0 * z 3 + t 3 * z 0 + t 1 * z 2 - t 2 * z 1]
      map_add' := by
        intro x y
        funext i
        fin_cases i <;> simp <;> ring
      map_smul' := by
        intro s x
        funext i
        fin_cases i <;> simp <;> ring }
  let g : (Fin 4 → K) → (Fin 4 → K) := fun w => ![
      (t 0 * w 0 - (a : K) * t 1 * w 1 -
        (b : K) * t 2 * w 2 + (a : K) * (b : K) * t 3 * w 3) / (c : K),
      (t 0 * w 1 - t 1 * w 0 + (b : K) * t 2 * w 3 -
        (b : K) * t 3 * w 2) / (c : K),
      (t 0 * w 2 - t 2 * w 0 - (a : K) * t 1 * w 3 +
        (a : K) * t 3 * w 1) / (c : K),
      (t 0 * w 3 - t 3 * w 0 - t 1 * w 2 + t 2 * w 1) / (c : K)]
  have hleft : ∀ z, g (f z) = z := by
    intro z
    funext i
    fin_cases i
    · simp [g, f]
      field_simp [Units.ne_zero c]
      linear_combination (z 0) * ht'
    · simp [g, f]
      field_simp [Units.ne_zero c]
      linear_combination (z 1) * ht'
    · simp [g, f]
      field_simp [Units.ne_zero c]
      linear_combination (z 2) * ht'
    · simp [g, f]
      field_simp [Units.ne_zero c]
      linear_combination (z 3) * ht'
  refine ⟨f, ?_, ?_⟩
  · intro x y hxy
    have := congrArg g hxy
    simpa only [hleft] using this
  · intro z
    simp only [scaledQuaternionNormCoefficients,
      quaternionNormCoefficients, diagonalQuadratic, Fin.sum_univ_four]
    dsimp [f]
    linear_combination
      (z 0 ^ 2 - (a : K) * z 1 ^ 2 - (b : K) * z 2 ^ 2 +
        (a : K) * (b : K) * z 3 ^ 2) * ht'

/-- A square-determinant quaternary form is represented by a scalar
multiple of a quaternion norm form. -/
theorem diagonalUnitQuaternary_represents_scaledQuaternionNorm
    (base : Fin 4 → Kˣ)
    (hdet : IsSquare (diagonalUnitDeterminant base)) :
    ∃ A x y : Kˣ,
      DiagonalRepresents (diagonalUnitCoefficients base)
        (scaledQuaternionNormCoefficients A x y) := by
  let A : Kˣ := base 0
  let B : Kˣ := base 1
  let C : Kˣ := base 2
  let x : Kˣ := -(A⁻¹ * B)
  let y : Kˣ := -(A⁻¹ * C)
  let model : Fin 4 → Kˣ :=
    ![A, -(A * x), -(A * y), A * (x * y)]
  have hprefixEq : diagonalUnitPrefix base = diagonalUnitPrefix model := by
    funext i
    change base i.castSucc = model i.castSucc
    fin_cases i
    · rfl
    · dsimp [model, x, A, B]
      apply Units.ext
      simp
    · dsimp [model, y, A, C]
      apply Units.ext
      simp
  have hprefix : DiagonalRepresents
      (diagonalUnitCoefficients (diagonalUnitPrefix base))
      (diagonalUnitCoefficients model) := by
    rw [hprefixEq]
    exact DiagonalRepresents.prefixSucc (diagonalUnitCoefficients model)
  have hmodelSquare : IsSquare (diagonalUnitDeterminant model) := by
    refine ⟨A ^ 2 * x * y, ?_⟩
    simp [diagonalUnitDeterminant, Fin.prod_univ_four, model, pow_two]
    ac_rfl
  have hbaseModel : DiagonalRepresents
      (diagonalUnitCoefficients base)
      (diagonalUnitCoefficients model) :=
    diagonalRepresents_of_prefix_of_determinant_square
      base model hprefix (hdet.mul hmodelSquare)
  refine ⟨A, x, y, ?_⟩
  convert hbaseModel using 1
  funext i
  change (A : K) * quaternionNormCoefficients x y i = (model i : K)
  fin_cases i <;> simp [model, quaternionNormCoefficients]

/-- The exact diagonal unit list `[1,-Δ,π,-Δπ]` appearing in Beli's
Corollary 4.5(ii). -/
noncomputable def beliAnisotropicQuaternaryUnits : Fin 4 → Kˣ :=
  let delta :=
    (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
  let pi := uniformizerPowerUnit K (1 : Int)
  ![(1 : Kˣ), -delta, pi, -(delta * pi)]

/-- The paper's anisotropic quaternary quadratic space. -/
noncomputable def beliAnisotropicQuaternaryForm :
    QuadraticSpace K (Fin 4 → K) :=
  QuadraticSpace.finiteDiagonal
    (diagonalUnitCoefficients (beliAnisotropicQuaternaryUnits (K := K)))
    (fun i => Units.ne_zero
      (beliAnisotropicQuaternaryUnits (K := K) i))

/-- The paper's unit list is the quaternion norm list `(Delta,-pi)`. -/
theorem beliAnisotropicQuaternaryUnits_coefficients :
    diagonalUnitCoefficients (beliAnisotropicQuaternaryUnits (K := K)) =
      quaternionNormCoefficients
        (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
        (-(uniformizerPowerUnit K (1 : Int))) := by
  funext i
  fin_cases i <;>
    simp [beliAnisotropicQuaternaryUnits, quaternionNormCoefficients,
      diagonalUnitCoefficients]

/-- The distinguished quaternary model is anisotropic. -/
theorem beliAnisotropicQuaternaryForm_isAnisotropic :
    (beliAnisotropicQuaternaryForm (K := K)).IsAnisotropicSpace := by
  let delta :=
    (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
  let pi := uniformizerPowerUnit K (1 : Int)
  have hpiOdd : Odd (ordUnit K (-pi)) := by
    rw [ordUnit_neg]
    dsimp only [pi]
    rw [ordUnit_uniformizerPowerUnit]
    exact odd_one
  have hpiNotNorm : ¬ IsQuadraticNorm K delta (-pi) := by
    intro h
    have heven := (isQuadraticNorm_discriminant_iff_even_order (-pi)).1 h
    exact Int.not_even_iff_odd.mpr hpiOdd heven
  have hdiag := (quaternionNorm_anisotropic_iff_nonnorm delta (-pi)).2
    hpiNotNorm
  intro z hz
  apply hdiag z
  rw [← beliAnisotropicQuaternaryUnits_coefficients (K := K)]
  simpa only [beliAnisotropicQuaternaryForm,
    QuadraticSpace.finiteDiagonal_quadratic_apply] using hz

/-- Anisotropy is invariant under a quadratic-space isometry. -/
theorem QuadraticSpace.Isometry.isAnisotropicSpace_iff
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {r : QuadraticSpace K (Fin 4 → K)}
    (f : q.Isometry r) : q.IsAnisotropicSpace ↔ r.IsAnisotropicSpace := by
  constructor
  · intro hq y hy
    have hx : q.quadratic (f.toLinearEquiv.symm y) = 0 := by
      rw [← f.map_quadratic]
      simpa using hy
    have := hq (f.toLinearEquiv.symm y) hx
    simpa using congrArg f.toLinearEquiv this
  · intro hr x hx
    have hy : r.quadratic (f.toLinearEquiv x) = 0 := by
      rw [f.map_quadratic, hx]
    have := hr (f.toLinearEquiv x) hy
    exact f.toLinearEquiv.injective (by simpa using this)

/-- Every anisotropic quaternary quadratic space over the dyadic local
field is isometric to Beli's fixed model `[1,-Δ,π,-Δπ]`. -/
theorem anisotropicQuaternary_isIsometric_beliModel
    {V : Type v} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    (q : QuadraticSpace K V) (hrank : finrank K V = 4)
    (han : q.IsAnisotropicSpace) :
    q.IsIsometric (beliAnisotropicQuaternaryForm (K := K)) := by
  classical
  let e : Fin 4 ≃ Fin (finrank K V) := finCongr hrank.symm
  let base : Fin 4 → Kˣ := fun i => q.diagonalUnits (e i)
  let qToBase : QuadraticSpace.Isometry q
      (QuadraticSpace.finiteDiagonal (diagonalUnitCoefficients base)
        (fun i => Units.ne_zero (base i))) :=
    q.diagonalizationIsometry.trans
      (QuadraticSpace.finiteDiagonalReindexIsometry
        (diagonalUnitCoefficients q.diagonalUnits)
        (fun i => Units.ne_zero (q.diagonalUnits i)) e)
  have hbaseSpace :
      (QuadraticSpace.finiteDiagonal (diagonalUnitCoefficients base)
        (fun i => Units.ne_zero (base i))).IsAnisotropicSpace :=
    (qToBase.isAnisotropicSpace_iff).1 han
  have hbase : DiagonalAnisotropic (diagonalUnitCoefficients base) := by
    intro z hz
    apply hbaseSpace z
    simpa only [QuadraticSpace.finiteDiagonal_quadratic_apply] using hz
  have hdet : IsSquare (diagonalUnitDeterminant base) := by
    by_contra hnot
    exact ((not_diagonalIsotropic_iff_diagonalAnisotropic
      (diagonalUnitCoefficients base)).2 hbase)
      (diagonalUnitQuaternary_isotropic_of_not_determinant_square base hnot)
  obtain ⟨A, a, b, hscaled⟩ :=
    diagonalUnitQuaternary_represents_scaledQuaternionNorm base hdet
  have hscaledAnisotropic :
      DiagonalAnisotropic (scaledQuaternionNormCoefficients A a b) :=
    hscaled.symm_of_sameRank.anisotropic_of hbase
  have hab : ¬ IsQuadraticNorm K a b := by
    intro hab
    rcases hab with ⟨x, y, hxy⟩
    let z : Fin 4 → K := ![x, y, 1, 0]
    have hzNe : z ≠ 0 := by
      intro hz
      have := congrFun hz (2 : Fin 4)
      simp [z] at this
    apply hzNe
    apply hscaledAnisotropic z
    simp only [scaledQuaternionNormCoefficients,
      quaternionNormCoefficients, diagonalQuadratic, Fin.sum_univ_four]
    dsimp [z]
    linear_combination (A : K) * hxy
  have hremoveScalar :=
    scaledQuaternionNorm_represents_quaternionNorm A a b
  have htoStandard := quaternionNorm_to_standard_of_nonnorm a b hab
  let delta :=
    (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
  let pi := uniformizerPowerUnit K (1 : Int)
  have hnegOneNorm : IsQuadraticNorm K delta (pi / (-pi)) := by
    apply (isQuadraticNorm_discriminant_iff_even_order (pi / (-pi))).2
    refine ⟨0, ?_⟩
    rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv, ordUnit_neg]
    omega
  have hsign : DiagonalRepresents
      (quaternionNormCoefficients delta pi)
      (quaternionNormCoefficients delta (-pi)) :=
    quaternionNorm_fixed_left_of_norm_ratio delta pi (-pi) hnegOneNorm
  have hbaseToPaper : DiagonalRepresents
      (diagonalUnitCoefficients base)
      (diagonalUnitCoefficients
        (beliAnisotropicQuaternaryUnits (K := K))) := by
    rw [beliAnisotropicQuaternaryUnits_coefficients]
    exact ((hscaled.trans hremoveScalar).trans htoStandard).trans hsign
  have hspace :=
    (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
      base (beliAnisotropicQuaternaryUnits (K := K))).2 hbaseToPaper
  rcases hspace with ⟨f⟩
  let baseToPaper : QuadraticSpace.Isometry
      (QuadraticSpace.finiteDiagonal (diagonalUnitCoefficients base)
        (fun i => Units.ne_zero (base i)))
      (beliAnisotropicQuaternaryForm (K := K)) :=
    f.toIsometryOfFinrankEq rfl
  exact ⟨qToBase.trans baseToPaper⟩

end Bong
