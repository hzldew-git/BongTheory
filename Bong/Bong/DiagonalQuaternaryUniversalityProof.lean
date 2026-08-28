/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.DiagonalIsometryInvariantProof
import Bong.Bong.DiagonalDeterminantExtension
import Bong.Bong.DiagonalCodimensionOneCancellationProof
import Bong.Bong.DiagonalQuaternaryComplement
import Bong.Dyadic.HilbertSymbolProof

/-!
# Quaternary universality over dyadic local fields

This file proves O'Meara 63:17--63:18 in the exact form needed by the Beli
formalization.  Hilbert-pairing nondegeneracy shows that a quaternary
diagonal form with nonsquare determinant is isotropic.  A square-determinant
form is a scalar multiple of a quaternion norm form.  The already proved
O'Meara 63:11 normal form reduces its nonsplit case to `(Δ, π)`, whose two
unramified norm summands represent scalars of even and odd valuation,
respectively.

Consequently every nondegenerate quaternary diagonal form represents every
nonzero scalar, and explicit orthogonal splitting supplies the requested
ternary complement.  No local-law parameter is used.
-/

namespace Bong

open Dyadic BONG.GoodBONG

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- A nontrivial second Hilbert character has a negative value on the
kernel of an independent first character. -/
theorem exists_hilbert_one_neg_one_of_independent
    (p q : Kˣ) (hpq : ¬ IsSquare (p * q)) (hq : ¬ IsSquare q) :
    ∃ u : Kˣ,
      hilbertSymbol K u p = 1 ∧ hilbertSymbol K u q = -1 := by
  obtain ⟨z, hz'⟩ :=
    Dyadic.exists_hilbertSymbol_eq_neg_one_of_not_isSquare_proved
      (p * q) hpq
  have hz : hilbertSymbol K z (p * q) = -1 := by
    rw [hilbertSymbol_comm K]
    exact hz'
  rw [hilbertSymbol_mul_right] at hz
  rcases Int.units_eq_one_or (hilbertSymbol K z p) with hzp | hzp
  · refine ⟨z, hzp, ?_⟩
    simpa [hzp] using hz
  · have hzq : hilbertSymbol K z q = 1 := by
      rcases Int.units_eq_one_or (hilbertSymbol K z q) with hzq | hzq
      · exact hzq
      · simp [hzp, hzq] at hz
    obtain ⟨w, hw'⟩ :=
      Dyadic.exists_hilbertSymbol_eq_neg_one_of_not_isSquare_proved q hq
    have hwq : hilbertSymbol K w q = -1 := by
      rw [hilbertSymbol_comm K]
      exact hw'
    rcases Int.units_eq_one_or (hilbertSymbol K w p) with hwp | hwp
    · exact ⟨w, hwp, hwq⟩
    · refine ⟨z * w, ?_, ?_⟩
      · rw [hilbertSymbol_mul_left, hzp, hwp]
        norm_num
      · rw [hilbertSymbol_mul_left, hzq, hwq]
        norm_num

/-- Two independent Hilbert characters admit simultaneous prescribed
values, provided each prescribed value is individually realized. -/
theorem exists_hilbert_pair_matches_of_independent
    (p q x y : Kˣ) (hpq : ¬ IsSquare (p * q)) :
    ∃ t : Kˣ,
      hilbertSymbol K t p = hilbertSymbol K x p ∧
        hilbertSymbol K t q = hilbertSymbol K y q := by
  by_cases hmatch : hilbertSymbol K x q = hilbertSymbol K y q
  · exact ⟨x, rfl, hmatch⟩
  · have hq : ¬ IsSquare q := by
      intro hq
      have hx := hilbertSymbol_eq_one_of_isSquare_right K
        (a := x) hq
      have hy := hilbertSymbol_eq_one_of_isSquare_right K
        (a := y) hq
      exact hmatch (hx.trans hy.symm)
    obtain ⟨u, hup, huq⟩ :=
      exists_hilbert_one_neg_one_of_independent p q hpq hq
    refine ⟨x * u, ?_, ?_⟩
    · rw [hilbertSymbol_mul_left, hup, mul_one]
    · rw [hilbertSymbol_mul_left, huq]
      rcases Int.units_eq_one_or (hilbertSymbol K x q) with hx | hx <;>
        rcases Int.units_eq_one_or (hilbertSymbol K y q) with hy | hy <;>
          simp [hx, hy] at hmatch ⊢

/-- A nondegenerate quaternary diagonal form with nonsquare determinant is
isotropic.  The proof intersects the two binary value cosets by Hilbert
nondegeneracy. -/
theorem diagonalUnitQuaternary_isotropic_of_not_determinant_square
    (base : Fin 4 → Kˣ)
    (hdet : ¬ IsSquare (diagonalUnitDeterminant base)) :
    DiagonalIsotropic (diagonalUnitCoefficients base) := by
  let A : Kˣ := base 0
  let B : Kˣ := base 1
  let C : Kˣ := base 2
  let D : Kˣ := base 3
  let p : Kˣ := -(A * B)
  let q : Kˣ := -(C * D)
  have hpq : ¬ IsSquare (p * q) := by
    intro hsquare
    apply hdet
    simpa [p, q, A, B, C, D, diagonalUnitDeterminant,
      Fin.prod_univ_four, mul_assoc, mul_comm, mul_left_comm] using hsquare
  obtain ⟨t, htp, htq⟩ :=
    exists_hilbert_pair_matches_of_independent p q A (-C) hpq
  have hAinv : hilbertSymbol K A⁻¹ p = hilbertSymbol K A p := by
    rw [show A⁻¹ = A * (A⁻¹) ^ 2 by group,
      hilbertSymbol_mul_square_left]
  have hCinv : hilbertSymbol K (-C⁻¹) q = hilbertSymbol K (-C) q := by
    rw [show -C⁻¹ = (-C) * (C⁻¹) ^ 2 by
        apply Units.ext
        simp only [Units.val_neg, Units.val_inv_eq_inv_val,
          Units.val_mul, Units.val_pow_eq_pow_val]
        field_simp [Units.ne_zero C],
      hilbertSymbol_mul_square_left]
  have hfirstNorm : hilbertSymbol K (t * A⁻¹) p = 1 := by
    rw [hilbertSymbol_mul_left, htp, hAinv,
      hilbertSymbol_mul_self]
  have hsecondNorm : hilbertSymbol K ((-t) * C⁻¹) q = 1 := by
    rw [show (-t) * C⁻¹ = t * (-C⁻¹) by
        apply Units.ext
        simp,
      hilbertSymbol_mul_left, htq, hCinv,
      hilbertSymbol_mul_self]
  have hfirst : DiagonalRepresents
      (fun _ : Fin 1 => (t : K))
      (Fin.cons (A : K) (fun _ : Fin 1 => (B : K))) :=
    (DiagonalRepresents.unary_binary_iff_hilbertSymbol_one A B t).2
      (by simpa only [p] using hfirstNorm)
  have hsecond : DiagonalRepresents
      (fun _ : Fin 1 => ((-t : Kˣ) : K))
      (Fin.cons (C : K) (fun _ : Fin 1 => (D : K))) :=
    (DiagonalRepresents.unary_binary_iff_hilbertSymbol_one C D (-t)).2
      (by simpa only [q] using hsecondNorm)
  rcases hfirst with ⟨f, hf, hqf⟩
  rcases hsecond with ⟨g, hg, hqg⟩
  let e : Fin 1 → K := fun _ => 1
  let x : Fin 2 → K := f e
  let y : Fin 2 → K := g e
  have he : e ≠ 0 := by
    intro heq
    have h := congrFun heq (0 : Fin 1)
    simp [e] at h
  have hx : x ≠ 0 := by
    intro hx
    apply he
    apply hf
    rw [show f e = 0 by exact hx, map_zero]
  have hxvalue :
      (A : K) * (x 0) ^ 2 + (B : K) * (x 1) ^ 2 = (t : K) := by
    simpa [x, e, diagonalQuadratic] using hqf e
  have hyvalue :
      (C : K) * (y 0) ^ 2 + (D : K) * (y 1) ^ 2 = ((-t : Kˣ) : K) := by
    simpa [y, e, diagonalQuadratic] using hqg e
  let z : Fin 4 → K := ![x 0, x 1, y 0, y 1]
  refine ⟨z, ?_, ?_⟩
  · intro hz
    apply hx
    funext i
    fin_cases i
    · have h := congrFun hz (0 : Fin 4)
      simpa [z] using h
    · have h := congrFun hz (1 : Fin 4)
      simpa [z] using h
  · simp only [diagonalQuadratic, Fin.sum_univ_four]
    change
      (A : K) * (x 0) ^ 2 + (B : K) * (x 1) ^ 2 +
          (C : K) * (y 0) ^ 2 + (D : K) * (y 1) ^ 2 = 0
    have hyvalue' :
        (C : K) * (y 0) ^ 2 + (D : K) * (y 1) ^ 2 = -(t : K) := by
      simpa using hyvalue
    linear_combination hxvalue + hyvalue'

/-- Every nondegenerate isotropic diagonal form of positive dimension
represents every nonzero scalar. -/
theorem diagonal_exists_value_of_isotropic
    {n : Nat} (c : Fin n → K) (hc : ∀ i, c i ≠ 0)
    (hiso : DiagonalIsotropic c) (b : Kˣ) :
    ∃ x : Fin n → K, diagonalQuadratic c x = (b : K) := by
  classical
  rcases hiso with ⟨v, hv, hvzero⟩
  have hexists : ∃ j : Fin n, v j ≠ 0 := by
    by_contra h
    push Not at h
    apply hv
    funext j
    exact h j
  obtain ⟨j, hvj⟩ := hexists
  let ej : Fin n → K := Pi.basisFun K (Fin n) j
  let s : K := ((b : K) - c j) / (2 * c j * v j)
  let x : Fin n → K := s • v + ej
  have hsmul : diagonalQuadratic c (s • v) =
      s ^ 2 * diagonalQuadratic c v := by
    unfold diagonalQuadratic
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hcross : ∑ i, c i * (s • v) i * ej i = c j * s * v j := by
    rw [Finset.sum_eq_single j]
    · simp [ej, Pi.basisFun_apply]
      ring
    · intro i _hi hij
      simp [ej, Pi.basisFun_apply, hij]
    · simp
  have hden : (2 : K) * c j * v j ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (hc j)) hvj
  refine ⟨x, ?_⟩
  dsimp only [x]
  rw [DiagonalRepresents.diagonalQuadratic_add, hsmul, hvzero,
    mul_zero, zero_add,
    DiagonalRepresents.diagonalQuadratic_basisFun, hcross]
  dsimp only [s]
  field_simp [hden, hc j, hvj]
  ring

/-- A diagonal representation transports a represented scalar. -/
theorem diagonal_exists_value_of_represents
    {m n : Nat} {source : Fin m → K} {target : Fin n → K}
    (hrep : DiagonalRepresents source target) {d : K}
    (hvalue : ∃ x : Fin m → K, diagonalQuadratic source x = d) :
    ∃ y : Fin n → K, diagonalQuadratic target y = d := by
  rcases hrep with ⟨f, _hf, hq⟩
  rcases hvalue with ⟨x, hx⟩
  exact ⟨f x, (hq x).trans hx⟩

/-- The split quaternion norm form represents every nonzero scalar. -/
theorem splitQuaternionNorm_exists_value (a t : Kˣ) :
    ∃ z : Fin 4 → K,
      diagonalQuadratic (quaternionNormCoefficients a 1) z = (t : K) := by
  let x : K := ((t : K) + 1) / 2
  let y : K := (1 - (t : K)) / 2
  let z : Fin 4 → K := ![x, 0, y, 0]
  refine ⟨z, ?_⟩
  simp only [quaternionNormCoefficients, diagonalQuadratic,
    Fin.sum_univ_four]
  dsimp [z, x, y]
  field_simp
  ring

/-- The fixed nonsplit dyadic quaternion norm form `(Δ,π)` represents
every nonzero scalar.  Even valuations occur in its first norm summand and
odd valuations in its second norm summand. -/
theorem standardQuaternionNorm_exists_value (t : Kˣ) :
    let delta : Kˣ :=
      (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
    let pi : Kˣ := uniformizerPowerUnit K (1 : Int)
    ∃ z : Fin 4 → K,
      diagonalQuadratic (quaternionNormCoefficients delta pi) z = (t : K) := by
  let delta : Kˣ :=
    (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
  let pi : Kˣ := uniformizerPowerUnit K (1 : Int)
  rcases Int.even_or_odd (ordUnit K t) with htEven | htOdd
  · have hnorm : IsQuadraticNorm K delta t :=
      (isQuadraticNorm_discriminant_iff_even_order t).2 htEven
    rcases hnorm with ⟨x, y, hxy⟩
    let z : Fin 4 → K := ![x, y, 0, 0]
    refine ⟨z, ?_⟩
    simp only [quaternionNormCoefficients, diagonalQuadratic,
      Fin.sum_univ_four]
    dsimp [z]
    simp only [one_mul, mul_zero, zero_pow (by norm_num : 2 ≠ 0),
      add_zero]
    change x ^ 2 + (-(delta : K)) * y ^ 2 = (t : K)
    linear_combination hxy
  · let u : Kˣ := -(t / pi)
    have huEven : Even (ordUnit K u) := by
      rcases htOdd with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      dsimp only [u]
      rw [ordUnit_neg, div_eq_mul_inv, ordUnit_mul, ordUnit_inv,
        show ordUnit K pi = 1 by
          dsimp only [pi]
          exact ordUnit_uniformizerPowerUnit (K := K) (1 : Int)]
      omega
    have hnorm : IsQuadraticNorm K delta u :=
      (isQuadraticNorm_discriminant_iff_even_order u).2 huEven
    rcases hnorm with ⟨x, y, hxy⟩
    let z : Fin 4 → K := ![0, 0, x, y]
    refine ⟨z, ?_⟩
    simp only [quaternionNormCoefficients, diagonalQuadratic,
      Fin.sum_univ_four]
    dsimp [z]
    simp only [zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_add]
    have hxy' : x ^ 2 - (delta : K) * y ^ 2 = (u : K) := hxy
    change (-(pi : K)) * x ^ 2 + ((delta : K) * (pi : K)) * y ^ 2 =
      (t : K)
    rw [show (-(pi : K)) * x ^ 2 + ((delta : K) * (pi : K)) * y ^ 2 =
        -(pi : K) * (x ^ 2 - (delta : K) * y ^ 2) by ring,
      hxy']
    dsimp only [u]
    simp only [Units.val_neg, Units.val_div_eq_div_val]
    field_simp [Units.ne_zero pi]

/-- Every quaternion norm form over the dyadic local field represents every
nonzero scalar. -/
theorem quaternionNorm_exists_value (a b t : Kˣ) :
    ∃ z : Fin 4 → K,
      diagonalQuadratic (quaternionNormCoefficients a b) z = (t : K) := by
  by_cases hnorm : IsQuadraticNorm K a b
  · have htoSplit : DiagonalRepresents
        (quaternionNormCoefficients a b)
        (quaternionNormCoefficients a 1) := by
      apply quaternionNorm_fixed_left_of_norm_ratio a b 1
      simpa using hnorm
    exact diagonal_exists_value_of_represents
      (DiagonalRepresents.symm_of_sameRank htoSplit)
      (splitQuaternionNorm_exists_value a t)
  · have htoStandard := quaternionNorm_to_standard_of_nonnorm a b hnorm
    exact diagonal_exists_value_of_represents
      (DiagonalRepresents.symm_of_sameRank htoStandard)
      (standardQuaternionNorm_exists_value t)

/-- A quaternary diagonal form with square determinant is a scalar multiple
of a quaternion norm form, up to a square change in its final coordinate;
hence it represents every nonzero scalar. -/
theorem diagonalUnitQuaternary_exists_value_of_determinant_square
    (base : Fin 4 → Kˣ)
    (hdet : IsSquare (diagonalUnitDeterminant base)) (t : Kˣ) :
    ∃ z : Fin 4 → K,
      diagonalQuadratic (diagonalUnitCoefficients base) z = (t : K) := by
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
  obtain ⟨z, hz⟩ := quaternionNorm_exists_value x y (t / A)
  have hmodelCoefficient (i : Fin 4) :
      diagonalUnitCoefficients model i =
        (A : K) * quaternionNormCoefficients x y i := by
    change (model i : K) =
      (A : K) * quaternionNormCoefficients x y i
    fin_cases i
    · simp [model, quaternionNormCoefficients]
    · simp [model, quaternionNormCoefficients]
    · simp [model, quaternionNormCoefficients]
    · simp [model, quaternionNormCoefficients]
  have hmodelValue :
      diagonalQuadratic (diagonalUnitCoefficients model) z = (t : K) := by
    unfold diagonalQuadratic at hz ⊢
    simp_rw [hmodelCoefficient]
    calc
      ∑ i, (A : K) * quaternionNormCoefficients x y i * z i ^ 2 =
          (A : K) *
            ∑ i, quaternionNormCoefficients x y i * z i ^ 2 := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _hi
              ring
      _ = (A : K) * ((t : K) / (A : K)) := by
        rw [hz]
        simp only [Units.val_div_eq_div_val]
      _ = (t : K) := by field_simp [Units.ne_zero A]
  exact diagonal_exists_value_of_represents
    (DiagonalRepresents.symm_of_sameRank hbaseModel) ⟨z, hmodelValue⟩

/-- Every nondegenerate quaternary diagonal form over the dyadic local field
represents every nonzero scalar. -/
theorem diagonalUnitQuaternary_exists_value
    (base : Fin 4 → Kˣ) (t : Kˣ) :
    ∃ z : Fin 4 → K,
      diagonalQuadratic (diagonalUnitCoefficients base) z = (t : K) := by
  by_cases hdet : IsSquare (diagonalUnitDeterminant base)
  · exact diagonalUnitQuaternary_exists_value_of_determinant_square
      base hdet t
  · exact diagonal_exists_value_of_isotropic
      (diagonalUnitCoefficients base)
      (fun i => Units.ne_zero (base i))
      (diagonalUnitQuaternary_isotropic_of_not_determinant_square base hdet)
      t

/-- The unconditional quaternary-complement law obtained from the concrete
local quaternion calculation. -/
noncomputable instance dyadicQuaternaryComplementLawsDirect :
    DyadicQuaternaryComplementLaws K where
  complement b base := by
    obtain ⟨x, hx⟩ := diagonalUnitQuaternary_exists_value base b
    obtain ⟨c, hrep, _hhasse⟩ :=
      exists_diagonal_split_first (K := K) 3 base b x hx
    exact ⟨c, hrep⟩

example : DyadicQuaternaryComplementLaws K := inferInstance

end Bong
