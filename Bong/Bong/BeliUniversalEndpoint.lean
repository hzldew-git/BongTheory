/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliUniversalAmbient
import Bong.Bong.BinaryEndpointProduct
import Bong.Bong.DiagonalBinaryRepresentation
import Bong.Dyadic.HilbertSymbolProof
import Bong.Dyadic.UnramifiedNormDirectProof

/-!
# The binary endpoint in Beli's universal-lattice theorem

This file proves the part of Lemma 2.11 needed by Theorem 2.1.  If
`R₁ = 0` and `R₂ = -2e`, the signed product `-a₁a₂` is either a square or
the unramified discriminant class.  Hence the binary prefix is isotropic or
represents exactly the even-order square classes.  In particular, `R₃ = 0`
forces the ternary prefix to be isotropic.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

noncomputable local instance universalDiscriminant :
    DyadicDiscriminantClassLaws K :=
  dyadicDiscriminantClassLawsProved

noncomputable local instance universalUnramifiedNorm :
    DyadicUnramifiedNormLaws K :=
  dyadicUnramifiedNormLawsProvedDirect

/-- A binary diagonal form is isotropic when its negative determinant is a
square. -/
theorem diagonalBinary_isotropic_of_isSquare_neg_product
    (a b : Kˣ) (h : IsSquare (-(a * b))) :
    DiagonalIsotropic
      (fun i ↦ ![(a : K), (b : K)] i) := by
  rcases h with ⟨s, hs⟩
  let x : Fin 2 → K := ![((s / a : Kˣ) : K), 1]
  refine ⟨x, ?_, ?_⟩
  · intro hx
    have hone := congrFun hx (1 : Fin 2)
    simpa [x] using hone
  ·
    have hsK : -((a : K) * (b : K)) = (s : K) ^ 2 := by
      simpa [pow_two] using congrArg Units.val hs
    simp only [x, diagonalQuadratic, Fin.sum_univ_two]
    simp
    field_simp [Units.ne_zero a]
    rw [← hsK]
    ring

/-- The converse binary determinant criterion: an isotropic nondegenerate
binary diagonal form has square negative determinant. -/
theorem isSquare_neg_product_of_diagonalBinary_isotropic
    (a b : Kˣ)
    (hiso : DiagonalIsotropic
      (fun i ↦ ![(a : K), (b : K)] i)) :
    IsSquare (-(a * b)) := by
  rcases hiso with ⟨x, hxne, hquadratic⟩
  have hvalue :
      (a : K) * (x 0) ^ 2 + (b : K) * (x 1) ^ 2 = 0 := by
    simpa [diagonalQuadratic] using hquadratic
  have hxzero : x 0 ≠ 0 := by
    intro hxzero
    have hxone : x 1 = 0 := by
      have hb : (b : K) * (x 1) ^ 2 = 0 := by
        simpa [hxzero] using hvalue
      exact (sq_eq_zero_iff).mp (mul_eq_zero.mp hb |>.resolve_left
        (Units.ne_zero b))
    apply hxne
    funext i
    fin_cases i
    · exact hxzero
    · exact hxone
  have hxone : x 1 ≠ 0 := by
    intro hxone
    have hxzero' : x 0 = 0 := by
      have ha : (a : K) * (x 0) ^ 2 = 0 := by
        simpa [hxone] using hvalue
      exact (sq_eq_zero_iff).mp (mul_eq_zero.mp ha |>.resolve_left
        (Units.ne_zero a))
    exact hxzero hxzero'
  let s : Kˣ := Units.mk0 ((a : K) * x 0 / x 1)
    (div_ne_zero (mul_ne_zero (Units.ne_zero a) hxzero) hxone)
  refine ⟨s, ?_⟩
  apply Units.ext
  change -((a : K) * (b : K)) =
    (((a : K) * x 0 / x 1) * ((a : K) * x 0 / x 1))
  field_simp [hxone]
  linear_combination -hvalue

/-- Binary isotropy is equivalent to the usual square-class determinant
criterion. -/
theorem diagonalBinary_isotropic_iff_isSquare_neg_product (a b : Kˣ) :
    DiagonalIsotropic (fun i ↦ ![(a : K), (b : K)] i) ↔
      IsSquare (-(a * b)) := by
  constructor
  · exact isSquare_neg_product_of_diagonalBinary_isotropic a b
  · exact diagonalBinary_isotropic_of_isSquare_neg_product a b

/-- An isotropic nondegenerate binary diagonal form represents every
nonzero unary coefficient. -/
theorem diagonalBinary_represents_of_isotropic
    (a₁ a₂ b : Kˣ)
    (hiso : DiagonalIsotropic
      (fun i ↦ ![(a₁ : K), (a₂ : K)] i)) :
    DiagonalRepresents (fun _ : Fin 1 ↦ (b : K))
      (Fin.cons (a₁ : K) (fun _ : Fin 1 ↦ (a₂ : K))) := by
  apply (DiagonalRepresents.unary_binary_iff_hilbertSymbol_one
    a₁ a₂ b).2
  exact hilbertSymbol_eq_one_of_isSquare_right K
    (isSquare_neg_product_of_diagonalBinary_isotropic a₁ a₂ hiso)

/-- In the discriminant endpoint case the binary diagonal form represents
every coefficient of even order, provided its first coefficient is a unit. -/
theorem diagonalBinary_represents_even_of_discriminant_endpoint
    (a₁ a₂ b : Kˣ) (ha₁ : ordUnit K a₁ = 0)
    (hendpoint : IsSquare
      (-(a₁ * a₂) *
        (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit))
    (hb : Even (ordUnit K b)) :
    DiagonalRepresents (fun _ : Fin 1 ↦ (b : K))
      (Fin.cons (a₁ : K) (fun _ : Fin 1 ↦ (a₂ : K))) := by
  let delta : Kˣ :=
    (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
  rcases hendpoint with ⟨s, hs⟩
  let t : Kˣ := s / delta
  have hfactor : -(a₁ * a₂) = delta * t ^ 2 := by
    calc
      -(a₁ * a₂) = (-(a₁ * a₂) * delta) / delta :=
        (mul_div_cancel_right _ _).symm
      _ = (s * s) / delta := by
        simpa only [delta] using congrArg (fun z : Kˣ ↦ z / delta) hs
      _ = s * (s / delta) := mul_div_assoc _ _ _
      _ = (s / delta * delta) * (s / delta) := by
        rw [div_mul_cancel]
      _ = delta * (s / delta) * (s / delta) := by ac_rfl
      _ = delta * t ^ 2 := by
        simp only [t, pow_two]
        exact mul_assoc _ _ _
  apply (DiagonalRepresents.unary_binary_iff_isQuadraticNorm a₁ a₂ b).2
  rw [hfactor, isQuadraticNorm_mul_square_left_iff]
  apply (isQuadraticNorm_discriminant_iff_even_order (b * a₁⁻¹)).2
  rw [ordUnit_mul, ordUnit_inv, ha₁, neg_zero, add_zero]
  exact hb

/-- At the discriminant endpoint the binary form represents a nonzero
coefficient exactly when that coefficient has even order. -/
theorem diagonalBinary_represents_iff_even_of_discriminant_endpoint
    (a₁ a₂ b : Kˣ) (ha₁ : ordUnit K a₁ = 0)
    (hendpoint : IsSquare
      (-(a₁ * a₂) *
        (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit)) :
    DiagonalRepresents (fun _ : Fin 1 ↦ (b : K))
        (Fin.cons (a₁ : K) (fun _ : Fin 1 ↦ (a₂ : K))) ↔
      Even (ordUnit K b) := by
  constructor
  · intro hrep
    have hhilbert :=
      (DiagonalRepresents.unary_binary_iff_hilbertSymbol_one a₁ a₂ b).mp
        hrep
    have hsame :=
      hilbertSymbol_eq_discriminant_of_isSquare_mul_discriminant
        (K := K) (b := b * a₁⁻¹) hendpoint
    rw [hilbertSymbol_comm K] at hhilbert
    rw [hsame] at hhilbert
    have hevenRatio :=
      (hilbertSymbol_discriminant_eq_one_iff_even_order
        (b * a₁⁻¹)).mp hhilbert
    rw [ordUnit_mul, ordUnit_inv, ha₁, neg_zero, add_zero] at hevenRatio
    exact hevenRatio
  · exact diagonalBinary_represents_even_of_discriminant_endpoint
      a₁ a₂ b ha₁ hendpoint

/-- Appending `a₃` to a binary representation of `-a₃` produces a
nonzero isotropic ternary vector. -/
theorem diagonalTernary_isotropic_of_binary_represents_negative
    (a₁ a₂ a₃ : Kˣ)
    (hrep : DiagonalRepresents (fun _ : Fin 1 ↦ (-(a₃ : K)))
      (Fin.cons (a₁ : K) (fun _ : Fin 1 ↦ (a₂ : K)))) :
    DiagonalIsotropic
      (fun i ↦ ![(a₁ : K), (a₂ : K), (a₃ : K)] i) := by
  rcases hrep with ⟨f, hf, hquadratic⟩
  let one : Fin 1 → K := fun _ ↦ 1
  let x : Fin 3 → K := ![f one 0, f one 1, 1]
  refine ⟨x, ?_, ?_⟩
  · intro hx
    have hone := congrFun hx (2 : Fin 3)
    simpa [x] using hone
  · have hvalue := hquadratic one
    have hvalue' :
        (a₁ : K) * (f one 0) ^ 2 + (a₂ : K) * (f one 1) ^ 2 =
          -(a₃ : K) := by
      simpa [diagonalQuadratic, one] using hvalue
    simp only [x, diagonalQuadratic, Fin.sum_univ_three]
    simp
    rw [hvalue']
    ring

namespace BONG.GoodBONG

/-- Beli, Lemma 2.11(i), determinant-class form. -/
theorem firstBinary_endpoint_signedProduct_cases {tail : Nat}
    (a : GoodBONG q L (tail + 2))
    (hzero : a.order 0 = 0)
    (hsecond : a.order 1 = -(2 * (ramificationIndex K : Int))) :
    IsSquare (-(a.valueUnit 0 * a.valueUnit 1)) ∨
      IsSquare (-(a.valueUnit 0 * a.valueUnit 1) *
        (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit) := by
  have hgap :
      a.order (1 : Fin (tail + 2)) - a.order (0 : Fin (tail + 2)) =
        -(2 * (ramificationIndex K : Int)) := by
    rw [hzero, hsecond]
    omega
  have hclasses := a.toBONG.adjacentUnitSquareClass_endpoint_cases
    (0 : Fin (tail + 2)) (by
      simpa [Nat.add_comm] using Nat.one_lt_succ_succ tail) hgap
  exact a.toBONG.adjacentSignedProduct_endpoint_cases
    (0 : Fin (tail + 2)) (by
      simpa [Nat.add_comm] using Nat.one_lt_succ_succ tail) hclasses

/-- Beli, Lemma 2.11(i): at the discriminant endpoint, the first two
coefficients represent every even-order scalar. -/
theorem firstTwo_represents_even_of_discriminant_endpoint {tail : Nat}
    (a : GoodBONG q L (tail + 2))
    (hzero : a.order 0 = 0)
    (hendpoint : IsSquare (-(a.valueUnit 0 * a.valueUnit 1) *
      (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit))
    (b : Kˣ) (hb : Even (ordUnit K b)) :
    DiagonalRepresents (fun _ : Fin 1 ↦ (b : K))
      (a.prefixValues 2 (by omega)) := by
  have hraw := diagonalBinary_represents_even_of_discriminant_endpoint
    (a.valueUnit 0) (a.valueUnit 1) b (by
      calc
        ordUnit K (a.valueUnit 0) = a.order 0 := by
          simpa only [GoodBONG.order, GoodBONG.valueUnit] using
            (a.toBONG.order_eq_ordUnit (0 : Fin (tail + 2))).symm
        _ = 0 := hzero) hendpoint hb
  convert hraw using 1
  funext i
  fin_cases i <;> rfl

/-- Good-BONG form of the exact representation classification at the
discriminant endpoint. -/
theorem firstTwo_represents_iff_even_of_discriminant_endpoint {tail : Nat}
    (a : GoodBONG q L (tail + 2))
    (hzero : a.order 0 = 0)
    (hendpoint : IsSquare (-(a.valueUnit 0 * a.valueUnit 1) *
      (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit))
    (b : Kˣ) :
    DiagonalRepresents (fun _ : Fin 1 ↦ (b : K))
        (a.prefixValues 2 (by omega)) ↔
      Even (ordUnit K b) := by
  have haOrder : ordUnit K (a.valueUnit 0) = 0 := by
    calc
      ordUnit K (a.valueUnit 0) = a.order 0 := by
        simpa only [GoodBONG.order, GoodBONG.valueUnit] using
          (a.toBONG.order_eq_ordUnit (0 : Fin (tail + 2))).symm
      _ = 0 := hzero
  have hraw := diagonalBinary_represents_iff_even_of_discriminant_endpoint
    (a.valueUnit 0) (a.valueUnit 1) b haOrder hendpoint
  have htarget : a.prefixValues 2 (by omega) =
      Fin.cons (a.valueUnit 0 : K) (fun _ : Fin 1 ↦ (a.valueUnit 1 : K)) := by
    funext i
    fin_cases i <;> rfl
  rw [htarget]
  exact hraw

/-- Under the `R_2=-2e` endpoint, representation of one odd-order scalar by
the first binary prefix forces that prefix to be isotropic. -/
theorem firstTwo_isotropic_of_represents_odd_at_endpoint {tail : Nat}
    (a : GoodBONG q L (tail + 2))
    (hzero : a.order 0 = 0)
    (hsecond : a.order 1 = -(2 * (ramificationIndex K : Int)))
    (b : Kˣ) (hbOdd : Odd (ordUnit K b))
    (hrep : DiagonalRepresents (fun _ : Fin 1 ↦ (b : K))
      (a.prefixValues 2 (by omega))) :
    a.UniversalFirstTwoIsotropic := by
  rcases a.firstBinary_endpoint_signedProduct_cases hzero hsecond with
    hsquare | hdiscriminant
  · have hisotropic := diagonalBinary_isotropic_of_isSquare_neg_product
      (a.valueUnit 0) (a.valueUnit 1) hsquare
    change DiagonalIsotropic (a.prefixValues 2 (by omega))
    convert hisotropic using 1
    funext i
    fin_cases i <;> rfl
  · have heven :=
      (a.firstTwo_represents_iff_even_of_discriminant_endpoint
        hzero hdiscriminant b).mp hrep
    exact False.elim (Int.not_even_iff_odd.mpr hbOdd heven)

/-- Under the `R_2=-2e` endpoint, the first binary prefix represents every
coefficient of even order, in both determinant square classes. -/
theorem firstTwo_represents_even_at_endpoint {tail : Nat}
    (a : GoodBONG q L (tail + 2))
    (hzero : a.order 0 = 0)
    (hsecond : a.order 1 = -(2 * (ramificationIndex K : Int)))
    (b : Kˣ) (hbEven : Even (ordUnit K b)) :
    DiagonalRepresents (fun _ : Fin 1 ↦ (b : K))
      (a.prefixValues 2 (by omega)) := by
  rcases a.firstBinary_endpoint_signedProduct_cases hzero hsecond with
    hsquare | hdiscriminant
  · have hisotropic := diagonalBinary_isotropic_of_isSquare_neg_product
      (a.valueUnit 0) (a.valueUnit 1) hsquare
    have hrep := diagonalBinary_represents_of_isotropic
      (a.valueUnit 0) (a.valueUnit 1) b hisotropic
    convert hrep using 1
    funext i
    fin_cases i <;> rfl
  · exact a.firstTwo_represents_even_of_discriminant_endpoint
      hzero hdiscriminant b hbEven

/-- The `R₃ = 0` assertion in Beli, Lemma 2.11(ii). -/
theorem firstThree_isotropic_of_endpoint_order_two_zero {tail : Nat}
    (a : GoodBONG q L (tail + 3))
    (hzero : a.order 0 = 0)
    (hsecond : a.order 1 = -(2 * (ramificationIndex K : Int)))
    (hthird : a.order 2 = 0) :
    a.UniversalFirstThreeIsotropic (by omega) := by
  have htwo : 2 ≤ tail + 3 := by omega
  have hthree : 3 ≤ tail + 3 := by omega
  change DiagonalIsotropic (a.prefixValues 3 hthree)
  rcases a.firstBinary_endpoint_signedProduct_cases (tail := tail + 1)
    hzero hsecond with
    hsquare | hdiscriminant
  · have hiso := diagonalBinary_isotropic_of_isSquare_neg_product
      (a.valueUnit 0) (a.valueUnit 1) hsquare
    have hiso' : DiagonalIsotropic (a.prefixValues 2 htwo) := by
      convert hiso using 1
      funext i
      fin_cases i <;> rfl
    have hrep : DiagonalRepresents
        (a.prefixValues 2 htwo) (a.prefixValues 3 hthree) := by
      unfold prefixValues
      exact DiagonalRepresents.prefixOfLE _ (by omega)
    exact hrep.isotropic_of hiso'
  · have hrep : DiagonalRepresents
        (fun _ : Fin 1 ↦ (-(a.valueUnit 2 : K)))
        (a.prefixValues 2 htwo) :=
      a.firstTwo_represents_even_of_discriminant_endpoint (tail := tail + 1) hzero
        hdiscriminant (-a.valueUnit 2) (by
          rw [ordUnit_neg, show ordUnit K (a.valueUnit 2) = 0 by
            calc
              ordUnit K (a.valueUnit 2) = a.order 2 := by
                simpa only [GoodBONG.order, GoodBONG.valueUnit] using
                  (a.toBONG.order_eq_ordUnit (2 : Fin (tail + 3))).symm
              _ = 0 := hthird]
          exact Even.zero)
    have hiso := diagonalTernary_isotropic_of_binary_represents_negative
      (a.valueUnit 0) (a.valueUnit 1) (a.valueUnit 2) (by
        convert hrep using 1
        funext i
        fin_cases i <;> rfl)
    convert hiso using 1
    funext i
    fin_cases i <;> rfl

end BONG.GoodBONG

end Bong
