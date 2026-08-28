/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.DiagonalQuaternaryUniversalityProof
import Bong.Bong.DiagonalCodimensionTwoRepresentation

/-!
# Codimension-two diagonal representation over dyadic local fields

The rank-one base case is obtained by adjoining the negative source line to
the ternary target.  Nonsquare determinant makes that quaternary form
isotropic, which yields either the desired representation directly or an
isotropic ternary target.  In higher rank, quaternary universality splits a
common represented line; determinant square classes reduce the obstruction
to the two-rank-smaller tail, and induction finishes the construction.

This proves the former `DyadicDiagonalCodimensionTwoLaws` trust boundary
without additional assumptions.
-/

namespace Bong

open Dyadic BONG.GoodBONG

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- A ternary diagonal form represents every line outside its unique signed
determinant square class. -/
theorem diagonalUnitTernary_exists_value_of_not_signedDeterminantSquare
    (target : Fin 3 → Kˣ) (A : Kˣ)
    (hdet : ¬ IsSquare (-diagonalUnitDeterminant target * A)) :
    ∃ x : Fin 3 → K,
      diagonalQuadratic (diagonalUnitCoefficients target) x = (A : K) := by
  let extended : Fin 4 → Kˣ := Fin.cons (-A) target
  have hextendedDet : diagonalUnitDeterminant extended =
      (-A) * diagonalUnitDeterminant target := by
    exact diagonalUnitDeterminant_cons (-A) target
  have hextendedNotSquare :
      ¬ IsSquare (diagonalUnitDeterminant extended) := by
    intro hsquare
    apply hdet
    rw [hextendedDet] at hsquare
    simpa [mul_comm] using hsquare
  rcases diagonalUnitQuaternary_isotropic_of_not_determinant_square
      extended hextendedNotSquare with ⟨v, hv, hvzero⟩
  let w : K := v 0
  let vt : Fin 3 → K := Fin.tail v
  have hvform : v = Fin.cons w vt := by
    exact (Fin.cons_self_tail v).symm
  have hdecomp : (-(A : K)) * w ^ 2 +
      diagonalQuadratic (diagonalUnitCoefficients target) vt = 0 := by
    rw [hvform, diagonalUnitCoefficients_cons,
      DiagonalRepresents.diagonalQuadratic_cons] at hvzero
    exact hvzero
  by_cases hw : w = 0
  · have hvt : vt ≠ 0 := by
      intro hvt
      apply hv
      rw [hvform, hw, hvt]
      funext i
      fin_cases i <;> rfl
    have hvtzero :
        diagonalQuadratic (diagonalUnitCoefficients target) vt = 0 := by
      simpa [hw] using hdecomp
    exact diagonal_exists_value_of_isotropic
      (diagonalUnitCoefficients target)
      (fun i => Units.ne_zero (target i)) ⟨vt, hvt, hvtzero⟩ A
  · let x : Fin 3 → K := w⁻¹ • vt
    have htail :
        diagonalQuadratic (diagonalUnitCoefficients target) vt =
          (A : K) * w ^ 2 := by
      linear_combination hdecomp
    have hscale :
        diagonalQuadratic (diagonalUnitCoefficients target) x =
          w⁻¹ ^ 2 *
            diagonalQuadratic (diagonalUnitCoefficients target) vt := by
      dsimp only [x]
      unfold diagonalQuadratic
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    refine ⟨x, ?_⟩
    rw [hscale, htail]
    field_simp [hw]

/-- Every diagonal form of rank at least four represents every nonzero
scalar, by its initial quaternary subform. -/
theorem diagonalUnit_exists_value_of_four_le
    {n : Nat} (target : Fin n → Kˣ) (hn : 4 ≤ n) (A : Kˣ) :
    ∃ x : Fin n → K,
      diagonalQuadratic (diagonalUnitCoefficients target) x = (A : K) := by
  let firstFour : Fin 4 → Kˣ :=
    fun i => target ⟨i.val, i.isLt.trans_le hn⟩
  have hprefix : DiagonalRepresents
      (diagonalUnitCoefficients firstFour)
      (diagonalUnitCoefficients target) := by
    exact DiagonalRepresents.prefixOfLE
      (diagonalUnitCoefficients target) hn
  exact diagonal_exists_value_of_represents hprefix
    (diagonalUnitQuaternary_exists_value firstFour A)

/-- Concrete codimension-two representation theorem over a dyadic local
field.  The rank-one base case is the ternary signed-determinant criterion;
higher ranks split a common represented line and recurse. -/
theorem dyadicDiagonalCodimensionTwo_represents
    (m : Nat) (source : Fin m → Kˣ) (target : Fin (m + 2) → Kˣ)
    (hdet : ¬ IsSquare
      (-diagonalUnitDeterminant target *
        diagonalUnitDeterminant source)) :
    DiagonalRepresents
      (diagonalUnitCoefficients source)
      (diagonalUnitCoefficients target) := by
  induction m with
  | zero =>
      exact DiagonalRepresents.of_source_length_eq_zero
        (diagonalUnitCoefficients source)
        (diagonalUnitCoefficients target) rfl
  | succ m ih =>
      by_cases hm : m = 0
      · subst m
        let A : Kˣ := source 0
        have hsource : source = fun _ : Fin 1 => A := by
          funext i
          have hi : i = (0 : Fin 1) := Fin.eq_zero i
          subst i
          rfl
        have hdetTernary :
            ¬ IsSquare (-diagonalUnitDeterminant target * A) := by
          simpa [hsource, diagonalUnitDeterminant] using hdet
        obtain ⟨x, hx⟩ :=
          diagonalUnitTernary_exists_value_of_not_signedDeterminantSquare
            target A hdetTernary
        obtain ⟨c, hsplit, _hhasse⟩ :=
          exists_diagonal_split_first (K := K) 2 target A x hx
        have hline : DiagonalRepresents
            (fun _ : Fin 1 => (A : K))
            (diagonalUnitCoefficients (Fin.cons A c)) := by
          convert DiagonalRepresents.prefixOfLE
            (k := 1) (diagonalUnitCoefficients (Fin.cons A c)) (by omega)
          simp [diagonalUnitCoefficients]
        rw [hsource]
        exact hline.trans hsplit
      · let A : Kˣ := source 0
        let sourceTail : Fin m → Kˣ := Fin.tail source
        have hsource : source = Fin.cons A sourceTail := by
          exact (Fin.cons_self_tail source).symm
        have hfour : 4 ≤ (m + 1) + 2 := by omega
        obtain ⟨x, hx⟩ :=
          diagonalUnit_exists_value_of_four_le target hfour A
        obtain ⟨c, hsplit, _hhasse⟩ :=
          exists_diagonal_split_first (K := K) (m + 2) target A x hx
        let C : Kˣ := diagonalUnitDeterminant c
        let S : Kˣ := diagonalUnitDeterminant sourceTail
        let T : Kˣ := diagonalUnitDeterminant target
        have hsplitDet : IsSquare ((A * C) * T) := by
          have h := DiagonalIsometryInvariantLaws.determinant_square
            (Fin.cons A c) target hsplit
          simpa [C, T] using h
        have htailDet : ¬ IsSquare (-C * S) := by
          intro htailSquare
          have hCSquare : IsSquare (C ^ 2) := by
            exact ⟨C, by simp [pow_two]⟩
          have hquotient : IsSquare
              ((((A * C) * T) * (-C * S)) / (C ^ 2)) :=
            (hsplitDet.mul htailSquare).div hCSquare
          have heq : ((((A * C) * T) * (-C * S)) / (C ^ 2)) =
              -T * (A * S) := by
            apply Units.ext
            simp only [Units.val_div_eq_div_val, Units.val_mul,
              Units.val_neg, Units.val_pow_eq_pow_val]
            field_simp [Units.ne_zero C]
          have hdesired : IsSquare (-T * (A * S)) := by
            rw [← heq]
            exact hquotient
          apply hdet
          have hsourceDet : diagonalUnitDeterminant source = A * S := by
            rw [hsource, diagonalUnitDeterminant_cons]
          simpa only [T, hsourceDet] using hdesired
        have htailRep : DiagonalRepresents
            (diagonalUnitCoefficients sourceTail)
            (diagonalUnitCoefficients c) :=
          ih sourceTail c (by simpa only [C, S] using htailDet)
        have hcons : DiagonalRepresents
            (diagonalUnitCoefficients (Fin.cons A sourceTail))
            (diagonalUnitCoefficients (Fin.cons A c)) := by
          simpa only [diagonalUnitCoefficients_cons] using
            diagonalRepresents_cons htailRep (A : K)
        rw [hsource]
        exact hcons.trans hsplit

/-- The unconditional codimension-two local representation instance. -/
noncomputable instance dyadicDiagonalCodimensionTwoLawsProvedDirect :
    DyadicDiagonalCodimensionTwoLaws K where
  represents_of_not_negative_determinant_square source target hrank hdet := by
    subst hrank
    exact dyadicDiagonalCodimensionTwo_represents _ source target hdet

example : DyadicDiagonalCodimensionTwoLaws K := inferInstance

end Bong
