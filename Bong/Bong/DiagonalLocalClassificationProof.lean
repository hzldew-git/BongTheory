/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.DiagonalLocalClassification
import Bong.Bong.DiagonalCodimensionTwoRepresentationProof
import Bong.Bong.DiagonalDeterminantExtension

/-!
# Local classification of diagonal quadratic spaces over dyadic fields

This file discharges the former `DyadicDiagonalClassificationLaws` boundary.
Ranks at most two are treated explicitly with the Hilbert-symbol norm
criterion.  In rank three, a nonsquare auxiliary line is split from both
forms and the binary result is applied to the complements.  From rank four
on, quaternary universality supplies a common represented line and strong
induction classifies the tails.

Thus the classification theorem is derived from the concrete dyadic Hilbert
symbol, quaternion, splitting, and cancellation developments, without an
additional local-law assumption.
-/

namespace Bong

open Dyadic BONG.GoodBONG

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- Beli's binary Hasse symbol in determinant-cross-term form. -/
theorem diagonalHasseSymbol_fin_two_eq_det_cross (a : Fin 2 → Kˣ) :
    diagonalHasseSymbol K a =
      hilbertSymbol K (diagonalUnitDeterminant a) (-1) *
        hilbertSymbol K (a 0) (a 1) := by
  have hexpand : diagonalHasseSymbol K a =
      hilbertSymbol K (a 0) (a 0) *
        hilbertSymbol K (a 0) (a 1) *
          hilbertSymbol K (a 1) (a 1) := by
    rw [show a =
        Fin.snoc (Fin.snoc (fun _ : Fin 0 => (1 : Kˣ)) (a 0)) (a 1) by
      funext i
      fin_cases i <;> rfl]
    simp [diagonalUnitDeterminant]
    rfl
  rw [hexpand, hilbertSymbol_self_eq_neg_one,
    hilbertSymbol_self_eq_neg_one, diagonalUnitDeterminant]
  rw [Fin.prod_univ_two, hilbertSymbol_mul_left]
  ac_rfl

/-- Binary diagonal forms with equal determinant square class and equal
Hasse symbol are isometric. -/
theorem diagonalUnitBinary_represents_of_invariants
    (a b : Fin 2 → Kˣ)
    (hdet : IsSquare
      (diagonalUnitDeterminant a * diagonalUnitDeterminant b))
    (hhasse : diagonalHasseSymbol K a = diagonalHasseSymbol K b) :
    DiagonalRepresents
      (diagonalUnitCoefficients a)
      (diagonalUnitCoefficients b) := by
  let A : Kˣ := a 0
  let D : Kˣ := a 1
  let B : Kˣ := b 0
  let C : Kˣ := b 1
  have hdetFactor : IsSquare ((A * D) * (B * C)) := by
    simpa [A, D, B, C, diagonalUnitDeterminant, Fin.prod_univ_two]
      using hdet
  have hdetHilbert : hilbertSymbol K (A * D) (-1) =
      hilbertSymbol K (B * C) (-1) :=
    hilbertSymbol_eq_of_isSquare_mul_left hdetFactor
  have hcross : hilbertSymbol K A D = hilbertSymbol K B C := by
    rw [diagonalHasseSymbol_fin_two_eq_det_cross,
      diagonalHasseSymbol_fin_two_eq_det_cross] at hhasse
    have hhasse' :
        hilbertSymbol K (A * D) (-1) * hilbertSymbol K A D =
          hilbertSymbol K (B * C) (-1) * hilbertSymbol K B C := by
      simpa [A, D, B, C, diagonalUnitDeterminant, Fin.prod_univ_two]
        using hhasse
    rw [hdetHilbert] at hhasse'
    exact mul_left_cancel hhasse'
  let Z : Kˣ := -(B * C)
  have hclass : IsSquare (D * (A * B * C)) := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using hdetFactor
  have hAD : hilbertSymbol K A D =
      hilbertSymbol K A (A * B * C) :=
    hilbertSymbol_eq_of_isSquare_mul_right hclass
  have hAZ : hilbertSymbol K A Z = hilbertSymbol K B Z := by
    calc
      hilbertSymbol K A Z =
          hilbertSymbol K A (-1) * hilbertSymbol K A B *
            hilbertSymbol K A C := by
              dsimp only [Z]
              rw [show -(B * C) = (-1 : Kˣ) * B * C by simp,
                hilbertSymbol_mul_right, hilbertSymbol_mul_right]
      _ = hilbertSymbol K A A * hilbertSymbol K A B *
            hilbertSymbol K A C := by
              rw [hilbertSymbol_self_eq_neg_one]
      _ = hilbertSymbol K A (A * B * C) := by
              rw [hilbertSymbol_mul_right, hilbertSymbol_mul_right]
      _ = hilbertSymbol K A D := hAD.symm
      _ = hilbertSymbol K B C := hcross
      _ = hilbertSymbol K B Z := by
              dsimp only [Z]
              rw [show -(B * C) = (-B) * C by simp,
                hilbertSymbol_mul_right, hilbertSymbol_self_neg_eq_one,
                one_mul]
  have hBinv : hilbertSymbol K B⁻¹ Z = hilbertSymbol K B Z := by
    rw [show B⁻¹ = B * (B⁻¹) ^ 2 by group,
      hilbertSymbol_mul_square_left]
  have hnorm : hilbertSymbol K (A * B⁻¹) (-(B * C)) = 1 := by
    change hilbertSymbol K (A * B⁻¹) Z = 1
    rw [hilbertSymbol_mul_left, hBinv, hAZ,
      hilbertSymbol_mul_self]
  have hline : DiagonalRepresents
      (fun _ : Fin 1 => (A : K))
      (diagonalUnitCoefficients b) := by
    have h :=
      (DiagonalRepresents.unary_binary_iff_hilbertSymbol_one B C A).2 hnorm
    convert h using 1
    funext i
    fin_cases i <;> rfl
  have hprefix : DiagonalRepresents
      (diagonalUnitCoefficients (diagonalUnitPrefix a))
      (diagonalUnitCoefficients b) := by
    convert hline using 1
    funext i
    fin_cases i
    rfl
  exact diagonalRepresents_of_prefix_of_determinant_square
    a b hprefix hdet

/-- Equality of square classes, written multiplicatively, is transitive. -/
theorem isSquare_mul_trans (x y z : Kˣ)
    (hxy : IsSquare (x * y)) (hyz : IsSquare (y * z)) :
    IsSquare (x * z) := by
  have hy2 : IsSquare (y ^ 2) := ⟨y, pow_two y⟩
  have hquotient : IsSquare (((x * y) * (y * z)) / (y ^ 2)) :=
    (hxy.mul hyz).div hy2
  have heq : ((x * y) * (y * z)) / (y ^ 2) = x * z := by
    apply Units.ext
    simp only [Units.val_div_eq_div_val, Units.val_mul,
      Units.val_pow_eq_pow_val]
    field_simp [Units.ne_zero y]
  rw [heq] at hquotient
  exact hquotient

/-- Remove a common first diagonal line from a determinant square-class
identity. -/
theorem diagonalUnitDeterminant_tail_square_of_cons
    {n : Nat} (A : Kˣ) (c d : Fin n → Kˣ)
    (hdet : IsSquare
      (diagonalUnitDeterminant (Fin.cons A c) *
        diagonalUnitDeterminant (Fin.cons A d))) :
    IsSquare (diagonalUnitDeterminant c * diagonalUnitDeterminant d) := by
  have hA2 : IsSquare (A ^ 2) := ⟨A, pow_two A⟩
  have hquotient : IsSquare
      ((diagonalUnitDeterminant (Fin.cons A c) *
          diagonalUnitDeterminant (Fin.cons A d)) / (A ^ 2)) :=
    hdet.div hA2
  have heq :
      (diagonalUnitDeterminant (Fin.cons A c) *
          diagonalUnitDeterminant (Fin.cons A d)) / (A ^ 2) =
        diagonalUnitDeterminant c * diagonalUnitDeterminant d := by
    rw [diagonalUnitDeterminant_cons, diagonalUnitDeterminant_cons]
    apply Units.ext
    simp only [Units.val_div_eq_div_val, Units.val_mul,
      Units.val_pow_eq_pow_val]
    field_simp [Units.ne_zero A]
  rw [heq] at hquotient
  exact hquotient

/-- Cancel a common first line from equality of Beli Hasse symbols once the
two tails have the same determinant square class. -/
theorem diagonalHasseSymbol_tail_eq_of_cons
    {n : Nat} (A : Kˣ) (c d : Fin n → Kˣ)
    (hdet : IsSquare
      (diagonalUnitDeterminant c * diagonalUnitDeterminant d))
    (hhasse : diagonalHasseSymbol K (Fin.cons A c) =
      diagonalHasseSymbol K (Fin.cons A d)) :
    diagonalHasseSymbol K c = diagonalHasseSymbol K d := by
  have hcross :
      hilbertSymbol K (diagonalUnitDeterminant c) A =
        hilbertSymbol K (diagonalUnitDeterminant d) A :=
    hilbertSymbol_eq_of_isSquare_mul_left hdet
  rw [diagonalHasseSymbol_cons, diagonalHasseSymbol_cons, hcross] at hhasse
  exact mul_right_cancel (mul_right_cancel hhasse)

/-- The two tail invariants obtained after splitting a common represented
line from equal-invariant diagonal spaces. -/
theorem diagonal_tail_invariants_of_common_head
    {n : Nat} (A : Kˣ) (c d : Fin n → Kˣ)
    (hdet : IsSquare
      (diagonalUnitDeterminant (Fin.cons A c) *
        diagonalUnitDeterminant (Fin.cons A d)))
    (hhasse : diagonalHasseSymbol K (Fin.cons A c) =
      diagonalHasseSymbol K (Fin.cons A d)) :
    IsSquare (diagonalUnitDeterminant c * diagonalUnitDeterminant d) ∧
      diagonalHasseSymbol K c = diagonalHasseSymbol K d := by
  have htailDet :=
    diagonalUnitDeterminant_tail_square_of_cons A c d hdet
  exact ⟨htailDet,
    diagonalHasseSymbol_tail_eq_of_cons A c d htailDet hhasse⟩

/-- A square unit has even additive valuation. -/
private theorem even_ordUnit_of_isSquare_classification
    (a : Kˣ) (ha : IsSquare a) : Even (ordUnit K a) := by
  rcases ha with ⟨s, rfl⟩
  refine ⟨ordUnit K s, ?_⟩
  rw [ordUnit_mul]

/-- The distinguished uniformizer gives a nonsquare unit class. -/
private theorem uniformizerUnit_not_isSquare_classification :
    ¬ IsSquare (uniformizerUnit K) := by
  intro hsquare
  have heven := even_ordUnit_of_isSquare_classification (K := K)
    (uniformizerUnit K) hsquare
  have horder : ordUnit K (uniformizerUnit K) = 1 := by
    simpa [uniformizerPowerUnit] using
      (ordUnit_uniformizerPowerUnit (K := K) (1 : Int))
  rw [horder] at heven
  rcases heven with ⟨z, hz⟩
  omega

/-- Every square class can be multiplied by a class so that the product is
nonsquare. -/
theorem exists_nonsquare_multiplier (X : Kˣ) :
    ∃ A : Kˣ, ¬ IsSquare (X * A) := by
  by_cases hX : IsSquare X
  · refine ⟨uniformizerUnit K, ?_⟩
    intro hproduct
    have hquotient : IsSquare
        ((X * uniformizerUnit K) / X) := hproduct.div hX
    have heq : (X * uniformizerUnit K) / X = uniformizerUnit K := by
      apply Units.ext
      simp only [Units.val_div_eq_div_val, Units.val_mul]
      field_simp [Units.ne_zero X]
    rw [heq] at hquotient
    exact uniformizerUnit_not_isSquare_classification (K := K) hquotient
  · exact ⟨1, by simpa using hX⟩

/-- A nonsquare product remains nonsquare after replacing one factor by an
equal square class. -/
theorem not_isSquare_mul_of_square_mul
    (x y A : Kˣ) (hxy : IsSquare (x * y))
    (hxA : ¬ IsSquare (x * A)) :
    ¬ IsSquare (y * A) := by
  intro hyA
  exact hxA (isSquare_mul_trans x y A hxy hyA)

/-- Ternary diagonal forms with the same determinant square class and Hasse
symbol are isometric. -/
theorem diagonalUnitTernary_represents_of_invariants
    (a b : Fin 3 → Kˣ)
    (hdet : IsSquare
      (diagonalUnitDeterminant a * diagonalUnitDeterminant b))
    (hhasse : diagonalHasseSymbol K a = diagonalHasseSymbol K b) :
    DiagonalRepresents
      (diagonalUnitCoefficients a)
      (diagonalUnitCoefficients b) := by
  let X : Kˣ := -diagonalUnitDeterminant a
  let Y : Kˣ := -diagonalUnitDeterminant b
  obtain ⟨A, hXA⟩ := exists_nonsquare_multiplier (K := K) X
  have hXY : IsSquare (X * Y) := by
    simpa [X, Y] using hdet
  have hYA : ¬ IsSquare (Y * A) :=
    not_isSquare_mul_of_square_mul X Y A hXY hXA
  have haNotSquare :
      ¬ IsSquare (-diagonalUnitDeterminant a * A) := by
    simpa only [X] using hXA
  have hbNotSquare :
      ¬ IsSquare (-diagonalUnitDeterminant b * A) := by
    simpa only [Y] using hYA
  obtain ⟨xa, hxa⟩ :=
    diagonalUnitTernary_exists_value_of_not_signedDeterminantSquare
      a A haNotSquare
  obtain ⟨ca, haSplit, haSplitHasse⟩ :=
    exists_diagonal_split_first (K := K) 2 a A xa hxa
  obtain ⟨xb, hxb⟩ :=
    diagonalUnitTernary_exists_value_of_not_signedDeterminantSquare
      b A hbNotSquare
  obtain ⟨cb, hbSplit, hbSplitHasse⟩ :=
    exists_diagonal_split_first (K := K) 2 b A xb hxb
  have haSplitDet := DiagonalIsometryInvariantLaws.determinant_square
    (Fin.cons A ca) a haSplit
  have hbSplitDet := DiagonalIsometryInvariantLaws.determinant_square
    (Fin.cons A cb) b hbSplit
  have hleftToB : IsSquare
      (diagonalUnitDeterminant (Fin.cons A ca) *
        diagonalUnitDeterminant b) :=
    isSquare_mul_trans _ (diagonalUnitDeterminant a) _
      haSplitDet hdet
  have hBToRight : IsSquare
      (diagonalUnitDeterminant b *
        diagonalUnitDeterminant (Fin.cons A cb)) := by
    simpa only [mul_comm] using hbSplitDet
  have hfullDet : IsSquare
      (diagonalUnitDeterminant (Fin.cons A ca) *
        diagonalUnitDeterminant (Fin.cons A cb)) :=
    isSquare_mul_trans _ (diagonalUnitDeterminant b) _
      hleftToB hBToRight
  have hfullHasse :
      diagonalHasseSymbol K (Fin.cons A ca) =
        diagonalHasseSymbol K (Fin.cons A cb) :=
    haSplitHasse.trans (hhasse.trans hbSplitHasse.symm)
  obtain ⟨htailDet, htailHasse⟩ :=
    diagonal_tail_invariants_of_common_head A ca cb hfullDet hfullHasse
  have htailRep := diagonalUnitBinary_represents_of_invariants
    ca cb htailDet htailHasse
  have hcons : DiagonalRepresents
      (diagonalUnitCoefficients (Fin.cons A ca))
      (diagonalUnitCoefficients (Fin.cons A cb)) := by
    simpa only [diagonalUnitCoefficients_cons] using
      diagonalRepresents_cons htailRep (A : K)
  exact (haSplit.symm_of_sameRank.trans hcons).trans hbSplit

/-- Concrete classification of nondegenerate diagonal forms over a dyadic
local field by dimension, determinant square class, and Beli's Hasse
symbol. -/
theorem dyadicDiagonalClassification_represents :
    ∀ (n : Nat) (a b : Fin n → Kˣ),
      IsSquare
          (diagonalUnitDeterminant a * diagonalUnitDeterminant b) →
        diagonalHasseSymbol K a = diagonalHasseSymbol K b →
          DiagonalRepresents
            (diagonalUnitCoefficients a)
            (diagonalUnitCoefficients b) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro a b hdet hhasse
      cases n with
      | zero =>
          exact DiagonalRepresents.of_source_length_eq_zero
            (diagonalUnitCoefficients a)
            (diagonalUnitCoefficients b) rfl
      | succ n =>
          cases n with
          | zero =>
              have hprefix : DiagonalRepresents
                  (diagonalUnitCoefficients (diagonalUnitPrefix a))
                  (diagonalUnitCoefficients b) :=
                DiagonalRepresents.of_source_length_eq_zero
                  (diagonalUnitCoefficients (diagonalUnitPrefix a))
                  (diagonalUnitCoefficients b) rfl
              exact diagonalRepresents_of_prefix_of_determinant_square
                a b hprefix hdet
          | succ n =>
              cases n with
              | zero =>
                  exact diagonalUnitBinary_represents_of_invariants
                    a b hdet hhasse
              | succ n =>
                  cases n with
                  | zero =>
                      exact diagonalUnitTernary_represents_of_invariants
                        a b hdet hhasse
                  | succ n =>
                      let A : Kˣ := a 0
                      let aTail : Fin (n + 3) → Kˣ := Fin.tail a
                      have ha : a = Fin.cons A aTail := by
                        exact (Fin.cons_self_tail a).symm
                      obtain ⟨xb, hxb⟩ :=
                        diagonalUnit_exists_value_of_four_le b (by omega) A
                      obtain ⟨c, hbSplit, hbSplitHasse⟩ :=
                        exists_diagonal_split_first (K := K) (n + 3)
                          b A xb hxb
                      have hbSplitDet :=
                        DiagonalIsometryInvariantLaws.determinant_square
                          (Fin.cons A c) b hbSplit
                      have haToB : IsSquare
                          (diagonalUnitDeterminant (Fin.cons A aTail) *
                            diagonalUnitDeterminant b) := by
                        simpa only [ha] using hdet
                      have hBToSplit : IsSquare
                          (diagonalUnitDeterminant b *
                            diagonalUnitDeterminant (Fin.cons A c)) := by
                        simpa only [mul_comm] using hbSplitDet
                      have hfullDet : IsSquare
                          (diagonalUnitDeterminant (Fin.cons A aTail) *
                            diagonalUnitDeterminant (Fin.cons A c)) :=
                        isSquare_mul_trans _ (diagonalUnitDeterminant b) _
                          haToB hBToSplit
                      have hfullHasse :
                          diagonalHasseSymbol K (Fin.cons A aTail) =
                            diagonalHasseSymbol K (Fin.cons A c) := by
                        calc
                          diagonalHasseSymbol K (Fin.cons A aTail) =
                              diagonalHasseSymbol K a := by rw [ha]
                          _ = diagonalHasseSymbol K b := hhasse
                          _ = diagonalHasseSymbol K (Fin.cons A c) :=
                            hbSplitHasse.symm
                      obtain ⟨htailDet, htailHasse⟩ :=
                        diagonal_tail_invariants_of_common_head
                          A aTail c hfullDet hfullHasse
                      have htailRep := ih (n + 3) (by omega)
                        aTail c htailDet htailHasse
                      have hcons : DiagonalRepresents
                          (diagonalUnitCoefficients (Fin.cons A aTail))
                          (diagonalUnitCoefficients (Fin.cons A c)) := by
                        simpa only [diagonalUnitCoefficients_cons] using
                          diagonalRepresents_cons htailRep (A : K)
                      rw [ha]
                      exact hcons.trans hbSplit

/-- The unconditional local classification instance. -/
noncomputable instance dyadicDiagonalClassificationLawsProved :
    DyadicDiagonalClassificationLaws K where
  represents_of_invariants a b hdet hhasse :=
    dyadicDiagonalClassification_represents _ a b hdet hhasse

example : DyadicDiagonalClassificationLaws K := inferInstance

end Bong
