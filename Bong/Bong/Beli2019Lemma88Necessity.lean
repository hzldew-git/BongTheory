/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma88Statement
import Bong.Bong.Beli2019Lemma82
import Bong.Bong.Beli2006SectionThree
import Bong.Bong.DiagonalCodimensionOneCancellation
import Bong.Bong.DiagonalTernaryCore

/-!
# Beli (2019), Lemma 8.8: necessity

This file proves the obstruction direction of Lemma 8.8.  The first step is
an algebraic bridge from representation of a unary diagonal form by the
first binary prefix to the Hilbert-symbol identity used in the paper.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {N : Nat}

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K] [DyadicContext K] in
/-- An injective diagonal representation pulls anisotropy back from the
target form to the source form. -/
theorem diagonalAnisotropic_of_represents {n : Nat}
    {source target : Fin n → K}
    (hrep : DiagonalRepresents source target)
    (htarget : ∀ x : Fin n → K,
      diagonalQuadratic target x = 0 → x = 0) :
    ∀ x : Fin n → K, diagonalQuadratic source x = 0 → x = 0 := by
  rcases hrep with ⟨f, hf, hquadratic⟩
  intro x hx
  have hfx : f x = 0 := by
    apply htarget (f x)
    rw [hquadratic]
    exact hx
  apply hf
  simpa using hfx

omit [ValuativeRel K] [TopologicalSpace K] [DyadicContext K] in
/-- Complete a represented binary diagonal form by the determinant line.
Codimension-one cancellation then identifies the resulting ternary form with
the original ternary form. -/
theorem determinantCompletion_represents_base
    [DiagonalCodimensionOneCancellationLaws K]
    (base : Fin 3 → Kˣ) (head : Fin 2 → Kˣ)
    (hrep : DiagonalRepresents
      (diagonalUnitCoefficients head)
      (diagonalUnitCoefficients base)) :
    let d := diagonalUnitDeterminant base *
      diagonalUnitDeterminant head
    DiagonalRepresents
      (diagonalUnitCoefficients (Fin.snoc head d))
      (diagonalUnitCoefficients base) := by
  let d := diagonalUnitDeterminant base *
    diagonalUnitDeterminant head
  let candidate : Fin 3 → Kˣ := Fin.snoc head d
  let extended : Fin 4 → Kˣ := Fin.snoc base d
  have happended : DiagonalRepresents
      (diagonalUnitCoefficients candidate)
      (diagonalUnitCoefficients extended) := by
    have h := diagonalRepresents_snoc hrep (d : K)
    have hcandidate :
        diagonalUnitCoefficients candidate =
          Fin.snoc (diagonalUnitCoefficients head) (d : K) := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · change
          ((((Fin.snoc head d : Fin 3 → Kˣ) (Fin.last 2)) : Kˣ) : K) =
            (Fin.snoc (diagonalUnitCoefficients head) (d : K) : Fin 3 → K)
              (Fin.last 2)
        rw [Fin.snoc_last, Fin.snoc_last]
      · simp [candidate, diagonalUnitCoefficients]
    have hextended :
        diagonalUnitCoefficients extended =
          Fin.snoc (diagonalUnitCoefficients base) (d : K) := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · change
          ((((Fin.snoc base d : Fin 4 → Kˣ) (Fin.last 3)) : Kˣ) : K) =
            (Fin.snoc (diagonalUnitCoefficients base) (d : K) : Fin 4 → K)
              (Fin.last 3)
        rw [Fin.snoc_last, Fin.snoc_last]
      · simp [extended, diagonalUnitCoefficients]
    rw [hcandidate, hextended]
    exact h
  apply DiagonalCodimensionOneCancellationLaws.cancel
    base candidate extended
  · exact diagonalUnitPrefix_snoc base d
  · exact happended
  · rw [show diagonalUnitDeterminant candidate =
        diagonalUnitDeterminant head * d by
      exact diagonalUnitDeterminant_snoc head d]
    refine ⟨diagonalUnitDeterminant base *
      diagonalUnitDeterminant head, ?_⟩
    simp only [d]
    ac_rfl

/-- Equality of embedded rational defect orders reflects to equality of the
underlying extended-natural quadratic defects. -/
theorem quadraticDefect_eq_of_defectOrder_eq (a b : Kˣ)
    (h : defectOrder (K := K) a = defectOrder (K := K) b) :
    quadraticDefect K a = quadraticDefect K b := by
  let f : Nat → ℚ := Nat.castAddMonoidHom ℚ
  have hf : Function.Injective (f : Nat → ℚ) := by
    intro m n hmn
    change (m : ℚ) = (n : ℚ) at hmn
    exact_mod_cast hmn
  apply (WithTop.map_injective hf)
  exact h

/-- Strict inequalities of quadratic defects remain strict after embedding
from `ℕ∞` into `ℚ ∪ {∞}`. -/
theorem defectOrder_lt_of_quadraticDefect_lt (a b : Kˣ)
    (h : quadraticDefect K a < quadraticDefect K b) :
    defectOrder (K := K) a < defectOrder (K := K) b := by
  cases ha : quadraticDefect K a with
  | top =>
      rw [ha] at h
      exact (not_lt_of_ge le_top h).elim
  | coe m =>
      cases hb : quadraticDefect K b with
      | top =>
          unfold defectOrder
          rw [ha, hb]
          change ((m : ℚ) : WithTop ℚ) < ⊤
          simp
      | coe n =>
          have hmn : m < n := by simpa [ha, hb] using h
          unfold defectOrder
          rw [ha, hb]
          change ((m : ℚ) : WithTop ℚ) < ((n : ℚ) : WithTop ℚ)
          exact_mod_cast hmn

/-- A finite rational defect-order value comes from a finite quadratic
defect. -/
theorem quadraticDefect_ne_top_of_defectOrder_eq_coe (a : Kˣ) (d : ℚ)
    (h : defectOrder (K := K) a = (d : WithTop ℚ)) :
    quadraticDefect K a ≠ ⊤ := by
  intro htop
  unfold defectOrder at h
  rw [htop] at h
  exact WithTop.top_ne_coe h

/-- Equality of embedded rational defect sums reflects to equality of the
underlying extended-natural defects. -/
theorem quadraticDefect_add_eq_twoE_of_defectOrder_add_eq_twoE
    (a d : Kˣ)
    (h : defectOrder (K := K) a + defectOrder (K := K) d =
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ)) :
    quadraticDefect K a + quadraticDefect K d =
      ((2 * ramificationIndex K : Nat) : WithTop Nat) := by
  let f : Nat →+ ℚ := Nat.castAddMonoidHom ℚ
  have hf : Function.Injective (f : Nat → ℚ) := by
    intro m n hmn
    change (m : ℚ) = (n : ℚ) at hmn
    exact_mod_cast hmn
  let da : WithTop Nat := quadraticDefect K a
  let dd : WithTop Nat := quadraticDefect K d
  change da + dd = ((2 * ramificationIndex K : Nat) : WithTop Nat)
  apply (WithTop.map_injective hf)
  rw [WithTop.map_add]
  change defectOrder (K := K) a + defectOrder (K := K) d =
    (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ)
  exact h

/-- Rational-scale form of the boundary obstruction in Lemma 8.2(iii). -/
theorem hilbertSymbol_ne_one_of_residue_two_of_defectOrder_add_eq_twoE
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    (hres : ¬HasResidueFieldMoreThanTwoElements (K := K))
    (a d : Kˣ)
    (hsum : defectOrder (K := K) a + defectOrder (K := K) d =
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ)) :
    hilbertSymbol K a d ≠ 1 := by
  intro hone
  have hne := (beli2019Lemma82_iii hres a d).mp
    ⟨d, rfl, hone⟩
  exact hne
    (quadraticDefect_add_eq_twoE_of_defectOrder_add_eq_twoE a d hsum)

omit [ValuativeRel K] [TopologicalSpace K] [DyadicContext K] in
/-- Adjacent Hilbert products of an anisotropic diagonal ternary form cannot
pair trivially. -/
theorem hilbertSymbol_adjacent_ne_one_of_diagonalAnisotropic
    (a₀ a₁ a₂ : Kˣ)
    (hanisotropic : ∀ z : Fin 3 → K,
      diagonalQuadratic
        (fun i => ![(a₀ : K), (a₁ : K), (a₂ : K)] i) z = 0 → z = 0) :
    hilbertSymbol K (-(a₀ * a₁)) (-(a₁ * a₂)) ≠ 1 := by
  intro hone
  rcases diagonalTernary_isotropic_of_adjacent_hilbert_one
      a₀ a₁ a₂ hone with ⟨z, hz, hquadratic⟩
  exact hz (hanisotropic z hquadratic)

/-- Hence anisotropy of the first ternary prefix excludes Hilbert symbol
one for its two adjacent products. -/
theorem hilbertSymbol_firstAdjacent_secondAdjacent_ne_one
    (b : GoodBONG q L (N + 2)) (hthree : 3 ≤ N + 2)
    (hanisotropic : b.Lemma88FirstThreeAnisotropic hthree) :
    hilbertSymbol K
        (b.adjacentProduct ⟨0, by omega⟩)
        (b.adjacentProduct ⟨1, by omega⟩) ≠ 1 := by
  intro hone
  have hproducts :
      hilbertSymbol K
          (-(b.valueUnit ⟨0, by omega⟩ * b.valueUnit ⟨1, by omega⟩))
          (-(b.valueUnit ⟨1, by omega⟩ * b.valueUnit ⟨2, by omega⟩)) = 1 := by
    simpa [adjacentProduct] using hone
  rcases diagonalTernary_isotropic_of_adjacent_hilbert_one
      (b.valueUnit ⟨0, by omega⟩)
      (b.valueUnit ⟨1, by omega⟩)
      (b.valueUnit ⟨2, by omega⟩) hproducts with
    ⟨z, hz, hquadratic⟩
  apply hz
  apply hanisotropic z
  have hcoefficients :
      (fun i : Fin 3 =>
        ![b.value ⟨0, by omega⟩, b.value ⟨1, by omega⟩,
          b.value ⟨2, by omega⟩] i) =
        b.lemma88FirstThreeValues hthree := by
    funext i
    fin_cases i <;> simp [lemma88FirstThreeValues]
  rw [← hcoefficients]
  simpa only [coe_valueUnit] using hquadratic

/-- Remark 8.7 turns the half-gap equality in exception (c) into the exact
sum `α₁ + α₂ = 2e`. -/
theorem alphaSum_eq_twoE_of_lemma88ExceptionC
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q L (N + 2))
    (C : b.Beli2019Lemma88ExceptionC)
    (hhalf : b.AttainsHalfGap (lemma88FirstAlphaIndex (N := N))) :
    b.alphaValue (lemma88FirstAlphaIndex (N := N)) +
        b.alphaValue (lemma88SecondAlphaIndex (N := N) C.rank_three) =
      2 * (ramificationIndex K : ℚ) := by
  cases N with
  | zero =>
      exact False.elim ((by omega : ¬3 ≤ 0 + 2) C.rank_three)
  | succ N =>
      let p : Fin (N + 1) := ⟨0, by omega⟩
      have houter :
          b.order (remark87PreviousValue p) =
            b.order (remark87NextValue p) := by
        simpa [p, remark87PreviousValue, remark87NextValue] using
          C.outerOrders_eq
      have R := b.beli2019Remark87 p houter
      have hp : b.AttainsHalfGap (remark87PreviousAlpha p) := by
        simpa [p, remark87PreviousAlpha, lemma88FirstAlphaIndex] using hhalf
      have hsum := R.alphaSum_eq_twoE_iff.mpr hp
      simpa [p, remark87PreviousAlpha, remark87CurrentAlpha,
        lemma88FirstAlphaIndex, lemma88SecondAlphaIndex] using hsum

/-- At the same boundary, `α₂` is the complementary defect
`e - (R₂-R₁)/2`. -/
theorem secondAlpha_eq_complementary_of_lemma88ExceptionC
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q L (N + 2))
    (C : b.Beli2019Lemma88ExceptionC)
    (hhalf : b.AttainsHalfGap (lemma88FirstAlphaIndex (N := N))) :
    b.alphaValue (lemma88SecondAlphaIndex (N := N) C.rank_three) =
      b.lemma88ComplementaryDefect := by
  have hsum := b.alphaSum_eq_twoE_of_lemma88ExceptionC C hhalf
  unfold lemma88FirstAlphaIndex lemma88SecondAlphaIndex at hsum
  have hboundary := b.halfGap_add_lemma88ComplementaryDefect
  unfold AttainsHalfGap at hhalf
  unfold lemma88FirstAlphaIndex at hhalf
  have hzero : (0 : Fin (N + 1)) = ⟨0, by omega⟩ := by
    apply Fin.ext
    rfl
  rw [hzero] at hboundary
  unfold lemma88SecondAlphaIndex
  linarith

/-- Remark 8.7 gives the two raw adjacent-defect lower bounds used in the
anisotropic part of exception (c). -/
theorem adjacentDefect_lowerBounds_of_lemma88ExceptionC
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q L (N + 2))
    (C : b.Beli2019Lemma88ExceptionC) :
    (b.alphaValue (lemma88SecondAlphaIndex (N := N) C.rank_three) :
          WithTop ℚ) ≤
        b.adjacentDefect (lemma88FirstAlphaIndex (N := N)) ∧
      (b.alphaValue (lemma88FirstAlphaIndex (N := N)) : WithTop ℚ) ≤
        b.adjacentDefect
          (lemma88SecondAlphaIndex (N := N) C.rank_three) := by
  cases N with
  | zero =>
      exact False.elim ((by omega : ¬3 ≤ 0 + 2) C.rank_three)
  | succ N =>
      let p : Fin (N + 1) := ⟨0, by omega⟩
      have houter :
          b.order (remark87PreviousValue p) =
            b.order (remark87NextValue p) := by
        simpa [p, remark87PreviousValue, remark87NextValue] using
          C.outerOrders_eq
      have R := b.beli2019Remark87 p houter
      constructor
      · simpa [p, remark87PreviousAlpha, remark87CurrentAlpha,
          lemma88FirstAlphaIndex, lemma88SecondAlphaIndex] using
          R.currentAlpha_le_previousRawDefect
      · simpa [p, remark87PreviousAlpha, remark87CurrentAlpha,
          lemma88FirstAlphaIndex, lemma88SecondAlphaIndex] using
          R.previousAlpha_le_currentRawDefect

/-- Anisotropy forces both adjacent-defect lower bounds in exception (c) to
be equalities.  If either were strict, their sum would exceed `2e`, making
the adjacent Hilbert symbol one and the ternary prefix isotropic. -/
theorem adjacentDefects_eq_of_lemma88ExceptionC
    [Beli2006AlphaLaws.{u, v} K]
    [HilbertSymbolLaws K]
    (b : GoodBONG q L (N + 2))
    (C : b.Beli2019Lemma88ExceptionC)
    (hhalf : b.AttainsHalfGap (lemma88FirstAlphaIndex (N := N))) :
    b.adjacentDefect (lemma88FirstAlphaIndex (N := N)) =
        (b.alphaValue
          (lemma88SecondAlphaIndex (N := N) C.rank_three) : WithTop ℚ) ∧
      b.adjacentDefect
          (lemma88SecondAlphaIndex (N := N) C.rank_three) =
        (b.alphaValue (lemma88FirstAlphaIndex (N := N)) : WithTop ℚ) := by
  let first := lemma88FirstAlphaIndex (N := N)
  let second := lemma88SecondAlphaIndex (N := N) C.rank_three
  have hlower := b.adjacentDefect_lowerBounds_of_lemma88ExceptionC C
  have hsum := b.alphaSum_eq_twoE_of_lemma88ExceptionC C hhalf
  have hsumTop :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) =
        (b.alphaValue second : WithTop ℚ) +
          (b.alphaValue first : WithTop ℚ) := by
    change (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) =
      (b.alphaValue
          (lemma88SecondAlphaIndex (N := N) C.rank_three) : WithTop ℚ) +
        (b.alphaValue (lemma88FirstAlphaIndex (N := N)) : WithTop ℚ)
    exact_mod_cast (by
      rw [add_comm]
      push_cast
      exact hsum.symm)
  have hnotHilbert :
      hilbertSymbol K (b.adjacentProduct first)
          (b.adjacentProduct second) ≠ 1 := by
    apply b.hilbertSymbol_firstAdjacent_secondAdjacent_ne_one
      C.rank_three C.firstThree_anisotropic
  have forceContradiction
      (hgt : (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        b.adjacentDefect first + b.adjacentDefect second) : False := by
    apply hnotHilbert
    apply hilbertSymbol_eq_one_of_defectOrder_add_gt_two_mul_e
    simpa [adjacentDefect] using hgt
  constructor
  · apply le_antisymm
    · by_contra hnot
      have hstrict :
          (b.alphaValue second : WithTop ℚ) <
            b.adjacentDefect first := lt_of_not_ge hnot
      apply forceContradiction
      calc
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) =
            (b.alphaValue second : WithTop ℚ) +
              (b.alphaValue first : WithTop ℚ) := hsumTop
        _ < b.adjacentDefect first + b.adjacentDefect second :=
          WithTop.add_lt_add_of_lt_of_le WithTop.coe_ne_top
            hstrict hlower.2
    · exact hlower.1
  · apply le_antisymm
    · by_contra hnot
      have hstrict :
          (b.alphaValue first : WithTop ℚ) <
            b.adjacentDefect second := lt_of_not_ge hnot
      apply forceContradiction
      calc
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) =
            (b.alphaValue second : WithTop ℚ) +
              (b.alphaValue first : WithTop ℚ) := hsumTop
        _ < b.adjacentDefect first + b.adjacentDefect second :=
          WithTop.add_lt_add_of_le_of_lt WithTop.coe_ne_top
            hlower.1 hstrict
    · exact hlower.2

/-- If the new first coefficient is represented by the old binary prefix,
then `(a'₁a₁,-a₁a₂) = 1`.  This is the elementary norm calculation in the
necessity proof of Lemma 8.8. -/
theorem hilbertSymbol_firstChange_firstAdjacent_eq_one
    (a c : GoodBONG q L (N + 2))
    (hrep : DiagonalRepresents
      (c.prefixValues 1 (by omega))
      (a.prefixValues 2 (by omega))) :
    hilbertSymbol K
        (c.valueUnit 0 * a.valueUnit 0)
        (a.adjacentProduct 0) = 1 := by
  rcases hrep with ⟨f, _, hquadratic⟩
  let e : Fin 1 → K := fun _ => 1
  let x := f e
  have hvalue := hquadratic e
  rw [hilbertSymbol_comm]
  apply (hilbertSymbol_eq_one_iff K _ _).2
  refine ⟨(a.valueUnit 0 : K) * x 0, x 1, ?_⟩
  have hdiagonal :
      a.value 0 * x 0 ^ 2 + a.value 1 * x 1 ^ 2 = c.value 0 := by
    simpa [diagonalQuadratic, prefixValues, e, x] using hvalue
  change
    ((a.valueUnit 0 : K) * x 0) ^ 2 -
        (a.adjacentProduct 0 : K) * x 1 ^ 2 =
      ((c.valueUnit 0 * a.valueUnit 0 : Kˣ) : K)
  rw [show (a.adjacentProduct 0 : K) =
      -(a.value 0 * a.value 1) by
        simp [adjacentProduct]]
  simp only [Units.val_mul, coe_valueUnit]
  calc
    (a.value 0 * x 0) ^ 2 -
          -(a.value 0 * a.value 1) * x 1 ^ 2 =
        a.value 0 *
          (a.value 0 * x 0 ^ 2 + a.value 1 * x 1 ^ 2) := by ring
    _ = a.value 0 * c.value 0 := by rw [hdiagonal]
    _ = c.value 0 * a.value 0 := by ring

/-- In exception (b), the bracketed first adjacent defect is the raw
adjacent defect.  For rank at least three this uses the strict inequality
against `α₂`; in rank two the right cap is the terminal infinite cap. -/
theorem adjacentDefect_zero_eq_complementary_of_lemma88ExceptionB
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q L (N + 2))
    (B : b.Beli2019Lemma88ExceptionB) :
    b.adjacentDefect (0 : Fin (N + 1)) =
      (b.lemma88ComplementaryDefect : WithTop ℚ) := by
  have hcapped := B.cappedDefect_eq
  rw [lemma88FirstCappedDefect, truncatedPrefixDefect] at hcapped
  have hraw :
      defectOrder (K := K)
          ((-1) * b.prefixProduct 0 * b.prefixProduct 2) =
        b.adjacentDefect (0 : Fin (N + 1)) := by
    simpa using
      b.defectOrder_prefixPair_eq_adjacentDefect (0 : Fin (N + 1))
  rw [hraw, b.prefixAlphaCap_zero] at hcapped
  simp at hcapped
  cases N with
  | zero =>
      rw [show 2 = 1 + 1 by omega, b.prefixAlphaCap_last] at hcapped
      simpa using hcapped
  | succ N =>
      rw [b.prefixAlphaCap_of_internal (i := 2) (by omega) (by omega)]
        at hcapped
      have hstrict :
          (b.lemma88ComplementaryDefect : WithTop ℚ) <
            (b.alphaValue ⟨1, by omega⟩ : WithTop ℚ) := by
        exact_mod_cast B.nextAlpha_strict (by omega)
      apply le_antisymm
      · by_contra hnot
        have hraw :
            (b.lemma88ComplementaryDefect : WithTop ℚ) <
              b.adjacentDefect (0 : Fin (N + 1 + 1)) :=
          lt_of_not_ge hnot
        have hlt := lt_min hraw hstrict
        rw [hcapped] at hlt
        exact (lt_irrefl _ hlt)
      · rw [← hcapped]
        exact min_le_left _ _

set_option maxHeartbeats 400000 in
/-- Under exception (b) and the half-gap equality, the transformed first
coefficient is represented by the original first binary prefix.  In rank
two this is full-space coordinate change; in higher rank it is condition
(iv) of the good-BONG classification theorem. -/
theorem firstValue_represents_firstTwo_of_lemma88ExceptionB
    [GoodBONGClassificationLaws.{u, v, v} K]
    (b : GoodBONG q L (N + 2))
    (T : b.Beli2019FirstValueTransform)
    (hhalf : b.AttainsHalfGap (0 : Fin (N + 1)))
    (B : b.Beli2019Lemma88ExceptionB) :
    DiagonalRepresents
      (T.transformed.prefixValues 1 (by omega))
      (b.prefixValues 2 (by omega)) := by
  cases N with
  | zero =>
      have hprefix := T.transformed.prefixValues_represents_of_le
        1 2 (by omega) (by omega)
      have hfull := T.transformed.fullPrefix_represents b
      exact hprefix.trans hfull
  | succ N =>
      let first : Fin (N + 1 + 1) := ⟨0, by omega⟩
      let second : Fin (N + 1 + 1) := ⟨1, by omega⟩
      have H :=
        (isometric_iff_classificationConditions
          (QuadraticSpace.isIsometric_refl q) b T.transformed).mp
            (Lattice.isIsometric_refl q L)
      have hnext :
          b.lemma88ComplementaryDefect <
            b.alphaValue second := by
        have h := B.nextAlpha_strict (by omega)
        have hi : (⟨1, by omega⟩ : Fin (N + 1 + 1)) = second := by
          apply Fin.ext
          rfl
        rwa [hi] at h
      have hboundary :
          b.halfGapValue first + b.lemma88ComplementaryDefect =
            2 * (ramificationIndex K : ℚ) := by
        have h := b.halfGap_add_lemma88ComplementaryDefect
        have hi : (0 : Fin (N + 1 + 1)) = first := by
          apply Fin.ext
          rfl
        rwa [hi] at h
      have hhalf' : b.alphaValue first = b.halfGapValue first := by
        unfold AttainsHalfGap at hhalf
        have hi : (0 : Fin (N + 1 + 1)) = first := by
          apply Fin.ext
          rfl
        rwa [hi] at hhalf
      have htrigger :
          2 * (ramificationIndex K : ℚ) <
            b.alphaValue first + b.alphaValue second := by
        calc
          2 * (ramificationIndex K : ℚ) =
              b.halfGapValue first + b.lemma88ComplementaryDefect :=
            hboundary.symm
          _ = b.alphaValue first + b.lemma88ComplementaryDefect := by
            rw [hhalf']
          _ < b.alphaValue first + b.alphaValue second := by
            linarith only [hnext]
      apply H.internalRepresentations
        (⟨1, by omega⟩ : Fin (N + 1 + 1)) (by norm_num)
      change 2 * (ramificationIndex K : ℚ) <
        b.alphaValue first + b.alphaValue second
      exact htrigger

set_option maxHeartbeats 400000 in
/-- Under exception (c), the transformed binary prefix is represented by the
original ternary prefix.  In rank three this is a full-space coordinate
change; from rank four onward it is classification condition (iv) at the
third coordinate. -/
theorem firstTwo_represents_firstThree_of_lemma88ExceptionC
    [Beli2006AlphaLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    (b : GoodBONG q L (N + 2))
    (T : b.Beli2019FirstValueTransform)
    (hhalf : b.AttainsHalfGap (lemma88FirstAlphaIndex (N := N)))
    (C : b.Beli2019Lemma88ExceptionC) :
    DiagonalRepresents
      (T.transformed.prefixValues 2 (by omega))
      (b.prefixValues 3 C.rank_three) := by
  cases N with
  | zero =>
      exact False.elim ((by omega : ¬3 ≤ 0 + 2) C.rank_three)
  | succ N =>
      by_cases hN : N = 0
      · subst N
        have hprefix := T.transformed.prefixValues_represents_of_le
          2 3 (by omega) (by omega)
        have hfull := T.transformed.fullPrefix_represents b
        exact hprefix.trans hfull
      · have hfour : 4 ≤ N.succ + 2 := by omega
        have H :=
          (isometric_iff_classificationConditions
            (QuadraticSpace.isIsometric_refl q) b T.transformed).mp
              (Lattice.isIsometric_refl q L)
        have hsum := b.alphaSum_eq_twoE_of_lemma88ExceptionC C hhalf
        have hlater := C.laterAlpha_strict hfour
        have hhalf' :
            b.alphaValue (0 : Fin (N.succ + 1)) =
              b.halfGapValue (0 : Fin (N.succ + 1)) := by
          have h := hhalf
          unfold AttainsHalfGap at h
          simpa [lemma88FirstAlphaIndex] using h
        have htrigger :
            2 * (ramificationIndex K : ℚ) <
              b.alphaValue (⟨1, by omega⟩ : Fin (N.succ + 1)) +
                b.alphaValue (⟨2, by omega⟩ : Fin (N.succ + 1)) := by
          have hsum' :
              b.alphaValue (0 : Fin (N.succ + 1)) +
                  b.alphaValue (⟨1, by omega⟩ : Fin (N.succ + 1)) =
                2 * (ramificationIndex K : ℚ) := by
            simpa [lemma88FirstAlphaIndex, lemma88SecondAlphaIndex] using hsum
          have hlater' :
              b.alphaValue (0 : Fin (N.succ + 1)) <
                b.alphaValue (⟨2, by omega⟩ : Fin (N.succ + 1)) := by
            rw [hhalf']
            exact hlater
          linarith
        apply H.internalRepresentations
          (⟨2, by omega⟩ : Fin (N.succ + 1)) (by norm_num)
        simpa using htrigger

set_option maxHeartbeats 600000 in
/-- The determinant-completed transformed binary prefix is anisotropic.
After removing the square contributed by its second coefficient, this gives
the nontrivial Hilbert-symbol relation used in exception (c). -/
theorem completedTernary_hilbertSymbol_ne_one_of_lemma88ExceptionC
    [Beli2006AlphaLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DiagonalCodimensionOneCancellationLaws K]
    (b : GoodBONG q L (N + 2))
    (T : b.Beli2019FirstValueTransform)
    (hhalf : b.AttainsHalfGap (lemma88FirstAlphaIndex (N := N)))
    (C : b.Beli2019Lemma88ExceptionC) :
    hilbertSymbol K
        (T.transformed.adjacentProduct (0 : Fin (N + 1)))
        ((T.transformed.valueUnit 0 * b.valueUnit 0) *
          b.adjacentProduct
            (lemma88SecondAlphaIndex (N := N) C.rank_three)) ≠ 1 := by
  let base := b.prefixValueUnits 3 C.rank_three
  let head := T.transformed.prefixValueUnits 2 (by omega)
  let d := diagonalUnitDeterminant base * diagonalUnitDeterminant head
  let candidate : Fin 3 → Kˣ := Fin.snoc head d
  let second := lemma88SecondAlphaIndex (N := N) C.rank_three
  have hrepValues :=
    b.firstTwo_represents_firstThree_of_lemma88ExceptionC T hhalf C
  have hrepUnits : DiagonalRepresents
      (diagonalUnitCoefficients head)
      (diagonalUnitCoefficients base) := by
    simpa [head, base] using hrepValues
  have hcandidateRepresents : DiagonalRepresents
      (diagonalUnitCoefficients candidate)
      (diagonalUnitCoefficients base) := by
    simpa [candidate, d] using
      determinantCompletion_represents_base base head hrepUnits
  have hbaseAnisotropic : ∀ x : Fin 3 → K,
      diagonalQuadratic (diagonalUnitCoefficients base) x = 0 → x = 0 := by
    intro x hx
    apply C.firstThree_anisotropic x
    have hvalues :
        b.prefixValues 3 C.rank_three =
          b.lemma88FirstThreeValues C.rank_three := by
      funext i
      rfl
    rw [← hvalues]
    simpa [base] using hx
  have hcandidateAnisotropic : ∀ x : Fin 3 → K,
      diagonalQuadratic (diagonalUnitCoefficients candidate) x = 0 → x = 0 :=
    diagonalAnisotropic_of_represents hcandidateRepresents hbaseAnisotropic
  have hcandidateCoefficients :
      (fun i : Fin 3 =>
        ![((candidate 0 : Kˣ) : K), ((candidate 1 : Kˣ) : K),
          ((candidate 2 : Kˣ) : K)] i) =
        diagonalUnitCoefficients candidate := by
    funext i
    fin_cases i <;> rfl
  have hcandidateHilbert :
      hilbertSymbol K (-(candidate 0 * candidate 1))
          (-(candidate 1 * candidate 2)) ≠ 1 := by
    apply hilbertSymbol_adjacent_ne_one_of_diagonalAnisotropic
    intro z hz
    apply hcandidateAnisotropic z
    rw [← hcandidateCoefficients]
    exact hz
  have hcandidateZero : candidate (0 : Fin 3) = head (0 : Fin 2) := by
    change (Fin.snoc head d : Fin 3 → Kˣ) 0 = head 0
    rw [show (0 : Fin 3) = (0 : Fin 2).castSucc by rfl,
      Fin.snoc_castSucc]
  have hcandidateOne : candidate (1 : Fin 3) = head (1 : Fin 2) := by
    change (Fin.snoc head d : Fin 3 → Kˣ) 1 = head 1
    rw [show (1 : Fin 3) = (1 : Fin 2).castSucc by rfl,
      Fin.snoc_castSucc]
  have hcandidateTwo : candidate (2 : Fin 3) = d := by
    change (Fin.snoc head d : Fin 3 → Kˣ) 2 = d
    rw [show (2 : Fin 3) = Fin.last 2 by rfl, Fin.snoc_last]
  have hthree : 3 ≤ N + 2 := C.rank_three
  have hbaseZero : base (0 : Fin 3) = b.valueUnit 0 := by
    simp [base, prefixValueUnits]
  have hbaseOne : base (1 : Fin 3) = b.valueUnit 1 := by
    simp [base, prefixValueUnits]
  have hbaseTwo : base (2 : Fin 3) = b.valueUnit second.succ := by
    unfold base prefixValueUnits second lemma88SecondAlphaIndex
    congr 1
  have hheadZero : head (0 : Fin 2) = T.transformed.valueUnit 0 := by
    simp [head, prefixValueUnits]
  have hheadOne : head (1 : Fin 2) = T.transformed.valueUnit 1 := by
    simp [head, prefixValueUnits]
  have hsecondCast : b.valueUnit second.castSucc = b.valueUnit 1 := by
    unfold second lemma88SecondAlphaIndex
    congr 1
  have hd :
      d =
        (b.valueUnit 0 * b.valueUnit 1 *
            b.valueUnit second.succ) *
          (T.transformed.valueUnit 0 * T.transformed.valueUnit 1) := by
    simp only [d, diagonalUnitDeterminant, Fin.prod_univ_two,
      Fin.prod_univ_three]
    rw [hbaseZero, hbaseOne, hbaseTwo, hheadZero, hheadOne]
  have hfirst :
      -(candidate 0 * candidate 1) =
        T.transformed.adjacentProduct (0 : Fin (N + 1)) := by
    rw [hcandidateZero, hcandidateOne]
    rw [hheadZero, hheadOne]
    rfl
  have hsecond :
      -(candidate 1 * candidate 2) =
        ((T.transformed.valueUnit 0 * b.valueUnit 0) *
            b.adjacentProduct
              (lemma88SecondAlphaIndex (N := N) C.rank_three)) *
          (T.transformed.valueUnit 1) ^ 2 := by
    rw [hcandidateOne, hcandidateTwo, hheadOne, hd]
    change
      -(T.transformed.valueUnit 1 *
          ((b.valueUnit 0 * b.valueUnit 1 * b.valueUnit second.succ) *
            (T.transformed.valueUnit 0 * T.transformed.valueUnit 1))) =
        ((T.transformed.valueUnit 0 * b.valueUnit 0) *
            (-(b.valueUnit second.castSucc * b.valueUnit second.succ))) *
          (T.transformed.valueUnit 1) ^ 2
    rw [hsecondCast]
    apply Units.ext
    simp only [Units.val_neg, Units.val_mul, Units.val_pow_eq_pow_val]
    ring
  intro hone
  apply hcandidateHilbert
  rw [hfirst, hsecond, hilbertSymbol_mul_square_right]
  exact hone

/-- Over the two-element residue field in exception (c), the two factors in
the second Hilbert argument have the same finite defect `α₁`; Lemma 8.1(ii)
therefore makes the defect of their product strictly larger. -/
theorem firstComparisonDefect_lt_product_of_lemma88ExceptionC
    [Beli2006AlphaLaws.{u, v} K]
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    (b : GoodBONG q L (N + 2))
    (T : b.Beli2019FirstValueTransform)
    (hhalf : b.AttainsHalfGap (lemma88FirstAlphaIndex (N := N)))
    (C : b.Beli2019Lemma88ExceptionC) :
    defectOrder (K := K)
        (T.transformed.valueUnit 0 * b.valueUnit 0) <
      defectOrder (K := K)
        ((T.transformed.valueUnit 0 * b.valueUnit 0) *
          b.adjacentProduct
            (lemma88SecondAlphaIndex (N := N) C.rank_three)) := by
  let first := lemma88FirstAlphaIndex (N := N)
  let second := lemma88SecondAlphaIndex (N := N) C.rank_three
  let x := T.transformed.valueUnit 0 * b.valueUnit 0
  let y := b.adjacentProduct second
  have hproduct : x = T.epsilon * (b.valueUnit 0) ^ 2 := by
    unfold x
    rw [T.firstValue_eq]
    simp only [pow_two]
    ac_rfl
  have hx : defectOrder (K := K) x =
      (b.alphaValue first : WithTop ℚ) := by
    rw [hproduct, defectOrder_mul_square, T.epsilon_defect]
    rfl
  have hadjacent := b.adjacentDefects_eq_of_lemma88ExceptionC C hhalf
  have hy : defectOrder (K := K) y =
      (b.alphaValue first : WithTop ℚ) := by
    change b.adjacentDefect second =
      (b.alphaValue first : WithTop ℚ)
    exact hadjacent.2
  have hdefectEq : quadraticDefect K x = quadraticDefect K y :=
    quadraticDefect_eq_of_defectOrder_eq x y (hx.trans hy.symm)
  have hxFinite : quadraticDefect K x ≠ ⊤ :=
    quadraticDefect_ne_top_of_defectOrder_eq_coe x (b.alphaValue first) hx
  have hstrict := beli2019Lemma81_ii_strict
    C.residueTwo x y hdefectEq hxFinite
  have hstrict' := defectOrder_lt_of_quadraticDefect_lt x (x * y) hstrict
  simpa [x, y, second] using hstrict'

set_option maxHeartbeats 600000 in
/-- A realized first-value transformation excludes exception (c).  The
anisotropic determinant completion makes the relevant Hilbert symbol
nontrivial, whereas Remark 8.7 and the strict product-defect increase force
the same symbol to be one. -/
theorem Beli2019FirstValueTransform.not_exceptionC
    [Beli2006AlphaLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    {b : GoodBONG q L (N + 2)}
    (T : b.Beli2019FirstValueTransform)
    (hhalf : b.AttainsHalfGap (lemma88FirstAlphaIndex (N := N))) :
    ¬Nonempty b.Beli2019Lemma88ExceptionC := by
  rintro ⟨C⟩
  cases N with
  | zero =>
      exact (by omega : ¬3 ≤ 0 + 2) C.rank_three
  | succ N =>
      let p : Fin (N + 1) := ⟨0, by omega⟩
      let first := lemma88FirstAlphaIndex (N := N + 1)
      let second := lemma88SecondAlphaIndex (N := N + 1) C.rank_three
      let x := T.transformed.valueUnit 0 * b.valueUnit 0
      let product := x * b.adjacentProduct second
      have horders := b.order_invariant T.transformed
      have halphas := b.alpha_invariant T.transformed
      have houterTransformed :
          T.transformed.order (remark87PreviousValue p) =
            T.transformed.order (remark87NextValue p) := by
        calc
          T.transformed.order (remark87PreviousValue p) =
              b.order (remark87PreviousValue p) :=
            (horders (remark87PreviousValue p)).symm
          _ = b.order (remark87NextValue p) := by
            simpa [p, remark87PreviousValue, remark87NextValue] using
              C.outerOrders_eq
          _ = T.transformed.order (remark87NextValue p) :=
            horders (remark87NextValue p)
      have R := T.transformed.beli2019Remark87 p houterTransformed
      have hcurrentAlpha :
          T.transformed.alphaValue (remark87CurrentAlpha p) =
            b.alphaValue second := by
        have h := halphas (remark87CurrentAlpha p)
        symm
        simpa [p, second, lemma88SecondAlphaIndex,
          remark87CurrentAlpha] using h
      have hraw :
          (b.alphaValue second : WithTop ℚ) ≤
            defectOrder (K := K)
              (T.transformed.adjacentProduct first) := by
        have h := R.currentAlpha_le_previousRawDefect
        rw [← hcurrentAlpha] at ⊢
        simpa [p, first, lemma88FirstAlphaIndex, remark87PreviousAlpha,
          adjacentDefect] using h
      have hproductStrict :=
        b.firstComparisonDefect_lt_product_of_lemma88ExceptionC T hhalf C
      have hproductIdentity : x = T.epsilon * (b.valueUnit 0) ^ 2 := by
        unfold x
        rw [T.firstValue_eq]
        simp only [pow_two]
        ac_rfl
      have hx : defectOrder (K := K) x =
          (b.alphaValue first : WithTop ℚ) := by
        rw [hproductIdentity, defectOrder_mul_square, T.epsilon_defect]
        rfl
      have hproductLower :
          (b.alphaValue first : WithTop ℚ) <
            defectOrder (K := K) product := by
        rw [← hx]
        simpa [x, product, second] using hproductStrict
      have hsum := b.alphaSum_eq_twoE_of_lemma88ExceptionC C hhalf
      have hsumTop :
          (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) =
            (b.alphaValue second : WithTop ℚ) +
              (b.alphaValue first : WithTop ℚ) := by
        exact_mod_cast (by
          rw [add_comm]
          push_cast
          simpa [first, second] using hsum.symm)
      have hdefectSum :
          (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
            defectOrder (K := K)
                (T.transformed.adjacentProduct first) +
              defectOrder (K := K) product := by
        calc
          (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) =
              (b.alphaValue second : WithTop ℚ) +
                (b.alphaValue first : WithTop ℚ) := hsumTop
          _ < defectOrder (K := K)
                  (T.transformed.adjacentProduct first) +
                defectOrder (K := K) product :=
            WithTop.add_lt_add_of_le_of_lt WithTop.coe_ne_top
              hraw hproductLower
      have hone :
          hilbertSymbol K (T.transformed.adjacentProduct first) product = 1 :=
        hilbertSymbol_eq_one_of_defectOrder_add_gt_two_mul_e hdefectSum
      have hne :=
        b.completedTernary_hilbertSymbol_ne_one_of_lemma88ExceptionC
          T hhalf C
      have hfirstZero : first = (0 : Fin (N + 2)) := by
        unfold first lemma88FirstAlphaIndex
        apply Fin.ext
        rfl
      rw [hfirstZero] at hone
      apply hne
      simpa [second, x, product] using hone

/-- A realized first-value transformation excludes exception (b) at the
half-gap boundary.  This is exactly the Hilbert-symbol contradiction in the
first necessity paragraph of the paper. -/
theorem Beli2019FirstValueTransform.not_exceptionB
    [Beli2006AlphaLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    {b : GoodBONG q L (N + 2)}
    (T : b.Beli2019FirstValueTransform)
    (hhalf : b.AttainsHalfGap (0 : Fin (N + 1))) :
    ¬Nonempty b.Beli2019Lemma88ExceptionB := by
  rintro ⟨B⟩
  have hrep :=
    b.firstValue_represents_firstTwo_of_lemma88ExceptionB T hhalf B
  have hhilbert :=
    hilbertSymbol_firstChange_firstAdjacent_eq_one
      b T.transformed hrep
  have hproduct :
      T.transformed.valueUnit 0 * b.valueUnit 0 =
        T.epsilon * (b.valueUnit 0) ^ 2 := by
    rw [T.firstValue_eq]
    simp only [pow_two]
    ac_rfl
  have hfirstDefect :
      defectOrder (K := K)
          (T.transformed.valueUnit 0 * b.valueUnit 0) =
        (b.alphaValue 0 : WithTop ℚ) := by
    rw [hproduct, defectOrder_mul_square, T.epsilon_defect]
  have hadjacentDefect :=
    b.adjacentDefect_zero_eq_complementary_of_lemma88ExceptionB B
  have hsum :
      defectOrder (K := K)
          (T.transformed.valueUnit 0 * b.valueUnit 0) +
          defectOrder (K := K) (b.adjacentProduct 0) =
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
    rw [hfirstDefect]
    change (b.alphaValue 0 : WithTop ℚ) + b.adjacentDefect 0 = _
    rw [hadjacentDefect]
    unfold AttainsHalfGap at hhalf
    rw [hhalf]
    exact_mod_cast b.halfGap_add_lemma88ComplementaryDefect
  exact
    (hilbertSymbol_ne_one_of_residue_two_of_defectOrder_add_eq_twoE
      B.residueTwo
      (T.transformed.valueUnit 0 * b.valueUnit 0)
      (b.adjacentProduct 0) hsum) hhilbert

/-- Necessity direction of Beli (2019), Lemma 8.8(i): every realized
first-value transformation rules out the complete exceptional alternative.
-/
theorem beli2019Lemma88_necessity
    [Beli2006AlphaLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    (b : GoodBONG q L (N + 2)) :
    Nonempty b.Beli2019FirstValueTransform →
      ¬b.Beli2019Lemma88Exceptional := by
  rintro ⟨T⟩ ⟨hhalf, hA | hB | hC⟩
  · exact T.not_exceptionA hA
  · exact T.not_exceptionB hhalf hB
  · apply T.not_exceptionC
      (by simpa [lemma88FirstAlphaIndex] using hhalf)
    exact hC

/-- The forward implication in the exact Lemma 8.8 claim. -/
theorem beli2019Lemma88Claim_forward
    [Beli2006AlphaLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    (b : GoodBONG q L (N + 2)) :
    Nonempty b.Beli2019FirstValueTransform →
      ¬b.Beli2019Lemma88Exceptional :=
  beli2019Lemma88_necessity b

end BONG.GoodBONG

end Bong
