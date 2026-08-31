/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliUniversalDefectCriterion
import Bong.Bong.BeliUniversalEndpoint

/-!
# The central unary condition in Beli's universal-lattice theorem

This file formalizes the rank and trigger reductions used in Lemma 2.13.
For a unary target, condition (iii') has one possible index.  Its abstract
`CentralRepresentationIndex` trigger is normalized here to the literal
inequality displayed in Lemma 2.3.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG.GoodBONG

/-- The exact Case I(b) clause, separated from I(a) and I(c). -/
def UniversalCentralCaseIConditions {tail : Nat}
    (a : GoodBONG q L (tail + 2)) : Prop :=
  (tail = 0 → a.UniversalFirstTwoIsotropic) ∧
    ∀ hthree : 0 < tail,
      1 < a.order ⟨2, by omega⟩ → a.UniversalFirstTwoIsotropic

/-- The exact Case II(b) clause, separated from II(a) and II(c). -/
def UniversalCentralCaseIIConditions {tail : Nat}
    (a : GoodBONG q L (tail + 2)) : Prop :=
  (a.order ⟨1, by omega⟩ = 1 ∨
      ∃ hthree : 0 < tail, 1 < a.order ⟨2, by omega⟩) →
    ∃ hfour : 1 < tail,
      a.alphaValue ⟨2, by omega⟩ ≤
        a.universalAlphaThreeUpperBound hfour

/-- Condition (iii') for every unary target of order zero or one. -/
def UniversalAllUnaryCentralConditions {tail : Nat}
    (a : GoodBONG q L (tail + 2)) : Prop :=
  ∀ b : Kˣ, ordUnit K b = 0 ∨ ordUnit K b = 1 →
    a.CentralRepresentationConditionsPrime (BONG.unaryModelGoodBONG b)

/-- The unary specialization of the revised trigger (iii'). -/
theorem unary_centralDefectTrigger_iff
    {m : Nat} (a : GoodBONG q L (m + 3)) (b : Kˣ) :
    a.centralDefectTrigger (BONG.unaryModelGoodBONG b)
        (unaryCentralRepresentationIndex m) ↔
      ordUnit K b < a.order 2 ∧
        ((((2 * (ramificationIndex K : ℚ) : ℚ) +
          (ordUnit K b : ℚ) - (a.order 2 : ℚ)) : ℚ) : WithTop ℚ) <
          a.truncatedPrefixDefect a (-1) 0 2 +
            a.truncatedPrefixDefect (BONG.unaryModelGoodBONG b) (-1) 3 1 := by
  unfold centralDefectTrigger centralPreviousDefect centralCurrentDefect
  change
    (((BONG.unaryModelGoodBONG b).order 0 < a.order 2 ∧
      ((((2 * (ramificationIndex K : ℚ) : ℚ) +
        ((BONG.unaryModelGoodBONG b).order 0 : ℚ) -
          (a.order 2 : ℚ)) : ℚ) : WithTop ℚ) <
        a.truncatedPrefixDefect (BONG.unaryModelGoodBONG b) (-1) 2 0 +
          a.truncatedPrefixDefect (BONG.unaryModelGoodBONG b) (-1) 3 1) ↔ _)
  rw [BONG.unaryModelGoodBONG_order,
    a.unary_primary_cappedDefect_eq_adjacent b]

/-- The unary central condition is the literal implication in Lemma 2.3. -/
theorem unary_centralRepresentationConditionsPrime_iff_literal
    {m : Nat} (a : GoodBONG q L (m + 3)) (b : Kˣ) :
    a.CentralRepresentationConditionsPrime (BONG.unaryModelGoodBONG b) ↔
      ((ordUnit K b < a.order 2 ∧
          ((((2 * (ramificationIndex K : ℚ) : ℚ) +
            (ordUnit K b : ℚ) - (a.order 2 : ℚ)) : ℚ) : WithTop ℚ) <
            a.truncatedPrefixDefect a (-1) 0 2 +
              a.truncatedPrefixDefect (BONG.unaryModelGoodBONG b)
                (-1) 3 1) →
        DiagonalRepresents
          ((BONG.unaryModelGoodBONG b).prefixValues 1 (by omega))
          (a.prefixValues 2 (by omega))) := by
  rw [a.unary_centralRepresentationConditionsPrime_iff b]
  rw [a.unary_centralDefectTrigger_iff b]

/-- A unary good-BONG prefix is its coefficient. -/
theorem unary_prefixValues_one_eq (b : Kˣ) :
    (BONG.unaryModelGoodBONG b).prefixValues 1 (by omega) =
      (fun _ : Fin 1 ↦ (b : K)) := by
  funext i
  fin_cases i
  exact BONG.unaryModelBONG_value b 0

/-- An isotropic first binary prefix represents every unary coefficient. -/
theorem firstTwo_represents_of_isotropic {tail : Nat}
    (a : GoodBONG q L (tail + 2))
    (hiso : a.UniversalFirstTwoIsotropic) (b : Kˣ) :
    DiagonalRepresents (fun _ : Fin 1 ↦ (b : K))
      (a.prefixValues 2 (by omega)) := by
  have hisoRaw : DiagonalIsotropic
      (fun i ↦ ![(a.valueUnit 0 : K), (a.valueUnit 1 : K)] i) := by
    change DiagonalIsotropic (a.prefixValues 2 (by omega)) at hiso
    convert hiso using 1
    funext i
    fin_cases i <;> rfl
  have hrep := diagonalBinary_represents_of_isotropic
    (a.valueUnit 0) (a.valueUnit 1) b hisoRaw
  convert hrep using 1
  funext i
  fin_cases i <;> rfl

/-- The first order following `R_1=0` is `-2e` when `alpha_1=0`. -/
theorem order_one_eq_neg_two_e_of_alphaValue_zero {tail : Nat}
    (a : GoodBONG q L (tail + 2)) (hzero : a.order 0 = 0)
    (halpha : a.alphaValue (0 : Fin (tail + 1)) = 0) :
    a.order 1 = -(2 * (ramificationIndex K : Int)) := by
  have hgap := (a.alpha_p2 (0 : Fin (tail + 1))).2.mp halpha
  unfold orderGap at hgap
  change a.order 1 - a.order 0 =
    -(2 * (ramificationIndex K : Int)) at hgap
  rw [hzero] at hgap
  simpa using hgap

/-- In rank at least three, the first capped adjacent defect is the minimum
of the ordinary defect of `-a₁a₂` and the next alpha invariant. -/
theorem firstAdjacentDefect_eq_min_raw_alphaTwo {tail : Nat}
    (a : GoodBONG q L (tail + 2)) (htail : 0 < tail) :
    a.truncatedPrefixDefect a (-1) 0 2 =
      min (defectOrder (K := K) (-(a.valueUnit 0 * a.valueUnit 1)))
        (a.alphaValue (1 : Fin (tail + 1)) : WithTop ℚ) := by
  have hzero : a.prefixProduct 0 = 1 :=
    a.toBONG.prefixProduct_zero
  have hone : a.prefixProduct 1 = a.valueUnit 0 := by
    calc
      a.prefixProduct 1 =
          a.prefixProduct 0 * a.valueUnit (0 : Fin (tail + 2)) :=
        a.toBONG.prefixProduct_succ 0 (by omega)
      _ = a.valueUnit 0 := by rw [hzero, one_mul]
  have htwo : a.prefixProduct 2 = a.valueUnit 0 * a.valueUnit 1 := by
    calc
      a.prefixProduct 2 =
          a.prefixProduct 1 * a.valueUnit (1 : Fin (tail + 2)) :=
        a.toBONG.prefixProduct_succ 1 (by omega)
      _ = a.valueUnit 0 * a.valueUnit 1 := by rw [hone]
  have hcap : a.prefixAlphaCap 2 =
      (a.alphaValue (1 : Fin (tail + 1)) : WithTop ℚ) := by
    unfold prefixAlphaCap
    rw [dif_pos (by omega)]
    congr 2
    apply Fin.ext
    change 1 = 1 % (tail + 1)
    exact (Nat.mod_eq_of_lt (by omega)).symm
  unfold truncatedPrefixDefect
  rw [a.prefixAlphaCap_zero, hcap, hzero, htwo]
  simp

/-- In the nonpositive `R₂`, large `R₃` branch of Case II', the next
alpha invariant lies strictly above the sharp first defect `1-R₂`. -/
theorem one_sub_order_one_lt_alphaTwo_of_caseIIPrime
    {tail : Nat} (a : GoodBONG q L (tail + 2))
    (hzero : a.order 0 = 0) (hcase : a.UniversalCaseIIPrime)
    (hsecond : a.order 1 ≤ 0) (hthird : 1 < a.order 2) :
    (((1 - a.order 1 : Int) : ℚ)) <
      a.alphaValue (1 : Fin (tail + 1)) := by
  letI : Beli2006AlphaLaws.{u, v} K := beliUniversalAlphaLaws
  have htail : 0 < tail := hcase.1
  have hgapZero : a.orderGap (0 : Fin (tail + 1)) = a.order 1 := by
    unfold orderGap
    simpa [hzero]
  have hsecondLower :
      2 - 2 * (ramificationIndex K : Int) ≤ a.order 1 := by
    have hparity :=
      (a.alphaValue_eq_one_consequences (0 : Fin (tail + 1))
        hcase.2.1).2.1
    rw [hgapZero] at hparity
    rcases hparity with hone | heven
    · have hePos := ramificationIndex_pos (K := K)
      omega
    · exact heven.2.1
  let i : Fin (tail + 1) := (1 : Fin (tail + 1))
  change ((1 - a.order 1 : Int) : ℚ) < a.alphaValue i
  have hcast : i.castSucc = (1 : Fin (tail + 2)) := by
    apply Fin.ext
    dsimp [i]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hsucc : i.succ = (2 : Fin (tail + 2)) := by
    apply Fin.ext
    dsimp [i]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hgap : a.orderGap i = a.order 2 - a.order 1 := by
    unfold orderGap
    rw [hcast, hsucc]
  by_cases hle : a.orderGap i ≤
      2 * (ramificationIndex K : Int)
  · have hlower := (a.alpha_p3 i hle).1
    rw [hgap] at hlower
    have hstrictInt : 1 - a.order 1 < a.order 2 - a.order 1 := by
      omega
    have hstrictQ : ((1 - a.order 1 : Int) : ℚ) <
        ((a.order 2 - a.order 1 : Int) : ℚ) := by
      exact_mod_cast hstrictInt
    exact hstrictQ.trans_le hlower
  · have hgapLarge :
        2 * (ramificationIndex K : Int) < a.orderGap i := by
      omega
    have halphaLarge : 2 * (ramificationIndex K : ℚ) <
        a.alphaValue i := (a.alpha_p5 i).2.2.mpr hgapLarge
    have hstrictInt : 1 - a.order 1 <
        2 * (ramificationIndex K : Int) := by
      omega
    have hstrictQ : ((1 - a.order 1 : Int) : ℚ) <
        2 * (ramificationIndex K : ℚ) := by
      exact_mod_cast hstrictInt
    exact hstrictQ.trans halphaLarge

/-- In the high branch of Case II', the capped equality is already the
ordinary quadratic-defect equality `d(-a₁a₂)=1-R₂`. -/
theorem firstTwo_rawDefect_eq_one_sub_order_one_of_caseIIPrime
    {tail : Nat} (a : GoodBONG q L (tail + 2))
    (hzero : a.order 0 = 0) (hcase : a.UniversalCaseIIPrime)
    (hhigh : a.order 1 = 1 ∨ 1 < a.order 2) :
    defectOrder (K := K) (-(a.valueUnit 0 * a.valueUnit 1)) =
      ((((1 : ℚ) - (a.order 1 : ℚ)) : ℚ) : WithTop ℚ) := by
  letI : QuadraticDefectLaws K := quadraticDefectLawsOfHensel K
  letI : Beli2006AlphaLaws.{u, v} K := beliUniversalAlphaLaws
  have htail : 0 < tail := hcase.1
  have hgapZero : a.orderGap (0 : Fin (tail + 1)) = a.order 1 := by
    unfold orderGap
    simpa [hzero]
  have hsharp : a.truncatedPrefixDefect a (-1) 0 2 =
      ((((1 : ℚ) - (a.order 1 : ℚ)) : ℚ) : WithTop ℚ) := by
    simpa only [hgapZero] using hcase.2.2
  have hoddDefect (hone : a.order 1 = 1) :
      defectOrder (K := K) (-(a.valueUnit 0 * a.valueUnit 1)) = 0 := by
    have horderZero : ordUnit K (a.valueUnit 0) = a.order 0 :=
      (a.toBONG.order_eq_ordUnit (0 : Fin (tail + 2))).symm
    have horderOne : ordUnit K (a.valueUnit 1) = a.order 1 :=
      (a.toBONG.order_eq_ordUnit (1 : Fin (tail + 2))).symm
    have horder : ordUnit K (-(a.valueUnit 0 * a.valueUnit 1)) = 1 := by
      rw [ordUnit_neg, ordUnit_mul, horderZero, horderOne, hzero, hone]
      norm_num
    have hodd : Odd (ordUnit K (-(a.valueUnit 0 * a.valueUnit 1))) := by
      rw [horder]
      exact odd_one
    unfold defectOrder
    rw [quadraticDefect_eq_zero_of_odd_ordUnit _ hodd]
    rfl
  rcases hhigh with hone | hthird
  · rw [hoddDefect hone, hone]
    norm_num
  · by_cases hone : a.order 1 = 1
    · rw [hoddDefect hone, hone]
      norm_num
    · have hsecondUpper : a.order 1 ≤ 1 := by
        have hbounds :=
          (a.alphaValue_eq_one_consequences (0 : Fin (tail + 1))
            hcase.2.1).1.2
        rw [hgapZero] at hbounds
        exact hbounds
      have hsecond : a.order 1 ≤ 0 := by omega
      have halphaStrict :=
        a.one_sub_order_one_lt_alphaTwo_of_caseIIPrime
          hzero hcase hsecond hthird
      have halphaStrictTop :
          ((((1 : ℚ) - (a.order 1 : ℚ)) : ℚ) : WithTop ℚ) <
            (a.alphaValue (1 : Fin (tail + 1)) : WithTop ℚ) := by
        apply WithTop.coe_lt_coe.mpr
        simpa only [Int.cast_sub, Int.cast_one] using halphaStrict
      have hminimum :
          min (defectOrder (K := K)
              (-(a.valueUnit 0 * a.valueUnit 1)))
              (a.alphaValue (1 : Fin (tail + 1)) : WithTop ℚ) =
            ((((1 : ℚ) - (a.order 1 : ℚ)) : ℚ) : WithTop ℚ) := by
        rw [← a.firstAdjacentDefect_eq_min_raw_alphaTwo htail]
        exact hsharp
      apply le_antisymm
      · by_contra hnot
        have hstrictRaw :
            ((((1 : ℚ) - (a.order 1 : ℚ)) : ℚ) : WithTop ℚ) <
              defectOrder (K := K)
                (-(a.valueUnit 0 * a.valueUnit 1)) :=
          lt_of_not_ge hnot
        have hstrictMin := lt_min hstrictRaw halphaStrictTop
        rw [hminimum] at hstrictMin
        exact (lt_irrefl _ hstrictMin).elim
      · rw [← hminimum]
        exact min_le_left _ _

/-- The order of the signed ternary/unary prefix product occurring in
condition (iii'). -/
theorem unary_mixedPrefix_three_one_order {tail : Nat}
    (a : GoodBONG q L (tail + 2)) (htail : 0 < tail) (b : Kˣ) :
    ordUnit K ((-1 : Kˣ) * a.prefixProduct 3 *
        (BONG.unaryModelGoodBONG b).prefixProduct 1) =
      a.order 0 + a.order 1 + a.order 2 + ordUnit K b := by
  have hnegOne : ordUnit K (-1 : Kˣ) = 0 := by
    have hone : ordUnit K (1 : Kˣ) = 0 := by
      have h := ordUnit_mul K (1 : Kˣ) 1
      simp only [mul_one] at h
      omega
    have h := ordUnit_mul K (-1 : Kˣ) (-1)
    have hmul : (-1 : Kˣ) * (-1) = 1 := by norm_num
    rw [hmul, hone] at h
    omega
  have hsourceZero : a.order ⟨0, by omega⟩ = a.order 0 := by
    congr 1
  have hsourceOne : a.order ⟨1, by omega⟩ = a.order 1 := by
    congr 1
  have hsourceTwo : a.order ⟨2, by omega⟩ = a.order 2 := by
    congr 1
    apply Fin.ext
    change 2 = 2 % (tail + 2)
    exact (Nat.mod_eq_of_lt (by omega)).symm
  have hunary : (BONG.unaryModelGoodBONG b).order ⟨0, by omega⟩ =
      ordUnit K b := by
    calc
      (BONG.unaryModelGoodBONG b).order ⟨0, by omega⟩ =
          (BONG.unaryModelGoodBONG b).order (0 : Fin 1) := by
        congr 1
      _ = ordUnit K b := BONG.unaryModelGoodBONG_order b
  rw [ordUnit_mul, ordUnit_mul, hnegOne, zero_add,
    a.ordUnit_prefixProduct_eq_orderSequence_prefixSum 3 (by omega),
    (BONG.unaryModelGoodBONG b).ordUnit_prefixProduct_eq_orderSequence_prefixSum
      1 (by omega),
    a.orderSequence.prefixSum_succ 2,
    a.orderSequence.prefixSum_succ 1,
    a.orderSequence.prefixSum_one,
    (BONG.unaryModelGoodBONG b).orderSequence.prefixSum_one,
    a.orderSequence_entryOrZero_eq_order ⟨0, by omega⟩,
    a.orderSequence_entryOrZero_eq_order ⟨1, by omega⟩,
    a.orderSequence_entryOrZero_eq_order ⟨2, by omega⟩,
    (BONG.unaryModelGoodBONG b).orderSequence_entryOrZero_eq_order
      ⟨0, by omega⟩,
    hsourceZero, hsourceOne, hsourceTwo, hunary]

/-- The low Case II' range `R₂ ≤ 0`, `R₃ ≤ 1` never activates the
strict trigger in condition (iii'), so the condition holds unconditionally. -/
theorem universalAllUnaryCentralConditions_of_caseIIPrime_low
    {tail : Nat} (a : GoodBONG q L (tail + 2))
    (hzero : a.order 0 = 0) (hcase : a.UniversalCaseIIPrime)
    (hsecond : a.order 1 ≤ 0) (hthird : a.order 2 ≤ 1) :
    a.UniversalAllUnaryCentralConditions := by
  letI : Beli2006AlphaLaws.{u, v} K := beliUniversalAlphaLaws
  have htail : 0 < tail := hcase.1
  have htailNe : tail ≠ 0 := Nat.ne_of_gt htail
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero htailNe
  have hthirdNonnegative : 0 ≤ a.order 2 :=
    a.order_two_nonnegative_of_order_zero_eq_zero hzero
  have hgapZero : a.orderGap (0 : Fin (m + 2)) = a.order 1 := by
    unfold orderGap
    simpa [hzero]
  have hsecondEven : Even (a.order 1) := by
    have hparity :=
      (a.alphaValue_eq_one_consequences (0 : Fin (m + 2))
        hcase.2.1).2.1
    rw [hgapZero] at hparity
    rcases hparity with hone | heven
    · omega
    · exact heven.1
  have hsecondLower :
      2 - 2 * (ramificationIndex K : Int) ≤ a.order 1 := by
    have hparity :=
      (a.alphaValue_eq_one_consequences (0 : Fin (m + 2))
        hcase.2.1).2.1
    rw [hgapZero] at hparity
    rcases hparity with hone | heven
    · have hePos := ramificationIndex_pos (K := K)
      omega
    · exact heven.2.1
  have hsharp : a.truncatedPrefixDefect a (-1) 0 2 =
      ((((1 : ℚ) - (a.order 1 : ℚ)) : ℚ) : WithTop ℚ) := by
    simpa only [hgapZero] using hcase.2.2
  intro b hb
  rw [a.unary_centralRepresentationConditionsPrime_iff_literal b]
  intro htrigger
  have hthirdCases : a.order 2 = 0 ∨ a.order 2 = 1 := by omega
  rcases hthirdCases with hthirdZero | hthirdOne
  · have hleft := htrigger.1
    rcases hb with hbZero | hbOne
    · rw [hbZero, hthirdZero] at hleft
      omega
    · rw [hbOne, hthirdZero] at hleft
      omega
  · rcases hb with hbZero | hbOne
    · have hoddOrder : Odd (ordUnit K
          ((-1 : Kˣ) * a.prefixProduct 3 *
            (BONG.unaryModelGoodBONG b).prefixProduct 1)) := by
        rw [a.unary_mixedPrefix_three_one_order (by omega) b,
          hzero, hthirdOne, hbZero]
        rcases hsecondEven with ⟨z, hz⟩
        refine ⟨z, ?_⟩
        omega
      have hcurrent :
          a.truncatedPrefixDefect (BONG.unaryModelGoodBONG b) (-1) 3 1 = 0 :=
        a.truncatedPrefixDefect_eq_zero_of_odd_order_mixed
          (alphaV := beliUniversalAlphaLaws)
          (alphaW := beliUniversalAlphaLaws)
          (BONG.unaryModelGoodBONG b) (-1) 3 1 hoddOrder
      have hboundInt : 1 - a.order 1 ≤
          2 * (ramificationIndex K : Int) - 1 := by
        omega
      have hboundQ : (1 : ℚ) - (a.order 1 : ℚ) ≤
          2 * (ramificationIndex K : ℚ) - 1 := by
        exact_mod_cast hboundInt
      have hstrict := htrigger.2
      rw [hbZero, hthirdOne, hsharp, hcurrent] at hstrict
      norm_num at hstrict
      exact (not_lt_of_ge (WithTop.coe_le_coe.mpr hboundQ) hstrict).elim
    · have hleft := htrigger.1
      rw [hbOne, hthirdOne] at hleft
      omega

/-- The ternary prefix product has order `R₁+R₂+R₃`. -/
theorem prefixProduct_three_order {tail : Nat}
    (a : GoodBONG q L (tail + 2)) (htail : 0 < tail) :
    ordUnit K (a.prefixProduct 3) = a.order 0 + a.order 1 + a.order 2 := by
  have hsourceZero : a.order ⟨0, by omega⟩ = a.order 0 := by
    congr 1
  have hsourceOne : a.order ⟨1, by omega⟩ = a.order 1 := by
    congr 1
  have hsourceTwo : a.order ⟨2, by omega⟩ = a.order 2 := by
    congr 1
    apply Fin.ext
    change 2 = 2 % (tail + 2)
    exact (Nat.mod_eq_of_lt (by omega)).symm
  rw [a.ordUnit_prefixProduct_eq_orderSequence_prefixSum 3 (by omega),
    a.orderSequence.prefixSum_succ 2,
    a.orderSequence.prefixSum_succ 1,
    a.orderSequence.prefixSum_one,
    a.orderSequence_entryOrZero_eq_order ⟨0, by omega⟩,
    a.orderSequence_entryOrZero_eq_order ⟨1, by omega⟩,
    a.orderSequence_entryOrZero_eq_order ⟨2, by omega⟩,
    hsourceZero, hsourceOne, hsourceTwo]

/-- A parity-compatible order `S` is realized in the square class
`-a₁a₂a₃ F^{×2}` used in the necessity parts of Lemmas 2.13 and 2.14. -/
theorem exists_order_in_negative_ternary_prefix_squareClass
    {tail : Nat} (a : GoodBONG q L (tail + 2))
    (htail : 0 < tail) (hzero : a.order 0 = 0) (S : Int)
    (hparity : Even (S - (a.order 1 + a.order 2))) :
    ∃ b : Kˣ, ordUnit K b = S ∧
      IsSquare ((-1 : Kˣ) * a.prefixProduct 3 * b) := by
  rcases hparity with ⟨k, hk⟩
  let t : Kˣ := uniformizerPowerUnit K k
  let b : Kˣ := -(t ^ 2 * a.prefixProduct 3)
  have ht : ordUnit K t = k :=
    ordUnit_uniformizerPowerUnit (K := K) k
  have hprefix := a.prefixProduct_three_order htail
  have hb : ordUnit K b = S := by
    dsimp only [b]
    rw [ordUnit_neg, ordUnit_mul, ordUnit_pow, ht, hprefix, hzero]
    omega
  refine ⟨b, hb, ?_⟩
  refine ⟨a.prefixProduct 3 * t, ?_⟩
  dsimp only [b]
  simp only [neg_mul, mul_neg, neg_neg, one_mul, pow_two]
  ac_rfl

/-- The complete prefix product of the unary model is its coefficient. -/
theorem unary_prefixProduct_one_eq (b : Kˣ) :
    (BONG.unaryModelGoodBONG b).prefixProduct 1 = b := by
  change (BONG.unaryModelBONG b).prefixProduct 1 = b
  rw [(BONG.unaryModelBONG b).prefixProduct_succ 0 (by omega),
    (BONG.unaryModelBONG b).prefixProduct_zero, one_mul,
    BONG.unaryModelBONG_valueUnit]

/-- At source rank three, both caps in the current unary defect are
endpoints, so the capped and ordinary defects coincide. -/
theorem unary_currentDefect_rankThree_eq_raw
    (a : GoodBONG q L 3) (b : Kˣ) :
    a.truncatedPrefixDefect (BONG.unaryModelGoodBONG b) (-1) 3 1 =
      defectOrder (K := K) ((-1 : Kˣ) * a.prefixProduct 3 * b) := by
  unfold truncatedPrefixDefect
  rw [a.prefixAlphaCap_last,
    (BONG.unaryModelGoodBONG b).prefixAlphaCap_last,
    unary_prefixProduct_one_eq]
  simp

/-- At source rank at least four, the only finite cap in the current unary
defect is `alpha₃`. -/
theorem unary_currentDefect_eq_min_raw_alphaThree {tail : Nat}
    (a : GoodBONG q L (tail + 2)) (hfour : 1 < tail) (b : Kˣ) :
    a.truncatedPrefixDefect (BONG.unaryModelGoodBONG b) (-1) 3 1 =
      min (defectOrder (K := K)
          ((-1 : Kˣ) * a.prefixProduct 3 * b))
        (a.alphaValue (2 : Fin (tail + 1)) : WithTop ℚ) := by
  have hsourceCap : a.prefixAlphaCap 3 =
      (a.alphaValue (2 : Fin (tail + 1)) : WithTop ℚ) := by
    unfold prefixAlphaCap
    rw [dif_pos (by omega)]
    congr 2
    apply Fin.ext
    change 2 = 2 % (tail + 1)
    exact (Nat.mod_eq_of_lt (by omega)).symm
  unfold truncatedPrefixDefect
  rw [hsourceCap,
    (BONG.unaryModelGoodBONG b).prefixAlphaCap_last,
    unary_prefixProduct_one_eq]
  simp

/-- Multiplying a square class by `epsilon` leaves precisely the defect of
`epsilon`. -/
theorem defectOrder_mul_eq_of_isSquare_left
    (x epsilon : Kˣ) (hx : IsSquare x) :
    defectOrder (K := K) (x * epsilon) = defectOrder (K := K) epsilon := by
  rcases hx with ⟨s, hs⟩
  rw [hs]
  have hreorder : s * s * epsilon = epsilon * s ^ 2 := by
    simp only [pow_two]
    ac_rfl
  rw [hreorder, defectOrder_mul_square]

/-- A representation by the first binary prefix gives the Hilbert-symbol
equation used in the necessity argument of Lemma 2.13. -/
theorem firstTwo_hilbert_eq_one_of_represents {tail : Nat}
    (a : GoodBONG q L (tail + 2)) (b : Kˣ)
    (hrep : DiagonalRepresents (fun _ : Fin 1 ↦ (b : K))
      (a.prefixValues 2 (by omega))) :
    hilbertSymbol K (b * (a.valueUnit 0)⁻¹)
        (-(a.valueUnit 0 * a.valueUnit 1)) = 1 := by
  apply (DiagonalRepresents.unary_binary_iff_hilbertSymbol_one
    (a.valueUnit 0) (a.valueUnit 1) b).mp
  convert hrep using 1
  funext i
  fin_cases i <;> rfl

/-- A negative Hilbert partner prevents the first binary prefix from
representing both `b` and `b*epsilon`. -/
theorem not_both_firstTwo_represents_of_hilbert_neg {tail : Nat}
    (a : GoodBONG q L (tail + 2)) (b epsilon : Kˣ)
    (hnegative : hilbertSymbol K epsilon
      (-(a.valueUnit 0 * a.valueUnit 1)) = -1) :
    ¬(DiagonalRepresents (fun _ : Fin 1 ↦ (b : K))
          (a.prefixValues 2 (by omega)) ∧
      DiagonalRepresents (fun _ : Fin 1 ↦ ((b * epsilon : Kˣ) : K))
          (a.prefixValues 2 (by omega))) := by
  rintro ⟨hrep, hrepTwist⟩
  have hone := a.firstTwo_hilbert_eq_one_of_represents b hrep
  have htwist :=
    a.firstTwo_hilbert_eq_one_of_represents (b * epsilon) hrepTwist
  have hfactor : (b * epsilon) * (a.valueUnit 0)⁻¹ =
      (b * (a.valueUnit 0)⁻¹) * epsilon := by
    ac_rfl
  rw [hfactor, hilbertSymbol_mul_left, hone, hnegative] at htwist
  norm_num at htwist

/-- The parity-compatible order `S ∈ {0,1}` used by Beli.  Besides its
existence, this packages the strict inequality `S<R₃` in the high branch
and the exact floor identity in Case II(b). -/
theorem exists_universalParityTarget_of_caseIIPrime_high
    {tail : Nat} (a : GoodBONG q L (tail + 2))
    (hzero : a.order 0 = 0) (hcase : a.UniversalCaseIIPrime)
    (hhigh : a.order 1 = 1 ∨ 1 < a.order 2) :
    ∃ S : Int,
      (S = 0 ∨ S = 1) ∧
      Even (S - (a.order 1 + a.order 2)) ∧
      S < a.order 2 ∧
      2 * (ramificationIndex K : Int) - 1 + S + a.order 1 - a.order 2 =
      2 * ((ramificationIndex K : Int) -
          (a.order 2 - a.order 1) / 2) - 1 := by
  have htail : 0 < tail := hcase.1
  have htailNe : tail ≠ 0 := Nat.ne_of_gt htail
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero htailNe
  have hthirdNonnegative : 0 ≤ a.order 2 :=
    a.order_two_nonnegative_of_order_zero_eq_zero hzero
  have hgapZero : a.orderGap (0 : Fin (m + 2)) = a.order 1 := by
    unfold orderGap
    simpa [hzero]
  have hsecondUpper : a.order 1 ≤ 1 := by
    have hbounds :=
      (a.alphaValue_eq_one_consequences (0 : Fin (m + 2))
        hcase.2.1).1.2
    rw [hgapZero] at hbounds
    exact hbounds
  have hgapNonnegative : 0 ≤ a.order 2 - a.order 1 := by
    rcases hhigh with hone | hthird
    · have hthirdOne :=
        a.one_le_order_two_of_order_zero_eq_zero_order_one_eq_one
          hzero hone
      omega
    · omega
  rcases Int.even_or_odd (a.order 2 - a.order 1) with heven | hodd
  · rcases heven with ⟨k, hk⟩
    refine ⟨0, Or.inl rfl, ?_, ?_, ?_⟩
    · refine ⟨-(k + a.order 1), ?_⟩
      omega
    · rcases hhigh with hone | hthird
      · have hthirdOne :=
          a.one_le_order_two_of_order_zero_eq_zero_order_one_eq_one
            hzero hone
        omega
      · omega
    · have hdiv : (a.order 2 - a.order 1) / 2 = k := by omega
      rw [hdiv]
      omega
  · rcases hodd with ⟨k, hk⟩
    refine ⟨1, Or.inr rfl, ?_, ?_, ?_⟩
    · refine ⟨-(k + a.order 1), ?_⟩
      omega
    · rcases hhigh with hone | hthird
      · have hthirdOne :=
          a.one_le_order_two_of_order_zero_eq_zero_order_one_eq_one
            hzero hone
        omega
      · omega
    · have hdiv : (a.order 2 - a.order 1) / 2 = k := by omega
      rw [hdiv]
      omega

/-- Rational form of the parity-floor identity used to rewrite the upper
bound in Case II(b). -/
theorem universalAlphaThreeUpperBound_eq_parity_expression
    {tail : Nat} (a : GoodBONG q L (tail + 2)) (hfour : 1 < tail)
    (S : Int)
    (hidentity :
      2 * (ramificationIndex K : Int) - 1 + S + a.order 1 - a.order 2 =
        2 * ((ramificationIndex K : Int) -
          (a.order 2 - a.order 1) / 2) - 1) :
    a.universalAlphaThreeUpperBound hfour =
      ((2 * (ramificationIndex K : Int) - 1 + S +
        a.order 1 - a.order 2 : Int) : ℚ) := by
  unfold universalAlphaThreeUpperBound
  have hone : a.order ⟨1, by omega⟩ = a.order 1 := by
    congr 1
  have htwo : a.order ⟨2, by omega⟩ = a.order 2 := by
    congr 1
    apply Fin.ext
    change 2 = 2 % (tail + 2)
    exact (Nat.mod_eq_of_lt (by omega)).symm
  rw [hone, htwo]
  exact_mod_cast hidentity.symm

/-- The Hilbert-pair obstruction in the necessity half of Lemma 2.13.
If the Case II(b) upper bound fails at every available rank-four boundary
(vacuously at rank three), the unary central condition cannot hold for all
targets. -/
theorem not_universalAllUnaryCentralConditions_of_caseIIPrime_high_bad
    {m : Nat} (a : GoodBONG q L (m + 3))
    (hzero : a.order 0 = 0) (hcase : a.UniversalCaseIIPrime)
    (hhigh : a.order 1 = 1 ∨ 1 < a.order 2)
    (hbad : ∀ hfour : 1 < m + 1,
      a.universalAlphaThreeUpperBound hfour <
        a.alphaValue (2 : Fin (m + 2))) :
    ¬a.UniversalAllUnaryCentralConditions := by
  letI : QuadraticDefectLaws K := quadraticDefectLawsOfHensel K
  letI : HilbertSymbolLaws K := Dyadic.hilbertSymbolLawsProved
  letI : Beli2006AlphaLaws.{u, v} K := beliUniversalAlphaLaws
  intro hall
  obtain ⟨S, hSAllowed, hSParity, hSlt, hparityIdentity⟩ :=
    a.exists_universalParityTarget_of_caseIIPrime_high
      hzero hcase hhigh
  have hSltQ : (S : ℚ) < (a.order 2 : ℚ) := by
    exact_mod_cast hSlt
  obtain ⟨b, hbOrder, hbSquare⟩ :=
    a.exists_order_in_negative_ternary_prefix_squareClass
      hcase.1 hzero S hSParity
  have hgapZero : a.orderGap (0 : Fin (m + 2)) = a.order 1 := by
    unfold orderGap
    simpa [hzero]
  have hsecondUpper : a.order 1 ≤ 1 := by
    have hbounds :=
      (a.alphaValue_eq_one_consequences (0 : Fin (m + 2))
        hcase.2.1).1.2
    rw [hgapZero] at hbounds
    exact hbounds
  have hsecondLower :
      2 - 2 * (ramificationIndex K : Int) ≤ a.order 1 := by
    have hparity :=
      (a.alphaValue_eq_one_consequences (0 : Fin (m + 2))
        hcase.2.1).2.1
    rw [hgapZero] at hparity
    rcases hparity with hone | heven
    · have hePos := ramificationIndex_pos (K := K)
      omega
    · exact heven.2.1
  let d : ℚ := 1 - (a.order 1 : ℚ)
  have hzDefect :
      defectOrder (K := K) (-(a.valueUnit 0 * a.valueUnit 1)) =
        (d : WithTop ℚ) := by
    simpa only [d] using
      a.firstTwo_rawDefect_eq_one_sub_order_one_of_caseIIPrime
        hzero hcase hhigh
  have hdNonnegative : 0 ≤ d := by
    have hsecondUpperQ : (a.order 1 : ℚ) ≤ 1 := by
      exact_mod_cast hsecondUpper
    dsimp only [d]
    linarith
  have hdLt : d < 2 * (ramificationIndex K : ℚ) := by
    have hsecondLowerQ :
        2 - 2 * (ramificationIndex K : ℚ) ≤ (a.order 1 : ℚ) := by
      exact_mod_cast hsecondLower
    dsimp only [d]
    linarith
  rcases BONG.exists_complementaryDefect_hilbert_neg_of_nonnegative
      (K := K) (-(a.valueUnit 0 * a.valueUnit 1)) d
      hzDefect hdNonnegative hdLt with
    ⟨epsilon, hepsilonUnit, hepsilonDefect, hepsilonHilbert⟩
  have hepsilonOrder : ordUnit K epsilon = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero (K := K) epsilon).mp hepsilonUnit
  have htwistOrder : ordUnit K (b * epsilon) = S := by
    rw [ordUnit_mul, hbOrder, hepsilonOrder, add_zero]
  have htwistRawFactor :
      (-1 : Kˣ) * a.prefixProduct 3 * (b * epsilon) =
        (((-1 : Kˣ) * a.prefixProduct 3 * b) * epsilon) := by
    ac_rfl
  have htwistRawDefect :
      defectOrder (K := K)
          ((-1 : Kˣ) * a.prefixProduct 3 * (b * epsilon)) =
        ((2 * (ramificationIndex K : ℚ) - d : ℚ) : WithTop ℚ) := by
    rw [htwistRawFactor,
      defectOrder_mul_eq_of_isSquare_left _ _ hbSquare,
      hepsilonDefect]
  have hfirstDefect : a.truncatedPrefixDefect a (-1) 0 2 =
      (d : WithTop ℚ) := by
    simpa only [hgapZero, d] using hcase.2.2
  have hbAllowed : ordUnit K b = 0 ∨ ordUnit K b = 1 := by
    rcases hSAllowed with hSZero | hSOne
    · exact Or.inl (hbOrder.trans hSZero)
    · exact Or.inr (hbOrder.trans hSOne)
  have htwistAllowed :
      ordUnit K (b * epsilon) = 0 ∨ ordUnit K (b * epsilon) = 1 := by
    rcases hSAllowed with hSZero | hSOne
    · exact Or.inl (htwistOrder.trans hSZero)
    · exact Or.inr (htwistOrder.trans hSOne)
  have finish
      (hstrict :
        ((((2 * (ramificationIndex K : ℚ) : ℚ) + (S : ℚ) -
          (a.order 2 : ℚ) : ℚ)) : WithTop ℚ) <
          a.truncatedPrefixDefect a (-1) 0 2 +
            a.truncatedPrefixDefect (BONG.unaryModelGoodBONG b) (-1) 3 1)
      (hstrictTwist :
        ((((2 * (ramificationIndex K : ℚ) : ℚ) + (S : ℚ) -
          (a.order 2 : ℚ) : ℚ)) : WithTop ℚ) <
          a.truncatedPrefixDefect a (-1) 0 2 +
            a.truncatedPrefixDefect
              (BONG.unaryModelGoodBONG (b * epsilon)) (-1) 3 1) : False := by
    have hcentral := hall b hbAllowed
    rw [a.unary_centralRepresentationConditionsPrime_iff_literal b]
      at hcentral
    have hrep := hcentral ⟨by simpa only [hbOrder] using hSlt, by
      simpa only [hbOrder] using hstrict⟩
    rw [unary_prefixValues_one_eq b] at hrep
    have hcentralTwist := hall (b * epsilon) htwistAllowed
    rw [a.unary_centralRepresentationConditionsPrime_iff_literal
      (b * epsilon)] at hcentralTwist
    have hrepTwist := hcentralTwist ⟨by
      simpa only [htwistOrder] using hSlt, by
      simpa only [htwistOrder] using hstrictTwist⟩
    rw [unary_prefixValues_one_eq (b * epsilon)] at hrepTwist
    exact a.not_both_firstTwo_represents_of_hilbert_neg
      b epsilon hepsilonHilbert ⟨hrep, hrepTwist⟩
  cases m with
  | zero =>
      have hcurrent :
          a.truncatedPrefixDefect (BONG.unaryModelGoodBONG b) (-1) 3 1 =
            ⊤ := by
        rw [a.unary_currentDefect_rankThree_eq_raw b,
          defectOrder_eq_top_of_isSquare hbSquare]
      have hcurrentTwist :
          a.truncatedPrefixDefect
              (BONG.unaryModelGoodBONG (b * epsilon)) (-1) 3 1 =
            ((2 * (ramificationIndex K : ℚ) - d : ℚ) : WithTop ℚ) := by
        rw [a.unary_currentDefect_rankThree_eq_raw (b * epsilon),
          htwistRawDefect]
      apply finish
      · rw [hcurrent]
        simp only [add_top]
        exact WithTop.coe_lt_top _
      · rw [hfirstDefect, hcurrentTwist]
        rw [← WithTop.coe_add]
        apply WithTop.coe_lt_coe.mpr
        dsimp only [d]
        push_cast
        linarith
  | succ k =>
      have hfour : 1 < k.succ + 1 := by omega
      have hupper :=
        a.universalAlphaThreeUpperBound_eq_parity_expression
          hfour S hparityIdentity
      have hbadAlpha := hbad hfour
      rw [hupper] at hbadAlpha
      have hsumAlpha :
          2 * (ramificationIndex K : ℚ) + (S : ℚ) -
              (a.order 2 : ℚ) <
            d + a.alphaValue (2 : Fin (k.succ + 2)) := by
        dsimp only [d]
        push_cast at hbadAlpha
        linarith
      have hcurrent :
          a.truncatedPrefixDefect (BONG.unaryModelGoodBONG b) (-1) 3 1 =
            (a.alphaValue (2 : Fin (k.succ + 2)) : WithTop ℚ) := by
        rw [a.unary_currentDefect_eq_min_raw_alphaThree hfour b,
          defectOrder_eq_top_of_isSquare hbSquare]
        simp
      have hcurrentTwist :
          a.truncatedPrefixDefect
              (BONG.unaryModelGoodBONG (b * epsilon)) (-1) 3 1 =
            min ((2 * (ramificationIndex K : ℚ) - d : ℚ) : WithTop ℚ)
              (a.alphaValue (2 : Fin (k.succ + 2)) : WithTop ℚ) := by
        rw [a.unary_currentDefect_eq_min_raw_alphaThree hfour
          (b * epsilon), htwistRawDefect]
      apply finish
      · rw [hfirstDefect, hcurrent]
        simpa only [WithTop.coe_add] using
          (WithTop.coe_lt_coe.mpr hsumAlpha)
      · rw [hfirstDefect, hcurrentTwist]
        rcases le_total
            (((2 * (ramificationIndex K : ℚ) - d : ℚ) : WithTop ℚ))
            (a.alphaValue (2 : Fin (k.succ + 2)) : WithTop ℚ) with
          hcomplement | halpha
        · rw [min_eq_left hcomplement]
          rw [← WithTop.coe_add]
          apply WithTop.coe_lt_coe.mpr
          dsimp only [d]
          push_cast
          linarith
        · rw [min_eq_right halpha]
          simpa only [WithTop.coe_add] using
            (WithTop.coe_lt_coe.mpr hsumAlpha)

/-- Sufficiency of Case II(b): its alpha bound makes every same-parity
trigger weak, while an opposite-parity trigger would force the displayed
upper bound below zero. -/
theorem universalAllUnaryCentralConditions_of_caseIIPrime_high_bound
    {tail : Nat} (a : GoodBONG q L (tail + 2))
    (hzero : a.order 0 = 0) (hcase : a.UniversalCaseIIPrime)
    (hhigh : a.order 1 = 1 ∨ 1 < a.order 2)
    (hfour : 1 < tail)
    (halpha : a.alphaValue (2 : Fin (tail + 1)) ≤
      a.universalAlphaThreeUpperBound hfour) :
    a.UniversalAllUnaryCentralConditions := by
  letI : Beli2006AlphaLaws.{u, v} K := beliUniversalAlphaLaws
  have htailNe : tail ≠ 0 := by omega
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero htailNe
  obtain ⟨T, hTAllowed, hTParity, _hTlt, hparityIdentity⟩ :=
    a.exists_universalParityTarget_of_caseIIPrime_high
      hzero hcase hhigh
  have hupper :=
    a.universalAlphaThreeUpperBound_eq_parity_expression
      hfour T hparityIdentity
  have hgapZero : a.orderGap (0 : Fin (m + 2)) = a.order 1 := by
    unfold orderGap
    simpa [hzero]
  let d : ℚ := 1 - (a.order 1 : ℚ)
  have hfirstDefect : a.truncatedPrefixDefect a (-1) 0 2 =
      (d : WithTop ℚ) := by
    simpa only [hgapZero, d] using hcase.2.2
  intro b hb
  rw [a.unary_centralRepresentationConditionsPrime_iff_literal b]
  intro htrigger
  let S : Int := ordUnit K b
  have hSAllowed : S = 0 ∨ S = 1 := by
    simpa only [S] using hb
  rcases Int.even_or_odd (S - (a.order 1 + a.order 2)) with
    heven | hodd
  · have hST : S = T := by
      rcases heven with ⟨x, hx⟩
      rcases hTParity with ⟨y, hy⟩
      rcases hSAllowed with hSZero | hSOne <;>
        rcases hTAllowed with hTZero | hTOne <;> omega
    have hbT : ordUnit K b = T := by
      simpa only [S] using hST
    have hsumAlpha :
        d + a.alphaValue (2 : Fin (m + 2)) ≤
          2 * (ramificationIndex K : ℚ) + (T : ℚ) -
            (a.order 2 : ℚ) := by
      rw [hupper] at halpha
      dsimp only [d]
      push_cast at halpha
      linarith
    have hcurrentLe :
        a.truncatedPrefixDefect (BONG.unaryModelGoodBONG b) (-1) 3 1 ≤
          (a.alphaValue (2 : Fin (m + 2)) : WithTop ℚ) := by
      rw [a.unary_currentDefect_eq_min_raw_alphaThree hfour b]
      exact min_le_right _ _
    have hsumTop :
        a.truncatedPrefixDefect a (-1) 0 2 +
            a.truncatedPrefixDefect (BONG.unaryModelGoodBONG b) (-1) 3 1 ≤
          ((((2 * (ramificationIndex K : ℚ) : ℚ) + (T : ℚ) -
            (a.order 2 : ℚ) : ℚ)) : WithTop ℚ) := by
      rw [hfirstDefect]
      calc
        (d : WithTop ℚ) +
              a.truncatedPrefixDefect
                (BONG.unaryModelGoodBONG b) (-1) 3 1 ≤
            (d : WithTop ℚ) +
              (a.alphaValue (2 : Fin (m + 2)) : WithTop ℚ) :=
          (by simpa only [add_comm] using
            add_le_add_left hcurrentLe (d : WithTop ℚ))
        _ = ((d + a.alphaValue (2 : Fin (m + 2)) : ℚ) :
              WithTop ℚ) := by rw [WithTop.coe_add]
        _ ≤ _ := WithTop.coe_le_coe.mpr hsumAlpha
    have hstrict := htrigger.2
    rw [hbT] at hstrict
    exact (not_lt_of_ge hsumTop hstrict).elim
  · have hrawOdd : Odd (ordUnit K
        ((-1 : Kˣ) * a.prefixProduct 3 *
          (BONG.unaryModelGoodBONG b).prefixProduct 1)) := by
      rw [a.unary_mixedPrefix_three_one_order hcase.1 b]
      dsimp only [S] at hodd
      rcases hodd with ⟨x, hx⟩
      refine ⟨x + a.order 1 + a.order 2, ?_⟩
      omega
    have hcurrentZero :
        a.truncatedPrefixDefect (BONG.unaryModelGoodBONG b) (-1) 3 1 = 0 :=
      a.truncatedPrefixDefect_eq_zero_of_odd_order_mixed
        (alphaV := beliUniversalAlphaLaws)
        (alphaW := beliUniversalAlphaLaws)
        (BONG.unaryModelGoodBONG b) (-1) 3 1 hrawOdd
    have hstrictTop := htrigger.2
    rw [hfirstDefect, hcurrentZero, add_zero] at hstrictTop
    have hstrictQ :
        2 * (ramificationIndex K : ℚ) + (S : ℚ) -
            (a.order 2 : ℚ) < d := by
      exact WithTop.coe_lt_coe.mp hstrictTop
    have hstrictInt :
        2 * (ramificationIndex K : Int) + S - a.order 2 <
          1 - a.order 1 := by
      dsimp only [d] at hstrictQ
      exact_mod_cast hstrictQ
    have hgapLarge :
        2 * (ramificationIndex K : Int) ≤ a.order 2 - a.order 1 := by
      rcases hSAllowed with hSZero | hSOne <;> omega
    have hrightLe :
        2 * ((ramificationIndex K : Int) -
            (a.order 2 - a.order 1) / 2) - 1 ≤ -1 := by
      omega
    have hupperLe :
        a.universalAlphaThreeUpperBound hfour ≤ (-1 : ℚ) := by
      rw [hupper]
      have hleftLe :
          2 * (ramificationIndex K : Int) - 1 + T +
              a.order 1 - a.order 2 ≤ -1 := by
        rw [hparityIdentity]
        exact hrightLe
      exact_mod_cast hleftLe
    have halphaNonnegative :
        0 ≤ a.alphaValue (2 : Fin (m + 2)) :=
      (a.alpha_p2 (2 : Fin (m + 2))).1
    linarith

/-- Beli, Lemma 2.13 in Case I: under ambient universality and I(a), the
unary central conditions are equivalent to I(b). -/
theorem universalAllUnaryCentralConditions_iff_caseI
    {tail : Nat} (a : GoodBONG q L (tail + 2))
    (hline : q.IsLineUniversal) (hzero : a.order 0 = 0)
    (halpha : a.alphaValue (0 : Fin (tail + 1)) = 0) :
    a.UniversalAllUnaryCentralConditions ↔
      a.UniversalCentralCaseIConditions := by
  constructor
  · intro hall
    refine ⟨?_, ?_⟩
    · intro htail
      subst tail
      exact a.firstTwoIsotropic_of_isLineUniversal_rankTwo hline
    · intro hthree hthird
      have htailNe : tail ≠ 0 := Nat.ne_of_gt hthree
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero htailNe
      let b : Kˣ := uniformizerPowerUnit K (1 : Int)
      have hb : ordUnit K b = 1 :=
        ordUnit_uniformizerPowerUnit (K := K) (1 : Int)
      have hcentral := hall b (Or.inr hb)
      rw [a.unary_centralRepresentationConditionsPrime_iff_literal b]
        at hcentral
      have hleft : ordUnit K b < a.order 2 := by rw [hb]; exact hthird
      have hadjacent :=
        a.cappedAdjacent_ge_two_e_of_alphaValue_eq_zero
          (0 : Fin (m + 2)) halpha
      have hcurrent : (0 : WithTop ℚ) ≤
          a.truncatedPrefixDefect (BONG.unaryModelGoodBONG b) (-1) 3 1 :=
        a.truncatedPrefixDefect_nonneg
          (alphaV := beliUniversalAlphaLaws)
          (alphaW := beliUniversalAlphaLaws)
          (BONG.unaryModelGoodBONG b) (-1) 3 1
      have hsum :
          ((2 * ramificationIndex K : ℚ) : WithTop ℚ) ≤
            a.truncatedPrefixDefect a (-1) 0 2 +
              a.truncatedPrefixDefect (BONG.unaryModelGoodBONG b)
                (-1) 3 1 :=
        hadjacent.trans (le_add_of_nonneg_right hcurrent)
      have hthreshold :
          ((((2 * (ramificationIndex K : ℚ) : ℚ) +
            (ordUnit K b : ℚ) - (a.order 2 : ℚ)) : ℚ) : WithTop ℚ) <
              ((2 * ramificationIndex K : ℚ) : WithTop ℚ) := by
        apply WithTop.coe_lt_coe.mpr
        rw [hb]
        have hthirdQ : (1 : ℚ) < (a.order 2 : ℚ) := by
          exact_mod_cast hthird
        norm_num at hthirdQ ⊢
        linarith
      have hrep := hcentral ⟨hleft, hthreshold.trans_le hsum⟩
      rw [unary_prefixValues_one_eq b] at hrep
      have hsecond :=
        a.order_one_eq_neg_two_e_of_alphaValue_zero hzero halpha
      exact a.firstTwo_isotropic_of_represents_odd_at_endpoint
        hzero hsecond b (hb.symm ▸ odd_one) hrep
  · intro hcase b hb
    by_cases htail : tail = 0
    · subst tail
      unfold CentralRepresentationConditionsPrime
      intro i
      have := i.lt_large
      have := i.one_lt
      omega
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero htail
      rw [a.unary_centralRepresentationConditionsPrime_iff_literal b]
      intro htrigger
      rw [unary_prefixValues_one_eq b]
      have hsecond :=
        a.order_one_eq_neg_two_e_of_alphaValue_zero hzero halpha
      rcases hb with hbZero | hbOne
      · apply a.firstTwo_represents_even_at_endpoint hzero hsecond b
        rw [hbZero]
        exact Even.zero
      · by_cases hthird : 1 < a.order 2
        · exact a.firstTwo_represents_of_isotropic
            (hcase.2 (by omega) hthird) b
        · have hleft := htrigger.1
          rw [hbOne] at hleft
          omega

/-- Beli, Lemma 2.13 in Case II': under `R₁=0`, the unary central
conditions are equivalent to the literal Case II(b) alpha bound. -/
theorem universalAllUnaryCentralConditions_iff_caseII
    {tail : Nat} (a : GoodBONG q L (tail + 2))
    (hzero : a.order 0 = 0) (hcase : a.UniversalCaseIIPrime) :
    a.UniversalAllUnaryCentralConditions ↔
      a.UniversalCentralCaseIIConditions := by
  have htail : 0 < tail := hcase.1
  have htailNe : tail ≠ 0 := Nat.ne_of_gt htail
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero htailNe
  constructor
  · intro hall
    unfold UniversalCentralCaseIIConditions
    intro hbranch
    have hhigh : a.order 1 = 1 ∨ 1 < a.order 2 := by
      rcases hbranch with hone | hthird
      · exact Or.inl hone
      · exact Or.inr hthird.choose_spec
    by_contra hnot
    have hbad : ∀ hfour : 1 < m + 1,
        a.universalAlphaThreeUpperBound hfour <
          a.alphaValue (2 : Fin (m + 2)) := by
      intro hfour
      have hindex : (⟨2, by omega⟩ : Fin (m + 2)) =
          (2 : Fin (m + 2)) := by
        apply Fin.ext
        change 2 = 2 % (m + 2)
        exact (Nat.mod_eq_of_lt (by omega)).symm
      apply lt_of_not_ge
      intro hle
      apply hnot
      refine ⟨hfour, ?_⟩
      simpa only [hindex] using hle
    exact (a.not_universalAllUnaryCentralConditions_of_caseIIPrime_high_bad
      hzero hcase hhigh hbad) hall
  · intro hbound
    by_cases hhigh : a.order 1 = 1 ∨ 1 < a.order 2
    · have hbranch : a.order 1 = 1 ∨
          ∃ hthree : 0 < m + 1, 1 < a.order 2 := by
        rcases hhigh with hone | hthird
        · exact Or.inl hone
        · exact Or.inr ⟨by omega, hthird⟩
      obtain ⟨hfour, halpha⟩ := hbound hbranch
      have hindex : (⟨2, by omega⟩ : Fin (m + 2)) =
          (2 : Fin (m + 2)) := by
        apply Fin.ext
        change 2 = 2 % (m + 2)
        exact (Nat.mod_eq_of_lt (by omega)).symm
      have halpha' : a.alphaValue (2 : Fin (m + 2)) ≤
          a.universalAlphaThreeUpperBound hfour := by
        simpa only [hindex] using halpha
      exact a.universalAllUnaryCentralConditions_of_caseIIPrime_high_bound
        hzero hcase hhigh hfour halpha'
    · have hgapZero : a.orderGap (0 : Fin (m + 2)) = a.order 1 := by
        unfold orderGap
        simpa [hzero]
      have hsecondUpper : a.order 1 ≤ 1 := by
        have hbounds :=
          (a.alphaValue_eq_one_consequences (0 : Fin (m + 2))
            hcase.2.1).1.2
        rw [hgapZero] at hbounds
        exact hbounds
      have hsecond : a.order 1 ≤ 0 := by
        push_neg at hhigh
        omega
      have hthird : a.order 2 ≤ 1 := by
        push_neg at hhigh
        exact hhigh.2
      exact a.universalAllUnaryCentralConditions_of_caseIIPrime_low
        hzero hcase hsecond hthird

end BONG.GoodBONG

end Bong
