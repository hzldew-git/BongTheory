/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliTheoremThree
import Bong.Bong.BeliLemma72Proof
import Bong.Bong.BeliLemma73Proof
import Bong.Bong.BinarySpinorLocalProof
import Bong.QuadraticSpace.BinaryImproperIsometry

/-!
# Proof of Beli (2003), Theorem 3

This file verifies the low-rank cases and proves that the Lemma 7.3
replacement preserves the two conditions in Theorem 3.  Together with the
unconditional Lemma 7.3 instance, it supplies the induction law package.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {m : Nat}

namespace BONG

theorem normalizedUnitPart_adjacentParameter
    {r : Nat} (b : BONG V q L r) (i : Fin r)
    (hi : i.1 + 1 < r) :
    normalizedUnitPart K (b.adjacentParameter i hi) =
      b.normalizedValue ⟨i.1 + 1, hi⟩ / b.normalizedValue i := by
  rw [b.adjacentParameter_eq_uniformizerPower_mul_normalized]
  apply normalizedUnitPart_uniformizerPower_mul_valuationUnit
  rw [isValuationUnit_iff_ordUnit_eq_zero, div_eq_mul_inv,
    ordUnit_mul, ordUnit_inv]
  rw [(isValuationUnit_iff_ordUnit_eq_zero K _).1
      (b.normalizedValue_isValuationUnit ⟨i.1 + 1, hi⟩),
    (isValuationUnit_iff_ordUnit_eq_zero K _).1
      (b.normalizedValue_isValuationUnit i)]
  simp

theorem Lemma73SplittingWitness.valueUnit_before
    {r : Nat} {b : BONG V q L (r + 3)} {i : Fin (r + 1)}
    (w : Lemma73SplittingWitness b i) (j : Fin (r + 1))
    (hj : j.1 < i.1) :
    w.remainderBONG.valueUnit j = b.valueUnit ⟨j.1, by omega⟩ := by
  apply Units.ext
  exact w.value_before j hj

theorem Lemma73SplittingWitness.order_before
    {r : Nat} {b : BONG V q L (r + 3)} {i : Fin (r + 1)}
    (w : Lemma73SplittingWitness b i) (j : Fin (r + 1))
    (hj : j.1 < i.1) :
    w.remainderBONG.order j = b.order ⟨j.1, by omega⟩ := by
  change ordUnit K (w.remainderBONG.valueUnit j) =
    ordUnit K (b.valueUnit ⟨j.1, by omega⟩)
  rw [w.valueUnit_before j hj]

theorem Lemma73SplittingWitness.normalizedValue_before
    {r : Nat} {b : BONG V q L (r + 3)} {i : Fin (r + 1)}
    (w : Lemma73SplittingWitness b i) (j : Fin (r + 1))
    (hj : j.1 < i.1) :
    w.remainderBONG.normalizedValue j =
      b.normalizedValue ⟨j.1, by omega⟩ := by
  unfold normalizedValue
  rw [w.valueUnit_before j hj, w.order_before j hj]

theorem Lemma73SplittingWitness.valueUnit_after
    {r : Nat} {b : BONG V q L (r + 3)} {i : Fin (r + 1)}
    (w : Lemma73SplittingWitness b i) (j : Fin (r + 1))
    (hj : i.1 < j.1) :
    w.remainderBONG.valueUnit j = b.valueUnit ⟨j.1 + 2, by omega⟩ := by
  apply Units.ext
  exact w.value_after j hj

theorem Lemma73SplittingWitness.order_after
    {r : Nat} {b : BONG V q L (r + 3)} {i : Fin (r + 1)}
    (w : Lemma73SplittingWitness b i) (j : Fin (r + 1))
    (hj : i.1 < j.1) :
    w.remainderBONG.order j = b.order ⟨j.1 + 2, by omega⟩ := by
  change ordUnit K (w.remainderBONG.valueUnit j) =
    ordUnit K (b.valueUnit ⟨j.1 + 2, by omega⟩)
  rw [w.valueUnit_after j hj]

theorem Lemma73SplittingWitness.normalizedValue_after
    {r : Nat} {b : BONG V q L (r + 3)} {i : Fin (r + 1)}
    (w : Lemma73SplittingWitness b i) (j : Fin (r + 1))
    (hj : i.1 < j.1) :
    w.remainderBONG.normalizedValue j =
      b.normalizedValue ⟨j.1 + 2, by omega⟩ := by
  unfold normalizedValue
  rw [w.valueUnit_after j hj, w.order_after j hj]

theorem Lemma73SplittingWitness.valueUnit_replacement
    {r : Nat} {b : BONG V q L (r + 3)} {i : Fin (r + 1)}
    (w : Lemma73SplittingWitness b i) :
    w.remainderBONG.valueUnit ⟨i.1, by omega⟩ =
      b.lemma73ResidualValue i := by
  apply Units.ext
  exact w.replacement_value

theorem Lemma73SplittingWitness.normalizedValue_replacement
    {r : Nat} {b : BONG V q L (r + 3)} {i : Fin (r + 1)}
    (w : Lemma73SplittingWitness b i) :
    w.remainderBONG.normalizedValue ⟨i.1, by omega⟩ =
      -(b.normalizedValue (lemma73FirstIndex i) *
        b.normalizedValue (lemma73MiddleIndex i) *
        b.normalizedValue (lemma73LastIndex i)) := by
  change normalizedUnitPart K
      (w.remainderBONG.valueUnit ⟨i.1, by omega⟩) = _
  rw [w.valueUnit_replacement]
  let ε : Kˣ := -(b.normalizedValue (lemma73FirstIndex i) *
    b.normalizedValue (lemma73MiddleIndex i) *
    b.normalizedValue (lemma73LastIndex i))
  have hε : IsValuationUnit K (ε : K) := by
    rw [isValuationUnit_iff_ordUnit_eq_zero]
    dsimp [ε]
    rw [ordUnit_neg, ordUnit_mul, ordUnit_mul]
    rw [(isValuationUnit_iff_ordUnit_eq_zero K _).1
        (b.normalizedValue_isValuationUnit (lemma73FirstIndex i)),
      (isValuationUnit_iff_ordUnit_eq_zero K _).1
        (b.normalizedValue_isValuationUnit (lemma73MiddleIndex i)),
      (isValuationUnit_iff_ordUnit_eq_zero K _).1
        (b.normalizedValue_isValuationUnit (lemma73LastIndex i))]
    simp
  have hres : b.lemma73ResidualValue i =
      uniformizerPowerUnit K (b.order (lemma73FirstIndex i)) * ε := by
    unfold lemma73ResidualValue
    dsimp [ε]
    apply Units.ext
    simp only [Units.val_neg, Units.val_mul]
    ring
  rw [hres, normalizedUnitPart_uniformizerPower_mul_valuationUnit _ _ hε]

theorem Lemma73SplittingWitness.adjacentParameter_before
    {r : Nat} {b : BONG V q L (r + 3)} {i : Fin (r + 1)}
    (w : Lemma73SplittingWitness b i) (j : Fin (r + 1))
    (hj : j.1 + 1 < r + 1) (hbefore : j.1 + 1 < i.1) :
    w.remainderBONG.adjacentParameter j hj =
      b.adjacentParameter ⟨j.1, by omega⟩ (by simp; omega) := by
  unfold adjacentParameter
  rw [w.valueUnit_before j (by omega)]
  rw [w.valueUnit_before ⟨j.1 + 1, hj⟩ hbefore]

theorem Lemma73SplittingWitness.adjacentParameter_after
    {r : Nat} {b : BONG V q L (r + 3)} {i : Fin (r + 1)}
    (w : Lemma73SplittingWitness b i) (j : Fin (r + 1))
    (hj : j.1 + 1 < r + 1) (hafter : i.1 < j.1) :
    w.remainderBONG.adjacentParameter j hj =
      b.adjacentParameter ⟨j.1 + 2, by omega⟩ (by simp; omega) := by
  unfold adjacentParameter
  rw [w.valueUnit_after j hafter]
  rw [w.valueUnit_after ⟨j.1 + 1, hj⟩ (by
    change i.1 < j.1 + 1
    omega)]

theorem Lemma73SplittingWitness.leftBoundary_unit
    [BeliLemma72Laws K]
    {r : Nat} {b : BONG V q L (r + 3)} {i : Fin (r + 1)}
    (w : Lemma73SplittingWitness b i)
    (hgood : b.IsGood) (h : b.SatisfiesTheoremThreeConditions)
    (hblock : b.Lemma73Hypotheses i)
    (j : Fin (r + 1)) (hj : j.1 + 1 = i.1) :
    beliSpinorGroup K
        (w.remainderBONG.adjacentUnitSquareClass j (by omega)) ≤
      valuationUnitSquareClassSubgroup K := by
  let prev : Fin (r + 3) := ⟨j.1, by omega⟩
  let first : Fin (r + 3) := lemma73FirstIndex i
  let middle : Fin (r + 3) := lemma73MiddleIndex i
  let last : Fin (r + 3) := lemma73LastIndex i
  have hp0 : prev.1 + 1 < r + 3 := by simp only [prev]; omega
  have hp1 : middle.1 + 1 < r + 3 := by
    simp only [middle, lemma73MiddleIndex]
    omega
  let p0 : Kˣ := b.adjacentParameter prev hp0
  let p1 : Kˣ := b.adjacentParameter middle hp1
  let params : Fin 2 → Kˣ := fun k => Fin.cases p0 (fun _ => p1) k
  let R : Int := b.order first - b.order prev
  have hprevNext : (⟨prev.1 + 1, hp0⟩ : Fin (r + 3)) = first := by
    apply Fin.ext
    simp only [prev, first, lemma73FirstIndex, Fin.val_mk]
    omega
  have hmiddleNext : (⟨middle.1 + 1, hp1⟩ : Fin (r + 3)) = last := by
    apply Fin.ext
    simp only [middle, last, lemma73MiddleIndex, lemma73LastIndex, Fin.val_mk]
  have hparams : ∀ k, IsLemma72UnitParameter (K := K) (params k) := by
    intro k
    fin_cases k
    · change IsLemma72UnitParameter (K := K) p0
      refine ⟨b.adjacentParameter_isBinaryParameterAdmissible prev hp0, ?_⟩
      simpa only [p0, adjacentUnitSquareClass,
        beliSpinorGroup_unitSquareClass] using h.1 prev hp0
    · change IsLemma72UnitParameter (K := K) p1
      refine ⟨b.adjacentParameter_isBinaryParameterAdmissible middle hp1, ?_⟩
      simpa only [p1, adjacentUnitSquareClass,
        beliSpinorGroup_unitSquareClass] using h.1 middle hp1
  have hEven : Even R := by
    have he := h.adjacentOrderGap_even prev hp0
    change Even (b.order ⟨prev.1 + 1, hp0⟩ - b.order prev) at he
    rw [hprevNext] at he
    exact he
  have horders : ∀ k, ordUnit K (params k) ≤ R := by
    intro k
    fin_cases k
    · change ordUnit K p0 ≤ R
      rw [show p0 = b.adjacentParameter prev hp0 from rfl,
        b.ordUnit_adjacentParameter, hprevNext]
    · change ordUnit K p1 ≤ R
      rw [show p1 = b.adjacentParameter middle hp1 from rfl,
        b.ordUnit_adjacentParameter, hmiddleNext]
      have hprevMiddle : b.order prev ≤ b.order middle := by
        have hg := hgood prev (by simp only [prev]; omega)
        convert hg using 1
        apply congrArg b.order
        apply Fin.ext
        simp only [prev, middle, lemma73MiddleIndex, Fin.val_mk]
        omega
      rw [hblock.1.symm]
      simpa only [R] using
        (sub_le_sub_left hprevMiddle (b.order first))
  have hc := beliLemma72_ii (K := K) params R (by decide)
    hparams hEven horders
  have hactual :
      w.remainderBONG.adjacentParameter j (by omega) =
        lemma72CombinedParameter (K := K) params R *
          b.normalizedValue middle ^ 2 := by
    rw [w.remainderBONG.adjacentParameter_eq_uniformizerPower_mul_normalized]
    have hremNext :
        (⟨j.1 + 1, by omega⟩ : Fin (r + 1)) =
          ⟨i.1, by omega⟩ := by ext; omega
    rw [hremNext, w.normalizedValue_replacement]
    rw [w.normalizedValue_before j (by omega)]
    have hremReplacement :
        w.remainderBONG.order ⟨i.1, by omega⟩ =
          b.order first := by
      simpa only [first] using w.replacement_order
    rw [w.order_before j (by omega), hremReplacement]
    unfold lemma72CombinedParameter
    have hparamsOne : params (1 : Fin 2) = p1 := by
      rfl
    simp only [Fin.prod_univ_two, params, Fin.cases_zero,
      hparamsOne, Nat.reduceSubDiff, pow_one]
    rw [show p0 = b.adjacentParameter prev hp0 from rfl,
      show p1 = b.adjacentParameter middle hp1 from rfl,
      normalizedUnitPart_adjacentParameter,
      normalizedUnitPart_adjacentParameter, hprevNext, hmiddleNext]
    change uniformizerUnit K ^ (b.order first - b.order prev) *
        (-(b.normalizedValue first * b.normalizedValue middle *
          b.normalizedValue last) / b.normalizedValue prev) =
      ((-1 : Kˣ) * uniformizerPowerUnit K R *
          ((b.normalizedValue first / b.normalizedValue prev) *
            (b.normalizedValue last / b.normalizedValue middle))) *
        b.normalizedValue middle ^ 2
    rw [show uniformizerPowerUnit K R = uniformizerUnit K ^ R from rfl]
    dsimp [R]
    apply Units.ext
    simp only [Units.val_neg, Units.val_mul, Units.val_div_eq_div_val,
      Units.val_pow_eq_pow_val]
    field_simp [Units.ne_zero (b.normalizedValue prev),
      Units.ne_zero (b.normalizedValue middle)]
    simp
  have hmiddleUnit : IsValuationUnit K (b.normalizedValue middle : K) :=
    b.normalizedValue_isValuationUnit middle
  have hclass :
      unitSquareClass K
          (w.remainderBONG.adjacentParameter
            j (by omega)) =
        unitSquareClass K (lemma72CombinedParameter (K := K) params R) := by
    rw [hactual]
    exact unitSquareClass_mul_unit_square K _ _ hmiddleUnit
  rw [adjacentUnitSquareClass, hclass]
  simpa only [beliSpinorGroup_unitSquareClass] using hc.2

theorem Lemma73SplittingWitness.rightBoundary_unit
    [BeliLemma72Laws K]
    {r : Nat} {b : BONG V q L (r + 3)} {i : Fin (r + 1)}
    (w : Lemma73SplittingWitness b i)
    (hgood : b.IsGood) (h : b.SatisfiesTheoremThreeConditions)
    (hblock : b.Lemma73Hypotheses i)
    (hi : i.1 + 1 < r + 1) :
    beliSpinorGroup K
        (w.remainderBONG.adjacentUnitSquareClass i hi) ≤
      valuationUnitSquareClassSubgroup K := by
  let first : Fin (r + 3) := lemma73FirstIndex i
  let middle : Fin (r + 3) := lemma73MiddleIndex i
  let last : Fin (r + 3) := lemma73LastIndex i
  let next : Fin (r + 3) := ⟨i.1 + 3, by omega⟩
  have hp0 : first.1 + 1 < r + 3 := by
    simp only [first, lemma73FirstIndex]
    omega
  have hp1 : last.1 + 1 < r + 3 := by
    simp only [last, lemma73LastIndex]
    omega
  let p0 : Kˣ := b.adjacentParameter first hp0
  let p1 : Kˣ := b.adjacentParameter last hp1
  let params : Fin 2 → Kˣ := fun k => Fin.cases p0 (fun _ => p1) k
  let R : Int := b.order next - b.order first
  have hfirstNext : (⟨first.1 + 1, hp0⟩ : Fin (r + 3)) = middle := by
    apply Fin.ext
    simp only [first, middle, lemma73FirstIndex, lemma73MiddleIndex, Fin.val_mk]
  have hlastNext : (⟨last.1 + 1, hp1⟩ : Fin (r + 3)) = next := by
    apply Fin.ext
    simp only [last, next, lemma73LastIndex, Fin.val_mk]
  have hparams : ∀ k, IsLemma72UnitParameter (K := K) (params k) := by
    intro k
    fin_cases k
    · change IsLemma72UnitParameter (K := K) p0
      refine ⟨b.adjacentParameter_isBinaryParameterAdmissible first hp0, ?_⟩
      simpa only [p0, adjacentUnitSquareClass,
        beliSpinorGroup_unitSquareClass] using h.1 first hp0
    · change IsLemma72UnitParameter (K := K) p1
      refine ⟨b.adjacentParameter_isBinaryParameterAdmissible last hp1, ?_⟩
      simpa only [p1, adjacentUnitSquareClass,
        beliSpinorGroup_unitSquareClass] using h.1 last hp1
  have hEven : Even R := by
    have he := h.adjacentOrderGap_even last hp1
    change Even (b.order ⟨last.1 + 1, hp1⟩ - b.order last) at he
    rw [hlastNext] at he
    have hfirstLast : b.order first = b.order last := hblock.1
    rw [← hfirstLast] at he
    exact he
  have horders : ∀ k, ordUnit K (params k) ≤ R := by
    intro k
    fin_cases k
    · change ordUnit K p0 ≤ R
      rw [show p0 = b.adjacentParameter first hp0 from rfl,
        b.ordUnit_adjacentParameter, hfirstNext]
      have hmiddleNextOrder : b.order middle ≤ b.order next := by
        have hg := hgood middle (by
          simp only [middle, lemma73MiddleIndex]
          omega)
        convert hg using 1
        apply congrArg b.order
        apply Fin.ext
        simp only [middle, next, lemma73MiddleIndex, Fin.val_mk]
      simpa only [R] using
        (sub_le_sub_right hmiddleNextOrder (b.order first))
    · change ordUnit K p1 ≤ R
      rw [show p1 = b.adjacentParameter last hp1 from rfl,
        b.ordUnit_adjacentParameter, hlastNext]
      rw [← hblock.1]
  have hc := beliLemma72_ii (K := K) params R (by decide)
    hparams hEven horders
  have hactual :
      w.remainderBONG.adjacentParameter i hi =
        lemma72CombinedParameter (K := K) params R *
          (b.normalizedValue middle)⁻¹ ^ 2 := by
    rw [w.remainderBONG.adjacentParameter_eq_uniformizerPower_mul_normalized]
    let remNext : Fin (r + 1) := ⟨i.1 + 1, hi⟩
    have hremNextAfter : i.1 < remNext.1 := by
      simp only [remNext]
      omega
    rw [w.normalizedValue_after remNext hremNextAfter]
    rw [w.normalizedValue_replacement]
    rw [w.order_after remNext hremNextAfter]
    have hremReplacement :
        w.remainderBONG.order ⟨i.1, by omega⟩ =
          b.order first := by
      simpa only [first] using w.replacement_order
    rw [hremReplacement]
    have hafterIndex :
        (⟨remNext.1 + 2, by omega⟩ : Fin (r + 3)) = next := by
      apply Fin.ext
      simp only [remNext, next]
    rw [hafterIndex]
    unfold lemma72CombinedParameter
    have hparamsOne : params (1 : Fin 2) = p1 := by
      rfl
    simp only [Fin.prod_univ_two, params, Fin.cases_zero,
      hparamsOne, Nat.reduceSubDiff, pow_one]
    rw [show p0 = b.adjacentParameter first hp0 from rfl,
      show p1 = b.adjacentParameter last hp1 from rfl,
      normalizedUnitPart_adjacentParameter,
      normalizedUnitPart_adjacentParameter, hfirstNext, hlastNext]
    change uniformizerUnit K ^ (b.order next - b.order first) *
        (b.normalizedValue next /
          -(b.normalizedValue first * b.normalizedValue middle *
            b.normalizedValue last)) =
      ((-1 : Kˣ) * uniformizerPowerUnit K R *
          ((b.normalizedValue middle / b.normalizedValue first) *
            (b.normalizedValue next / b.normalizedValue last))) *
        (b.normalizedValue middle)⁻¹ ^ 2
    rw [show uniformizerPowerUnit K R = uniformizerUnit K ^ R from rfl]
    dsimp [R]
    apply Units.ext
    simp only [Units.val_neg, Units.val_mul, Units.val_div_eq_div_val,
      Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
    field_simp [Units.ne_zero (b.normalizedValue first),
      Units.ne_zero (b.normalizedValue middle),
      Units.ne_zero (b.normalizedValue last)]
    simp
  have hmiddleInvUnit :
      IsValuationUnit K
        (((b.normalizedValue middle)⁻¹ : Kˣ) : K) := by
    simpa only [IsValuationUnit, Units.val_inv_eq_inv_val,
      AddValuation.map_inv, neg_eq_zero] using
      b.normalizedValue_isValuationUnit middle
  have hclass :
      unitSquareClass K
          (w.remainderBONG.adjacentParameter i hi) =
        unitSquareClass K (lemma72CombinedParameter (K := K) params R) := by
    rw [hactual]
    exact unitSquareClass_mul_unit_square K _ _ hmiddleInvUnit
  rw [adjacentUnitSquareClass, hclass]
  simpa only [beliSpinorGroup_unitSquareClass] using hc.2

theorem Lemma73SplittingWitness.replacement_adjacentConditions
    [BeliLemma72Laws K]
    {r : Nat} {b : BONG V q L (r + 3)} {i : Fin (r + 1)}
    (w : Lemma73SplittingWitness b i)
    (hgood : b.IsGood) (h : b.SatisfiesTheoremThreeConditions)
    (hblock : b.Lemma73Hypotheses i) :
    ∀ (k : Fin (r + 1)) (hk : k.1 + 1 < r + 1),
      beliSpinorGroup K
          (w.remainderBONG.adjacentUnitSquareClass k hk) ≤
        valuationUnitSquareClassSubgroup K := by
  intro k hk
  by_cases hstrictBefore : k.1 + 1 < i.1
  · rw [adjacentUnitSquareClass,
      w.adjacentParameter_before k hk hstrictBefore]
    simpa only [adjacentUnitSquareClass] using
      h.1 ⟨k.1, by omega⟩ (by simp; omega)
  · by_cases hleft : k.1 + 1 = i.1
    · exact w.leftBoundary_unit hgood h hblock k hleft
    · have hik : i.1 ≤ k.1 := by omega
      by_cases hright : i.1 = k.1
      · have hki : k = i := by
          apply Fin.ext
          omega
        subst k
        exact w.rightBoundary_unit hgood h hblock hk
      · have hafter : i.1 < k.1 := by omega
        rw [adjacentUnitSquareClass,
          w.adjacentParameter_after k hk hafter]
        simpa only [adjacentUnitSquareClass] using
          h.1 ⟨k.1 + 2, by omega⟩ (by simp; omega)

theorem Lemma73SplittingWitness.replacement_twoStepConditions
    [BeliLemma72Laws K]
    {r : Nat} {b : BONG V q L (r + 3)} {i : Fin (r + 1)}
    (w : Lemma73SplittingWitness b i)
    (hgood : b.IsGood) (h : b.SatisfiesTheoremThreeConditions)
    (hblock : b.Lemma73Hypotheses i) :
    ∀ (k : Fin (r + 1)) (hk : k.1 + 2 < r + 1),
      w.remainderBONG.order k =
          w.remainderBONG.order ⟨k.1 + 2, hk⟩ →
        Int.ModEq 2
          ((w.remainderBONG.order ⟨k.1 + 1, by omega⟩ -
            w.remainderBONG.order k) / 2)
          (ramificationIndex K : Int) := by
  intro k hk heq
  let k1 : Fin (r + 1) := ⟨k.1 + 1, by omega⟩
  let k2 : Fin (r + 1) := ⟨k.1 + 2, hk⟩
  by_cases hbefore : k.1 + 2 < i.1
  · have heq' := heq
    rw [w.order_before k (by omega),
      w.order_before k2 (by simp only [k2]; omega)] at heq'
    have hc := h.2 ⟨k.1, by omega⟩ (by simp; omega) (by
      simpa only [k2] using heq')
    rw [w.order_before k (by omega),
      w.order_before k1 (by simp only [k1]; omega)]
    simpa only [k1] using hc
  · by_cases hrightEndpoint : k.1 + 2 = i.1
    · have hk2i : k2 = i := by
        apply Fin.ext
        simp only [k2]
        omega
      have hk2i' : (⟨k.1 + 2, hk⟩ : Fin (r + 1)) = i := by
        simpa only [k2] using hk2i
      have heq' := heq
      rw [w.order_before k (by omega), hk2i',
        w.replacement_order] at heq'
      have heqOrig :
          b.order ⟨k.1, by omega⟩ =
            b.order ⟨k.1 + 2, by omega⟩ := by
        convert heq' using 1
        apply congrArg b.order
        apply Fin.ext
        simp only [lemma73FirstIndex, Fin.val_mk]
        omega
      have hc := h.2 ⟨k.1, by omega⟩ (by simp; omega) heqOrig
      rw [w.order_before k (by omega),
        w.order_before k1 (by simp only [k1]; omega)]
      simpa only [k1] using hc
    · by_cases hmiddle : k.1 + 1 = i.1
      · have hk1i : k1 = i := by
          apply Fin.ext
          simp only [k1]
          omega
        have hk1i' : (⟨k.1 + 1, by omega⟩ : Fin (r + 1)) = i := by
          simpa only [k1] using hk1i
        let prev : Fin (r + 3) := ⟨k.1, by omega⟩
        let middle : Fin (r + 3) := ⟨k.1 + 2, by omega⟩
        let next : Fin (r + 3) := ⟨k.1 + 4, by omega⟩
        have heq' := heq
        rw [w.order_before k (by omega),
          w.order_after k2 (by simp only [k2]; omega)] at heq'
        have heqPrevNext : b.order prev = b.order next := by
          simpa only [prev, next, k2] using heq'
        have hprevMiddle : b.order prev ≤ b.order middle := by
          have hg := hgood prev (by simp only [prev]; omega)
          simpa only [prev, middle] using hg
        have hmiddleNext : b.order middle ≤ b.order next := by
          have hg := hgood middle (by simp only [middle]; omega)
          simpa only [middle, next] using hg
        have hprevMiddleEq : b.order prev = b.order middle := by
          apply le_antisymm hprevMiddle
          calc
            b.order middle ≤ b.order next := hmiddleNext
            _ = b.order prev := heqPrevNext.symm
        have hc := h.2 prev (by simp only [prev]; omega) (by
          simpa only [prev, middle] using hprevMiddleEq)
        have hprevNext :
            (⟨prev.1 + 1, by simp only [prev]; omega⟩ : Fin (r + 3)) =
              lemma73FirstIndex i := by
          apply Fin.ext
          simp only [prev, lemma73FirstIndex, Fin.val_mk]
          omega
        rw [hprevNext] at hc
        rw [w.order_before k (by omega), hk1i',
          w.replacement_order]
        simpa only [prev] using hc
      · have hik : i.1 ≤ k.1 := by omega
        by_cases hleftEndpoint : i.1 = k.1
        · have hki : k = i := by
            apply Fin.ext
            omega
          subst k
          have heq' := heq
          rw [w.replacement_order,
            w.order_after k2 (by simp only [k2]; omega)] at heq'
          let last : Fin (r + 3) := lemma73LastIndex i
          let after1 : Fin (r + 3) := ⟨i.1 + 3, by omega⟩
          let after2 : Fin (r + 3) := ⟨i.1 + 4, by omega⟩
          have heqLastAfter2 : b.order last = b.order after2 := by
            calc
              b.order last = b.order (lemma73FirstIndex i) := hblock.1.symm
              _ = b.order after2 := by
                simpa only [after2, k2] using heq'
          have hlastPlusTwo :
              (⟨last.1 + 2, by
                simp only [last, lemma73LastIndex]
                omega⟩ : Fin (r + 3)) = after2 := by
            apply Fin.ext
            simp only [last, after2, lemma73LastIndex, Fin.val_mk]
          have hc := h.2 last (by simp only [last, lemma73LastIndex]; omega)
            (by rw [hlastPlusTwo]; exact heqLastAfter2)
          have hlastPlusOne :
              (⟨last.1 + 1, by
                simp only [last, lemma73LastIndex]
                omega⟩ : Fin (r + 3)) = after1 := by
            apply Fin.ext
            simp only [last, after1, lemma73LastIndex, Fin.val_mk]
          rw [hlastPlusOne] at hc
          rw [w.replacement_order,
            w.order_after k1 (by simp only [k1]; omega)]
          rw [hblock.1]
          simpa only [k1, after1, last] using hc
        · have hafter : i.1 < k.1 := by omega
          have heq' := heq
          rw [w.order_after k hafter,
            w.order_after k2 (by simp only [k2]; omega)] at heq'
          have hc := h.2 ⟨k.1 + 2, by omega⟩ (by simp; omega) (by
            simpa only [k2] using heq')
          rw [w.order_after k hafter,
            w.order_after k1 (by simp only [k1]; omega)]
          simpa only [k1] using hc

theorem low_rank_unitBounded_proved
    (b : BONG V q L m) (hgood : b.IsGood) (hm : m ≤ 2)
    (h : b.SatisfiesTheoremThreeConditions) :
    Lattice.SpinorNormIsUnitBounded q L := by
  interval_cases m
  · letI : Module.Finite K V := L.moduleFinite
    intro a ha
    rcases ha with ⟨f, rfl⟩
    have hfin : Module.finrank K V = 0 := b.length_eq_finrank.symm
    haveI : Subsingleton V := Module.finrank_zero_iff.mp hfin
    have hf : f.toIntegralOrthogonalGroup.toQuadraticSpaceIsometry =
        QuadraticSpace.Isometry.refl q := by
      apply QuadraticSpace.Isometry.ext
      intro x
      exact Subsingleton.elim _ _
    change QuadraticSpace.spinorNorm
        f.toIntegralOrthogonalGroup.toQuadraticSpaceIsometry ∈
      valuationUnitSquareClassSubgroup K
    rw [hf, QuadraticSpace.spinorNorm_refl]
    exact Subgroup.one_mem _
  · intro a ha
    rcases ha with ⟨f, rfl⟩
    have hfin : Module.finrank K V = 1 := b.length_eq_finrank.symm
    letI : Module.Finite K V := L.moduleFinite
    have hlinear : f.toIntegralOrthogonalGroup.toLinearEquiv =
        LinearEquiv.refl K V := by
      apply QuadraticSpace.linearEquiv_eq_of_finrank_eq_one_of_det_eq hfin
      simpa using f.det_eq_one
    have hf : f.toIntegralOrthogonalGroup.toQuadraticSpaceIsometry =
        QuadraticSpace.Isometry.refl q := by
      apply QuadraticSpace.Isometry.ext
      intro x
      exact DFunLike.congr_fun hlinear x
    change QuadraticSpace.spinorNorm
        f.toIntegralOrthogonalGroup.toQuadraticSpaceIsometry ∈
      valuationUnitSquareClassSubgroup K
    rw [hf, QuadraticSpace.spinorNorm_refl]
    exact Subgroup.one_mem _
  · intro a ha
    have ha' : a ∈ Lattice.spinorNormImage (q := q) (L := L) := by
      rw [← Lattice.coe_spinorNormImageSubgroup]
      exact ha
    rw [b.spinorNormImage_eq_beliSpinorGroup] at ha'
    exact h.1 (0 : Fin 2) (by decide) ha'

theorem replacement_conditions_proved
    [BeliLemma72Laws K]
    {r : Nat} {b : BONG V q L (r + 3)} {i : Fin (r + 1)}
    (w : Lemma73SplittingWitness b i)
    (hgood : b.IsGood) (h : b.SatisfiesTheoremThreeConditions)
    (hblock : b.Lemma73Hypotheses i) :
    w.remainderBONG.SatisfiesTheoremThreeConditions := by
  exact ⟨w.replacement_adjacentConditions hgood h hblock,
    w.replacement_twoStepConditions hgood h hblock⟩

instance beliTheoremThreeLawsProved : BeliTheoremThreeLaws.{u, v} K where
  low_rank_unitBounded b hgood hm h :=
    low_rank_unitBounded_proved b hgood hm h
  replacement_conditions _b _i hgood h hblock w :=
    replacement_conditions_proved w hgood h hblock

end BONG

end Bong
