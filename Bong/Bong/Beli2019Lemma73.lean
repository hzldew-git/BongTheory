/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009AlphaArithmetic
import Bong.Bong.BeliLemma411

/-!
# Beli (2019), Lemma 7.3

On a plateau of the monotone sequence `R_i + alpha_i`, all relevant order
entries have the same parity and all alpha values are integral with the same
parity.  The adjacent gaps and alpha values are at most `2e`.
-/

namespace Bong

open Dyadic

universe u v

/-- Two rational numbers are integral and congruent modulo two. -/
def RationalModEqTwo (x y : ℚ) : Prop :=
  ∃ a b : Int, x = (a : ℚ) ∧ y = (b : ℚ) ∧ Int.ModEq 2 a b

namespace RationalModEqTwo

theorem refl {x : ℚ} (hx : IsRationalInteger x) : RationalModEqTwo x x := by
  rcases hx with ⟨a, rfl⟩
  exact ⟨a, a, rfl, rfl, Int.ModEq.rfl⟩

theorem symm {x y : ℚ} (h : RationalModEqTwo x y) : RationalModEqTwo y x := by
  rcases h with ⟨a, b, rfl, rfl, hab⟩
  exact ⟨b, a, rfl, rfl, hab.symm⟩

theorem trans {x y z : ℚ}
    (hxy : RationalModEqTwo x y) (hyz : RationalModEqTwo y z) :
    RationalModEqTwo x z := by
  rcases hxy with ⟨a, b, hxa, hyb, hab⟩
  rcases hyz with ⟨b', c, hyb', hzc, hbc⟩
  have hbb' : b = b' := by
    exact_mod_cast hyb.symm.trans hyb'
  subst b'
  exact ⟨a, c, hxa, hzc, hab.trans hbc⟩

end RationalModEqTwo

theorem int_modEq_two_of_even_successive
    (f : Nat → Int) {i k : Nat} (hik : i ≤ k)
    (hstep : ∀ t, i ≤ t → t < k → Even (f (t + 1) - f t)) :
    Int.ModEq 2 (f k) (f i) := by
  induction k, hik using Nat.le_induction with
  | base => exact Int.ModEq.rfl
  | succ k hik ih =>
      have heven := hstep k hik (Nat.lt_succ_self k)
      rcases heven with ⟨c, hc⟩
      have hmod : Int.ModEq 2 (f (k + 1)) (f k) := by
        rw [Int.modEq_iff_dvd]
        refine ⟨-c, ?_⟩
        omega
      exact hmod.trans (ih fun t hit htk ↦ hstep t hit (htk.trans_le (Nat.le_succ k)))

theorem rationalModEqTwo_of_successive
    (f : Nat → ℚ) {i k : Nat} (hik : i ≤ k)
    (hi : IsRationalInteger (f i))
    (hstep : ∀ t, i ≤ t → t < k → RationalModEqTwo (f (t + 1)) (f t)) :
    RationalModEqTwo (f k) (f i) := by
  induction k, hik using Nat.le_induction with
  | base => exact RationalModEqTwo.refl hi
  | succ k hik ih =>
      exact (hstep k hik (Nat.lt_succ_self k)).trans
        (ih fun t hit htk ↦ hstep t hit (htk.trans_le (Nat.le_succ k)))

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

namespace BONG.GoodBONG

variable [Beli2006AlphaLaws.{u, v} K]
  [Beli2009AlphaParityLaws.{u, v} K]

/-- The weak `2e` comparison in Corollary 2.8(ii). -/
theorem alphaValue_le_twoE_iff_orderGap_le_twoE
    (b : GoodBONG q L (n + 1)) (i : Fin n) :
    b.alphaValue i ≤ 2 * (ramificationIndex K : ℚ) ↔
      b.orderGap i ≤ 2 * (ramificationIndex K : Int) := by
  constructor
  · intro halpha
    by_contra hgap
    have hgap' : 2 * (ramificationIndex K : Int) < b.orderGap i := by omega
    have halpha' : 2 * (ramificationIndex K : ℚ) < b.alphaValue i :=
      (b.beli2009Corollary28_ii i).2.2.mpr hgap'
    exact (not_lt_of_ge halpha) halpha'
  · intro hgap
    by_contra halpha
    have halpha' : 2 * (ramificationIndex K : ℚ) < b.alphaValue i := by
      exact lt_of_not_ge halpha
    have hgap' : 2 * (ramificationIndex K : Int) < b.orderGap i :=
      (b.beli2009Corollary28_ii i).2.2.mp halpha'
    exact (not_lt_of_ge hgap) hgap'

/-- The conclusions obtained from one adjacent equality
`R_i + alpha_i = R_(i+1) + alpha_(i+1)`. -/
structure Lemma73StepConsequences
    (b : GoodBONG q L (n + 2)) (i : Fin (n + 1))
    (hi : i.1 + 1 < n + 1) : Prop where
  orderGap_even : Even (b.orderGap i)
  alpha_modEq : RationalModEqTwo
    (b.alphaValue ⟨i.1 + 1, hi⟩) (b.alphaValue i)
  currentAlpha_le : b.alphaValue i ≤ 2 * (ramificationIndex K : ℚ)
  nextAlpha_le :
    b.alphaValue ⟨i.1 + 1, hi⟩ ≤ 2 * (ramificationIndex K : ℚ)
  currentGap_le : b.orderGap i ≤ 2 * (ramificationIndex K : Int)
  nextGap_le :
    b.orderGap ⟨i.1 + 1, hi⟩ ≤ 2 * (ramificationIndex K : Int)

/-- The one-step parity and bound calculation in Lemma 7.3. -/
theorem beli2019Lemma73_step
    (b : GoodBONG q L (n + 2)) (i : Fin (n + 1))
    (hi : i.1 + 1 < n + 1)
    (heq : b.alphaLeftEndpoint i =
      b.alphaLeftEndpoint ⟨i.1 + 1, hi⟩) :
    Lemma73StepConsequences b i hi := by
  let next : Fin (n + 1) := ⟨i.1 + 1, hi⟩
  have hnextCast : next.castSucc = i.succ := by
    apply Fin.ext
    rfl
  have heq' : (b.order i.castSucc : ℚ) + b.alphaValue i =
      (b.order i.succ : ℚ) + b.alphaValue next := by
    unfold alphaLeftEndpoint at heq
    change (b.order i.castSucc : ℚ) + b.alphaValue i =
      (b.order next.castSucc : ℚ) + b.alphaValue next at heq
    rwa [hnextCast] at heq
  have hcurrentHalf := b.alphaValue_le_halfGapValue i
  have hnextHalf := b.alphaValue_le_halfGapValue next
  have hgood : b.order i.castSucc ≤ b.order next.succ := by
    let k : Fin (n + 2) := ⟨i.1, by omega⟩
    have hk : k.1 + 2 < n + 2 := by simp only [k]; omega
    have hg := b.good k hk
    change b.order i.castSucc ≤ b.order next.succ at hg
    exact hg
  have hgapLower : -(2 * (ramificationIndex K : Int)) ≤ b.orderGap i := by
    have hg := b.toBONG.adjacentOrderGap_ge_neg_two_mul_e i.castSucc
      (Nat.succ_lt_succ i.isLt)
    change -(2 * (ramificationIndex K : Int)) ≤ b.orderGap i at hg
    exact hg
  by_cases hcurrent : b.alphaValue i = b.halfGapValue i
  · have hnextNonnegative := (b.beli2009Lemma27_i next).1
    have hgapLe : b.orderGap i ≤ 2 * (ramificationIndex K : Int) := by
      have hgapLeQ : (b.orderGap i : ℚ) ≤
          2 * (ramificationIndex K : ℚ) := by
        unfold halfGapValue at hcurrent
        unfold orderGap at hcurrent heq'
        push_cast at hcurrent heq'
        change 0 ≤ b.alphaValue next at hnextNonnegative
        unfold orderGap
        push_cast
        linarith
      exact_mod_cast hgapLeQ
    have hgapEven : Even (b.orderGap i) := by
      apply Int.not_odd_iff_even.mp
      intro hodd
      have halphaGap := (b.beli2009Lemma27_iii i hgapLe).2.mpr (Or.inr hodd)
      unfold halfGapValue at hcurrent
      rw [halphaGap] at hcurrent
      push_cast at hcurrent
      have hgapEq : b.orderGap i =
          2 * (ramificationIndex K : Int) := by
        exact_mod_cast (show (b.orderGap i : ℚ) =
          2 * (ramificationIndex K : ℚ) by linarith)
      rcases hodd with ⟨z, hz⟩
      rw [hgapEq] at hz
      omega
    rcases b.halfGapValue_isRationalInteger_of_even i hgapEven with
      ⟨a, ha⟩
    have hcurrentA : b.alphaValue i = (a : ℚ) := hcurrent.trans ha
    have hnextEq : b.alphaValue next =
        ((a - b.orderGap i : Int) : ℚ) := by
      rw [hcurrentA] at heq'
      unfold orderGap at ⊢
      push_cast at heq' ⊢
      linarith
    have hmod : Int.ModEq 2 (a - b.orderGap i) a := by
      rcases hgapEven with ⟨c, hc⟩
      rw [Int.modEq_iff_dvd]
      refine ⟨c, ?_⟩
      omega
    have hcurrentLe :
        b.alphaValue i ≤ 2 * (ramificationIndex K : ℚ) := by
      rw [hcurrent]
      unfold halfGapValue
      have hgapLeQ : (b.orderGap i : ℚ) ≤
          2 * (ramificationIndex K : ℚ) := by
        exact_mod_cast hgapLe
      linarith
    have hnextLe :
        b.alphaValue next ≤ 2 * (ramificationIndex K : ℚ) := by
      have hgapLowerQ : -(2 * (ramificationIndex K : ℚ)) ≤
          (b.orderGap i : ℚ) := by
        exact_mod_cast hgapLower
      have haFormula : (a : ℚ) = (b.orderGap i : ℚ) / 2 +
          (ramificationIndex K : ℚ) := by
        simpa only [halfGapValue] using ha.symm
      rw [hnextEq]
      push_cast
      linarith
    exact {
      orderGap_even := hgapEven
      alpha_modEq := ⟨a - b.orderGap i, a, hnextEq, hcurrentA, hmod⟩
      currentAlpha_le := hcurrentLe
      nextAlpha_le := hnextLe
      currentGap_le := hgapLe
      nextGap_le := (b.alphaValue_le_twoE_iff_orderGap_le_twoE next).mp hnextLe }
  · have hcurrentLt : b.alphaValue i < b.halfGapValue i :=
      lt_of_le_of_ne hcurrentHalf hcurrent
    by_cases hnextEqHalf : b.alphaValue next = b.halfGapValue next
    · exfalso
      rw [hnextEqHalf] at heq'
      unfold halfGapValue orderGap at hcurrentLt heq'
      push_cast at hcurrentLt heq'
      rw [hnextCast] at heq'
      have hgoodQ : (b.order i.castSucc : ℚ) ≤
          (b.order next.succ : ℚ) := by exact_mod_cast hgood
      linarith
    · rcases b.beli2009Lemma27_iv i hcurrent with ⟨a, haOdd, ha⟩
      rcases b.beli2009Lemma27_iv next hnextEqHalf with
        ⟨c, hcOdd, hc⟩
      have hgapEq : b.orderGap i = a - c := by
        rw [ha, hc] at heq'
        unfold orderGap
        push_cast at heq' ⊢
        exact_mod_cast (show (b.order i.succ : ℚ) -
          b.order i.castSucc = (a : ℚ) - c by linarith)
      have hgapEven : Even (b.orderGap i) := by
        rw [hgapEq]
        exact haOdd.sub_odd hcOdd
      have hmod : Int.ModEq 2 c a := by
        rw [Int.modEq_iff_dvd]
        rcases hgapEven with ⟨d, hd⟩
        refine ⟨d, ?_⟩
        omega
      have hcurrentGapLt :
          b.orderGap i < 2 * (ramificationIndex K : Int) := by
        by_contra hnot
        have hlarge : 2 * (ramificationIndex K : Int) ≤ b.orderGap i := by
          omega
        exact hcurrent (b.beli2009Lemma27_ii i hlarge)
      have hnextGapLt :
          b.orderGap next < 2 * (ramificationIndex K : Int) := by
        by_contra hnot
        have hlarge : 2 * (ramificationIndex K : Int) ≤ b.orderGap next := by
          omega
        exact hnextEqHalf (b.beli2009Lemma27_ii next hlarge)
      have hcurrentLe :
          b.alphaValue i ≤ 2 * (ramificationIndex K : ℚ) :=
        (b.alphaValue_le_twoE_iff_orderGap_le_twoE i).mpr hcurrentGapLt.le
      have hnextLe :
          b.alphaValue next ≤ 2 * (ramificationIndex K : ℚ) :=
        (b.alphaValue_le_twoE_iff_orderGap_le_twoE next).mpr hnextGapLt.le
      exact {
        orderGap_even := hgapEven
        alpha_modEq := ⟨c, a, hc, ha, hmod⟩
        currentAlpha_le := hcurrentLe
        nextAlpha_le := hnextLe
        currentGap_le := hcurrentGapLt.le
        nextGap_le := hnextGapLt.le }

/-- The complete interval conclusions of Beli (2019), Lemma 7.3(i). -/
structure Lemma73LeftConsequences
    (b : GoodBONG q L (n + 2)) (i j : Fin (n + 1)) : Prop where
  order_modEq (k : Fin (n + 1)) (hik : i ≤ k) (hkj : k ≤ j) :
    Int.ModEq 2 (b.order k.castSucc) (b.order i.castSucc)
  alpha_modEq (k : Fin (n + 1)) (hik : i ≤ k) (hkj : k ≤ j) :
    RationalModEqTwo (b.alphaValue k) (b.alphaValue i)
  alpha_le (k : Fin (n + 1)) (hik : i ≤ k) (hkj : k ≤ j) :
    b.alphaValue k ≤ 2 * (ramificationIndex K : ℚ)
  gap_le (k : Fin (n + 1)) (hik : i ≤ k) (hkj : k ≤ j) :
    b.orderGap k ≤ 2 * (ramificationIndex K : Int)

/-- Beli (2019), Lemma 7.3(i). -/
theorem beli2019Lemma73_i
    (b : GoodBONG q L (n + 2)) (i j : Fin (n + 1)) (hij : i < j)
    (heq : b.alphaLeftEndpoint i = b.alphaLeftEndpoint j) :
    Lemma73LeftConsequences b i j := by
  have hmono := b.alphaLeftEndpoint_monotone
  have hplateau (k : Fin (n + 1)) (hik : i ≤ k) (hkj : k ≤ j) :
      b.alphaLeftEndpoint k = b.alphaLeftEndpoint i := by
    apply le_antisymm
    · rw [heq]
      exact hmono hkj
    · exact hmono hik
  have hstep (k : Fin (n + 1)) (hik : i ≤ k) (hkj : k < j) :
      Lemma73StepConsequences b k (by omega) := by
    let next : Fin (n + 1) := ⟨k.1 + 1, by omega⟩
    have hnexti : i ≤ next := by
      change i.1 ≤ next.1
      simp only [next]
      omega
    have hnextj : next ≤ j := by
      change next.1 ≤ j.1
      simp only [next]
      omega
    have hEq := (hplateau k hik hkj.le).trans
      (hplateau next hnexti hnextj).symm
    exact b.beli2019Lemma73_step k (by omega) hEq
  have hfirst := hstep i le_rfl hij
  refine {
    order_modEq := ?_
    alpha_modEq := ?_
    alpha_le := ?_
    gap_le := ?_ }
  · intro k hik hkj
    let orderAt : Nat → Int := fun t ↦
      if ht : t < n + 2 then b.order ⟨t, ht⟩ else 0
    have hchain := int_modEq_two_of_even_successive orderAt
      (i := i.1) (k := k.1) (by exact hik) (by
        intro t hit htk
        let kt : Fin (n + 1) := ⟨t, by omega⟩
        have hkti : i ≤ kt := by change i.1 ≤ kt.1; exact hit
        have hktj : kt < j := by
          change kt.1 < j.1
          simp only [kt]
          exact htk.trans_le hkj
        have hs := (hstep kt hkti hktj).orderGap_even
        change Even (b.order ⟨t + 1, by omega⟩ -
          b.order ⟨t, by omega⟩) at hs
        simpa [orderAt, show t < n + 2 by omega,
          show t + 1 < n + 2 by omega] using hs)
    have hkBound : k.1 < n + 2 := by omega
    have hiBound : i.1 < n + 2 := by omega
    simp only [orderAt, dif_pos hkBound, dif_pos hiBound] at hchain
    have hkEq : k.castSucc = (⟨k.1, hkBound⟩ : Fin (n + 2)) := by
      apply Fin.ext
      rfl
    have hiEq : i.castSucc = (⟨i.1, hiBound⟩ : Fin (n + 2)) := by
      apply Fin.ext
      rfl
    simpa only [hkEq, hiEq] using hchain
  · intro k hik hkj
    rcases hfirst.alpha_modEq with ⟨_, a, _, ha, _⟩
    let alphaAt : Nat → ℚ := fun t ↦
      if ht : t < n + 1 then b.alphaValue ⟨t, ht⟩ else 0
    have hiAt : IsRationalInteger (alphaAt i.1) := by
      simpa only [alphaAt, dif_pos i.isLt] using
        (show IsRationalInteger (b.alphaValue i) from ⟨a, ha⟩)
    have hchain := rationalModEqTwo_of_successive alphaAt
      (i := i.1) (k := k.1) (by exact hik) hiAt (by
        intro t hit htk
        let kt : Fin (n + 1) := ⟨t, by omega⟩
        have hkti : i ≤ kt := by change i.1 ≤ kt.1; exact hit
        have hktj : kt < j := by
          change kt.1 < j.1
          simp only [kt]
          exact htk.trans_le hkj
        have hs := (hstep kt hkti hktj).alpha_modEq
        change RationalModEqTwo (b.alphaValue ⟨t + 1, by omega⟩)
          (b.alphaValue ⟨t, by omega⟩) at hs
        have htBound : t < n + 1 := by omega
        have htsBound : t + 1 < n + 1 := by omega
        simpa only [alphaAt, dif_pos htsBound, dif_pos htBound] using hs)
    have hkBound : k.1 < n + 1 := k.isLt
    have hiBound : i.1 < n + 1 := i.isLt
    simp only [alphaAt, dif_pos hkBound, dif_pos hiBound] at hchain
    convert hchain using 1 <;> apply Fin.ext <;> rfl
  · intro k hik hkj
    by_cases hki : k = i
    · subst k
      exact hfirst.currentAlpha_le
    · let t : Nat := k.1 - 1
      have ht : t + 1 = k.1 := by dsimp [t]; omega
      have hit : i.1 ≤ t := by dsimp [t]; omega
      have htj : t < j.1 := by dsimp [t]; omega
      let kt : Fin (n + 1) := ⟨t, htj.trans j.isLt⟩
      have hs := hstep kt (by change i.1 ≤ kt.1; exact hit)
        (by change kt.1 < j.1; exact htj)
      have hnext := hs.nextAlpha_le
      have hbound : kt.1 + 1 < n + 1 := by
        change t + 1 < n + 1
        rw [ht]
        exact k.isLt
      have hindex : (⟨kt.1 + 1, hbound⟩ : Fin (n + 1)) = k := by
        apply Fin.ext
        change kt.1 + 1 = k.1
        simpa only [kt] using ht
      rw [hindex] at hnext
      exact hnext
  · intro k hik hkj
    by_cases hki : k = i
    · subst k
      exact hfirst.currentGap_le
    · let t : Nat := k.1 - 1
      have ht : t + 1 = k.1 := by dsimp [t]; omega
      have hit : i.1 ≤ t := by dsimp [t]; omega
      have htj : t < j.1 := by dsimp [t]; omega
      let kt : Fin (n + 1) := ⟨t, htj.trans j.isLt⟩
      have hs := hstep kt (by change i.1 ≤ kt.1; exact hit)
        (by change kt.1 < j.1; exact htj)
      have hnext := hs.nextGap_le
      have hbound : kt.1 + 1 < n + 1 := by
        change t + 1 < n + 1
        rw [ht]
        exact k.isLt
      have hindex : (⟨kt.1 + 1, hbound⟩ : Fin (n + 1)) = k := by
        apply Fin.ext
        change kt.1 + 1 = k.1
        simpa only [kt] using ht
      rw [hindex] at hnext
      exact hnext

/-- The complete interval conclusions of Beli (2019), Lemma 7.3(ii). -/
structure Lemma73RightConsequences
    (b : GoodBONG q L (n + 2)) (i j : Fin (n + 1)) : Prop where
  order_modEq (k : Fin (n + 1)) (hik : i ≤ k) (hkj : k ≤ j) :
    Int.ModEq 2 (b.order k.succ) (b.order i.succ)
  alpha_modEq (k : Fin (n + 1)) (hik : i ≤ k) (hkj : k ≤ j) :
    RationalModEqTwo (b.alphaValue k) (b.alphaValue i)
  alpha_le (k : Fin (n + 1)) (hik : i ≤ k) (hkj : k ≤ j) :
    b.alphaValue k ≤ 2 * (ramificationIndex K : ℚ)
  gap_le (k : Fin (n + 1)) (hik : i ≤ k) (hkj : k ≤ j) :
    b.orderGap k ≤ 2 * (ramificationIndex K : Int)

/-- Beli (2019), Lemma 7.3(ii), obtained from part (i) by reverse duality. -/
theorem beli2019Lemma73_ii
    [BONGStructuralLaws.{u, v} K]
    (b : GoodBONG q L (n + 2)) (i j : Fin (n + 1)) (hij : i < j)
    (heq : b.alphaRightEndpoint i = b.alphaRightEndpoint j) :
    Lemma73RightConsequences b i j := by
  rcases b.exists_reverseDual_with_alpha with
    ⟨c, _, _, horders, halphas⟩
  have horderFormula (k : Fin (n + 1)) :
      c.order (Fin.rev k).castSucc = -b.order k.succ := by
    rw [horders, Fin.rev_castSucc, Fin.rev_rev]
  have halphaFormula (k : Fin (n + 1)) :
      c.alphaValue (Fin.rev k) = b.alphaValue k := by
    rw [halphas, Fin.rev_rev]
  have hgapFormula (k : Fin (n + 1)) :
      c.orderGap (Fin.rev k) = b.orderGap k := by
    unfold orderGap
    rw [horders, horders, Fin.rev_succ, Fin.rev_castSucc, Fin.rev_rev]
    ring
  have hleftFormula (k : Fin (n + 1)) :
      c.alphaLeftEndpoint (Fin.rev k) = b.alphaRightEndpoint k := by
    unfold alphaLeftEndpoint alphaRightEndpoint
    rw [horderFormula, halphaFormula]
    push_cast
    ring
  let ri : Fin (n + 1) := Fin.rev i
  let rj : Fin (n + 1) := Fin.rev j
  have hrji : rj < ri := by
    change Fin.rev j < Fin.rev i
    exact Fin.rev_lt_rev.mpr hij
  have hcEq : c.alphaLeftEndpoint rj = c.alphaLeftEndpoint ri := by
    rw [show rj = Fin.rev j by rfl, show ri = Fin.rev i by rfl,
      hleftFormula, hleftFormula]
    exact heq.symm
  have hc := c.beli2019Lemma73_i rj ri hrji hcEq
  have hcOrderBase := hc.order_modEq ri hrji.le le_rfl
  have hcAlphaBase := hc.alpha_modEq ri hrji.le le_rfl
  refine {
    order_modEq := ?_
    alpha_modEq := ?_
    alpha_le := ?_
    gap_le := ?_ }
  · intro k hik hkj
    have hrjk : rj ≤ Fin.rev k := by
      change Fin.rev j ≤ Fin.rev k
      exact Fin.rev_le_rev.mpr hkj
    have hrki : Fin.rev k ≤ ri := by
      change Fin.rev k ≤ Fin.rev i
      exact Fin.rev_le_rev.mpr hik
    have hkOrder := hc.order_modEq (Fin.rev k) hrjk hrki
    have hneg := hkOrder.trans hcOrderBase.symm
    rw [horderFormula k, horderFormula i] at hneg
    simpa using hneg.neg
  · intro k hik hkj
    have hrjk : rj ≤ Fin.rev k := by
      change Fin.rev j ≤ Fin.rev k
      exact Fin.rev_le_rev.mpr hkj
    have hrki : Fin.rev k ≤ ri := by
      change Fin.rev k ≤ Fin.rev i
      exact Fin.rev_le_rev.mpr hik
    have hkAlpha := hc.alpha_modEq (Fin.rev k) hrjk hrki
    have hki := hkAlpha.trans hcAlphaBase.symm
    rwa [halphaFormula k, halphaFormula i] at hki
  · intro k hik hkj
    have hrjk : rj ≤ Fin.rev k := by
      change Fin.rev j ≤ Fin.rev k
      exact Fin.rev_le_rev.mpr hkj
    have hrki : Fin.rev k ≤ ri := by
      change Fin.rev k ≤ Fin.rev i
      exact Fin.rev_le_rev.mpr hik
    have hkAlpha := hc.alpha_le (Fin.rev k) hrjk hrki
    rwa [halphaFormula k] at hkAlpha
  · intro k hik hkj
    have hrjk : rj ≤ Fin.rev k := by
      change Fin.rev j ≤ Fin.rev k
      exact Fin.rev_le_rev.mpr hkj
    have hrki : Fin.rev k ≤ ri := by
      change Fin.rev k ≤ Fin.rev i
      exact Fin.rev_le_rev.mpr hik
    have hkGap := hc.gap_le (Fin.rev k) hrjk hrki
    rwa [hgapFormula k] at hkGap

end BONG.GoodBONG

end Bong
