/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2022ClassicLemma42
import Bong.Bong.He2022ClassicLemma211
import Bong.Bong.Beli2019CappedDefectSharp
import Bong.Bong.HeHu2022Lemma313
import Bong.Dyadic.HilbertNondegeneracyProof

/-!
# He (2024), Lemma 4.3

This file formalizes the two exceptional central-condition obstructions used
in the necessity proof of Lemma 4.5.  The two `H` rows and the two `C` rows
remain literal exact good-BONG models, so the conclusion records which
published test fails rather than replacing it by an abstract existence claim.
-/

namespace Bong

open Dyadic AlternatingEndpointTower

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG.GoodBONG

/-- The terminal central index `i=n+1` used in Lemma 4.3, in the
repository's zero-based representation-index convention. -/
def he2022ClassicLemma43Index {m : Nat} (t : Nat)
    (hSource : 2 * t + 4 <= m + 3) :
    CentralRepresentationIndex (m + 3) (2 * t + 2) where
  val := 2 * t + 3
  one_lt := by omega
  lt_large := by omega
  le_small_succ := by omega

/-- If the numerical trigger holds for two targets but their required
prefix representations cannot both hold, condition (iii) fails for at
least one target. -/
theorem not_both_heClassicPublishedCentralConditionAt_of_triggers
    {m n₁ n₂ : Nat}
    {W₁ W₂ : Type u} [AddCommGroup W₁] [Module K W₁]
    [AddCommGroup W₂] [Module K W₂]
    {r₁ : QuadraticSpace K W₁} {r₂ : QuadraticSpace K W₂}
    {M₁ : Lattice K W₁} {M₂ : Lattice K W₂}
    (a : GoodBONG q L (m + 2))
    (b₁ : GoodBONG r₁ M₁ (n₁ + 2))
    (b₂ : GoodBONG r₂ M₂ (n₂ + 2))
    (i₁ : CentralRepresentationIndex (m + 2) (n₁ + 2))
    (i₂ : CentralRepresentationIndex (m + 2) (n₂ + 2))
  (htrigger₁ : a.centralDefectTrigger b₁ i₁)
  (htrigger₂ : a.centralDefectTrigger b₂ i₂)
  (hnotBoth : ¬ (DiagonalRepresents
        (b₁.prefixValues (i₁.val - 1) (by
          have := i₁.le_small_succ
          omega))
        (a.prefixValues i₁.val (by
          have := i₁.lt_large
          omega)) ∧
      DiagonalRepresents
        (b₂.prefixValues (i₂.val - 1) (by
          have := i₂.le_small_succ
          omega))
        (a.prefixValues i₂.val (by
          have := i₂.lt_large
          omega)))) :
    ¬ a.HeClassicPublishedCentralConditionAt b₁ i₁ ∨
      ¬ a.HeClassicPublishedCentralConditionAt b₂ i₂ := by
  by_contra hboth
  push Not at hboth
  exact hnotBoth ⟨hboth.1 htrigger₁, hboth.2 htrigger₂⟩

/-- The first `pairs` blocks of an exceptional row have product
`(-1)^pairs`, independently of the final parameter. -/
theorem heClassicEvenH_prefixProduct_even_general
    (pairs : Nat) (c : Kˣ)
    (hcClass : c = 1 ∨
      c = (Dyadic.dyadicDiscriminantClassLawsProved
        (K := K)).discriminantUnit)
    (hcOrder : ordUnit K c = 0)
    (j : Nat) (hj : j <= pairs) :
    let b := heClassicEvenHGoodBONG (K := K) pairs c hcClass hcOrder
    b.prefixProduct (2 * j) = (-1 : Kˣ) ^ j := by
  dsimp only
  let b := heClassicEvenHGoodBONG (K := K) pairs c hcClass hcOrder
  induction j with
  | zero =>
      simpa only [Nat.mul_zero, pow_zero, GoodBONG.prefixProduct] using
        b.toBONG.prefixProduct_zero
  | succ j ih =>
      have hjlt : j < pairs := by omega
      have hevenBound : 2 * j < 2 * pairs + 2 := by omega
      have hoddBound : 2 * j + 1 < 2 * pairs + 2 := by omega
      have hevenBefore : 2 * j < 2 * pairs + 1 := by omega
      have hoddBefore : 2 * j + 1 < 2 * pairs + 1 := by omega
      unfold GoodBONG.prefixProduct at ih ⊢
      rw [show 2 * (j + 1) = (2 * j + 1) + 1 by omega,
        b.toBONG.prefixProduct_succ (2 * j + 1) hoddBound,
        b.toBONG.prefixProduct_succ (2 * j) hevenBound,
        ih (by omega)]
      have hevenValue : b.toBONG.valueUnit
          (⟨2 * j, hevenBound⟩ : Fin (2 * pairs + 2)) =
          uniformizerPowerUnit K (ramificationIndex K : Int) := by
        change b.valueUnit _ = _
        simp only [b, heClassicEvenHGoodBONG,
          heHuExactGoodBONG_valueUnit]
        rw [heClassicEvenH_beforeLast pairs c _ hevenBefore]
        exact heClassicScaledHyperbolicTower_even
          (⟨j, by omega⟩ : Fin (pairs + 1))
      have hoddValue : b.toBONG.valueUnit
          (⟨2 * j + 1, hoddBound⟩ : Fin (2 * pairs + 2)) =
          -(uniformizerPowerUnit K (-(ramificationIndex K : Int))) := by
        change b.valueUnit _ = _
        simp only [b, heClassicEvenHGoodBONG,
          heHuExactGoodBONG_valueUnit]
        rw [heClassicEvenH_beforeLast pairs c _ hoddBefore]
        exact heClassicScaledHyperbolicTower_odd
          (⟨j, by omega⟩ : Fin (pairs + 1))
      rw [hevenValue, hoddValue, pow_succ]
      unfold uniformizerPowerUnit
      rw [mul_neg, mul_assoc, ← zpow_add]
      simp

/-- The complete product of `H_e^(2*pairs+2)(c)` is its parameter times
the usual even-rank sign. -/
theorem heClassicEvenH_prefixProduct_full
    (pairs : Nat) (c : Kˣ)
    (hcClass : c = 1 ∨
      c = (Dyadic.dyadicDiscriminantClassLawsProved
        (K := K)).discriminantUnit)
    (hcOrder : ordUnit K c = 0) :
    let b := heClassicEvenHGoodBONG (K := K) pairs c hcClass hcOrder
    b.prefixProduct (2 * pairs + 2) = (-1 : Kˣ) ^ (pairs + 1) * c := by
  dsimp only
  let b := heClassicEvenHGoodBONG (K := K) pairs c hcClass hcOrder
  have hp := heClassicEvenH_prefixProduct_even_general
    (K := K) pairs c hcClass hcOrder pairs le_rfl
  have heven : b.toBONG.valueUnit
      (⟨2 * pairs, by omega⟩ : Fin (2 * pairs + 2)) =
      uniformizerPowerUnit K (ramificationIndex K : Int) := by
    change b.valueUnit _ = _
    simp only [b, heClassicEvenHGoodBONG, heHuExactGoodBONG_valueUnit]
    have hbefore : (⟨2 * pairs, by omega⟩ : Fin (2 * pairs + 2)).val <
        2 * pairs + 1 := Nat.lt_succ_self _
    rw [heClassicEvenH_beforeLast pairs c _ hbefore]
    exact heClassicScaledHyperbolicTower_even
      (⟨pairs, by omega⟩ : Fin (pairs + 1))
  have hlast : b.toBONG.valueUnit
      (⟨2 * pairs + 1, by omega⟩ : Fin (2 * pairs + 2)) =
      -(c * uniformizerPowerUnit K (-(ramificationIndex K : Int))) := by
    change b.valueUnit _ = _
    simp only [b, heClassicEvenHGoodBONG, heHuExactGoodBONG_valueUnit]
    exact heClassicEvenH_last pairs c
  unfold GoodBONG.prefixProduct at hp ⊢
  change b.toBONG.prefixProduct ((2 * pairs + 1) + 1) = _
  rw [b.toBONG.prefixProduct_succ (2 * pairs + 1) (by omega),
    b.toBONG.prefixProduct_succ (2 * pairs) (by omega), hp,
    heven, hlast, pow_succ]
  apply Units.ext
  simp [uniformizerPowerUnit, mul_assoc, mul_left_comm, mul_comm]

/-- At full target rank the self capped defect of an exceptional row is
exactly the defect of its parameter. -/
theorem heClassicEvenH_fullSelfDefect
    (pairs : Nat) (c : Kˣ)
    (hcClass : c = 1 ∨
      c = (Dyadic.dyadicDiscriminantClassLawsProved
        (K := K)).discriminantUnit)
    (hcOrder : ordUnit K c = 0) :
    let b := heClassicEvenHGoodBONG (K := K) pairs c hcClass hcOrder
    b.truncatedPrefixDefect b ((-1) ^ (pairs + 1)) 0
        (2 * pairs + 2) = defectOrder (K := K) c := by
  dsimp only
  let b := heClassicEvenHGoodBONG (K := K) pairs c hcClass hcOrder
  unfold truncatedPrefixDefect
  rw [b.prefixAlphaCap_zero, b.prefixAlphaCap_last,
    min_eq_left (le_top), GoodBONG.prefixProduct,
    b.toBONG.prefixProduct_zero]
  rw [heClassicEvenH_prefixProduct_full pairs c hcClass hcOrder]
  simp only [mul_one]
  have hsign : (-1 : Kˣ) ^ (pairs + 1) *
      ((-1 : Kˣ) ^ (pairs + 1) * c) = c := by
    rw [← mul_assoc, ← pow_add]
    have heven : Even ((pairs + 1) + (pairs + 1)) :=
      ⟨pairs + 1, by omega⟩
    rw [Even.neg_one_pow heven]
    simp
  rw [hsign, min_eq_left le_top]

/-- The last entry of every exceptional `H` row has order `-e`. -/
theorem heClassicEvenH_lastOrder
    (pairs : Nat) (c : Kˣ)
    (hcClass : c = 1 ∨
      c = (Dyadic.dyadicDiscriminantClassLawsProved
        (K := K)).discriminantUnit)
    (hcOrder : ordUnit K c = 0) :
    let b := heClassicEvenHGoodBONG (K := K) pairs c hcClass hcOrder
    b.order (⟨2 * pairs + 1, by omega⟩ : Fin (2 * pairs + 2)) =
      -(ramificationIndex K : Int) := by
  dsimp only
  let b := heClassicEvenHGoodBONG (K := K) pairs c hcClass hcOrder
  simp only [heClassicEvenHGoodBONG, heHuExactGoodBONG_order]
  rw [heClassicEvenH_order pairs c hcOrder]
  exact if_neg (Nat.not_even_two_mul_add_one pairs)

/-- The domination-principle estimate used twice in Lemma 4.3(i).  Its
left side is the minimum of the source signed-prefix defect and the full
self-defect of `H_e^n(c)`; its right side is exactly the second capped
defect in condition (iii) at `i=n+1`. -/
theorem heClassicEvenH_centralCurrentDefect_lower
    {m : Nat} (pairs : Nat) (a : GoodBONG q L (m + 3))
    (hSource : 2 * pairs + 4 <= m + 3)
    (c : Kˣ)
    (hcClass : c = 1 ∨
      c = (Dyadic.dyadicDiscriminantClassLawsProved
        (K := K)).discriminantUnit)
    (hcOrder : ordUnit K c = 0) :
    let b := heClassicEvenHGoodBONG (K := K) pairs c hcClass hcOrder
    let i := he2022ClassicLemma43Index pairs hSource
    min
        (a.truncatedPrefixDefect a ((-1) ^ (pairs + 2))
          0 (2 * pairs + 4))
        (defectOrder (K := K) c) <=
      a.centralCurrentDefect b i := by
  dsimp only
  let b := heClassicEvenHGoodBONG (K := K) pairs c hcClass hcOrder
  let sourceSign : Kˣ := (-1) ^ (pairs + 2)
  let targetSign : Kˣ := (-1) ^ (pairs + 1)
  have hdom := a.truncatedPrefixDefect_domination a b
    sourceSign targetSign (2 * pairs + 4) 0 (2 * pairs + 2)
  have hsource :
      a.truncatedPrefixDefect a sourceSign (2 * pairs + 4) 0 =
        a.truncatedPrefixDefect a sourceSign 0 (2 * pairs + 4) :=
    a.truncatedPrefixDefect_comm a sourceSign (2 * pairs + 4) 0
  have htarget :
      a.truncatedPrefixDefect b targetSign 0 (2 * pairs + 2) =
        defectOrder (K := K) c := by
    rw [a.truncatedPrefixDefect_zero_left_eq_self b]
    exact heClassicEvenH_fullSelfDefect pairs c hcClass hcOrder
  have hsign : sourceSign * targetSign = (-1 : Kˣ) := by
    dsimp only [sourceSign, targetSign]
    rw [← pow_add]
    exact (show Odd ((pairs + 2) + (pairs + 1)) from
      ⟨pairs + 1, by omega⟩).neg_one_pow
  rw [hsource, htarget, hsign] at hdom
  unfold centralCurrentDefect
  dsimp only [he2022ClassicLemma43Index]
  have hplus : 2 * pairs + 3 + 1 = 2 * pairs + 4 := by omega
  have hminus : 2 * pairs + 3 - 1 = 2 * pairs + 2 := by omega
  rw [hplus, hminus]
  exact hdom

/-- `J1'_E(n)` propagates the zero source order two places forward to the
nonnegative order needed at the terminal central index. -/
theorem he2022ClassicLemma43_sourceNextOrder_nonneg
    {m : Nat} (pairs : Nat) (a : GoodBONG q L (m + 3))
    (hSource : 2 * pairs + 4 <= m + 3)
    (hJ1 : a.HeClassicJ1EPrime (2 * pairs + 2) (by omega)) :
    0 <= a.order ⟨2 * pairs + 3, by omega⟩ := by
  have hzero : a.order (⟨2 * pairs + 1, by omega⟩ : Fin (m + 3)) = 0 := by
    let j : Fin (2 * pairs + 3) := ⟨2 * pairs + 1, by omega⟩
    simpa only [j] using hJ1.1 j
  have htwo := a.orderSequence.twoStep (2 * pairs + 1) (by omega)
  change a.order (⟨2 * pairs + 1, by omega⟩ : Fin (m + 3)) <=
    a.order ⟨2 * pairs + 3, by omega⟩ at htwo
  simpa only [hzero] using htwo

/-- Numerical part of Lemma 4.3(i): whenever the source capped defect is
strictly below `2e`, both exceptional `H` rows satisfy the printed trigger. -/
theorem he2022ClassicLemma43_H_trigger_of_capped_lt_twoE
    {m : Nat} (pairs : Nat) (a : GoodBONG q L (m + 3))
    (hSource : 2 * pairs + 4 <= m + 3)
    (hJ1 : a.HeClassicJ1EPrime (2 * pairs + 2) (by omega))
    (heOne : ramificationIndex K = 1)
    (c : Kˣ)
    (hcClass : c = 1 ∨
      c = (Dyadic.dyadicDiscriminantClassLawsProved
        (K := K)).discriminantUnit)
    (hcOrder : ordUnit K c = 0)
    (hDefectLower :
      a.truncatedPrefixDefect a ((-1) ^ (pairs + 2))
          0 (2 * pairs + 4) <= defectOrder (K := K) c)
    (hSum :
      (1 : WithTop ℚ) <
        ((((a.order ⟨2 * pairs + 3, by omega⟩ : Int) : ℚ) :
            WithTop ℚ)) +
          a.truncatedPrefixDefect a ((-1) ^ (pairs + 2))
            0 (2 * pairs + 4)) :
    let b := heClassicEvenHGoodBONG (K := K) pairs c hcClass hcOrder
    a.centralDefectTrigger b (he2022ClassicLemma43Index pairs hSource) := by
  dsimp only
  let b := heClassicEvenHGoodBONG (K := K) pairs c hcClass hcOrder
  let i := he2022ClassicLemma43Index pairs hSource
  let D : WithTop ℚ :=
    a.truncatedPrefixDefect a ((-1) ^ (pairs + 2)) 0 (2 * pairs + 4)
  have hRnonneg : 0 <= a.order ⟨2 * pairs + 3, by omega⟩ :=
    a.he2022ClassicLemma43_sourceNextOrder_nonneg pairs hSource hJ1
  have hcurrentLower : D <= a.centralCurrentDefect b i := by
    have hmin : min D (defectOrder (K := K) c) = D :=
      min_eq_left hDefectLower
    rw [← hmin]
    exact a.heClassicEvenH_centralCurrentDefect_lower pairs hSource c
      hcClass hcOrder
  have hpreviousNonneg : (0 : WithTop ℚ) <=
      a.centralPreviousDefect b i := by
    unfold centralPreviousDefect
    exact a.truncatedPrefixDefect_nonneg b (-1) i.val (i.val - 2)
  unfold centralDefectTrigger
  constructor
  · change b.order ⟨2 * pairs + 1, by omega⟩ <
      a.order ⟨2 * pairs + 3, by omega⟩
    rw [heClassicEvenH_lastOrder pairs c hcClass hcOrder, heOne]
    omega
  · have hDgt :
        ((((1 : ℚ) -
          (a.order ⟨2 * pairs + 3, by omega⟩ : ℚ) : ℚ)) :
            WithTop ℚ) < D := by
      have hSum' := hSum
      change (1 : WithTop ℚ) <
        ((((a.order ⟨2 * pairs + 3, by omega⟩ : Int) : ℚ) :
          WithTop ℚ)) + D at hSum'
      by_cases htop : D = ⊤
      · rw [htop]
        exact WithTop.coe_lt_top _
      · obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp htop
        rw [← hd]
        apply WithTop.coe_lt_coe.mpr
        rw [← hd] at hSum'
        norm_cast at hSum'
        linarith
    have hthresholdCurrent :
        ((((1 : ℚ) -
          (a.order ⟨2 * pairs + 3, by omega⟩ : ℚ) : ℚ)) :
            WithTop ℚ) < a.centralCurrentDefect b i :=
      hDgt.trans_le hcurrentLower
    have hbOrder : b.order ⟨i.val - 2, by
        have := i.one_lt
        have := i.le_small_succ
        omega⟩ = -1 := by
      have hindex :
          (⟨i.val - 2, by
            have := i.one_lt
            have := i.le_small_succ
            omega⟩ : Fin (2 * pairs + 2)) =
            ⟨2 * pairs + 1, by omega⟩ := by
        apply Fin.ext
        dsimp only [i, he2022ClassicLemma43Index]
        omega
      rw [hindex, heClassicEvenH_lastOrder pairs c hcClass hcOrder, heOne]
      norm_num
    have haOrder : a.order ⟨i.val, by
        have := i.lt_large
        omega⟩ = a.order ⟨2 * pairs + 3, by omega⟩ := by
      congr 1
    calc
      ((2 * (ramificationIndex K : ℚ) +
          (b.order ⟨i.val - 2, by
            have := i.one_lt
            have := i.le_small_succ
            omega⟩ : ℚ) -
          (a.order ⟨i.val, by
            have := i.lt_large
            omega⟩ : ℚ) : ℚ) : WithTop ℚ) =
          ((((1 : ℚ) -
            (a.order ⟨2 * pairs + 3, by omega⟩ : ℚ) : ℚ)) :
              WithTop ℚ) := by
        rw [hbOrder, haOrder, heOne]
        norm_num
      _ < a.centralCurrentDefect b i := hthresholdCurrent
      _ = 0 + a.centralCurrentDefect b i := by simp
      _ <= a.centralPreviousDefect b i + a.centralCurrentDefect b i :=
        add_le_add hpreviousNonneg le_rfl

/-- The second numerical branch of Lemma 4.3(i): if both the source capped
defect and the target parameter defect are at least `2e`, the same terminal
trigger follows directly from nonnegativity of `R_(n+2)`. -/
theorem he2022ClassicLemma43_H_trigger_of_twoE_le_capped
    {m : Nat} (pairs : Nat) (a : GoodBONG q L (m + 3))
    (hSource : 2 * pairs + 4 <= m + 3)
    (hJ1 : a.HeClassicJ1EPrime (2 * pairs + 2) (by omega))
    (heOne : ramificationIndex K = 1)
    (c : Kˣ)
    (hcClass : c = 1 ∨
      c = (Dyadic.dyadicDiscriminantClassLawsProved
        (K := K)).discriminantUnit)
    (hcOrder : ordUnit K c = 0)
    (hCapped :
      (((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ)) <=
        a.truncatedPrefixDefect a ((-1) ^ (pairs + 2))
          0 (2 * pairs + 4))
    (hParameter :
      (((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ)) <=
        defectOrder (K := K) c) :
    let b := heClassicEvenHGoodBONG (K := K) pairs c hcClass hcOrder
    a.centralDefectTrigger b (he2022ClassicLemma43Index pairs hSource) := by
  dsimp only
  let b := heClassicEvenHGoodBONG (K := K) pairs c hcClass hcOrder
  let i := he2022ClassicLemma43Index pairs hSource
  let twoE : WithTop ℚ :=
    ((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ)
  have hRnonneg : 0 <= a.order ⟨2 * pairs + 3, by omega⟩ :=
    a.he2022ClassicLemma43_sourceNextOrder_nonneg pairs hSource hJ1
  have hmin : twoE <= min
      (a.truncatedPrefixDefect a ((-1) ^ (pairs + 2))
        0 (2 * pairs + 4))
      (defectOrder (K := K) c) := le_min hCapped hParameter
  have hcurrentLower : twoE <= a.centralCurrentDefect b i :=
    hmin.trans (a.heClassicEvenH_centralCurrentDefect_lower pairs hSource c
      hcClass hcOrder)
  have hthresholdTwoE :
      ((((1 : ℚ) -
        (a.order ⟨2 * pairs + 3, by omega⟩ : ℚ) : ℚ)) :
          WithTop ℚ) < twoE := by
    apply WithTop.coe_lt_coe.mpr
    have hRQ : (0 : ℚ) <=
        (a.order ⟨2 * pairs + 3, by omega⟩ : ℚ) := by
      exact_mod_cast hRnonneg
    rw [heOne]
    norm_num
    linarith
  have hcurrent :
      ((((1 : ℚ) -
        (a.order ⟨2 * pairs + 3, by omega⟩ : ℚ) : ℚ)) :
          WithTop ℚ) < a.centralCurrentDefect b i :=
    hthresholdTwoE.trans_le hcurrentLower
  have hpreviousNonneg : (0 : WithTop ℚ) <=
      a.centralPreviousDefect b i := by
    unfold centralPreviousDefect
    exact a.truncatedPrefixDefect_nonneg b (-1) i.val (i.val - 2)
  unfold centralDefectTrigger
  constructor
  · change b.order ⟨2 * pairs + 1, by omega⟩ <
      a.order ⟨2 * pairs + 3, by omega⟩
    rw [heClassicEvenH_lastOrder pairs c hcClass hcOrder, heOne]
    omega
  · have hbOrder : b.order ⟨i.val - 2, by
        have := i.one_lt
        have := i.le_small_succ
        omega⟩ = -1 := by
      have hindex :
          (⟨i.val - 2, by
            have := i.one_lt
            have := i.le_small_succ
            omega⟩ : Fin (2 * pairs + 2)) =
            ⟨2 * pairs + 1, by omega⟩ := by
        apply Fin.ext
        dsimp only [i, he2022ClassicLemma43Index]
        omega
      rw [hindex, heClassicEvenH_lastOrder pairs c hcClass hcOrder, heOne]
      norm_num
    have haOrder : a.order ⟨i.val, by
        have := i.lt_large
        omega⟩ = a.order ⟨2 * pairs + 3, by omega⟩ := by
      congr 1
    calc
      ((2 * (ramificationIndex K : ℚ) +
          (b.order ⟨i.val - 2, by
            have := i.one_lt
            have := i.le_small_succ
            omega⟩ : ℚ) -
          (a.order ⟨i.val, by
            have := i.lt_large
            omega⟩ : ℚ) : ℚ) : WithTop ℚ) =
          ((((1 : ℚ) -
            (a.order ⟨2 * pairs + 3, by omega⟩ : ℚ) : ℚ)) :
              WithTop ℚ) := by
        rw [hbOrder, haOrder, heOne]
        norm_num
      _ < a.centralCurrentDefect b i := hcurrent
      _ = 0 + a.centralCurrentDefect b i := by simp
      _ <= a.centralPreviousDefect b i + a.centralCurrentDefect b i :=
        add_le_add hpreviousNonneg le_rfl

/-! ## The two incompatible full prefixes in Lemma 4.3(i) -/

/-- Every standard hyperbolic block is isometric to the corresponding
`H_e` block. -/
theorem standardHyperbolicEndpointTower_represents_heClassicScaled
    (pairs : Nat) :
    DiagonalRepresents
      (diagonalUnitCoefficients
        (standardHyperbolicEndpointTower (K := K) pairs))
      (diagonalUnitCoefficients
        (heClassicScaledHyperbolicTower (K := K)
          (ramificationIndex K) pairs)) := by
  apply QuadraticSpace.diagonalRepresents_even_of_pair_signedRatioSquares
  · intro j
    rw [standardHyperbolicEndpointTower_even,
      standardHyperbolicEndpointTower_odd]
    refine ⟨1, ?_⟩
    simp
  · intro j
    rw [heClassicScaledHyperbolicTower_even,
      heClassicScaledHyperbolicTower_odd]
    refine ⟨uniformizerPowerUnit K (ramificationIndex K : Int), ?_⟩
    apply Units.ext
    simp [uniformizerPowerUnit, div_eq_mul_inv]

/-- The first canonical row of Lemma 2.11 represents the literal
`H_e^n(1)` row. -/
theorem heClassicLemma211First_represents_evenHOne
    (pairs : Nat) (_hOneOrder : ordUnit K (1 : Kˣ) = 0) :
    DiagonalRepresents
      (diagonalUnitCoefficients (heClassicLemma211First (K := K) pairs))
      (diagonalUnitCoefficients (heClassicEvenH (K := K) pairs 1)) := by
  have hhead :=
    standardHyperbolicEndpointTower_represents_heClassicScaled
      (K := K) pairs
  have htail : DiagonalRepresents
      (diagonalUnitCoefficients (heHuHyperbolicPair (K := K)))
      (diagonalUnitCoefficients
        ![uniformizerPowerUnit K (ramificationIndex K : Int),
          -((1 : Kˣ) * uniformizerPowerUnit K
            (-(ramificationIndex K : Int)))]) := by
    apply QuadraticSpace.finiteDiagonal_fin_two_diagonalRepresents_of_signedRatioSquares
    · refine ⟨1, ?_⟩
      simp [heHuHyperbolicPair]
    · refine ⟨uniformizerPowerUnit K (ramificationIndex K : Int), ?_⟩
      apply Units.ext
      simp [uniformizerPowerUnit, div_eq_mul_inv]
  have happ := DiagonalRepresents.appendBoth hhead htail
  simpa only [heClassicLemma211First, heClassicEvenH,
    diagonalUnitCoefficients_append] using happ

/-- When `e=1`, the second canonical row of Lemma 2.11 represents the
literal `H_e^n(Delta)` row. -/
theorem heClassicLemma211Second_represents_evenHDiscriminant
    (pairs : Nat) (heOne : ramificationIndex K = 1) :
    let delta := (Dyadic.dyadicDiscriminantClassLawsProved
      (K := K)).discriminantUnit
    DiagonalRepresents
      (diagonalUnitCoefficients (heClassicLemma211Second (K := K) pairs))
      (diagonalUnitCoefficients (heClassicEvenH (K := K) pairs delta)) := by
  dsimp only
  let delta := (Dyadic.dyadicDiscriminantClassLawsProved
    (K := K)).discriminantUnit
  have hhead :=
    standardHyperbolicEndpointTower_represents_heClassicScaled
      (K := K) pairs
  let sourceTail : Fin 2 → Kˣ := heClassicRamifiedBinary (K := K)
  let targetTail : Fin 2 → Kˣ :=
    ![uniformizerPowerUnit K (ramificationIndex K : Int),
      -(delta * uniformizerPowerUnit K
        (-(ramificationIndex K : Int)))]
  let multipliers : Fin 2 → Kˣ :=
    ![1, uniformizerPowerUnit K (1 : Int)]
  have hcoeff : ∀ i, sourceTail i = targetTail i * multipliers i ^ 2 := by
    intro i
    fin_cases i
    · change uniformizerPowerUnit K (1 : Int) =
        uniformizerPowerUnit K (ramificationIndex K : Int) * 1 ^ 2
      rw [heOne]
      simp
    · change -((uniformizerPowerUnit K (1 : Int)) * delta) =
        (-(delta * uniformizerPowerUnit K
          (-(ramificationIndex K : Int)))) *
            (uniformizerPowerUnit K (1 : Int)) ^ 2
      rw [heOne]
      apply Units.ext
      simp [delta, uniformizerPowerUnit, mul_comm]
      field_simp [uniformizer_ne_zero K]
  have htail :=
    Beli2009FinalRemarksProof.diagonalRepresents_of_pointwise_mul_square
      sourceTail targetTail multipliers hcoeff
  have happ := DiagonalRepresents.appendBoth hhead htail
  simpa only [heClassicLemma211Second, heClassicEvenH, sourceTail,
    targetTail, diagonalUnitCoefficients_append] using happ

/-- The full prefix of an exact exceptional good BONG is its displayed
coefficient row. -/
theorem heClassicEvenH_fullPrefixValues
    (pairs : Nat) (c : Kˣ)
    (hcClass : c = 1 ∨
      c = (Dyadic.dyadicDiscriminantClassLawsProved
        (K := K)).discriminantUnit)
    (hcOrder : ordUnit K c = 0) :
    let b := heClassicEvenHGoodBONG (K := K) pairs c hcClass hcOrder
    b.prefixValues (2 * pairs + 2) le_rfl =
      diagonalUnitCoefficients (heClassicEvenH (K := K) pairs c) := by
  dsimp only
  funext i
  change (((heClassicEvenHGoodBONG (K := K) pairs c hcClass hcOrder).valueUnit i :
    Kˣ) : K) = (heClassicEvenH (K := K) pairs c i : K)
  rw [heClassicEvenHGoodBONG, heHuExactGoodBONG_valueUnit]

/-- The source prefix `[a_1,...,a_(n+1)]` has unit determinant order under
`J1'_E(n)`. -/
theorem he2022ClassicLemma43_sourcePrefixDeterminantOrder
    {m : Nat} (pairs : Nat) (a : GoodBONG q L (m + 3))
    (hSource : 2 * pairs + 4 <= m + 3)
    (hJ1 : a.HeClassicJ1EPrime (2 * pairs + 2) (by omega)) :
    ordUnit K (diagonalUnitDeterminant
      (a.prefixValueUnits (2 * pairs + 3)
        (Nat.le_trans (by omega) hSource))) = 0 := by
  rw [a.diagonalUnitDeterminant_prefixValueUnits
      (2 * pairs + 3) (Nat.le_trans (by omega) hSource),
    a.ordUnit_prefixProduct_eq_orderSequence_prefixSum
      (2 * pairs + 3) (Nat.le_trans (by omega) hSource)]
  unfold BeliOrderSequence.prefixSum
  apply Finset.sum_eq_zero
  intro j hj
  simp only [Finset.mem_range] at hj
  rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence (by omega)]
  let i : Fin (2 * pairs + 3) := ⟨j, hj⟩
  change a.order ⟨j, by omega⟩ = 0
  simpa only [i] using hJ1.1 i

/-- Lemma 2.11(i) applied to the two literal `H` tests: the same source
prefix cannot represent both of them. -/
theorem he2022ClassicLemma43_H_notBothRepresents
    {m : Nat} (pairs : Nat) (a : GoodBONG q L (m + 3))
    (hSource : 2 * pairs + 4 <= m + 3)
    (hJ1 : a.HeClassicJ1EPrime (2 * pairs + 2) (by omega))
    (heOne : ramificationIndex K = 1) :
    let oneOrder : ordUnit K (1 : Kˣ) = 0 := by
      have h := ordUnit_mul K (1 : Kˣ) 1
      simp only [mul_one] at h
      omega
    let delta := (Dyadic.dyadicDiscriminantClassLawsProved
      (K := K)).discriminantUnit
    let deltaOrder : ordUnit K delta = 0 :=
      (isValuationUnit_iff_ordUnit_eq_zero K delta).1
        (Dyadic.dyadicDiscriminantClassLawsProved
          (K := K)).discriminant_isValuationUnit
    let bOne := heClassicEvenHGoodBONG (K := K) pairs 1
      (Or.inl rfl) oneOrder
    let bDelta := heClassicEvenHGoodBONG (K := K) pairs delta
      (Or.inr rfl) deltaOrder
    let i := he2022ClassicLemma43Index pairs hSource
    ¬ (DiagonalRepresents
        (bOne.prefixValues (i.val - 1) (by
          have := i.le_small_succ
          omega))
        (a.prefixValues i.val (by
          have := i.lt_large
          omega)) ∧
      DiagonalRepresents
        (bDelta.prefixValues (i.val - 1) (by
          have := i.le_small_succ
          omega))
        (a.prefixValues i.val (by
          have := i.lt_large
          omega))) := by
  dsimp only
  let oneOrder : ordUnit K (1 : Kˣ) = 0 := by
    have h := ordUnit_mul K (1 : Kˣ) 1
    simp only [mul_one] at h
    omega
  let delta := (Dyadic.dyadicDiscriminantClassLawsProved
    (K := K)).discriminantUnit
  let deltaOrder : ordUnit K delta = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K delta).1
      (Dyadic.dyadicDiscriminantClassLawsProved
        (K := K)).discriminant_isValuationUnit
  let bOne := heClassicEvenHGoodBONG (K := K) pairs 1
    (Or.inl rfl) oneOrder
  let bDelta := heClassicEvenHGoodBONG (K := K) pairs delta
    (Or.inr rfl) deltaOrder
  let i := he2022ClassicLemma43Index pairs hSource
  rintro ⟨hOne, hDelta⟩
  let sourceUnits := a.prefixValueUnits (2 * pairs + 3)
    (Nat.le_trans (by omega) hSource)
  have hdet : ordUnit K (diagonalUnitDeterminant sourceUnits) = 0 := by
    exact a.he2022ClassicLemma43_sourcePrefixDeterminantOrder pairs
      hSource hJ1
  have hOneNormal := heClassicLemma211First_represents_evenHOne
    (K := K) pairs oneOrder
  have hDeltaNormal :=
    heClassicLemma211Second_represents_evenHDiscriminant
      (K := K) pairs heOne
  let hs : i.val - 1 = 2 * pairs + 2 := by
    dsimp only [i, he2022ClassicLemma43Index]
    omega
  let ht : i.val = 2 * pairs + 3 := by rfl
  have hOneCast := heHuLemma43_diagonalRepresents_castLengths hs ht hOne
  have hDeltaCast := heHuLemma43_diagonalRepresents_castLengths hs ht hDelta
  have hOneTargetEq :
      (fun j : Fin (2 * pairs + 2) =>
        bOne.prefixValues (i.val - 1) (by
          have := i.le_small_succ
          omega) (Fin.cast hs.symm j)) =
        bOne.prefixValues (2 * pairs + 2) le_rfl := by
    funext j
    unfold prefixValues
    congr 1
  have hDeltaTargetEq :
      (fun j : Fin (2 * pairs + 2) =>
        bDelta.prefixValues (i.val - 1) (by
          have := i.le_small_succ
          omega) (Fin.cast hs.symm j)) =
        bDelta.prefixValues (2 * pairs + 2) le_rfl := by
    funext j
    unfold prefixValues
    congr 1
  have hsourceEq :
      (fun j : Fin (2 * pairs + 3) =>
        a.prefixValues i.val (by
          have := i.lt_large
          omega) (Fin.cast ht.symm j)) =
        a.prefixValues (2 * pairs + 3)
          (Nat.le_trans (by omega) hSource) := by
    funext j
    unfold prefixValues
    congr 1
  rw [hOneTargetEq, hsourceEq] at hOneCast
  rw [hDeltaTargetEq, hsourceEq] at hDeltaCast
  have hOneFull := heClassicEvenH_fullPrefixValues
    (K := K) pairs 1 (Or.inl rfl) oneOrder
  have hDeltaFull := heClassicEvenH_fullPrefixValues
    (K := K) pairs delta (Or.inr rfl) deltaOrder
  have hsourceFull := (a.diagonalUnitCoefficients_prefixValueUnits
    (2 * pairs + 3) (Nat.le_trans (by omega) hSource)).symm
  have hfirst : DiagonalRepresents
      (diagonalUnitCoefficients (heClassicLemma211First (K := K) pairs))
      (diagonalUnitCoefficients sourceUnits) := by
    rw [hOneFull, hsourceFull] at hOneCast
    exact hOneNormal.trans hOneCast
  have hsecond : DiagonalRepresents
      (diagonalUnitCoefficients (heClassicLemma211Second (K := K) pairs))
      (diagonalUnitCoefficients sourceUnits) := by
    rw [hDeltaFull, hsourceFull] at hDeltaCast
    exact hDeltaNormal.trans hDeltaCast
  exact (he2022ClassicLemma211i (K := K) pairs sourceUnits hdet)
    ⟨hfirst, hsecond⟩

/-- He, Lemma 4.3(i), with the disjunction printed in the publisher
version kept literally: either the raw signed-prefix defect is below `2e`,
or the capped signed-prefix defect is at least `2e`. -/
theorem he2022ClassicLemma43i
    {m : Nat} (pairs : Nat) (a : GoodBONG q L (m + 3))
    (hSource : 2 * pairs + 4 <= m + 3)
    (hJ1 : a.HeClassicJ1EPrime (2 * pairs + 2) (by omega))
    (heOne : ramificationIndex K = 1)
    (hSum :
      (1 : WithTop ℚ) <
        ((((a.order ⟨2 * pairs + 3, by omega⟩ : Int) : ℚ) :
            WithTop ℚ)) +
          a.truncatedPrefixDefect a ((-1) ^ (pairs + 2))
            0 (2 * pairs + 4))
    (hBranch :
      defectOrder (K := K)
          (((-1 : Kˣ) ^ (pairs + 2)) *
            a.prefixProduct (2 * pairs + 4)) <
          (((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ)) ∨
        (((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ)) <=
          a.truncatedPrefixDefect a ((-1) ^ (pairs + 2))
            0 (2 * pairs + 4)) :
    let oneOrder : ordUnit K (1 : Kˣ) = 0 := by
      have h := ordUnit_mul K (1 : Kˣ) 1
      simp only [mul_one] at h
      omega
    let delta := (Dyadic.dyadicDiscriminantClassLawsProved
      (K := K)).discriminantUnit
    let deltaOrder : ordUnit K delta = 0 :=
      (isValuationUnit_iff_ordUnit_eq_zero K delta).1
        (Dyadic.dyadicDiscriminantClassLawsProved
          (K := K)).discriminant_isValuationUnit
    let bOne := heClassicEvenHGoodBONG (K := K) pairs 1
      (Or.inl rfl) oneOrder
    let bDelta := heClassicEvenHGoodBONG (K := K) pairs delta
      (Or.inr rfl) deltaOrder
    let i := he2022ClassicLemma43Index pairs hSource
    ¬ a.HeClassicPublishedCentralConditionAt bOne i ∨
      ¬ a.HeClassicPublishedCentralConditionAt bDelta i := by
  dsimp only
  let oneOrder : ordUnit K (1 : Kˣ) = 0 := by
    have h := ordUnit_mul K (1 : Kˣ) 1
    simp only [mul_one] at h
    omega
  let delta := (Dyadic.dyadicDiscriminantClassLawsProved
    (K := K)).discriminantUnit
  let deltaOrder : ordUnit K delta = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K delta).1
      (Dyadic.dyadicDiscriminantClassLawsProved
        (K := K)).discriminant_isValuationUnit
  let bOne := heClassicEvenHGoodBONG (K := K) pairs 1
    (Or.inl rfl) oneOrder
  let bDelta := heClassicEvenHGoodBONG (K := K) pairs delta
    (Or.inr rfl) deltaOrder
  let i := he2022ClassicLemma43Index pairs hSource
  have hOneDefect : defectOrder (K := K) (1 : Kˣ) = ⊤ :=
    defectOrder_one (K := K)
  have hOneLower :
      a.truncatedPrefixDefect a ((-1) ^ (pairs + 2))
          0 (2 * pairs + 4) <= defectOrder (K := K) (1 : Kˣ) := by
    rw [hOneDefect]
    exact le_top
  have hOneTrigger : a.centralDefectTrigger bOne i := by
    exact a.he2022ClassicLemma43_H_trigger_of_capped_lt_twoE pairs
      hSource hJ1 heOne 1 (Or.inl rfl) oneOrder hOneLower hSum
  have hDeltaDefect : defectOrder (K := K) delta =
      (((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ)) := by
    simpa only [delta, Nat.cast_mul, Nat.cast_ofNat] using
      (defectOrder_discriminantUnit (K := K)
        (laws := Dyadic.dyadicDiscriminantClassLawsProved))
  have hDeltaTrigger : a.centralDefectTrigger bDelta i := by
    rcases hBranch with hRaw | hCapped
    · have hCappedRaw := a.truncatedPrefixDefect_le_defect a
        ((-1 : Kˣ) ^ (pairs + 2)) 0 (2 * pairs + 4)
      have hCappedLt :
          a.truncatedPrefixDefect a ((-1) ^ (pairs + 2))
              0 (2 * pairs + 4) <
            (((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ)) := by
        apply hCappedRaw.trans_lt
        simpa only [GoodBONG.prefixProduct, BONG.prefixProduct_zero,
          mul_one] using hRaw
      have hLower :
          a.truncatedPrefixDefect a ((-1) ^ (pairs + 2))
              0 (2 * pairs + 4) <= defectOrder (K := K) delta := by
        rw [hDeltaDefect]
        exact hCappedLt.le
      exact a.he2022ClassicLemma43_H_trigger_of_capped_lt_twoE pairs
        hSource hJ1 heOne delta (Or.inr rfl) deltaOrder hLower hSum
    · exact a.he2022ClassicLemma43_H_trigger_of_twoE_le_capped pairs
        hSource hJ1 heOne delta (Or.inr rfl) deltaOrder hCapped
        (by rw [hDeltaDefect])
  have hnot := a.he2022ClassicLemma43_H_notBothRepresents pairs
    hSource hJ1 heOne
  exact not_both_heClassicPublishedCentralConditionAt_of_triggers
    (m := m + 1) (n₁ := 2 * pairs) (n₂ := 2 * pairs)
    a bOne bDelta i i hOneTrigger hDeltaTrigger hnot

/-! ## The two `C` rows in Lemma 4.3(ii) -/

/-- The literal element `omega# = 1 + 4*rho*pi⁻¹` printed in Definition
2.6 is a negative Hilbert partner of `omega = 1+pi`.  The proof uses the
identity `Delta = omega - pi*omega#` and the elementary norm identity
`-pi = 1² - omega*1²`. -/
theorem heClassicOmegaSharp_hilbert_neg :
    hilbertSymbol K (heClassicOmegaSharp (K := K))
      (heClassicOmega (K := K)) = -1 := by
  let omega : Kˣ := heClassicOmega (K := K)
  let omegaSharp : Kˣ := heClassicOmegaSharp (K := K)
  let pi : Kˣ := uniformizerPowerUnit K (1 : Int)
  let delta : Kˣ :=
    (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
  let b : Kˣ := -(pi * omegaSharp)
  have hsum : (delta : K) = (omega : K) + (b : K) := by
    dsimp only [delta, omega, omegaSharp, b, pi]
    rw [(inferInstance : DyadicDiscriminantClassLaws K).discriminant_eq_one_sub_four_mul_rho,
      heClassicOmega_value]
    simp only [Units.val_neg, Units.val_mul]
    rw [heClassicOmegaSharp_value]
    simp [uniformizerPowerUnit]
    field_simp [uniformizer_ne_zero K]
    ring
  have hodd : Odd (ordUnit K (-omega * b)) := by
    have homega := heClassicOmega_order (K := K)
    have hsharp := heClassicOmegaSharp_order (K := K)
    dsimp only [b, pi, omega, omegaSharp]
    rw [ordUnit_mul, ordUnit_neg, homega]
    rw [ordUnit_neg, ordUnit_mul, ordUnit_uniformizerPowerUnit, hsharp]
    norm_num
  have hnegative : hilbertSymbol K omega b = -1 := by
    exact hilbertSymbol_eq_neg_one_of_add_eq_discriminant_of_product_odd
      omega b hsum hodd
  have hbase : hilbertSymbol K omega (-pi) = 1 := by
    rw [hilbertSymbol_eq_one_iff]
    refine ⟨1, 1, ?_⟩
    dsimp only [omega, pi]
    rw [heClassicOmega_value]
    simp [uniformizerPowerUnit]
  have hb : b = (-pi) * omegaSharp := by
    dsimp only [b]
    simp
  rw [hb, hilbertSymbol_mul_right, hbase, one_mul] at hnegative
  rw [hilbertSymbol_comm]
  exact hnegative

/-- The canonical defect-one sharp choice realizes the two displayed
`C_1(c)` and `C_2(c)` rows as the determinant-class pair of Proposition
3.3, with the common hyperbolic head left literal. -/
theorem heClassicEvenC_pairProperties
    (pairs : Nat) (c : Kˣ)
    (hcDefect : defectOrder (K := K) c = (1 : WithTop ℚ)) :
    HeHuSpacePairProperties
      (heClassicEvenC1 (K := K) pairs c)
      (heClassicEvenC2 (K := K) pairs c
        (heClassicDefectOneSharp (K := K) c hcDefect)) := by
  let hc := heClassicSharpDomain_of_defect_one (K := K) c hcDefect
  have Pbinary : HeHuSpacePairProperties
      (heHuBinaryFirst c) (heHuBinarySecond c hc) := by
    apply HeHuSpacePairProperties.of_det_not
    · exact heHuBinarySecond_determinantSquare_first c hc
    · exact heHuBinarySecond_not_represents_first c hc
  have P := Pbinary.append
    (standardHyperbolicEndpointTower (K := K) pairs)
  simpa only [heClassicEvenC1, heClassicEvenC2,
    heClassicScaledHyperbolicTower_zero, heHuBinaryFirst,
    heHuBinarySecond, heHuBinaryTwist, heClassicDefectOneSharp, hc] using P

/-- The two literal rows printed in Definition 2.6 form the same complete
determinant-class pair, now using the formula-defined `omega#` rather than
an abstract sharp choice. -/
theorem heClassicEvenC_literalPairProperties (pairs : Nat) :
    HeHuSpacePairProperties
      (heClassicEvenC1 (K := K) pairs (heClassicOmega (K := K)))
      (heClassicEvenC2 (K := K) pairs (heClassicOmega (K := K))
        (heClassicOmegaSharp (K := K))) := by
  let omega : Kˣ := heClassicOmega (K := K)
  let omegaSharp : Kˣ := heClassicOmegaSharp (K := K)
  have hnegative : hilbertSymbol K omegaSharp omega = -1 := by
    simpa only [omega, omegaSharp] using
      (heClassicOmegaSharp_hilbert_neg (K := K))
  have hclassification :=
    heHuBinaryTwist_classification omega omegaSharp hnegative
  have Pbinary : HeHuSpacePairProperties
      (heHuBinaryFirst omega) (heHuBinaryTwist omega omegaSharp) := by
    apply HeHuSpacePairProperties.of_det_not
    · exact hclassification.1
    · exact hclassification.2.1
  have P := Pbinary.append
    (standardHyperbolicEndpointTower (K := K) pairs)
  simpa only [omega, omegaSharp, heClassicEvenC1, heClassicEvenC2,
    heClassicScaledHyperbolicTower_zero, heHuBinaryFirst,
    heHuBinaryTwist] using P

/-- At full rank, the value units of the exact first `C` row are its
displayed coefficients. -/
theorem heClassicEvenC1_fullPrefixValueUnits
    (pairs : Nat) (c : Kˣ) (hc : 0 ≤ ordUnit K c) :
    let b := heClassicEvenC1GoodBONG (K := K) pairs c hc
    b.prefixValueUnits (2 * pairs + 2) le_rfl =
      heClassicEvenC1 (K := K) pairs c := by
  dsimp only
  funext i
  change (heClassicEvenC1GoodBONG (K := K) pairs c hc).valueUnit i =
    heClassicEvenC1 (K := K) pairs c i
  rw [heClassicEvenC1GoodBONG, heHuExactGoodBONG_valueUnit]

/-- At full rank, the value units of the exact second `C` row are its
displayed coefficients. -/
theorem heClassicEvenC2_fullPrefixValueUnits
    (pairs : Nat) (c cSharp : Kˣ) (hc : 0 ≤ ordUnit K c)
    (hcSharp : ordUnit K cSharp = 0) :
    let b := heClassicEvenC2GoodBONG (K := K) pairs c cSharp hc hcSharp
    b.prefixValueUnits (2 * pairs + 2) le_rfl =
      heClassicEvenC2 (K := K) pairs c cSharp := by
  dsimp only
  funext i
  change (heClassicEvenC2GoodBONG (K := K) pairs c cSharp hc
    hcSharp).valueUnit i = heClassicEvenC2 (K := K) pairs c cSharp i
  rw [heClassicEvenC2GoodBONG, heHuExactGoodBONG_valueUnit]

/-- The full product of the first `C` row is its parameter times the
standard even-rank sign. -/
theorem heClassicEvenC1_prefixProduct_full
    (pairs : Nat) (c : Kˣ) (hc : 0 ≤ ordUnit K c) :
    let b := heClassicEvenC1GoodBONG (K := K) pairs c hc
    b.prefixProduct (2 * pairs + 2) = (-1 : Kˣ) ^ (pairs + 1) * c := by
  dsimp only
  let b := heClassicEvenC1GoodBONG (K := K) pairs c hc
  rw [← b.diagonalUnitDeterminant_prefixValueUnits
      (2 * pairs + 2) le_rfl,
    heClassicEvenC1_fullPrefixValueUnits pairs c hc,
    heClassicEvenC1, heClassicScaledHyperbolicTower_zero,
    diagonalUnitDeterminant_append,
    diagonalUnitDeterminant_standardHyperbolicEndpointTower]
  simp [diagonalUnitDeterminant, Fin.prod_univ_two, pow_succ]

/-- The full product of the second `C` row differs from the first by the
square of the chosen sharp unit. -/
theorem heClassicEvenC2_prefixProduct_full
    (pairs : Nat) (c cSharp : Kˣ) (hc : 0 ≤ ordUnit K c)
    (hcSharp : ordUnit K cSharp = 0) :
    let b := heClassicEvenC2GoodBONG (K := K) pairs c cSharp hc hcSharp
    b.prefixProduct (2 * pairs + 2) =
      (-1 : Kˣ) ^ (pairs + 1) * (cSharp ^ 2 * c) := by
  dsimp only
  let b := heClassicEvenC2GoodBONG (K := K) pairs c cSharp hc hcSharp
  rw [← b.diagonalUnitDeterminant_prefixValueUnits
      (2 * pairs + 2) le_rfl,
    heClassicEvenC2_fullPrefixValueUnits pairs c cSharp hc hcSharp,
    heClassicEvenC2, heClassicScaledHyperbolicTower_zero,
    diagonalUnitDeterminant_append,
    diagonalUnitDeterminant_standardHyperbolicEndpointTower]
  simp [diagonalUnitDeterminant, Fin.prod_univ_two, pow_succ]
  noncomm_ring

/-- The full self capped defect of the first `C` row is the defect of its
determinant parameter. -/
theorem heClassicEvenC1_fullSelfDefect
    (pairs : Nat) (c : Kˣ) (hc : 0 ≤ ordUnit K c) :
    let b := heClassicEvenC1GoodBONG (K := K) pairs c hc
    b.truncatedPrefixDefect b ((-1) ^ (pairs + 1)) 0
        (2 * pairs + 2) = defectOrder (K := K) c := by
  dsimp only
  let b := heClassicEvenC1GoodBONG (K := K) pairs c hc
  unfold truncatedPrefixDefect
  rw [b.prefixAlphaCap_zero, b.prefixAlphaCap_last,
    min_eq_left (le_top), GoodBONG.prefixProduct,
    b.toBONG.prefixProduct_zero,
    heClassicEvenC1_prefixProduct_full pairs c hc]
  simp only [mul_one]
  have hsign : (-1 : Kˣ) ^ (pairs + 1) *
      ((-1 : Kˣ) ^ (pairs + 1) * c) = c := by
    rw [← mul_assoc, ← pow_add]
    rw [(show Even ((pairs + 1) + (pairs + 1)) from
      ⟨pairs + 1, by omega⟩).neg_one_pow]
    simp
  rw [hsign, min_eq_left le_top]

/-- The sharp square disappears from the full self capped defect of the
second `C` row. -/
theorem heClassicEvenC2_fullSelfDefect
    (pairs : Nat) (c cSharp : Kˣ) (hc : 0 ≤ ordUnit K c)
    (hcSharp : ordUnit K cSharp = 0) :
    let b := heClassicEvenC2GoodBONG (K := K) pairs c cSharp hc hcSharp
    b.truncatedPrefixDefect b ((-1) ^ (pairs + 1)) 0
        (2 * pairs + 2) = defectOrder (K := K) c := by
  dsimp only
  let b := heClassicEvenC2GoodBONG (K := K) pairs c cSharp hc hcSharp
  unfold truncatedPrefixDefect
  rw [b.prefixAlphaCap_zero, b.prefixAlphaCap_last,
    min_eq_left (le_top), GoodBONG.prefixProduct,
    b.toBONG.prefixProduct_zero,
    heClassicEvenC2_prefixProduct_full pairs c cSharp hc hcSharp]
  simp only [mul_one]
  have hsign : (-1 : Kˣ) ^ (pairs + 1) *
      ((-1 : Kˣ) ^ (pairs + 1) * (cSharp ^ 2 * c)) =
        c * cSharp ^ 2 := by
    rw [← mul_assoc, ← pow_add]
    rw [(show Even ((pairs + 1) + (pairs + 1)) from
      ⟨pairs + 1, by omega⟩).neg_one_pow]
    simp [mul_comm]
  rw [hsign, defectOrder_mul_square, min_eq_left le_top]

/-- Domination transfers the minimum of the source full self defect and
the target parameter defect to the current mixed defect at `i=n+1`.
This common form is used for both `C` rows. -/
theorem heClassicLemma43_C_centralCurrentDefect_lower_of_self
    {m : Nat} (pairs : Nat) (a : GoodBONG q L (m + 3))
    (hSource : 2 * pairs + 4 <= m + 3)
    {W : Type u} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (b : GoodBONG r M (2 * pairs + 2)) (c : Kˣ)
    (hself : b.truncatedPrefixDefect b ((-1) ^ (pairs + 1)) 0
      (2 * pairs + 2) = defectOrder (K := K) c) :
    min
        (a.truncatedPrefixDefect a ((-1) ^ (pairs + 2)) 0
          (2 * pairs + 4))
        (defectOrder (K := K) c) <=
      a.centralCurrentDefect b
        (he2022ClassicLemma43Index pairs hSource) := by
  let sourceSign : Kˣ := (-1) ^ (pairs + 2)
  let targetSign : Kˣ := (-1) ^ (pairs + 1)
  have hdom := a.truncatedPrefixDefect_domination a b
    sourceSign targetSign (2 * pairs + 4) 0 (2 * pairs + 2)
  have hsource :
      a.truncatedPrefixDefect a sourceSign (2 * pairs + 4) 0 =
        a.truncatedPrefixDefect a sourceSign 0 (2 * pairs + 4) :=
    a.truncatedPrefixDefect_comm a sourceSign (2 * pairs + 4) 0
  have htarget :
      a.truncatedPrefixDefect b targetSign 0 (2 * pairs + 2) =
        defectOrder (K := K) c := by
    rw [a.truncatedPrefixDefect_zero_left_eq_self b]
    simpa only [targetSign] using hself
  have hsign : sourceSign * targetSign = (-1 : Kˣ) := by
    dsimp only [sourceSign, targetSign]
    rw [← pow_add]
    exact (show Odd ((pairs + 2) + (pairs + 1)) from
      ⟨pairs + 1, by omega⟩).neg_one_pow
  rw [hsource, htarget, hsign] at hdom
  unfold centralCurrentDefect
  dsimp only [he2022ClassicLemma43Index]
  simpa only [show 2 * pairs + 3 + 1 = 2 * pairs + 4 by omega,
    show 2 * pairs + 3 - 1 = 2 * pairs + 2 by omega] using hdom

/-- The first mixed defect in Lemma 4.3(ii) is at least one.  The source
cap follows from `R_(n+2) >= 1`, the target cap is `beta_(n-1)=1`, and
the uncapped signed product has even order. -/
theorem he2022ClassicLemma43_C_previousDefect_one_le
    {m : Nat} (pairs : Nat) (a : GoodBONG q L (m + 3))
    (hSource : 2 * pairs + 4 <= m + 3)
    (hJ1 : a.HeClassicJ1EPrime (2 * pairs + 2) (by omega))
    {W : Type u} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (b : GoodBONG r M (2 * pairs + 2))
    (hTargetOrder : ∀ j : Fin (2 * pairs + 2), b.order j = 0)
    (hTargetAlpha :
      b.alphaValue (⟨2 * pairs, by omega⟩ : Fin (2 * pairs + 1)) = 1)
    (hR : 1 <= a.order ⟨2 * pairs + 3, by omega⟩) :
    (1 : WithTop ℚ) <= a.centralPreviousDefect b
      (he2022ClassicLemma43Index pairs hSource) := by
  let i := he2022ClassicLemma43Index pairs hSource
  have hsourceProduct : ordUnit K (a.prefixProduct (2 * pairs + 3)) = 0 := by
    have hdet := a.he2022ClassicLemma43_sourcePrefixDeterminantOrder pairs
      hSource hJ1
    rw [a.diagonalUnitDeterminant_prefixValueUnits
      (2 * pairs + 3) (Nat.le_trans (by omega) hSource)] at hdet
    exact hdet
  have htargetProduct : ordUnit K (b.prefixProduct (2 * pairs + 1)) = 0 := by
    rw [b.ordUnit_prefixProduct_eq_orderSequence_prefixSum
      (2 * pairs + 1) (by omega)]
    unfold BeliOrderSequence.prefixSum
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_range] at hj
    rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence (by omega)]
    exact hTargetOrder ⟨j, by omega⟩
  have hrawOrder : ordUnit K
      ((-1 : Kˣ) * a.prefixProduct (2 * pairs + 3) *
        b.prefixProduct (2 * pairs + 1)) = 0 := by
    have hone : ordUnit K (1 : Kˣ) = 0 := by
      have h := ordUnit_mul K (1 : Kˣ) 1
      simp only [mul_one] at h
      omega
    rw [ordUnit_mul, ordUnit_mul, ordUnit_neg,
      hone, hsourceProduct, htargetProduct]
    norm_num
  have hraw : (1 : WithTop ℚ) <= defectOrder (K := K)
      ((-1 : Kˣ) * a.prefixProduct (2 * pairs + 3) *
        b.prefixProduct (2 * pairs + 1)) := by
    apply defectOrder_one_le_of_even
    rw [hrawOrder]
    exact Even.zero
  have hsourceCap : (1 : WithTop ℚ) <=
      a.prefixAlphaCap (2 * pairs + 3) := by
    rw [a.prefixAlphaCap_of_internal (by omega) (by omega)]
    let gap : Fin (m + 2) := ⟨2 * pairs + 2, by omega⟩
    have hgap : a.orderGap gap =
        a.order ⟨2 * pairs + 3, by omega⟩ := by
      unfold orderGap
      have hzero : a.order
          (⟨2 * pairs + 2, by omega⟩ : Fin (m + 3)) = 0 := by
        let small : Fin (2 * pairs + 3) := ⟨2 * pairs + 2, by omega⟩
        simpa only [small] using hJ1.1 small
      have hcast : gap.castSucc =
          (⟨2 * pairs + 2, by omega⟩ : Fin (m + 3)) := Fin.ext rfl
      have hsucc : gap.succ =
          (⟨2 * pairs + 3, by omega⟩ : Fin (m + 3)) := Fin.ext rfl
      rw [hcast, hsucc, hzero]
      simp only [sub_zero]
    have halphaNe : a.alphaValue gap ≠ 0 := by
      intro halpha
      have hzeroGap := (a.he2022ClassicProposition23 gap).alphaZero.mp halpha
      rw [hgap] at hzeroGap
      have hePos := ramificationIndex_pos (K := K)
      omega
    have halpha := a.one_le_alphaValue_of_ne_zero gap halphaNe
    have hindex :
        (⟨2 * pairs + 3 - 1, by omega⟩ : Fin (m + 2)) = gap :=
      by
        apply Fin.ext
        dsimp only [gap]
        omega
    rw [hindex]
    exact_mod_cast halpha
  have htargetCap : (1 : WithTop ℚ) <=
      b.prefixAlphaCap (2 * pairs + 1) := by
    rw [b.prefixAlphaCap_of_internal (by omega) (by omega)]
    have hindex :
        (⟨2 * pairs + 1 - 1, by omega⟩ : Fin (2 * pairs + 1)) =
          ⟨2 * pairs, by omega⟩ := by
      have hval : 2 * pairs + 1 - 1 = 2 * pairs := by omega
      exact Fin.ext hval
    rw [hindex, hTargetAlpha]
    norm_num
  unfold centralPreviousDefect truncatedPrefixDefect
  dsimp only [i, he2022ClassicLemma43Index]
  simpa only [show 2 * pairs + 3 - 2 = 2 * pairs + 1 by omega] using
    (le_min hraw (le_min hsourceCap htargetCap))

/-- The second mixed defect in Lemma 4.3(ii) is strictly larger than
`1-R_(n+2)`.  The zero-alpha branch is kept explicit: Proposition 2.3(ii)
gives the order gap `-2e`, and two-step monotonicity gives
`R_(n+3) >= 0`, hence `R_(n+2) >= 2` when `e=1`. -/
theorem he2022ClassicLemma43_C_currentDefect_gt
    {m : Nat} (pairs : Nat) (a : GoodBONG q L (m + 3))
    (hExtra : 2 * pairs + 5 <= m + 3)
    (hJ1 : a.HeClassicJ1EPrime (2 * pairs + 2) (by omega))
    (heOne : ramificationIndex K = 1)
    {W : Type u} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (b : GoodBONG r M (2 * pairs + 2))
    (hDAlpha :
      a.truncatedPrefixDefect a ((-1) ^ (pairs + 2)) 0
          (2 * pairs + 4) =
        (a.alphaValue
          (⟨2 * pairs + 3, by omega⟩ : Fin (m + 2)) : WithTop ℚ))
    (hR : 1 <= a.order ⟨2 * pairs + 3, by omega⟩)
    (hcurrentLower :
      min
          (a.truncatedPrefixDefect a ((-1) ^ (pairs + 2)) 0
            (2 * pairs + 4))
          (1 : WithTop ℚ) <=
        a.centralCurrentDefect b
          (he2022ClassicLemma43Index pairs (by omega))) :
    ((((1 : ℚ) -
        (a.order ⟨2 * pairs + 3, by omega⟩ : ℚ) : ℚ)) :
          WithTop ℚ) <
      a.centralCurrentDefect b
        (he2022ClassicLemma43Index pairs (by omega)) := by
  let gap : Fin (m + 2) := ⟨2 * pairs + 3, by omega⟩
  by_cases halphaZero : a.alphaValue gap = 0
  · have hgap := (a.he2022ClassicProposition23 gap).alphaZero.mp
      halphaZero
    have hzero : a.order
        (⟨2 * pairs + 2, by omega⟩ : Fin (m + 3)) = 0 := by
      let small : Fin (2 * pairs + 3) := ⟨2 * pairs + 2, by omega⟩
      simpa only [small] using hJ1.1 small
    have hnextNonneg : 0 <=
        a.order (⟨2 * pairs + 4, by omega⟩ : Fin (m + 3)) := by
      have htwo := a.orderSequence.twoStep (2 * pairs + 2) (by omega)
      change a.order (⟨2 * pairs + 2, by omega⟩ : Fin (m + 3)) <=
        a.order ⟨2 * pairs + 4, by omega⟩ at htwo
      simpa only [hzero] using htwo
    have hcast : gap.castSucc =
        (⟨2 * pairs + 3, by omega⟩ : Fin (m + 3)) := Fin.ext rfl
    have hsucc : gap.succ =
        (⟨2 * pairs + 4, by omega⟩ : Fin (m + 3)) := Fin.ext rfl
    unfold orderGap at hgap
    rw [hcast, hsucc, heOne] at hgap
    have hRtwo : 2 <= a.order ⟨2 * pairs + 3, by omega⟩ := by
      omega
    have hcurrentNonneg : (0 : WithTop ℚ) <=
        a.centralCurrentDefect b
          (he2022ClassicLemma43Index pairs (by omega)) := by
      unfold centralCurrentDefect
      exact a.truncatedPrefixDefect_nonneg b (-1)
        ((he2022ClassicLemma43Index pairs (by omega)).val + 1)
        ((he2022ClassicLemma43Index pairs (by omega)).val - 1)
    have hthreshold :
        ((((1 : ℚ) -
          (a.order ⟨2 * pairs + 3, by omega⟩ : ℚ) : ℚ)) :
            WithTop ℚ) < 0 := by
      apply WithTop.coe_lt_coe.mpr
      have hRtwoQ : (2 : ℚ) <=
          (a.order ⟨2 * pairs + 3, by omega⟩ : ℚ) := by
        exact_mod_cast hRtwo
      linarith
    exact hthreshold.trans_le hcurrentNonneg
  · have halphaOneQ : (1 : ℚ) <= a.alphaValue gap :=
      a.one_le_alphaValue_of_ne_zero gap halphaZero
    have halphaOne : (1 : WithTop ℚ) <=
        (a.alphaValue gap : WithTop ℚ) := by
      exact_mod_cast halphaOneQ
    have hDOne : (1 : WithTop ℚ) <=
        a.truncatedPrefixDefect a ((-1) ^ (pairs + 2)) 0
          (2 * pairs + 4) := by
      rw [hDAlpha]
      simpa only [gap] using halphaOne
    have hcurrentOne : (1 : WithTop ℚ) <=
        a.centralCurrentDefect b
          (he2022ClassicLemma43Index pairs (by omega)) := by
      have hmin : min
          (a.truncatedPrefixDefect a ((-1) ^ (pairs + 2)) 0
            (2 * pairs + 4)) (1 : WithTop ℚ) = 1 :=
        min_eq_right hDOne
      rw [← hmin]
      exact hcurrentLower
    have hthreshold :
        ((((1 : ℚ) -
          (a.order ⟨2 * pairs + 3, by omega⟩ : ℚ) : ℚ)) :
            WithTop ℚ) < 1 := by
      apply WithTop.coe_lt_coe.mpr
      have hRQ : (1 : ℚ) <=
          (a.order ⟨2 * pairs + 3, by omega⟩ : ℚ) := by
        exact_mod_cast hR
      linarith
    exact hthreshold.trans_le hcurrentOne

/-- Common numerical trigger for the two `C` rows in Lemma 4.3(ii). -/
theorem he2022ClassicLemma43_C_trigger
    {m : Nat} (pairs : Nat) (a : GoodBONG q L (m + 3))
    (hExtra : 2 * pairs + 5 <= m + 3)
    (hJ1 : a.HeClassicJ1EPrime (2 * pairs + 2) (by omega))
    (heOne : ramificationIndex K = 1)
    {W : Type u} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (b : GoodBONG r M (2 * pairs + 2))
    (hTargetOrder : ∀ j : Fin (2 * pairs + 2), b.order j = 0)
    (hTargetAlpha :
      b.alphaValue (⟨2 * pairs, by omega⟩ : Fin (2 * pairs + 1)) = 1)
    (hDAlpha :
      a.truncatedPrefixDefect a ((-1) ^ (pairs + 2)) 0
          (2 * pairs + 4) =
        (a.alphaValue
          (⟨2 * pairs + 3, by omega⟩ : Fin (m + 2)) : WithTop ℚ))
    (hR : 1 <= a.order ⟨2 * pairs + 3, by omega⟩)
    (hcurrentLower :
      min
          (a.truncatedPrefixDefect a ((-1) ^ (pairs + 2)) 0
            (2 * pairs + 4))
          (1 : WithTop ℚ) <=
        a.centralCurrentDefect b
          (he2022ClassicLemma43Index pairs (by omega))) :
    a.centralDefectTrigger b
      (he2022ClassicLemma43Index pairs (by omega)) := by
  let i := he2022ClassicLemma43Index pairs (by omega :
    2 * pairs + 4 <= m + 3)
  have hprevious : (1 : WithTop ℚ) <=
      a.centralPreviousDefect b i :=
    a.he2022ClassicLemma43_C_previousDefect_one_le pairs (by omega)
      hJ1 b hTargetOrder hTargetAlpha hR
  have hcurrent :
      ((((1 : ℚ) -
        (a.order ⟨2 * pairs + 3, by omega⟩ : ℚ) : ℚ)) :
          WithTop ℚ) < a.centralCurrentDefect b i := by
    exact a.he2022ClassicLemma43_C_currentDefect_gt pairs hExtra hJ1
      heOne b hDAlpha hR hcurrentLower
  unfold centralDefectTrigger
  constructor
  · have hindex :
        (⟨i.val - 2, by
          have := i.one_lt
          have := i.le_small_succ
          omega⟩ : Fin (2 * pairs + 2)) =
          ⟨2 * pairs + 1, by omega⟩ := by
      apply Fin.ext
      dsimp only [i, he2022ClassicLemma43Index]
      omega
    rw [hindex, hTargetOrder]
    have haindex :
        (⟨i.val, by have := i.lt_large; omega⟩ : Fin (m + 3)) =
          ⟨2 * pairs + 3, by omega⟩ := Fin.ext rfl
    rw [haindex]
    omega
  · have hbOrder : b.order ⟨i.val - 2, by
        have := i.one_lt
        have := i.le_small_succ
        omega⟩ = 0 := hTargetOrder _
    have haOrder : a.order ⟨i.val, by
        have := i.lt_large
        omega⟩ = a.order ⟨2 * pairs + 3, by omega⟩ := by
      congr 1
    calc
      ((2 * (ramificationIndex K : ℚ) +
          (b.order ⟨i.val - 2, by
            have := i.one_lt
            have := i.le_small_succ
            omega⟩ : ℚ) -
          (a.order ⟨i.val, by
            have := i.lt_large
            omega⟩ : ℚ) : ℚ) : WithTop ℚ) =
          (((2 : ℚ) -
            (a.order ⟨2 * pairs + 3, by omega⟩ : ℚ) : ℚ) :
              WithTop ℚ) := by
        rw [hbOrder, haOrder, heOne]
        norm_num
      _ < a.centralPreviousDefect b i +
          a.centralCurrentDefect b i :=
        by
          by_cases hp : a.centralPreviousDefect b i = ⊤
          · rw [hp, top_add]
            exact WithTop.coe_lt_top _
          · by_cases hc : a.centralCurrentDefect b i = ⊤
            · rw [hc, add_top]
              exact WithTop.coe_lt_top _
            · obtain ⟨p, hpEq⟩ := WithTop.ne_top_iff_exists.mp hp
              obtain ⟨c, hcEq⟩ := WithTop.ne_top_iff_exists.mp hc
              rw [← hpEq] at hprevious
              rw [← hcEq] at hcurrent
              rw [← hpEq, ← hcEq]
              norm_cast at hprevious hcurrent ⊢
              push_cast at hcurrent ⊢
              linarith

/-- Lemma 3.13, applied at the rank required by condition (iii), says that
the source prefix `[a_1,...,a_(n+1)]` cannot represent both `C` tests.
The publisher proof writes `n+2` in its last sentence; the theorem being
checked and the codimension-one lemma both require `n+1`. -/
theorem he2022ClassicLemma43_C_notBothRepresents
    {m : Nat} (pairs : Nat) (a : GoodBONG q L (m + 3))
    (hExtra : 2 * pairs + 5 <= m + 3) :
    let omega := heClassicOmega (K := K)
    let omegaSharp := heClassicOmegaSharp (K := K)
    let homegaOrder := heClassicOmega_order (K := K)
    let homegaSharpOrder := heClassicOmegaSharp_order (K := K)
    let bC1 := heClassicEvenC1GoodBONG (K := K) pairs omega
      (by rw [homegaOrder])
    let bC2 := heClassicEvenC2GoodBONG (K := K) pairs omega omegaSharp
      (by rw [homegaOrder]) homegaSharpOrder
    let i := he2022ClassicLemma43Index (m := m) pairs (by omega)
    ¬ (DiagonalRepresents
        (bC1.prefixValues (i.val - 1) (by
          have := i.le_small_succ
          omega))
        (a.prefixValues i.val (by
          have := i.lt_large
          omega)) ∧
      DiagonalRepresents
        (bC2.prefixValues (i.val - 1) (by
          have := i.le_small_succ
          omega))
        (a.prefixValues i.val (by
          have := i.lt_large
          omega))) := by
  dsimp only
  let omega := heClassicOmega (K := K)
  let omegaSharp := heClassicOmegaSharp (K := K)
  let homegaOrder := heClassicOmega_order (K := K)
  let homegaSharpOrder := heClassicOmegaSharp_order (K := K)
  let hnonneg : 0 <= ordUnit K omega := by rw [homegaOrder]
  let bC1 := heClassicEvenC1GoodBONG (K := K) pairs omega hnonneg
  let bC2 := heClassicEvenC2GoodBONG (K := K) pairs omega omegaSharp
    hnonneg homegaSharpOrder
  let i := he2022ClassicLemma43Index pairs (by omega :
    2 * pairs + 4 <= m + 3)
  rintro ⟨hC1, hC2⟩
  let hs : i.val - 1 = 2 * pairs + 2 := by
    dsimp only [i, he2022ClassicLemma43Index]
    omega
  let ht : i.val = 2 * pairs + 3 := by rfl
  have hC1Cast := heHuLemma43_diagonalRepresents_castLengths hs ht hC1
  have hC2Cast := heHuLemma43_diagonalRepresents_castLengths hs ht hC2
  have hC1TargetEq :
      (fun j : Fin (2 * pairs + 2) =>
        bC1.prefixValues (i.val - 1) (by
          have := i.le_small_succ
          omega) (Fin.cast hs.symm j)) =
        bC1.prefixValues (2 * pairs + 2) le_rfl := by
    funext j
    unfold prefixValues
    congr 1
  have hC2TargetEq :
      (fun j : Fin (2 * pairs + 2) =>
        bC2.prefixValues (i.val - 1) (by
          have := i.le_small_succ
          omega) (Fin.cast hs.symm j)) =
        bC2.prefixValues (2 * pairs + 2) le_rfl := by
    funext j
    unfold prefixValues
    congr 1
  have hsourceEq :
      (fun j : Fin (2 * pairs + 3) =>
        a.prefixValues i.val (by
          have := i.lt_large
          omega) (Fin.cast ht.symm j)) =
        a.prefixValues (2 * pairs + 3) (by omega) := by
    funext j
    unfold prefixValues
    congr 1
  have hC1' : DiagonalRepresents
      (bC1.prefixValues (2 * pairs + 2) le_rfl)
      (a.prefixValues (2 * pairs + 3) (by omega)) := by
    rw [hC1TargetEq, hsourceEq] at hC1Cast
    exact hC1Cast
  have hC2' : DiagonalRepresents
      (bC2.prefixValues (2 * pairs + 2) le_rfl)
      (a.prefixValues (2 * pairs + 3) (by omega)) := by
    rw [hC2TargetEq, hsourceEq] at hC2Cast
    exact hC2Cast
  let source := a.prefixValueUnits (2 * pairs + 3) (by omega)
  have hC1Units : DiagonalRepresents
      (diagonalUnitCoefficients
        (heClassicEvenC1 (K := K) pairs omega))
      (diagonalUnitCoefficients source) := by
    change DiagonalRepresents
      (diagonalUnitCoefficients
        (bC1.prefixValueUnits (2 * pairs + 2) le_rfl))
      (diagonalUnitCoefficients source) at hC1'
    rw [heClassicEvenC1_fullPrefixValueUnits pairs omega hnonneg] at hC1'
    exact hC1'
  have hC2Units : DiagonalRepresents
      (diagonalUnitCoefficients
        (heClassicEvenC2 (K := K) pairs omega omegaSharp))
      (diagonalUnitCoefficients source) := by
    change DiagonalRepresents
      (diagonalUnitCoefficients
        (bC2.prefixValueUnits (2 * pairs + 2) le_rfl))
      (diagonalUnitCoefficients source) at hC2'
    rw [heClassicEvenC2_fullPrefixValueUnits pairs omega omegaSharp
      hnonneg homegaSharpOrder] at hC2'
    exact hC2'
  have pair := heClassicEvenC_literalPairProperties (K := K) pairs
  have hexact := heHu2022Lemma313CodimensionOne
    (heClassicEvenC1 (K := K) pairs omega)
    (heClassicEvenC2 (K := K) pairs omega omegaSharp)
    pair source
  rcases hexact with hfirst | hsecond
  · exact hfirst.2 hC2Units
  · exact hsecond.1 hC1Units

/-- He, Lemma 4.3(ii), for the two literal formula-defined rows
`C_1^n(omega), C_2^n(omega)` printed in Definition 2.6. -/
theorem he2022ClassicLemma43ii
    {m : Nat} (pairs : Nat) (a : GoodBONG q L (m + 3))
    (hExtra : 2 * pairs + 5 <= m + 3)
    (hJ1 : a.HeClassicJ1EPrime (2 * pairs + 2) (by omega))
    (heOne : ramificationIndex K = 1)
    (_hSum :
      (1 : WithTop ℚ) <
        ((((a.order ⟨2 * pairs + 3, by omega⟩ : Int) : ℚ) :
            WithTop ℚ)) +
          a.truncatedPrefixDefect a ((-1) ^ (pairs + 2))
            0 (2 * pairs + 4))
    (hDAlpha :
      a.truncatedPrefixDefect a ((-1) ^ (pairs + 2)) 0
          (2 * pairs + 4) =
        (a.alphaValue
          (⟨2 * pairs + 3, by omega⟩ : Fin (m + 2)) : WithTop ℚ))
    (hR : 1 <= a.order ⟨2 * pairs + 3, by omega⟩) :
    let omega := heClassicOmega (K := K)
    let omegaSharp := heClassicOmegaSharp (K := K)
    let homegaOrder := heClassicOmega_order (K := K)
    let homegaSharpOrder := heClassicOmegaSharp_order (K := K)
    let bC1 := heClassicEvenC1GoodBONG (K := K) pairs omega
      (by rw [homegaOrder])
    let bC2 := heClassicEvenC2GoodBONG (K := K) pairs omega omegaSharp
      (by rw [homegaOrder]) homegaSharpOrder
    let i := he2022ClassicLemma43Index pairs (by omega)
    ¬ a.HeClassicPublishedCentralConditionAt bC1 i ∨
      ¬ a.HeClassicPublishedCentralConditionAt bC2 i := by
  dsimp only
  let omega := heClassicOmega (K := K)
  let homegaDefect := heClassicOmega_defect (K := K)
  let omegaSharp := heClassicOmegaSharp (K := K)
  let homegaOrder := heClassicOmega_order (K := K)
  let homegaSharpOrder := heClassicOmegaSharp_order (K := K)
  let hnonneg : 0 <= ordUnit K omega := by rw [homegaOrder]
  let bC1 := heClassicEvenC1GoodBONG (K := K) pairs omega hnonneg
  let bC2 := heClassicEvenC2GoodBONG (K := K) pairs omega omegaSharp
    hnonneg homegaSharpOrder
  let i := he2022ClassicLemma43Index pairs (by omega :
    2 * pairs + 4 <= m + 3)
  have hC1Order : ∀ j : Fin (2 * pairs + 2), bC1.order j = 0 := by
    intro j
    simp only [bC1, heClassicEvenC1GoodBONG, heHuExactGoodBONG_order]
    rw [heClassicEvenC1_order]
    by_cases hj : j.val = 2 * pairs + 1
    · rw [if_pos hj]
      simpa only [omega] using homegaOrder
    · rw [if_neg hj]
  have hC2Order : ∀ j : Fin (2 * pairs + 2), bC2.order j = 0 := by
    intro j
    simp only [bC2, heClassicEvenC2GoodBONG, heHuExactGoodBONG_order]
    rw [heClassicEvenC2_order pairs omega omegaSharp homegaSharpOrder]
    by_cases hj : j.val = 2 * pairs + 1
    · rw [if_pos hj]
      simpa only [omega] using homegaOrder
    · rw [if_neg hj]
  have hC1Alpha : bC1.alphaValue
      (⟨2 * pairs, by omega⟩ : Fin (2 * pairs + 1)) = 1 := by
    have hall := heClassicEvenC1_alpha_eq_one (K := K) pairs omega 1
      hnonneg (Or.inr rfl) (by rw [homegaOrder]; norm_num)
      (by simpa only [homegaDefect])
    exact hall _
  have hC2Alpha : bC2.alphaValue
      (⟨2 * pairs, by omega⟩ : Fin (2 * pairs + 1)) = 1 := by
    have hall := heClassicEvenC2_alpha_eq_one (K := K) pairs omega
      omegaSharp 1 hnonneg homegaSharpOrder (Or.inr rfl)
      (by rw [homegaOrder]; norm_num)
      (by simpa only [homegaDefect])
    exact hall _
  have hC1Self := heClassicEvenC1_fullSelfDefect
    (K := K) pairs omega hnonneg
  have hC2Self := heClassicEvenC2_fullSelfDefect
    (K := K) pairs omega omegaSharp hnonneg homegaSharpOrder
  have hC1Current : min
      (a.truncatedPrefixDefect a ((-1) ^ (pairs + 2)) 0
        (2 * pairs + 4)) (1 : WithTop ℚ) <=
      a.centralCurrentDefect bC1 i := by
    have h := a.heClassicLemma43_C_centralCurrentDefect_lower_of_self
      pairs (by omega) bC1 omega hC1Self
    rw [homegaDefect] at h
    simpa only [i] using h
  have hC2Current : min
      (a.truncatedPrefixDefect a ((-1) ^ (pairs + 2)) 0
        (2 * pairs + 4)) (1 : WithTop ℚ) <=
      a.centralCurrentDefect bC2 i := by
    have h := a.heClassicLemma43_C_centralCurrentDefect_lower_of_self
      pairs (by omega) bC2 omega hC2Self
    rw [homegaDefect] at h
    simpa only [i] using h
  have hC1Trigger : a.centralDefectTrigger bC1 i := by
    exact a.he2022ClassicLemma43_C_trigger pairs hExtra hJ1 heOne bC1
      hC1Order hC1Alpha hDAlpha hR hC1Current
  have hC2Trigger : a.centralDefectTrigger bC2 i := by
    exact a.he2022ClassicLemma43_C_trigger pairs hExtra hJ1 heOne bC2
      hC2Order hC2Alpha hDAlpha hR hC2Current
  have hnot := a.he2022ClassicLemma43_C_notBothRepresents pairs hExtra
  exact not_both_heClassicPublishedCentralConditionAt_of_triggers
    (m := m + 1) (n₁ := 2 * pairs) (n₂ := 2 * pairs)
    a bC1 bC2 i i hC1Trigger hC2Trigger hnot

end BONG.GoodBONG

end Bong
