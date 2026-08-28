/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009MainTheorem

/-!
# Beli (2009/2010), Section 4

When the ramification index is one, the alpha invariants are determined by
the adjacent order gaps.  This file proves Lemma 4.1, reduces the defect and
representation conditions to the 2-adic forms in the paper, and derives
Theorem 4.2 from Theorem 3.1.
-/

namespace Bong

open Dyadic

universe u v w

/-- The alpha value determined by an adjacent order gap when `e = 1`. -/
def twoAdicAlphaFromGap (gap : Int) : ℚ :=
  if gap = 1 then 1 else (gap : ℚ) / 2 + 1

theorem twoAdic_gap_cases (gap : Int)
    (hlower : -2 ≤ gap) (heven : gap < 0 → Even gap) :
    gap = -2 ∨ gap = 0 ∨ gap = 1 ∨ 2 ≤ gap := by
  by_cases hnegative : gap < 0
  · obtain ⟨z, hz⟩ := heven hnegative
    omega
  · omega

/-- The correction term at the exceptional gap `1`. -/
def twoAdicOneGapPenalty (gap : Int) : Int :=
  if gap = 1 then 1 else 0

theorem two_mul_twoAdicAlphaFromGap (gap : Int) :
    2 * twoAdicAlphaFromGap gap =
      ((gap + 2 - twoAdicOneGapPenalty gap : Int) : ℚ) := by
  by_cases hgap : gap = 1
  · subst gap
    norm_num [twoAdicAlphaFromGap, twoAdicOneGapPenalty]
  · simp only [twoAdicAlphaFromGap, twoAdicOneGapPenalty,
      if_neg hgap]
    push_cast
    ring

theorem twoAdic_alpha_sum_gt_two_iff
    (leftGap rightGap : Int) :
    2 < twoAdicAlphaFromGap leftGap + twoAdicAlphaFromGap rightGap ↔
      0 < leftGap + rightGap ∧
        (leftGap, rightGap) ≠ (0, 1) ∧
        (leftGap, rightGap) ≠ (1, 0) ∧
        (leftGap, rightGap) ≠ (1, 1) := by
  have hidentity :
      ((leftGap + rightGap - twoAdicOneGapPenalty leftGap -
          twoAdicOneGapPenalty rightGap : Int) : ℚ) =
        2 * (twoAdicAlphaFromGap leftGap +
          twoAdicAlphaFromGap rightGap - 2) := by
    calc
      ((leftGap + rightGap - twoAdicOneGapPenalty leftGap -
          twoAdicOneGapPenalty rightGap : Int) : ℚ) =
          ((leftGap + 2 - twoAdicOneGapPenalty leftGap : Int) : ℚ) +
          ((rightGap + 2 - twoAdicOneGapPenalty rightGap : Int) : ℚ) -
            4 := by push_cast; ring
      _ = 2 * twoAdicAlphaFromGap leftGap +
          2 * twoAdicAlphaFromGap rightGap - 4 := by
        rw [two_mul_twoAdicAlphaFromGap,
          two_mul_twoAdicAlphaFromGap]
      _ = 2 * (twoAdicAlphaFromGap leftGap +
          twoAdicAlphaFromGap rightGap - 2) := by ring
  have hscale :
      2 < twoAdicAlphaFromGap leftGap +
          twoAdicAlphaFromGap rightGap ↔
        0 < leftGap + rightGap - twoAdicOneGapPenalty leftGap -
          twoAdicOneGapPenalty rightGap := by
    constructor
    · intro h
      have hcast : (0 : ℚ) <
          ((leftGap + rightGap - twoAdicOneGapPenalty leftGap -
            twoAdicOneGapPenalty rightGap : Int) : ℚ) := by
        rw [hidentity]
        linarith
      exact_mod_cast hcast
    · intro h
      have hcast : (0 : ℚ) <
          ((leftGap + rightGap - twoAdicOneGapPenalty leftGap -
            twoAdicOneGapPenalty rightGap : Int) : ℚ) := by
        exact_mod_cast h
      rw [hidentity] at hcast
      linarith
  rw [hscale]
  by_cases hleft : leftGap = 1 <;>
    by_cases hright : rightGap = 1 <;>
    simp [twoAdicOneGapPenalty, hleft, hright] <;>
    omega

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

namespace BONG.GoodBONG

theorem orderGap_ge_neg_two_mul_e
    (b : GoodBONG q L (n + 1)) (i : Fin n) :
    -(2 * (ramificationIndex K : Int)) ≤ b.orderGap i := by
  have hadmissible := b.toBONG.adjacentParameter_isBinaryParameterAdmissible
    i.castSucc (Nat.add_lt_add_right i.isLt 1)
  have hlower := hadmissible.ordUnit_ge_neg_two_mul_e
  rw [b.toBONG.ordUnit_adjacentParameter i.castSucc
    (Nat.add_lt_add_right i.isLt 1)] at hlower
  exact hlower

theorem orderGap_even_of_negative
    (b : GoodBONG q L (n + 1)) (i : Fin n)
    (hnegative : b.orderGap i < 0) : Even (b.orderGap i) := by
  have hadmissible := b.toBONG.adjacentParameter_isBinaryParameterAdmissible
    i.castSucc (Nat.add_lt_add_right i.isLt 1)
  have hnotOdd : ¬Odd (b.orderGap i) := by
    intro hodd
    have horder :
        ordUnit K (b.toBONG.adjacentParameter i.castSucc
          (Nat.add_lt_add_right i.isLt 1)) = b.orderGap i := by
      rw [b.toBONG.ordUnit_adjacentParameter i.castSucc
        (Nat.add_lt_add_right i.isLt 1)]
      rfl
    have hodd' : Odd (ordUnit K (b.toBONG.adjacentParameter i.castSucc
        (Nat.add_lt_add_right i.isLt 1))) := by
      rw [horder]
      exact hodd
    have hnonnegative := hadmissible.ordUnit_nonneg_of_odd hodd'
    rw [horder] at hnonnegative
    exact (not_lt_of_ge hnonnegative) hnegative
  exact Int.not_odd_iff_even.mp hnotOdd

variable [Beli2006AlphaLaws.{u, v} K]
  [Beli2009AlphaParityLaws.{u, v} K]

/-- Beli (2009/2010), Lemma 4.1. -/
theorem beli2009Lemma41
    (b : GoodBONG q L (n + 1)) (i : Fin n)
    (htwoAdic : ramificationIndex K = 1) :
    b.alphaValue i = twoAdicAlphaFromGap (b.orderGap i) := by
  by_cases hone : b.orderGap i = 1
  · have hle : b.orderGap i ≤ 2 * (ramificationIndex K : Int) := by
      rw [htwoAdic]
      omega
    have hodd : Odd (b.orderGap i) := by
      rw [hone]
      exact odd_one
    have halpha := (b.beli2009Lemma27_iii i hle).2.mpr (Or.inr hodd)
    rw [twoAdicAlphaFromGap, if_pos hone, halpha, hone]
    norm_num
  · have hlower := b.orderGap_ge_neg_two_mul_e i
    rw [htwoAdic] at hlower
    have hnegativeEven := b.orderGap_even_of_negative i
    have hcases := twoAdic_gap_cases (b.orderGap i) (by omega) hnegativeEven
    have hcorollaryCase :
        2 * (ramificationIndex K : Int) ≤ b.orderGap i ∨
        b.orderGap i = -(2 * (ramificationIndex K : Int)) ∨
        b.orderGap i = 2 - 2 * (ramificationIndex K : Int) ∨
        b.orderGap i = 2 * (ramificationIndex K : Int) - 2 := by
      rw [htwoAdic]
      rcases hcases with h | h | h | h <;> omega
    rw [b.beli2009Corollary29_i i hcorollaryCase]
    simp only [twoAdicAlphaFromGap, if_neg hone]
    unfold halfGapValue
    rw [htwoAdic]
    norm_num

end BONG.GoodBONG

/-- A scalar is a square or the distinguished 2-adic class times a square. -/
def IsSquareOrDistinguishedSquare {K : Type u} [Field K]
    (delta x : Kˣ) : Prop :=
  IsSquare x ∨ IsSquare (x / delta)

/-- The 2-adic endpoint classification of even-order square classes.
This interface intentionally has no default instance. -/
class Beli2009TwoAdicDefectClassLaws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] where
  distinguishedUnit : Kˣ
  defectOrder_one_le_of_even (x : Kˣ)
      (htwoAdic : ramificationIndex K = 1)
      (heven : Even (ordUnit K x)) :
    (1 : WithTop ℚ) ≤ BONG.GoodBONG.defectOrder (K := K) x
  defectOrder_two_le_iff (x : Kˣ)
      (htwoAdic : ramificationIndex K = 1)
      (heven : Even (ordUnit K x)) :
    (2 : WithTop ℚ) ≤ BONG.GoodBONG.defectOrder (K := K) x ↔
      IsSquareOrDistinguishedSquare distinguishedUnit x

namespace BONG.GoodBONG

variable [QuadraticDefectLaws K]

theorem defectOrder_ge_iff_isSquare_of_two_lt
    (x : Kˣ) (htwoAdic : ramificationIndex K = 1)
    (threshold : ℚ) (hthreshold : 2 < threshold) :
    (threshold : WithTop ℚ) ≤ defectOrder (K := K) x ↔ IsSquare x := by
  constructor
  · intro hbound
    by_contra hnonsquare
    have hle := quadraticDefect_le_two_mul_e_of_not_isSquare
      (K := K) hnonsquare
    rw [htwoAdic] at hle
    have hfinite : quadraticDefect K x ≠ ⊤ := by
      intro htop
      rw [htop] at hle
      simp at hle
    obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp hfinite
    have hdle : d ≤ 2 := by
      apply WithTop.coe_le_coe.mp
      rw [hd]
      exact hle
    have hdefect : defectOrder (K := K) x = (d : WithTop ℚ) := by
      unfold defectOrder
      rw [← hd]
      rfl
    rw [hdefect] at hbound
    have hcast : threshold ≤ (d : ℚ) := by exact_mod_cast hbound
    have hdcast : (d : ℚ) ≤ 2 := by exact_mod_cast hdle
    linarith
  · intro hsquare
    have htop := (quadraticDefect_eq_top_iff_isSquare (K := K) x).2 hsquare
    unfold defectOrder
    rw [htop]
    change (threshold : WithTop ℚ) ≤ ⊤
    exact le_top

end BONG.GoodBONG

namespace BONG.GoodBONG

theorem ordUnit_prefixProduct_eq_of_sameOrders
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (horders : a.SameOrders b) (m : Nat) (hm : m ≤ n + 1) :
    ordUnit K (a.prefixProduct m) = ordUnit K (b.prefixProduct m) := by
  induction m with
  | zero =>
      simp [GoodBONG.prefixProduct]
  | succ m ih =>
      have hmlt : m < n + 1 := by omega
      unfold GoodBONG.prefixProduct
      rw [a.toBONG.prefixProduct_succ m hmlt,
        b.toBONG.prefixProduct_succ m hmlt,
        ordUnit_mul, ordUnit_mul]
      have ih' := ih (by omega)
      change ordUnit K (a.toBONG.prefixProduct m) =
        ordUnit K (b.toBONG.prefixProduct m) at ih'
      rw [ih']
      have hvalue := horders ⟨m, hmlt⟩
      change ordUnit K (a.toBONG.valueUnit ⟨m, hmlt⟩) =
        ordUnit K (b.toBONG.valueUnit ⟨m, hmlt⟩) at hvalue
      rw [hvalue]

theorem comparisonPrefixProduct_order_even
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (horders : a.SameOrders b) (i : Fin n) :
    Even (ordUnit K (a.comparisonPrefixProduct b i)) := by
  have heq := a.ordUnit_prefixProduct_eq_of_sameOrders
    b horders (i.1 + 1) (by omega)
  unfold comparisonPrefixProduct
  rw [ordUnit_mul, heq]
  refine ⟨ordUnit K (b.prefixProduct (i.1 + 1)), ?_⟩
  omega

variable [alphaV : Beli2006AlphaLaws.{u, v} K]
  [parityV : Beli2009AlphaParityLaws.{u, v} K]

theorem sameAlphas_of_sameOrders_twoAdic
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    [parityW : Beli2009AlphaParityLaws.{u, w} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (htwoAdic : ramificationIndex K = 1)
    (horders : a.SameOrders b) : a.SameAlphas b := by
  intro i
  have ha : a.alphaValue i = twoAdicAlphaFromGap (a.orderGap i) := by
    letI : Beli2006AlphaLaws.{u, v} K := alphaV
    letI : Beli2009AlphaParityLaws.{u, v} K := parityV
    exact a.beli2009Lemma41 i htwoAdic
  have hb : b.alphaValue i = twoAdicAlphaFromGap (b.orderGap i) := by
    letI : Beli2006AlphaLaws.{u, w} K := alphaW
    letI : Beli2009AlphaParityLaws.{u, w} K := parityW
    exact b.beli2009Lemma41 i htwoAdic
  rw [ha, hb]
  congr 1
  unfold orderGap
  rw [horders i.succ, horders i.castSucc]

/-- The simplified representation trigger in Theorem 4.2(iii). -/
noncomputable def TwoAdicInternalRepresentationConditions
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1)) : Prop :=
  ∀ (i : Fin n) (hi : 0 < i.1),
    (a.order ⟨i.1 - 1, by omega⟩ < a.order ⟨i.1 + 1, by omega⟩ ∧
      (a.orderGap ⟨i.1 - 1, by omega⟩, a.orderGap i) ≠ (0, 1) ∧
      (a.orderGap ⟨i.1 - 1, by omega⟩, a.orderGap i) ≠ (1, 0) ∧
      (a.orderGap ⟨i.1 - 1, by omega⟩, a.orderGap i) ≠ (1, 1)) →
      DiagonalRepresents
        (b.prefixValues i.1 (by omega))
        (a.prefixValues (i.1 + 1) (by omega))

theorem twoAdicInternalTrigger_iff
    (a : GoodBONG q L (n + 1)) (i : Fin n) (hi : 0 < i.1)
    (htwoAdic : ramificationIndex K = 1) :
    (2 * (ramificationIndex K : ℚ) <
        a.alphaValue ⟨i.1 - 1, by omega⟩ + a.alphaValue i) ↔
      a.order ⟨i.1 - 1, by omega⟩ < a.order ⟨i.1 + 1, by omega⟩ ∧
        (a.orderGap ⟨i.1 - 1, by omega⟩, a.orderGap i) ≠ (0, 1) ∧
        (a.orderGap ⟨i.1 - 1, by omega⟩, a.orderGap i) ≠ (1, 0) ∧
        (a.orderGap ⟨i.1 - 1, by omega⟩, a.orderGap i) ≠ (1, 1) := by
  rw [a.beli2009Lemma41 ⟨i.1 - 1, by omega⟩ htwoAdic,
    a.beli2009Lemma41 i htwoAdic, htwoAdic]
  norm_num
  rw [twoAdic_alpha_sum_gt_two_iff]
  let j : Fin n := ⟨i.1 - 1, by omega⟩
  have hleft : j.succ = i.castSucc := by
    apply Fin.ext
    simp [j]
    omega
  have hleftCast :
      j.castSucc = (⟨i.1 - 1, by omega⟩ : Fin (n + 1)) := by
    apply Fin.ext
    rfl
  have hright : i.succ = (⟨i.1 + 1, by omega⟩ : Fin (n + 1)) := by
    apply Fin.ext
    rfl
  constructor
  · rintro ⟨hsum, hneOne, hneTwo, hneThree⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · change 0 < a.orderGap j + a.orderGap i at hsum
      unfold orderGap at hsum
      rw [hleft, hleftCast, hright] at hsum
      omega
    · intro hzero hone
      apply hneOne
      apply Prod.ext
      · exact hzero
      · exact hone
    · intro hone hzero
      apply hneTwo
      apply Prod.ext
      · exact hone
      · exact hzero
    · intro hleftOne hrightOne
      apply hneThree
      apply Prod.ext
      · exact hleftOne
      · exact hrightOne
  · rintro ⟨houter, hneOne, hneTwo, hneThree⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · change 0 < a.orderGap j + a.orderGap i
      unfold orderGap
      rw [hleft, hleftCast, hright]
      omega
    · intro hp
      exact hneOne (congrArg Prod.fst hp) (congrArg Prod.snd hp)
    · intro hp
      exact hneTwo (congrArg Prod.fst hp) (congrArg Prod.snd hp)
    · intro hp
      exact hneThree (congrArg Prod.fst hp) (congrArg Prod.snd hp)

theorem internalRepresentationConditions_iff_twoAdic
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (htwoAdic : ramificationIndex K = 1) :
    a.InternalRepresentationConditions b ↔
      a.TwoAdicInternalRepresentationConditions b := by
  unfold InternalRepresentationConditions
    TwoAdicInternalRepresentationConditions
  constructor
  · intro h i hi htrigger
    exact h i hi ((a.twoAdicInternalTrigger_iff i hi htwoAdic).2 htrigger)
  · intro h i hi htrigger
    exact h i hi ((a.twoAdicInternalTrigger_iff i hi htwoAdic).1 htrigger)

end BONG.GoodBONG

namespace BONG.GoodBONG

/-- The square-class condition in Theorem 4.2(ii). -/
noncomputable def TwoAdicPrefixSquareClassConditions
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (delta : Kˣ) (a : GoodBONG q L (n + 1))
    (b : GoodBONG r M (n + 1)) : Prop :=
  ∀ i : Fin n,
    (a.orderGap i = 2 →
      IsSquareOrDistinguishedSquare delta
        (a.comparisonPrefixProduct b i)) ∧
    (2 < a.orderGap i → IsSquare (a.comparisonPrefixProduct b i))

variable [alphaV : Beli2006AlphaLaws.{u, v} K]
  [parityV : Beli2009AlphaParityLaws.{u, v} K]

omit alphaV parityV in
theorem twoAdicAlphaFromGap_le_one
    (b : GoodBONG q L (n + 1)) (i : Fin n)
    (htwoAdic : ramificationIndex K = 1)
    (hgap : b.orderGap i ≤ 1) :
    twoAdicAlphaFromGap (b.orderGap i) ≤ 1 := by
  have hlower := b.orderGap_ge_neg_two_mul_e i
  rw [htwoAdic] at hlower
  have heven := b.orderGap_even_of_negative i
  rcases twoAdic_gap_cases (b.orderGap i) (by omega) heven with
    h | h | h | h
  · rw [h]
    norm_num [twoAdicAlphaFromGap]
  · rw [h]
    norm_num [twoAdicAlphaFromGap]
  · rw [h]
    norm_num [twoAdicAlphaFromGap]
  · omega

theorem alphaValue_eq_two_of_orderGap_eq_two
    (b : GoodBONG q L (n + 1)) (i : Fin n)
    (htwoAdic : ramificationIndex K = 1)
    (hgap : b.orderGap i = 2) : b.alphaValue i = 2 := by
  rw [b.beli2009Lemma41 i htwoAdic, hgap]
  norm_num [twoAdicAlphaFromGap]

theorem two_lt_alphaValue_of_two_lt_orderGap
    (b : GoodBONG q L (n + 1)) (i : Fin n)
    (htwoAdic : ramificationIndex K = 1)
    (hgap : 2 < b.orderGap i) : 2 < b.alphaValue i := by
  have hne : b.orderGap i ≠ 1 := by omega
  rw [b.beli2009Lemma41 i htwoAdic]
  simp only [twoAdicAlphaFromGap, if_neg hne]
  have hcast : (2 : ℚ) < (b.orderGap i : ℚ) := by exact_mod_cast hgap
  linarith

variable [QuadraticDefectLaws K]
  [twoAdicLaws : Beli2009TwoAdicDefectClassLaws K]

theorem prefixDefectBounds_iff_twoAdic
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (htwoAdic : ramificationIndex K = 1)
    (horders : a.SameOrders b) :
    a.PrefixDefectBounds b ↔
      a.TwoAdicPrefixSquareClassConditions
        twoAdicLaws.distinguishedUnit b := by
  constructor
  · intro hprefix i
    have heven := a.comparisonPrefixProduct_order_even b horders i
    constructor
    · intro hgap
      have halpha := a.alphaValue_eq_two_of_orderGap_eq_two
        i htwoAdic hgap
      have hbound := hprefix i
      rw [halpha] at hbound
      exact (twoAdicLaws.defectOrder_two_le_iff
        (a.comparisonPrefixProduct b i) htwoAdic heven).1 hbound
    · intro hgap
      have halpha := a.two_lt_alphaValue_of_two_lt_orderGap
        i htwoAdic hgap
      exact (defectOrder_ge_iff_isSquare_of_two_lt
        (a.comparisonPrefixProduct b i) htwoAdic
          (a.alphaValue i) halpha).1 (hprefix i)
  · intro hsquare i
    have heven := a.comparisonPrefixProduct_order_even b horders i
    rcases lt_trichotomy (a.orderGap i) 2 with hgap | hgap | hgap
    · have halphaFormula := a.beli2009Lemma41 i htwoAdic
      have halphaLe : a.alphaValue i ≤ 1 := by
        rw [halphaFormula]
        exact a.twoAdicAlphaFromGap_le_one i htwoAdic (by omega)
      have halphaCast : (a.alphaValue i : WithTop ℚ) ≤ 1 := by
        exact_mod_cast halphaLe
      exact halphaCast.trans
        (twoAdicLaws.defectOrder_one_le_of_even
          (a.comparisonPrefixProduct b i) htwoAdic heven)
    · have halpha := a.alphaValue_eq_two_of_orderGap_eq_two
        i htwoAdic hgap
      rw [halpha]
      exact (twoAdicLaws.defectOrder_two_le_iff
        (a.comparisonPrefixProduct b i) htwoAdic heven).2 ((hsquare i).1 hgap)
    · have halpha := a.two_lt_alphaValue_of_two_lt_orderGap
        i htwoAdic hgap
      exact (defectOrder_ge_iff_isSquare_of_two_lt
        (a.comparisonPrefixProduct b i) htwoAdic
          (a.alphaValue i) halpha).2 ((hsquare i).2 hgap)

end BONG.GoodBONG

/-- The three conditions in Beli's 2-adic classification theorem. -/
structure Beli2009TwoAdicClassificationConditions
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type w} [AddCommGroup W] [Module K W]
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W} {n : Nat}
    (delta : Kˣ) (a : BONG.GoodBONG q L (n + 1))
    (b : BONG.GoodBONG r M (n + 1)) : Prop where
  sameOrders : a.SameOrders b
  prefixSquareClasses : a.TwoAdicPrefixSquareClassConditions delta b
  internalRepresentations : a.TwoAdicInternalRepresentationConditions b

namespace Beli2009TwoAdicClassificationConditions

variable [alphaV : Beli2006AlphaLaws.{u, v} K]
  [parityV : Beli2009AlphaParityLaws.{u, v} K]
  [alphaW : Beli2006AlphaLaws.{u, w} K]
  [parityW : Beli2009AlphaParityLaws.{u, w} K]
  [QuadraticDefectLaws K]
  [twoAdicLaws : Beli2009TwoAdicDefectClassLaws K]
  {W : Type w} [AddCommGroup W] [Module K W]
  {r : QuadraticSpace K W} {M : Lattice K W}
  {a : BONG.GoodBONG q L (n + 1)}
  {b : BONG.GoodBONG r M (n + 1)}

theorem classificationConditions_iff
    (htwoAdic : ramificationIndex K = 1) :
    ClassificationConditions a b ↔
      Beli2009TwoAdicClassificationConditions
        twoAdicLaws.distinguishedUnit a b := by
  constructor
  · rintro ⟨horders, _halphas, hprefix, hinternal⟩
    exact ⟨horders,
      (a.prefixDefectBounds_iff_twoAdic
        (alphaV := alphaV) (parityV := parityV)
        b htwoAdic horders).1 hprefix,
      (a.internalRepresentationConditions_iff_twoAdic
        (alphaV := alphaV) (parityV := parityV) b htwoAdic).1
        hinternal⟩
  · rintro ⟨horders, hprefix, hinternal⟩
    exact ⟨horders,
      a.sameAlphas_of_sameOrders_twoAdic
        (alphaV := alphaV) (parityV := parityV)
        (alphaW := alphaW) (parityW := parityW) b htwoAdic horders,
      (a.prefixDefectBounds_iff_twoAdic
        (alphaV := alphaV) (parityV := parityV)
        b htwoAdic horders).2 hprefix,
      (a.internalRepresentationConditions_iff_twoAdic
        (alphaV := alphaV) (parityV := parityV) b htwoAdic).2
        hinternal⟩

end Beli2009TwoAdicClassificationConditions

namespace Beli2009ClassificationReduction

variable [alphaV : Beli2006AlphaLaws.{u, v} K]
  [parityV : Beli2009AlphaParityLaws.{u, v} K]
  [alphaW : Beli2006AlphaLaws.{u, w} K]
  [parityW : Beli2009AlphaParityLaws.{u, w} K]
  [QuadraticDefectLaws K]
  [twoAdicLaws : Beli2009TwoAdicDefectClassLaws K]
  {W : Type w} [AddCommGroup W] [Module K W]
  {r : QuadraticSpace K W} {M : Lattice K W}
  {ambient : q.IsIsometric r}
  {a : BONG.GoodBONG q L (n + 1)}
  {b : BONG.GoodBONG r M (n + 1)}

/-- Beli (2009/2010), Theorem 4.2. -/
theorem beli2009Theorem42
    (D : Beli2009ClassificationReduction ambient a b)
    [Beli2009Omeara9328Laws D]
    (htwoAdic : ramificationIndex K = 1) :
    Lattice.IsIsometric q r L M ↔
      Beli2009TwoAdicClassificationConditions
        twoAdicLaws.distinguishedUnit a b :=
  D.beli2009Theorem31.trans
    (Beli2009TwoAdicClassificationConditions.classificationConditions_iff
      (alphaV := alphaV) (parityV := parityV)
      (alphaW := alphaW) (parityW := parityW) htwoAdic)

end Beli2009ClassificationReduction

end Bong
