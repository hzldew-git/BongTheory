/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2022ClassicSectionFive

/-!
# He (2024), Lemma 5.4

The single printed test is the odd-rank lattice `C₁ⁿ(omega)`.  The reverse
direction in the publisher proof invokes Corollary 3.11(iii), whose terminal
case requires `alpha_n = 1` and the signed-prefix equality.  Those are exactly
`J2_E(n-1)`, already present in every later application (notably Proposition
5.2), but omitted from the printed statement of Lemma 5.4.  The formal theorem
therefore exposes that premise.
-/

namespace Bong

open Dyadic

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG.GoodBONG

/-- The literal middle condition of Lemma 5.4: Theorem 2.5(i)--(ii)
hold for `C₁ⁿ(omega)`. -/
noncomputable def HeClassicLemma54PublishedTest
    [QuadraticDefectLaws K] [DyadicDiscriminantClassLaws K]
    {m : Nat} (t : Nat) (a : GoodBONG q L (m + 3))
    (hRank : 2 * t + 3 <= m + 3) : Prop :=
  let omegaUnit : Kˣ := heClassicOmega (K := K)
  let b := heClassicOddC1GoodBONG (K := K) t omegaUnit
    (by rw [heClassicOmega_order (K := K)])
  a.RepresentationOrderCondition b (by omega) ∧
    a.RepresentationDefectCondition b

/-- Every order of the printed `C₁ⁿ(omega)` row is zero. -/
theorem heClassicLemma54Test_order_zero
    [QuadraticDefectLaws K] [DyadicDiscriminantClassLaws K]
    (t : Nat) :
    let omegaUnit : Kˣ := heClassicOmega (K := K)
    let b := heClassicOddC1GoodBONG (K := K) t omegaUnit
      (by rw [heClassicOmega_order (K := K)])
    forall i : Fin (2 * t + 3), b.order i = 0 := by
  dsimp only
  intro i
  simp only [heClassicOddC1GoodBONG, heHuExactGoodBONG_order]
  rw [heClassicOddC1_order]
  split
  · exact heClassicOmega_order (K := K)
  · rfl

/-- The single published test forces the zero source prefix in
`J1'_E(n-1)`. -/
theorem he2022ClassicLemma54_orders_of_publishedTest
    [QuadraticDefectLaws K] [DyadicDiscriminantClassLaws K]
    {m : Nat} (t : Nat) (a : GoodBONG q L (m + 3))
    (hSource : 2 * t + 5 <= m + 3)
    (hClassic : Lattice.IsClassicIntegral q L)
    (hTest : a.HeClassicLemma54PublishedTest t (by omega)) :
    forall i : Fin (2 * t + 3),
      a.order ⟨i.val, by omega⟩ = 0 := by
  unfold HeClassicLemma54PublishedTest at hTest
  dsimp only at hTest
  let omegaUnit : Kˣ := heClassicOmega (K := K)
  let b := heClassicOddC1GoodBONG (K := K) t omegaUnit
    (by rw [heClassicOmega_order (K := K)])
  have hTargetZero : forall i : Fin (2 * t + 3), b.order i = 0 := by
    simpa only [b, omegaUnit] using
      (heClassicLemma54Test_order_zero (K := K) t)
  have hFirstCondition := hTest.1 (0 : Fin (2 * t + 3))
  have hFirstLe : a.order (0 : Fin (m + 3)) <= 0 := by
    rcases hFirstCondition with hleft | hright
    · change a.order (0 : Fin (m + 3)) <= b.order 0 at hleft
      rw [hTargetZero 0] at hleft
      exact hleft
    · rcases hright with ⟨hpositive, _⟩
      exact (Nat.not_lt_zero _ hpositive).elim
  have hFirstNonnegative : 0 <= a.order (0 : Fin (m + 3)) :=
    ((a.he2022ClassicProposition24 hClassic).oddIndexed
      0 0 le_rfl Even.zero Even.zero).1
  have hFirst : a.order (0 : Fin (m + 3)) = 0 := by omega
  have hNonnegative :=
    (a.he2022ClassicProposition24 hClassic).nonnegativeOfFirstZero hFirst
  intro i
  have hCondition := hTest.1 i
  rcases hCondition with hleft | hright
  · have hSourceNonnegative :=
      hNonnegative (⟨i.val, by omega⟩ : Fin (m + 3))
    rw [hTargetZero i] at hleft
    omega
  · rcases hright with ⟨hiPositive, hiLarge, hsum⟩
    have hCurrentNonnegative :=
      hNonnegative (⟨i.val, by omega⟩ : Fin (m + 3))
    have hNextNonnegative :=
      hNonnegative (⟨i.val + 1, hiLarge⟩ : Fin (m + 3))
    have hPreviousZero :
        b.order ⟨i.val - 1, by omega⟩ = 0 := hTargetZero _
    have hCurrentZero : b.order i = 0 := hTargetZero i
    rw [hPreviousZero, hCurrentZero, zero_add] at hsum
    omega

/-- Necessity in Lemma 5.4: the printed test forces `J1'_E(n-1)`. -/
theorem he2022ClassicLemma54_j1Prime_of_publishedTest
    [QuadraticDefectLaws K] [DyadicDiscriminantClassLaws K]
    {m : Nat} (t : Nat) (a : GoodBONG q L (m + 3))
    (hSource : 2 * t + 5 <= m + 3)
    (hClassic : Lattice.IsClassicIntegral q L)
    (hTest : a.HeClassicLemma54PublishedTest t (by omega)) :
    a.HeClassicJ1EPrime (2 * t + 2) (by omega) := by
  have hOrders := a.he2022ClassicLemma54_orders_of_publishedTest t
    hSource hClassic hTest
  have hTest' := hTest
  unfold HeClassicLemma54PublishedTest at hTest'
  dsimp only at hTest'
  let omegaUnit : Kˣ := heClassicOmega (K := K)
  have hOmegaOrder : ordUnit K omegaUnit = 0 :=
    heClassicOmega_order (K := K)
  let b := heClassicOddC1GoodBONG (K := K) t omegaUnit
    (by rw [hOmegaOrder])
  let first : RepresentationIndex (m + 3) (2 * t + 3) :=
    { val := 1
      pos := by omega
      lt_large := by omega
      le_small := by omega }
  have hTargetOrder : b.order (0 : Fin (2 * t + 3)) = 0 := by
    exact (heClassicLemma54Test_order_zero (K := K) t) 0
  have hSourceLower := a.he2022Classic_alphaOne_le_firstRepresentationAlpha
    b (fun j _hj => hOrders ⟨j.val, by omega⟩) hTargetOrder first rfl
  have hDefect := hTest'.2 first
  have hTargetCap := a.truncatedPrefixDefect_le_rightCap
    b 1 first.val first.val
  rw [b.prefixAlphaCap_of_internal (by simp [first]) (by
      dsimp only [first]
      omega)] at hTargetCap
  have hCapIndex :
      (⟨first.val - 1, by dsimp only [first]; omega⟩ : Fin (2 * t + 2)) =
        0 := by
    apply Fin.ext
    dsimp only [first]
    norm_num
  rw [hCapIndex] at hTargetCap
  have hBeta : b.alphaValue (0 : Fin (2 * t + 2)) = 1 := by
    have hAll := heClassicOddC1_alpha_eq_one (K := K) t omegaUnit 1
      (by rw [hOmegaOrder]) (Or.inr rfl)
      (by rw [hOmegaOrder]; norm_num)
      (by
        rw [heClassicOmega_defect (K := K)]
        norm_num)
    exact hAll 0
  rw [hBeta] at hTargetCap
  have hAlphaUpperTop :
      (a.alphaValue (0 : Fin (m + 2)) : WithTop ℚ) <= 1 := by
    calc
      (a.alphaValue (0 : Fin (m + 2)) : WithTop ℚ) <=
          a.representationAlpha b first := hSourceLower
      _ = (a.representationAlphaValue b first : WithTop ℚ) :=
        (a.coe_representationAlphaValue b first).symm
      _ <= a.truncatedPrefixDefect b 1 first.val first.val := hDefect
      _ <= (1 : WithTop ℚ) := hTargetCap
  have hAlphaUpper : a.alphaValue (0 : Fin (m + 2)) <= 1 := by
    exact_mod_cast hAlphaUpperTop
  let terminal : Fin (m + 2) := ⟨2 * t + 2, by omega⟩
  have hZeroPrefix : forall j : Fin (m + 3),
      j <= terminal.castSucc → a.order j = 0 := by
    intro j hj
    have hjBound : j.val < 2 * t + 3 := by
      have hjVal := Fin.mk_le_mk.mp hj
      change j.val <= 2 * t + 2 at hjVal
      omega
    have h := hOrders ⟨j.val, hjBound⟩
    have hIndex : (⟨j.val, by omega⟩ : Fin (m + 3)) = j := Fin.ext rfl
    rw [hIndex] at h
    exact h
  have hAlphas :=
    (a.he2022ClassicProposition24 hClassic).alphaOneOnZeroPrefix
      terminal hZeroPrefix (0 : Fin (m + 2)) (Fin.zero_le terminal)
        hAlphaUpper
  constructor
  · exact hOrders
  · intro i
    let sourceGap : Fin (m + 2) := ⟨i.val, by omega⟩
    exact hAlphas sourceGap (Fin.mk_lt_mk.mpr i.isLt)

/-- `J1'_E(n-1)` together with the terminal data in `J2_E(n-1)`
implies Theorem 2.5(i)--(ii) for every classic integral odd-rank target. -/
theorem he2022ClassicLemma54_all_of_j1Prime_j2
    [QuadraticDefectLaws K]
    {m : Nat} (t : Nat) (a : GoodBONG q L (m + 3))
    (hSource : 2 * t + 5 <= m + 3)
    (hClassic : Lattice.IsClassicIntegral q L)
    (hJ1 : a.HeClassicJ1EPrime (2 * t + 2) (by omega))
    (hJ2 : a.HeClassicJ2E (2 * t + 2) (by omega)) :
    HeClassicAllOrderAndDefectConditions.{u, v, w}
      (n := 2 * t + 2) a (by omega) := by
  intro W _ _ r M b hBClassic
  have hZero : forall k : Fin (m + 3), k.val < 2 * t + 3 →
      a.order k = 0 := by
    intro k hk
    let small : Fin (2 * t + 3) := ⟨k.val, hk⟩
    have h := hJ1.1 small
    have hIndex : (⟨small.val, by omega⟩ : Fin (m + 3)) = k :=
      Fin.ext rfl
    rw [hIndex] at h
    exact h
  have hAlpha : forall k : Fin (m + 2), k.val < 2 * t + 3 →
      a.alphaValue k = 1 := by
    intro k hk
    by_cases hEarly : k.val < 2 * t + 2
    · let small : Fin (2 * t + 2) := ⟨k.val, hEarly⟩
      have h := hJ1.2 small
      have hIndex : (⟨small.val, by omega⟩ : Fin (m + 2)) = k :=
        Fin.ext rfl
      rw [hIndex] at h
      exact h
    · have hLast : k.val = 2 * t + 2 := by omega
      have hIndex : k = (⟨2 * t + 2, by omega⟩ : Fin (m + 2)) :=
        Fin.ext hLast
      rw [hIndex]
      exact hJ2.1
  have hEquality :
      a.truncatedPrefixDefect a ((-1) ^ (t + 2)) 0 (2 * t + 4) =
        ((((1 - a.order ⟨2 * t + 3, by omega⟩ : Int) : ℚ) :
          WithTop ℚ)) := by
    have hRaw := hJ2.2.1
    have hNext : 2 * t + 2 + 1 = 2 * t + 3 := by omega
    have hLength : 2 * t + 2 + 2 = 2 * t + 4 := by omega
    have hExponent : (2 * t + 2 + 2) / 2 = t + 2 := by omega
    have hSum :
        (((a.order ⟨2 * t + 3, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
          a.truncatedPrefixDefect a ((-1) ^ (t + 2)) 0
            (2 * t + 4) = 1 := by
      simpa only [hNext, hLength, hExponent] using hRaw
    apply WithTop.add_left_cancel (WithTop.coe_ne_top)
    calc
      (((a.order ⟨2 * t + 3, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
          a.truncatedPrefixDefect a ((-1) ^ (t + 2)) 0
            (2 * t + 4) = 1 := hSum
      _ = (((a.order ⟨2 * t + 3, by omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
          ((((1 - a.order ⟨2 * t + 3, by omega⟩ : Int) : ℚ) :
            WithTop ℚ)) := by
        norm_cast
        ring
  constructor
  · intro i
    exact a.he2022ClassicCorollary310ii (m := m + 1) t b
      (by omega) hBClassic hZero i
  · intro i
    exact a.he2022ClassicCorollary311iii t b (by omega)
      hClassic hBClassic hZero hAlpha hEquality i

/-- Universal validity immediately restricts to the single published
test. -/
theorem he2022ClassicLemma54_publishedTest_of_all
    [QuadraticDefectLaws K] [DyadicDiscriminantClassLaws K]
    {m : Nat} (t : Nat) (a : GoodBONG q L (m + 3))
    (hSource : 2 * t + 5 <= m + 3)
    (hAll : HeClassicAllOrderAndDefectConditions.{u, v, u}
      (n := 2 * t + 2) a (by omega)) :
    a.HeClassicLemma54PublishedTest t (by omega) := by
  unfold HeClassicLemma54PublishedTest
  dsimp only
  exact hAll _ (heClassicOddC1_isClassicIntegral (K := K) t
    (heClassicOmega (K := K)) (by
      rw [heClassicOmega_order (K := K)]))

/-- He (2024), Lemma 5.4, with the terminal `J2_E(n-1)` premise used by
the printed proof made explicit.  The ambient-space hypothesis is retained
to mirror the paper, although the numerical equivalence itself does not use
it. -/
theorem he2022ClassicLemma54
    [QuadraticDefectLaws K] [DyadicDiscriminantClassLaws K]
    {m : Nat} (t : Nat) (a : GoodBONG q L (m + 3))
    (hSource : 2 * t + 5 <= m + 3)
    (hClassic : Lattice.IsClassicIntegral q L)
    (_hAmbient : Lattice.AmbientlyNUniversal.{u, v, u} q (2 * t + 3))
    (hJ2 : a.HeClassicJ2E (2 * t + 2) (by omega)) :
    HeClassicAllOrderAndDefectConditions.{u, v, u}
        (n := 2 * t + 2) a (by omega) ↔
      a.HeClassicJ1EPrime (2 * t + 2) (by omega) := by
  constructor
  · intro hAll
    exact a.he2022ClassicLemma54_j1Prime_of_publishedTest t hSource
      hClassic (a.he2022ClassicLemma54_publishedTest_of_all t hSource hAll)
  · intro hJ1
    exact a.he2022ClassicLemma54_all_of_j1Prime_j2
      t hSource hClassic hJ1 hJ2

/-- Lemma 5.4(i) `<->` (ii), under the same explicit terminal premise. -/
theorem he2022ClassicLemma54_all_iff_publishedTest
    [QuadraticDefectLaws K] [DyadicDiscriminantClassLaws K]
    {m : Nat} (t : Nat) (a : GoodBONG q L (m + 3))
    (hSource : 2 * t + 5 <= m + 3)
    (hClassic : Lattice.IsClassicIntegral q L)
    (hJ2 : a.HeClassicJ2E (2 * t + 2) (by omega)) :
    HeClassicAllOrderAndDefectConditions.{u, v, u}
        (n := 2 * t + 2) a (by omega) ↔
      a.HeClassicLemma54PublishedTest t (by omega) := by
  constructor
  · exact a.he2022ClassicLemma54_publishedTest_of_all t hSource
  · intro hTest
    exact a.he2022ClassicLemma54_all_of_j1Prime_j2
      t hSource hClassic
      (a.he2022ClassicLemma54_j1Prime_of_publishedTest t
        hSource hClassic hTest) hJ2

end BONG.GoodBONG

end Bong
