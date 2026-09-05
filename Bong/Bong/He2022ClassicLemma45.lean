/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2022ClassicLemma43
import Bong.Bong.He2022ClassicLemma44
import Bong.Bong.He2022ClassicCorollary312
import Bong.Bong.SplitQuaternaryPrefixDeterminant

/-!
# He (2024), Lemma 4.5

The middle statement is retained as the four literal publisher tests
`H_e^n(1)`, `C_1^n(omega)`, `C_2^n(omega)`, and, when `e=1`,
`H_e^n(Delta)`.  The proof below first isolates equation (4.1), then derives
the alpha and signed-prefix equality in `J2_E(n)`, and finally invokes the
already checked Corollary 3.12(ii) for sufficiency.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG.GoodBONG

/-- The literal finite testing family in Lemma 4.5(ii). -/
noncomputable def HeClassicLemma45PublishedTests
    [QuadraticDefectLaws K] [DyadicDiscriminantClassLaws K]
    {m : Nat} (t : Nat) (a : GoodBONG q L (m + 4)) : Prop :=
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
  let omega := heClassicOmega (K := K)
  let omegaSharp := heClassicOmegaSharp (K := K)
  let omegaNonnegative : 0 <= ordUnit K omega := by
    rw [heClassicOmega_order (K := K)]
  let omegaSharpOrder : ordUnit K omegaSharp = 0 :=
    heClassicOmegaSharp_order (K := K)
  let bOne := heClassicEvenHGoodBONG (K := K) t 1 (Or.inl rfl) oneOrder
  let bDelta := heClassicEvenHGoodBONG (K := K) t delta
    (Or.inr rfl) deltaOrder
  let bC1 := heClassicEvenC1GoodBONG (K := K) t omega omegaNonnegative
  let bC2 := heClassicEvenC2GoodBONG (K := K) t omega omegaSharp
    omegaNonnegative omegaSharpOrder
  a.CentralRepresentationConditionsPrime bOne ∧
    a.CentralRepresentationConditionsPrime bC1 ∧
      a.CentralRepresentationConditionsPrime bC2 ∧
        (ramificationIndex K = 1 →
          a.CentralRepresentationConditionsPrime bDelta)

/-- Universal validity of condition (iii) implies its validity on the four
published test rows. -/
theorem he2022ClassicLemma45_publishedTests_of_all
    [QuadraticDefectLaws K] [DyadicDiscriminantClassLaws K]
    {m : Nat} (t : Nat) (a : GoodBONG q L (m + 4))
    (hAll : HeClassicAllCentralRepresentationConditionsPrime.{u, v, u}
      (n := 2 * t + 1) a) :
    a.HeClassicLemma45PublishedTests t := by
  unfold HeClassicLemma45PublishedTests
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
  let omega := heClassicOmega (K := K)
  let omegaSharp := heClassicOmegaSharp (K := K)
  let omegaNonnegative : 0 <= ordUnit K omega := by
    rw [heClassicOmega_order (K := K)]
  let omegaSharpOrder : ordUnit K omegaSharp = 0 :=
    heClassicOmegaSharp_order (K := K)
  let bOne := heClassicEvenHGoodBONG (K := K) t 1 (Or.inl rfl) oneOrder
  let bDelta := heClassicEvenHGoodBONG (K := K) t delta
    (Or.inr rfl) deltaOrder
  let bC1 := heClassicEvenC1GoodBONG (K := K) t omega omegaNonnegative
  let bC2 := heClassicEvenC2GoodBONG (K := K) t omega omegaSharp
    omegaNonnegative omegaSharpOrder
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hAll bOne
      (heClassicEvenH_isClassicIntegral (K := K) t 1 (Or.inl rfl) oneOrder)
  · exact hAll bC1
      (heClassicEvenC1_isClassicIntegral (K := K) t omega omegaNonnegative)
  · exact hAll bC2
      (heClassicEvenC2_isClassicIntegral (K := K) t omega omegaSharp
        omegaNonnegative omegaSharpOrder)
  · intro _heOne
    exact hAll bDelta
      (heClassicEvenH_isClassicIntegral (K := K) t delta
        (Or.inr rfl) deltaOrder)

/-- Equation (4.1), proved from the literal tests in Lemma 4.5(ii). -/
theorem he2022ClassicLemma45_signedPrefix_upper
    [QuadraticDefectLaws K] [DyadicDiscriminantClassLaws K]
    {m : Nat} (t : Nat) (a : GoodBONG q L (m + 4))
    (hSource : 2 * t + 4 <= m + 4)
    (hAClassic : Lattice.IsClassicIntegral q L)
    (hJ1 : a.HeClassicJ1EPrime (2 * t + 2) (by omega))
    (hJ2Prime : a.HeClassicJ2EPrime (2 * t + 2) (by omega))
    (hTests : a.HeClassicLemma45PublishedTests t) :
    a.truncatedPrefixDefect a ((-1) ^ (t + 2)) 0 (2 * t + 4) <=
      ((((1 - a.order ⟨2 * t + 3, by omega⟩ : Int) : ℚ) :
        WithTop ℚ)) := by
  let D : WithTop ℚ :=
    a.truncatedPrefixDefect a ((-1) ^ (t + 2)) 0 (2 * t + 4)
  let R : Int := a.order ⟨2 * t + 3, by omega⟩
  let raw : WithTop ℚ := defectOrder (K := K)
    (((-1 : Kˣ) ^ (t + 2)) * a.prefixProduct (2 * t + 4))
  let twoE : WithTop ℚ :=
    ((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ)
  by_cases heLarge : 1 < ramificationIndex K
  · have hadd := hJ2Prime heLarge
    have hhalfIndex : (2 * t + 2 + 2) / 2 = t + 2 := by omega
    have horderIndex : 2 * t + 2 + 1 = 2 * t + 3 := by omega
    have hlength : 2 * t + 2 + 2 = 2 * t + 4 := by omega
    exact truncatedPrefixDefect_le_one_sub_order_of_add_le R D (by
      simpa only [D, R, hhalfIndex, horderIndex, hlength] using hadd)
  · have hePositive : 0 < ramificationIndex K :=
      ramificationIndex_pos (K := K)
    have heOne : ramificationIndex K = 1 := by omega
    by_contra hupper
    have hstrict : ((((1 - R : Int) : ℚ) : WithTop ℚ)) < D :=
      lt_of_not_ge (by simpa only [D, R] using hupper)
    have hsum : (1 : WithTop ℚ) < (((R : Int) : ℚ) : WithTop ℚ) + D := by
      calc
        (1 : WithTop ℚ) =
            (((R : Int) : ℚ) : WithTop ℚ) +
              ((((1 - R : Int) : ℚ) : WithTop ℚ)) := by
                norm_cast
                ring
        _ < (((R : Int) : ℚ) : WithTop ℚ) + D :=
          WithTop.add_lt_add_left WithTop.coe_ne_top hstrict
    unfold HeClassicLemma45PublishedTests at hTests
    dsimp only at hTests
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
    let omegaUnit := heClassicOmega (K := K)
    let omegaSharp := heClassicOmegaSharp (K := K)
    let omegaNonnegative : 0 <= ordUnit K omegaUnit := by
      rw [heClassicOmega_order (K := K)]
    let omegaSharpOrder : ordUnit K omegaSharp = 0 :=
      heClassicOmegaSharp_order (K := K)
    let bOne := heClassicEvenHGoodBONG (K := K) t 1
      (Or.inl rfl) oneOrder
    let bDelta := heClassicEvenHGoodBONG (K := K) t delta
      (Or.inr rfl) deltaOrder
    let bC1 := heClassicEvenC1GoodBONG (K := K) t omegaUnit
      omegaNonnegative
    let bC2 := heClassicEvenC2GoodBONG (K := K) t omegaUnit omegaSharp
      omegaNonnegative omegaSharpOrder
    by_cases hRawLt : raw < twoE
    · have hfailure := a.he2022ClassicLemma43i t hSource hJ1 heOne
          (by simpa only [D, R] using hsum) (Or.inl (by
            simpa only [raw, twoE] using hRawLt))
      dsimp only at hfailure
      let i := he2022ClassicLemma43Index t hSource
      rcases hfailure with hOneFails | hDeltaFails
      · exact hOneFails
          ((a.heClassicPublishedCentralConditions_iff_forall_at bOne).mp
            hTests.1 i)
      · exact hDeltaFails
          ((a.heClassicPublishedCentralConditions_iff_forall_at bDelta).mp
            (hTests.2.2.2 heOne) i)
    · have hRawGe : twoE <= raw := le_of_not_gt hRawLt
      by_cases hTwoELeD : twoE <= D
      · have hfailure := a.he2022ClassicLemma43i t hSource hJ1 heOne
            (by simpa only [D, R] using hsum) (Or.inr (by
              simpa only [D, twoE] using hTwoELeD))
        dsimp only at hfailure
        let i := he2022ClassicLemma43Index t hSource
        rcases hfailure with hOneFails | hDeltaFails
        · exact hOneFails
            ((a.heClassicPublishedCentralConditions_iff_forall_at bOne).mp
              hTests.1 i)
        · exact hDeltaFails
            ((a.heClassicPublishedCentralConditions_iff_forall_at bDelta).mp
              (hTests.2.2.2 heOne) i)
      · have hDLtTwoE : D < twoE := lt_of_not_ge hTwoELeD
        have hExtra : 2 * t + 5 <= m + 4 := by
          by_contra hnotExtra
          have hlast : 2 * t + 4 = m + 4 := by omega
          have hDraw : D = raw := by
            dsimp only [D, raw]
            unfold truncatedPrefixDefect
            rw [a.prefixAlphaCap_zero, hlast, a.prefixAlphaCap_last]
            simp [GoodBONG.prefixProduct]
          rw [hDraw] at hDLtTwoE
          exact (not_lt_of_ge hRawGe) hDLtTwoE
        let gap : Fin (m + 3) := ⟨2 * t + 3, by omega⟩
        have hDFormula : D = min raw (a.alphaValue gap : WithTop ℚ) := by
          dsimp only [D, raw, gap]
          unfold truncatedPrefixDefect
          rw [a.prefixAlphaCap_zero,
            a.prefixAlphaCap_of_internal (by omega) (by omega)]
          simp [GoodBONG.prefixProduct]
        have hDAlpha : D = (a.alphaValue gap : WithTop ℚ) := by
          by_cases hRawLeAlpha : raw <= (a.alphaValue gap : WithTop ℚ)
          · rw [min_eq_left hRawLeAlpha] at hDFormula
            have : raw < twoE := by simpa only [hDFormula] using hDLtTwoE
            exact (not_lt_of_ge hRawGe this).elim
          · have hAlphaLeRaw : (a.alphaValue gap : WithTop ℚ) <= raw :=
              le_of_not_ge hRawLeAlpha
            simpa only [min_eq_right hAlphaLeRaw] using hDFormula
        have hfirst : a.order (0 : Fin (m + 4)) = 0 := by
          let first : Fin (2 * t + 3) := ⟨0, by omega⟩
          have h := hJ1.1 first
          have hindex : (⟨first.val, by omega⟩ : Fin (m + 4)) = 0 :=
            Fin.ext rfl
          rw [hindex] at h
          exact h
        have hRNonnegative : 0 <= R := by
          exact (a.he2022ClassicProposition24 hAClassic).nonnegativeOfFirstZero
            hfirst ⟨2 * t + 3, by omega⟩
        have hRZero : R = 0 := by
          by_contra hRNe
          have hROne : 1 <= R := by omega
          have hfailure := a.he2022ClassicLemma43ii t hExtra hJ1 heOne
            (by simpa only [D, R] using hsum)
            (by simpa only [D, gap] using hDAlpha)
            (by simpa only [R] using hROne)
          dsimp only at hfailure
          let i := he2022ClassicLemma43Index t (by omega :
            2 * t + 4 <= m + 4)
          rcases hfailure with hC1Fails | hC2Fails
          · exact hC1Fails
              ((a.heClassicPublishedCentralConditions_iff_forall_at bC1).mp
                hTests.2.1 i)
          · exact hC2Fails
              ((a.heClassicPublishedCentralConditions_iff_forall_at bC2).mp
                hTests.2.2.1 i)
        have hAlphaOneLt : (1 : ℚ) < a.alphaValue gap := by
          have hsum' := hsum
          rw [hRZero, Int.cast_zero, WithTop.coe_zero, zero_add, hDAlpha] at hsum'
          exact_mod_cast hsum'
        have hAlphaLtTwo : a.alphaValue gap < (2 : ℚ) := by
          have hlt := hDLtTwoE
          rw [hDAlpha] at hlt
          dsimp only [twoE] at hlt
          rw [heOne] at hlt
          norm_num at hlt
          rw [← a.coe_alphaValue gap] at hlt
          exact WithTop.coe_lt_coe.mp hlt
        have hAlphaIntegral : IsRationalInteger (a.alphaValue gap) := by
          rcases (a.he2022ClassicProposition23 gap).arithmeticShape with
            hsmall | hlarge
          · exact hsmall.2.2
          · rw [heOne] at hlarge
            norm_num at hlarge
            linarith
        rcases hAlphaIntegral with ⟨z, hz⟩
        have hzOne : (1 : Int) < z := by
          rw [hz] at hAlphaOneLt
          exact_mod_cast hAlphaOneLt
        have hzTwo : z < (2 : Int) := by
          rw [hz] at hAlphaLtTwo
          exact_mod_cast hAlphaLtTwo
        omega

/-- The first part of `J2_E(n)`: the next alpha is one.  The two cases
`R_(n+2)=1` and `R_(n+2)=0` are the two cases in the publisher proof. -/
theorem he2022ClassicLemma45_nextAlpha
    [QuadraticDefectLaws K]
    {m : Nat} (t : Nat) (a : GoodBONG q L (m + 4))
    (hSource : 2 * t + 4 <= m + 4)
    (hJ1 : a.HeClassicJ1EPrime (2 * t + 2) (by omega))
    (hUpper :
      (((a.order ⟨2 * t + 3, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
          a.truncatedPrefixDefect a ((-1) ^ (t + 2)) 0
            (2 * t + 4) <= 1) :
    a.alphaValue ⟨2 * t + 2, by omega⟩ = 1 := by
  have hcases := a.he2022ClassicLemma44 (j := 2 * t + 4)
    (by omega) hSource
    (by
      let previous : Fin (2 * t + 3) := ⟨2 * t + 1, by omega⟩
      have h := hJ1.1 previous
      change a.order ⟨2 * t + 1, by omega⟩ = 0 at h
      exact h)
    (by
      have hhalf : (2 * t + 4) / 2 = t + 2 := by omega
      have hindex : 2 * t + 4 - 1 = 2 * t + 3 := by omega
      simpa only [hhalf, hindex] using hUpper)
  rcases hcases.1 with hRZero | hROne
  · let leftGap : Fin (m + 3) := ⟨2 * t + 1, by omega⟩
    let rightGap : Fin (m + 3) := ⟨2 * t + 2, by omega⟩
    have hRZero' : a.order ⟨2 * t + 3, by omega⟩ = 0 := by
      change a.order ⟨2 * t + 3, by omega⟩ = 0 at hRZero
      exact hRZero
    have hleftOrder :
        a.order (⟨2 * t + 1, by omega⟩ : Fin (m + 4)) = 0 := by
      let small : Fin (2 * t + 3) := ⟨2 * t + 1, by omega⟩
      simpa only [small] using hJ1.1 small
    have hmiddleOrder :
        a.order (⟨2 * t + 2, by omega⟩ : Fin (m + 4)) = 0 := by
      let small : Fin (2 * t + 3) := ⟨2 * t + 2, by omega⟩
      simpa only [small] using hJ1.1 small
    have hconstant := (a.he2022ClassicProposition22).constantAdjacentSum
      leftGap rightGap (by apply Fin.mk_le_mk.mpr; omega)
      (by
        unfold adjacentOrderSum
        change a.order (⟨2 * t + 1, by omega⟩ : Fin (m + 4)) +
            a.order (⟨2 * t + 2, by omega⟩ : Fin (m + 4)) =
          a.order (⟨2 * t + 2, by omega⟩ : Fin (m + 4)) +
            a.order ⟨2 * t + 3, by omega⟩
        rw [hleftOrder, hmiddleOrder, hRZero'])
      rightGap (by apply Fin.mk_le_mk.mpr; omega) le_rfl
    unfold alphaLeftEndpoint at hconstant
    have hleftCast : a.order leftGap.castSucc = 0 := by
      have hindex : leftGap.castSucc =
          (⟨2 * t + 1, by omega⟩ : Fin (m + 4)) := Fin.ext rfl
      rw [hindex]
      exact hleftOrder
    have hrightCast : a.order rightGap.castSucc = 0 := by
      have hindex : rightGap.castSucc =
          (⟨2 * t + 2, by omega⟩ : Fin (m + 4)) := Fin.ext rfl
      rw [hindex]
      exact hmiddleOrder
    rw [hleftCast, hrightCast] at hconstant
    norm_num at hconstant
    have hprevious : a.alphaValue leftGap = 1 := by
      let small : Fin (2 * t + 2) := ⟨2 * t + 1, by omega⟩
      simpa only [leftGap, small] using hJ1.2 small
    simpa only [rightGap] using hconstant.trans hprevious
  · let gap : Fin (m + 3) := ⟨2 * t + 2, by omega⟩
    have hROne' : a.order ⟨2 * t + 3, by omega⟩ = 1 := by
      change a.order ⟨2 * t + 3, by omega⟩ = 1 at hROne
      exact hROne
    apply a.alphaValue_eq_one_of_orderGap_eq_endpoint gap
    right
    unfold orderGap
    have hleft : gap.castSucc =
        (⟨2 * t + 2, by omega⟩ : Fin (m + 4)) := Fin.ext rfl
    have hright : gap.succ =
        (⟨2 * t + 3, by omega⟩ : Fin (m + 4)) := Fin.ext rfl
    rw [hleft, hright, hROne']
    let small : Fin (2 * t + 3) := ⟨2 * t + 2, by omega⟩
    have hzero := hJ1.1 small
    have hindex : (⟨small.val, by omega⟩ : Fin (m + 4)) =
        ⟨2 * t + 2, by omega⟩ := Fin.ext rfl
    rw [hindex] at hzero
    rw [hzero]
    omega

/-- Repeated capped-defect domination gives the reverse inequality in the
signed-prefix equality of `J2_E(n)`. -/
theorem he2022ClassicLemma45_signedPrefix_lower
    [QuadraticDefectLaws K]
    {m : Nat} (t : Nat) (a : GoodBONG q L (m + 4))
    (hSource : 2 * t + 4 <= m + 4)
    (hJ1 : a.HeClassicJ1EPrime (2 * t + 2) (by omega))
    (hNextAlpha : a.alphaValue ⟨2 * t + 2, by omega⟩ = 1)
    (hRNonnegative : 0 <= a.order ⟨2 * t + 3, by omega⟩) :
    ((((1 - a.order ⟨2 * t + 3, by omega⟩ : Int) : ℚ) :
        WithTop ℚ)) <=
      a.truncatedPrefixDefect a ((-1) ^ (t + 2)) 0
        (2 * t + 4) := by
  let R : Int := a.order ⟨2 * t + 3, by omega⟩
  let threshold : WithTop ℚ := ((((1 - R : Int) : ℚ) : WithTop ℚ))
  have hAdjacent : forall k : Nat, k <= t + 1 ->
      threshold <= a.truncatedPrefixDefect a (-1) (2 * k) (2 * k + 2) := by
    intro k hk
    let gap : Fin (m + 3) := ⟨2 * k, by omega⟩
    have hAlpha : a.alphaValue gap = 1 := by
      by_cases hbefore : 2 * k < 2 * t + 2
      · let small : Fin (2 * t + 2) := ⟨2 * k, hbefore⟩
        simpa only [gap, small] using hJ1.2 small
      · have hfinal : 2 * k = 2 * t + 2 := by omega
        have hindex : gap = ⟨2 * t + 2, by omega⟩ := Fin.ext hfinal
        rw [hindex]
        exact hNextAlpha
    have hlocal := (a.he2022ClassicProposition23 gap).alphaOneDefect hAlpha
    have hleftZero : a.order gap.castSucc = 0 := by
      let small : Fin (2 * t + 3) := ⟨2 * k, by omega⟩
      have h := hJ1.1 small
      have hindex : (⟨small.val, by omega⟩ : Fin (m + 4)) =
          gap.castSucc := Fin.ext rfl
      rw [hindex] at h
      exact h
    by_cases hfinal : k = t + 1
    · have hright : gap.succ =
          (⟨2 * t + 3, by omega⟩ : Fin (m + 4)) := by
        apply Fin.ext
        simp only [gap, Fin.val_succ]
        omega
      have hgap : a.orderGap gap = R := by
        unfold orderGap
        rw [hleftZero, hright]
        simp only [R, sub_zero]
      rw [hgap] at hlocal
      simpa only [threshold, heHuAdjacentCappedDefect,
        Int.cast_sub, Int.cast_one] using hlocal.1
    · have hrightZero : a.order gap.succ = 0 := by
        let small : Fin (2 * t + 3) := ⟨2 * k + 1, by omega⟩
        have h := hJ1.1 small
        have hindex : (⟨small.val, by omega⟩ : Fin (m + 4)) =
            gap.succ := Fin.ext rfl
        rw [hindex] at h
        exact h
      have hgap : a.orderGap gap = 0 := by
        unfold orderGap
        rw [hleftZero, hrightZero]
        omega
      have hthresholdOne : threshold <= (1 : WithTop ℚ) := by
        dsimp only [threshold, R]
        exact_mod_cast (show
          (1 - a.order ⟨2 * t + 3, by omega⟩ : Int) <= 1 by omega)
      apply hthresholdOne.trans
      rw [hgap] at hlocal
      simpa only [heHuAdjacentCappedDefect, Int.cast_zero, sub_zero,
        WithTop.coe_one] using hlocal.1
  have hblocks : forall k : Nat, k <= t + 1 ->
      threshold <=
        a.truncatedPrefixDefect a ((-1) ^ (k + 1)) 0 (2 * (k + 1)) := by
    intro k
    induction k with
    | zero =>
        intro _hk
        simpa only [Nat.zero_add, Nat.mul_zero, zero_add, pow_one,
          Nat.mul_one] using hAdjacent 0 (by omega)
    | succ k ih =>
        intro hk
        have hprevious := ih (by omega)
        have hnext := hAdjacent (k + 1) (by omega)
        have hnext' : threshold <=
            a.truncatedPrefixDefect a (-1) (2 * (k + 1))
              (2 * (k + 2)) := by
          have hEnd : 2 * (k + 1) + 2 = 2 * (k + 2) := by omega
          simpa only [hEnd] using hnext
        have hdom := a.truncatedPrefixDefect_domination a a
          ((-1 : Kˣ) ^ (k + 1)) (-1) 0 (2 * (k + 1))
            (2 * (k + 2))
        have hmin : threshold <= min
            (a.truncatedPrefixDefect a ((-1) ^ (k + 1)) 0
              (2 * (k + 1)))
            (a.truncatedPrefixDefect a (-1) (2 * (k + 1))
              (2 * (k + 2))) := le_min hprevious hnext'
        have hsign : ((-1 : Kˣ) ^ (k + 1)) * (-1) =
            (-1 : Kˣ) ^ (k + 2) := by
          calc
            ((-1 : Kˣ) ^ (k + 1)) * (-1) =
                (-1 : Kˣ) ^ ((k + 1) + 1) :=
              (pow_succ (-1 : Kˣ) (k + 1)).symm
            _ = (-1 : Kˣ) ^ (k + 2) :=
              congrArg (fun n : Nat => (-1 : Kˣ) ^ n) (by omega)
        rw [hsign] at hdom
        exact hmin.trans hdom
  have hfinal := hblocks (t + 1) le_rfl
  have hexponent : t + 1 + 1 = t + 2 := by omega
  have hlength : 2 * (t + 1 + 1) = 2 * t + 4 := by omega
  simpa only [threshold, R, hexponent, hlength] using hfinal

/-- The alpha and signed-prefix-equality core of `J2_E(n)`.  The remaining
binary clause is the ambient rank assertion handled separately below. -/
theorem he2022ClassicLemma45_j2Core_of_publishedTests
    [QuadraticDefectLaws K] [DyadicDiscriminantClassLaws K]
    {m : Nat} (t : Nat) (a : GoodBONG q L (m + 4))
    (hSource : 2 * t + 4 <= m + 4)
    (hAClassic : Lattice.IsClassicIntegral q L)
    (hJ1 : a.HeClassicJ1EPrime (2 * t + 2) (by omega))
    (hJ2Prime : a.HeClassicJ2EPrime (2 * t + 2) (by omega))
    (hTests : a.HeClassicLemma45PublishedTests t) :
    a.alphaValue ⟨2 * t + 2, by omega⟩ = 1 ∧
      (((a.order ⟨2 * t + 3, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
          a.truncatedPrefixDefect a ((-1) ^ (t + 2)) 0
            (2 * t + 4) = 1 := by
  let R : Int := a.order ⟨2 * t + 3, by omega⟩
  let D : WithTop ℚ :=
    a.truncatedPrefixDefect a ((-1) ^ (t + 2)) 0 (2 * t + 4)
  have hUpper : D <= ((((1 - R : Int) : ℚ) : WithTop ℚ)) := by
    simpa only [D, R] using
      a.he2022ClassicLemma45_signedPrefix_upper t hSource hAClassic
        hJ1 hJ2Prime hTests
  have hUpperAdd : (((R : Int) : ℚ) : WithTop ℚ) + D <= 1 := by
    calc
      (((R : Int) : ℚ) : WithTop ℚ) + D <=
          (((R : Int) : ℚ) : WithTop ℚ) +
            ((((1 - R : Int) : ℚ) : WithTop ℚ)) :=
        by simpa only [add_comm] using
          (add_le_add_left hUpper (((R : Int) : ℚ) : WithTop ℚ))
      _ = 1 := by
        norm_cast
        ring
  have hNextAlpha := a.he2022ClassicLemma45_nextAlpha t hSource
    hJ1 (by simpa only [D, R] using hUpperAdd)
  have hfirst : a.order (0 : Fin (m + 4)) = 0 := by
    let first : Fin (2 * t + 3) := ⟨0, by omega⟩
    have h := hJ1.1 first
    have hindex : (⟨first.val, by omega⟩ : Fin (m + 4)) = 0 :=
      Fin.ext rfl
    rw [hindex] at h
    exact h
  have hRNonnegative : 0 <= R := by
    exact (a.he2022ClassicProposition24 hAClassic).nonnegativeOfFirstZero
      hfirst ⟨2 * t + 3, by omega⟩
  have hLower : ((((1 - R : Int) : ℚ) : WithTop ℚ)) <= D := by
    simpa only [D, R] using
      a.he2022ClassicLemma45_signedPrefix_lower t hSource hJ1 hNextAlpha
        (by simpa only [R] using hRNonnegative)
  have hDEq : D = ((((1 - R : Int) : ℚ) : WithTop ℚ)) :=
    le_antisymm hUpper hLower
  refine ⟨hNextAlpha, ?_⟩
  rw [show a.truncatedPrefixDefect a ((-1) ^ (t + 2)) 0
      (2 * t + 4) = D by rfl, hDEq]
  change (((R : Int) : ℚ) : WithTop ℚ) +
      ((((1 - R : Int) : ℚ) : WithTop ℚ)) = 1
  norm_cast
  ring

/-- The binary-rank clause in `J2_E(n)`.  Ambient universality leaves one
apparent rank-four exception, namely `H ⊥ H`; its full BONG determinant is
a square, so the signed full-prefix defect is infinite and contradicts the
finite equality already forced by the four publisher tests. -/
theorem he2022ClassicLemma45_binaryRank_of_ambient_and_equality
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [DyadicDiscriminantClassLaws K]
    {m : Nat} (t : Nat) (a : GoodBONG q L (m + 4))
    (hAmbient :
      Lattice.AmbientlyNUniversal.{u, v, u} q (2 * t + 2))
    (hSource : 2 * t + 4 <= m + 4)
    (hEquality :
      (((a.order ⟨2 * t + 3, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
          a.truncatedPrefixDefect a ((-1) ^ (t + 2)) 0
            (2 * t + 4) = 1) :
    2 * t + 2 = 2 -> 4 <= m + 3 := by
  letI : Module.Finite K V := L.moduleFinite
  have hClassification :=
    (Lattice.ambientlyEvenUniversal_rank_classification
      (q := q) t).mp hAmbient
  intro hbinary
  have ht : t = 0 := by omega
  subst t
  rcases hClassification with hStable | hExceptional
  · have hRank : Module.finrank K V = m + 4 :=
      a.toBONG.length_eq_finrank.symm
    omega
  · rcases hExceptional with ⟨_, hRankFour, hSplit⟩
    have hRank : Module.finrank K V = m + 4 :=
      a.toBONG.length_eq_finrank.symm
    have hm : m = 0 := by omega
    subst m
    have hPrefixSquare : IsSquare (a.prefixProduct 4) :=
      a.splitQuaternary_fullPrefix_isSquare hSplit
    have hPrefixSquareRaw :
        IsSquare (a.toBONG.prefixProduct 4) := by
      simpa only [GoodBONG.prefixProduct] using hPrefixSquare
    have hFullTop :
        a.truncatedPrefixDefect a ((-1 : Kˣ) ^ 2) 0 4 = ⊤ := by
      unfold truncatedPrefixDefect
      rw [a.prefixAlphaCap_zero]
      have hCap : a.prefixAlphaCap 4 = ⊤ := by
        exact a.prefixAlphaCap_last
      rw [hCap]
      simp only [min_top_right, GoodBONG.prefixProduct,
        BONG.prefixProduct_zero]
      rw [show (-1 : Kˣ) ^ 2 = 1 by norm_num]
      simpa only [one_mul] using
        (defectOrder_eq_top_of_isSquare hPrefixSquareRaw)
    have hFinite := hEquality
    rw [hFullTop] at hFinite
    exact (WithTop.top_ne_coe hFinite).elim

/-- Lemma 4.5(ii) implies the full invariant condition `J2_E(n)`, including
the exceptional binary-rank clause. -/
theorem he2022ClassicLemma45_j2_of_publishedTests
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [DyadicDiscriminantClassLaws K]
    {m : Nat} (t : Nat) (a : GoodBONG q L (m + 4))
    (hSource : 2 * t + 4 <= m + 4)
    (hAClassic : Lattice.IsClassicIntegral q L)
    (hAmbient :
      Lattice.AmbientlyNUniversal.{u, v, u} q (2 * t + 2))
    (hJ1 : a.HeClassicJ1EPrime (2 * t + 2) (by omega))
    (hJ2Prime : a.HeClassicJ2EPrime (2 * t + 2) (by omega))
    (hTests : a.HeClassicLemma45PublishedTests t) :
    a.HeClassicJ2E (2 * t + 2) (by omega) := by
  have hCore := a.he2022ClassicLemma45_j2Core_of_publishedTests t
    hSource hAClassic hJ1 hJ2Prime hTests
  unfold HeClassicJ2E
  refine ⟨hCore.1, ?_, ?_⟩
  · have hNext : 2 * t + 2 + 1 = 2 * t + 3 := by omega
    have hLength : 2 * t + 2 + 2 = 2 * t + 4 := by omega
    have hExponent : (2 * t + 2 + 2) / 2 = t + 2 := by omega
    simpa only [hNext, hLength, hExponent] using hCore.2
  · exact a.he2022ClassicLemma45_binaryRank_of_ambient_and_equality t
      hAmbient hSource hCore.2

/-- `J2_E(n)` implies condition (iii) for every classic integral target,
by the second assertion of Corollary 3.12(ii). -/
theorem he2022ClassicLemma45_all_of_j2
    {m : Nat} (t : Nat) (a : GoodBONG q L (m + 4))
    (hSource : 2 * t + 4 <= m + 4)
    (hAClassic : Lattice.IsClassicIntegral q L)
    (hJ1 : a.HeClassicJ1EPrime (2 * t + 2) (by omega))
    (hJ2 : a.HeClassicJ2E (2 * t + 2) (by omega)) :
    HeClassicAllCentralRepresentationConditionsPrime.{u, v, u}
      (n := 2 * t + 1) a := by
  intro W _ _ r M b hBClassic
  apply (a.heClassicPublishedCentralConditions_iff_forall_at b).2
  intro i
  have hzero : forall k : Fin (m + 4), k.val < 2 * t + 2 ->
      a.order k = 0 := by
    intro k hk
    let small : Fin (2 * t + 3) := ⟨k.val, by omega⟩
    have h := hJ1.1 small
    have hindex : (⟨small.val, by omega⟩ : Fin (m + 4)) = k :=
      Fin.ext rfl
    rw [hindex] at h
    exact h
  have hnext : a.order ⟨2 * t + 2, by omega⟩ = 0 := by
    let next : Fin (2 * t + 3) := ⟨2 * t + 2, by omega⟩
    have h := hJ1.1 next
    have hindex : (⟨next.val, by omega⟩ : Fin (m + 4)) =
        ⟨2 * t + 2, by omega⟩ := Fin.ext rfl
    rw [hindex] at h
    exact h
  have hSourceEquality :
      a.truncatedPrefixDefect a ((-1) ^ (t + 2)) 0 (2 * t + 4) =
        ((((1 - a.order ⟨2 * t + 3, by omega⟩ : Int) : ℚ) :
          WithTop ℚ)) := by
    have hJ2Equality :
        (((a.order ⟨2 * t + 3, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
            a.truncatedPrefixDefect a ((-1) ^ (t + 2)) 0
              (2 * t + 4) = 1 := by
      have hNext : 2 * t + 2 + 1 = 2 * t + 3 := by omega
      have hLength : 2 * t + 2 + 2 = 2 * t + 4 := by omega
      have hExponent : (2 * t + 2 + 2) / 2 = t + 2 := by omega
      simpa only [hNext, hLength, hExponent] using hJ2.2.1
    apply WithTop.add_left_cancel (WithTop.coe_ne_top)
    calc
      (((a.order ⟨2 * t + 3, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
          a.truncatedPrefixDefect a ((-1) ^ (t + 2)) 0 (2 * t + 4) = 1 :=
        hJ2Equality
      _ = (((a.order ⟨2 * t + 3, by omega⟩ : Int) : ℚ) :
            WithTop ℚ) +
          ((((1 - a.order ⟨2 * t + 3, by omega⟩ : Int) : ℚ) :
            WithTop ℚ)) := by
        norm_cast
        ring
  exact a.he2022ClassicCorollary312ii t b hSource hAClassic hBClassic
    hzero hnext hJ2.1 hSourceEquality i

/-- He (2024), Lemma 4.5(ii) ⇔ (iii): the four literal test lattices are
equivalent to `J2_E(n)`. -/
theorem he2022ClassicLemma45_publishedTests_iff_j2
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [DyadicDiscriminantClassLaws K]
    {m : Nat} (t : Nat) (a : GoodBONG q L (m + 4))
    (hSource : 2 * t + 4 <= m + 4)
    (hAClassic : Lattice.IsClassicIntegral q L)
    (hAmbient :
      Lattice.AmbientlyNUniversal.{u, v, u} q (2 * t + 2))
    (hJ1 : a.HeClassicJ1EPrime (2 * t + 2) (by omega))
    (hJ2Prime : a.HeClassicJ2EPrime (2 * t + 2) (by omega)) :
    a.HeClassicLemma45PublishedTests t ↔
      a.HeClassicJ2E (2 * t + 2) (by omega) := by
  constructor
  · exact a.he2022ClassicLemma45_j2_of_publishedTests t hSource
      hAClassic hAmbient hJ1 hJ2Prime
  · intro hJ2
    exact a.he2022ClassicLemma45_publishedTests_of_all t
      (a.he2022ClassicLemma45_all_of_j2 t hSource hAClassic hJ1 hJ2)

/-- He (2024), Lemma 4.5(i) ⇔ (ii): validity on every classic target is
equivalent to validity on the four printed test lattices. -/
theorem he2022ClassicLemma45_all_iff_publishedTests
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [DyadicDiscriminantClassLaws K]
    {m : Nat} (t : Nat) (a : GoodBONG q L (m + 4))
    (hSource : 2 * t + 4 <= m + 4)
    (hAClassic : Lattice.IsClassicIntegral q L)
    (hAmbient :
      Lattice.AmbientlyNUniversal.{u, v, u} q (2 * t + 2))
    (hJ1 : a.HeClassicJ1EPrime (2 * t + 2) (by omega))
    (hJ2Prime : a.HeClassicJ2EPrime (2 * t + 2) (by omega)) :
    HeClassicAllCentralRepresentationConditionsPrime.{u, v, u}
        (n := 2 * t + 1) a ↔
      a.HeClassicLemma45PublishedTests t := by
  constructor
  · exact a.he2022ClassicLemma45_publishedTests_of_all t
  · intro hTests
    exact a.he2022ClassicLemma45_all_of_j2 t hSource hAClassic hJ1
      (a.he2022ClassicLemma45_j2_of_publishedTests t hSource
        hAClassic hAmbient hJ1 hJ2Prime hTests)

/-- He (2024), Lemma 4.5, in its main invariant form: under the printed
ambient, classic-integrality, `J1'_E`, and `J2'_E` assumptions, condition
(iii) for all classic targets is equivalent to `J2_E`. -/
theorem he2022ClassicLemma45
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [DyadicDiscriminantClassLaws K]
    {m : Nat} (t : Nat) (a : GoodBONG q L (m + 4))
    (hSource : 2 * t + 4 <= m + 4)
    (hAClassic : Lattice.IsClassicIntegral q L)
    (hAmbient :
      Lattice.AmbientlyNUniversal.{u, v, u} q (2 * t + 2))
    (hJ1 : a.HeClassicJ1EPrime (2 * t + 2) (by omega))
    (hJ2Prime : a.HeClassicJ2EPrime (2 * t + 2) (by omega)) :
    HeClassicAllCentralRepresentationConditionsPrime.{u, v, u}
        (n := 2 * t + 1) a ↔
      a.HeClassicJ2E (2 * t + 2) (by omega) := by
  constructor
  · intro hAll
    exact a.he2022ClassicLemma45_j2_of_publishedTests t hSource
      hAClassic hAmbient hJ1 hJ2Prime
        (a.he2022ClassicLemma45_publishedTests_of_all t hAll)
  · exact a.he2022ClassicLemma45_all_of_j2 t hSource hAClassic hJ1

end BONG.GoodBONG

end Bong
