/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2022ClassicLemma45
import Bong.Bong.He2022ClassicCorollary313
import Bong.Bong.HeHu2022Lemma313

/-!
# He (2024), Lemma 4.6

The middle statement is kept as the literal pair `C_1^n(c), C_2^n(c)` for
normalized square-class representatives with defect zero or one.  It is
activated exactly under the publisher's extra-rank and large-last-gap
hypotheses.
-/

namespace Bong

open Dyadic AlternatingEndpointTower

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG.GoodBONG

/-- Every square class of finite defect zero or one lies in the domain of
the publisher's sharp operation. -/
theorem heClassicLowDefectSharpDomain
    [QuadraticDefectLaws K] [DyadicDiscriminantClassLaws K]
    (c : Kˣ)
    (hc : defectOrder (K := K) c = (0 : WithTop ℚ) ∨
      defectOrder (K := K) c = (1 : WithTop ℚ)) :
    HeHuSharpDomain c := by
  rcases hc with hzero | hone
  · apply heHuLemma45_sharpDomain_of_defect_lt_twoE c 0
    · simpa using hzero
    · have hePositive := ramificationIndex_pos (K := K)
      omega
  · apply heHuLemma45_sharpDomain_of_defect_lt_twoE c 1
    · simpa using hone
    · have hePositive := ramificationIndex_pos (K := K)
      omega

/-- The corresponding sharp parameter is a valuation unit. -/
theorem heClassicLowDefectSharp_order
    [QuadraticDefectLaws K] [DyadicDiscriminantClassLaws K]
    (c : Kˣ)
    (hc : defectOrder (K := K) c = (0 : WithTop ℚ) ∨
      defectOrder (K := K) c = (1 : WithTop ℚ)) :
    ordUnit K (heHuSharp c (heClassicLowDefectSharpDomain c hc)) = 0 := by
  apply (isValuationUnit_iff_ordUnit_eq_zero K _).1
  exact (heHu2022Proposition32 c
    (heClassicLowDefectSharpDomain c hc)).1

/-- For a low-defect parameter, the two even `C` rows are the two distinct
isometry classes in their common determinant square class. -/
theorem heClassicEvenC_lowDefectPairProperties
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [DyadicDiscriminantClassLaws K]
    (pairs : Nat) (c : Kˣ)
    (hc : defectOrder (K := K) c = (0 : WithTop ℚ) ∨
      defectOrder (K := K) c = (1 : WithTop ℚ)) :
    HeHuSpacePairProperties
      (heClassicEvenC1 (K := K) pairs c)
      (heClassicEvenC2 (K := K) pairs c
        (heHuSharp c (heClassicLowDefectSharpDomain c hc))) := by
  let hdomain := heClassicLowDefectSharpDomain c hc
  have Pbinary : HeHuSpacePairProperties
      (heHuBinaryFirst c) (heHuBinarySecond c hdomain) := by
    apply HeHuSpacePairProperties.of_det_not
    · exact heHuBinarySecond_determinantSquare_first c hdomain
    · exact heHuBinarySecond_not_represents_first c hdomain
  have P := Pbinary.append
    (standardHyperbolicEndpointTower (K := K) pairs)
  simpa only [hdomain, heClassicEvenC1, heClassicEvenC2,
    heClassicScaledHyperbolicTower_zero, heHuBinaryFirst,
    heHuBinarySecond, heHuBinaryTwist] using P

/-- The literal testing statement in Lemma 4.6(ii).  Representatives are
normalized to orders zero or one, as in Definition 2.6. -/
noncomputable def HeClassicLemma46PublishedTests
    [QuadraticDefectLaws K] [DyadicDiscriminantClassLaws K]
    {m : Nat} (t : Nat) (a : GoodBONG q L (m + 4)) : Prop :=
  forall (hExtra : 2 * t + 5 <= m + 4),
    2 * (ramificationIndex K : Int) <
        a.order ⟨2 * t + 4, by omega⟩ -
          a.order ⟨2 * t + 3, by omega⟩ ->
    forall (c : Kˣ)
      (hcOrder : ordUnit K c = 0 ∨ ordUnit K c = 1)
      (hcDefect : defectOrder (K := K) c = (0 : WithTop ℚ) ∨
        defectOrder (K := K) c = (1 : WithTop ℚ)),
      let hcNonnegative : 0 <= ordUnit K c := by rcases hcOrder with h | h <;> omega
      let hcDomain := heClassicLowDefectSharpDomain c hcDefect
      let cSharp := heHuSharp c hcDomain
      let hcSharpOrder : ordUnit K cSharp = 0 := by
        exact heClassicLowDefectSharp_order c hcDefect
      let bC1 := heClassicEvenC1GoodBONG (K := K) t c hcNonnegative
      let bC2 := heClassicEvenC2GoodBONG (K := K) t c cSharp
        hcNonnegative hcSharpOrder
      a.LongRepresentationConditions bC1 ∧
        a.LongRepresentationConditions bC2

/-- Universal validity of condition (iv) implies validity on the printed
pair of `C` tests. -/
theorem he2022ClassicLemma46_publishedTests_of_all
    [QuadraticDefectLaws K] [DyadicDiscriminantClassLaws K]
    {m : Nat} (t : Nat) (a : GoodBONG q L (m + 4))
    (hAll : HeClassicAllLongRepresentationConditions.{u, v, u}
      (n := 2 * t + 1) a) :
    a.HeClassicLemma46PublishedTests t := by
  intro hExtra hGap c hcOrder hcDefect
  dsimp only
  let hcNonnegative : 0 <= ordUnit K c := by omega
  let hcDomain := heClassicLowDefectSharpDomain c hcDefect
  let cSharp := heHuSharp c hcDomain
  let hcSharpOrder : ordUnit K cSharp = 0 := by
    exact heClassicLowDefectSharp_order c hcDefect
  let bC1 := heClassicEvenC1GoodBONG (K := K) t c hcNonnegative
  let bC2 := heClassicEvenC2GoodBONG (K := K) t c cSharp
    hcNonnegative hcSharpOrder
  refine ⟨hAll bC1 ?_, hAll bC2 ?_⟩
  · exact heClassicEvenC1_isClassicIntegral (K := K) t c hcNonnegative
  · exact heClassicEvenC2_isClassicIntegral (K := K) t c cSharp
      hcNonnegative hcSharpOrder

/-- The equality in `J2_E(n)`, together with Lemma 4.4, puts both its last
order and its signed capped defect in `{0,1}`. -/
theorem he2022ClassicLemma46_j2_cases
    [QuadraticDefectLaws K]
    {m : Nat} (t : Nat) (a : GoodBONG q L (m + 4))
    (hSource : 2 * t + 4 <= m + 4)
    (hJ1 : a.HeClassicJ1EPrime (2 * t + 2) (by omega))
    (hJ2 : a.HeClassicJ2E (2 * t + 2) (by omega)) :
    (a.order ⟨2 * t + 3, by omega⟩ = 0 ∨
        a.order ⟨2 * t + 3, by omega⟩ = 1) ∧
      (a.truncatedPrefixDefect a ((-1) ^ (t + 2)) 0
            (2 * t + 4) = 0 ∨
        a.truncatedPrefixDefect a ((-1) ^ (t + 2)) 0
            (2 * t + 4) = 1) := by
  have hPrevious : a.order ⟨2 * t + 1, by omega⟩ = 0 := by
    let previous : Fin (2 * t + 3) := ⟨2 * t + 1, by omega⟩
    have h := hJ1.1 previous
    change a.order ⟨2 * t + 1, by omega⟩ = 0 at h
    exact h
  have hJ2Equality :
      (((a.order ⟨2 * t + 3, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
          a.truncatedPrefixDefect a ((-1) ^ (t + 2)) 0
            (2 * t + 4) = 1 := by
    have hNext : 2 * t + 2 + 1 = 2 * t + 3 := by omega
    have hLength : 2 * t + 2 + 2 = 2 * t + 4 := by omega
    have hExponent : (2 * t + 2 + 2) / 2 = t + 2 := by omega
    simpa only [hNext, hLength, hExponent] using hJ2.2.1
  have hPreviousIndex : 2 * t + 4 - 1 = 2 * t + 3 := by omega
  have hExponent : (2 * t + 4) / 2 = t + 2 := by omega
  have hSum :
      (((a.order ⟨2 * t + 4 - 1, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
          a.truncatedPrefixDefect a ((-1) ^ ((2 * t + 4) / 2)) 0
            (2 * t + 4) <= 1 := by
    simpa only [hPreviousIndex, hExponent] using le_of_eq hJ2Equality
  have hCases := a.he2022ClassicLemma44 (j := 2 * t + 4)
    (by omega) hSource hPrevious hSum
  simpa only [hPreviousIndex, hExponent] using hCases

/-- Under failure of the last-gap bound, Proposition 2.2 removes the right
alpha cap.  Thus the `J2_E` capped defect is the actual defect of the signed
source prefix used as the parameter `c` in Lemma 4.6. -/
theorem he2022ClassicLemma46_rawDefect_eq_capped
    [QuadraticDefectLaws K]
    {m : Nat} (t : Nat) (a : GoodBONG q L (m + 4))
    (hSource : 2 * t + 4 <= m + 4)
    (hExtra : 2 * t + 5 <= m + 4)
    (hJ1 : a.HeClassicJ1EPrime (2 * t + 2) (by omega))
    (hJ2 : a.HeClassicJ2E (2 * t + 2) (by omega))
    (hLargeGap : 2 * (ramificationIndex K : Int) <
      a.order ⟨2 * t + 4, by omega⟩ -
        a.order ⟨2 * t + 3, by omega⟩) :
    let c := ((-1 : Kˣ) ^ (t + 2)) * a.prefixProduct (2 * t + 4)
    defectOrder (K := K) c =
      a.truncatedPrefixDefect a ((-1) ^ (t + 2)) 0
        (2 * t + 4) := by
  let gap : Fin (m + 3) := ⟨2 * t + 3, by omega⟩
  let c := ((-1 : Kˣ) ^ (t + 2)) * a.prefixProduct (2 * t + 4)
  let D := a.truncatedPrefixDefect a ((-1) ^ (t + 2)) 0
    (2 * t + 4)
  let raw := defectOrder (K := K) c
  have hGap : 2 * (ramificationIndex K : Int) < a.orderGap gap := by
    unfold orderGap
    have hleft : gap.castSucc =
        (⟨2 * t + 3, by omega⟩ : Fin (m + 4)) := Fin.ext rfl
    have hright : gap.succ =
        (⟨2 * t + 4, by omega⟩ : Fin (m + 4)) := Fin.ext rfl
    rw [hleft, hright]
    exact hLargeGap
  have hAlphaLarge :
      2 * (ramificationIndex K : ℚ) < a.alphaValue gap :=
    ((a.he2022ClassicProposition22).compareTwoE gap).1.mpr hGap
  have hAlphaGtOneQ : (1 : ℚ) < a.alphaValue gap := by
    have hePositive := ramificationIndex_pos (K := K)
    have hOneLe : (1 : ℚ) <= 2 * (ramificationIndex K : ℚ) := by
      exact_mod_cast (show (1 : Int) <=
        2 * (ramificationIndex K : Int) by omega)
    exact hOneLe.trans_lt hAlphaLarge
  have hAlphaGtOne : (1 : WithTop ℚ) < (a.alphaValue gap : WithTop ℚ) := by
    exact_mod_cast hAlphaGtOneQ
  have hDFormula : D = min (a.alphaValue gap : WithTop ℚ) raw := by
    dsimp only [D]
    unfold truncatedPrefixDefect
    rw [a.prefixAlphaCap_zero,
      a.prefixAlphaCap_of_internal (by omega) (by omega)]
    have hindex :
        (⟨2 * t + 4 - 1, by omega⟩ : Fin (m + 3)) = gap := by
      apply Fin.ext
      simp only [gap]
      omega
    rw [hindex]
    simp only [min_top_left, GoodBONG.prefixProduct,
      BONG.prefixProduct_zero, mul_one, raw, c, min_comm]
  have hDCases :=
    (a.he2022ClassicLemma46_j2_cases t hSource hJ1 hJ2).2
  have hDLeOne : D <= (1 : WithTop ℚ) := by
    rcases hDCases with hzero | hone
    · change D = 0 at hzero
      rw [hzero]
      norm_num
    · change D = 1 at hone
      rw [hone]
  have hRawLeAlpha : raw <= (a.alphaValue gap : WithTop ℚ) := by
    by_contra hnot
    have hAlphaLtRaw : (a.alphaValue gap : WithTop ℚ) < raw :=
      lt_of_not_ge hnot
    have hDEqAlpha : D = (a.alphaValue gap : WithTop ℚ) := by
      rw [hDFormula, min_eq_left hAlphaLtRaw.le]
    have hAlphaLeOne : (a.alphaValue gap : WithTop ℚ) <= 1 := by
      rw [← hDEqAlpha]
      exact hDLeOne
    exact (not_lt_of_ge hAlphaLeOne) hAlphaGtOne
  dsimp only [c]
  change raw = D
  rw [hDFormula, min_eq_right hRawLeAlpha]

/-- The valuation order of the signed prefix parameter is precisely the
last order occurring in `J2_E(n)`. -/
theorem he2022ClassicLemma46_signedPrefix_order
    {m : Nat} (t : Nat) (a : GoodBONG q L (m + 4))
    (hSource : 2 * t + 4 <= m + 4)
    (hJ1 : a.HeClassicJ1EPrime (2 * t + 2) (by omega)) :
    ordUnit K (((-1 : Kˣ) ^ (t + 2)) *
        a.prefixProduct (2 * t + 4)) =
      a.order ⟨2 * t + 3, by omega⟩ := by
  have hPrefixZero :
      a.orderSequence.prefixSum (2 * t + 3) = 0 := by
    unfold BeliOrderSequence.prefixSum
    apply Finset.sum_eq_zero
    intro i hi
    simp only [Finset.mem_range] at hi
    rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence (by omega)]
    let small : Fin (2 * t + 3) := ⟨i, by omega⟩
    have h := hJ1.1 small
    change a.order ⟨i, by omega⟩ = 0 at h
    exact h
  have hSign : ordUnit K ((-1 : Kˣ) ^ (t + 2)) = 0 := by
    have hOne : ordUnit K (1 : Kˣ) = 0 := by
      have h := ordUnit_mul K (1 : Kˣ) 1
      simp only [mul_one] at h
      omega
    rw [ordUnit_pow, ordUnit_neg, hOne]
    simp
  rw [ordUnit_mul, hSign, zero_add,
    a.ordUnit_prefixProduct_eq_orderSequence_prefixSum
      (2 * t + 4) (by omega),
    show 2 * t + 4 = (2 * t + 3) + 1 by omega,
    a.orderSequence.prefixSum_succ, hPrefixZero,
    a.orderSequence_entryOrZero_eq_order
      (⟨2 * t + 3, by omega⟩ : Fin (m + 4)), zero_add]

/-- The terminal index `i=n+1` in Theorem 2.5(iv). -/
def he2022ClassicLemma46Index {m : Nat} (t : Nat)
    (hExtra : 2 * t + 5 <= m + 4) :
    LongRepresentationIndex (m + 4) (2 * t + 2) where
  val := 2 * t + 3
  one_lt := by omega
  succ_lt_large := by omega
  le_small_succ := by omega

/-- At the terminal index, the large last gap activates condition (iv) as
soon as the target's final order agrees with the signed-prefix order. -/
theorem he2022ClassicLemma46_terminalRepresentation
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    {m : Nat} (t : Nat) (a : GoodBONG q L (m + 4))
    (b : GoodBONG r M (2 * t + 2))
    (hExtra : 2 * t + 5 <= m + 4)
    (hLargeGap : 2 * (ramificationIndex K : Int) <
      a.order ⟨2 * t + 4, by omega⟩ -
        a.order ⟨2 * t + 3, by omega⟩)
    (hLast : b.order ⟨2 * t + 1, by omega⟩ =
      a.order ⟨2 * t + 3, by omega⟩)
    (hLong : a.LongRepresentationConditions b) :
    DiagonalRepresents
      (b.prefixValues (2 * t + 2) le_rfl)
      (a.prefixValues (2 * t + 4) (by omega)) := by
  let i := he2022ClassicLemma46Index t hExtra
  have hi := (a.heClassicLongConditions_iff_forall_at b).mp hLong i
  have hRep := hi (by
    refine ⟨?_, ?_, ?_⟩
    · simp [i, he2022ClassicLemma46Index]
    · change b.order ⟨2 * t + 1, by omega⟩ +
          2 * (ramificationIndex K : Int) <
        a.order ⟨2 * t + 4, by omega⟩
      rw [hLast]
      omega
    · change a.order ⟨2 * t + 3, by omega⟩ +
          2 * (ramificationIndex K : Int) <=
        b.order ⟨2 * t + 1, by omega⟩ +
          2 * (ramificationIndex K : Int)
      rw [hLast])
  simpa [i, he2022ClassicLemma46Index] using hRep

/-- Lemma 4.6(ii) forces the last-gap bound `J3_E(n)`.  If the bound
failed, the signed prefix itself supplies a low-defect parameter `c`; the
two asserted terminal representations would then contradict Lemma 3.13. -/
theorem he2022ClassicLemma46_j3_of_publishedTests
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [DyadicDiscriminantClassLaws K]
    {m : Nat} (t : Nat) (a : GoodBONG q L (m + 4))
    (hSource : 2 * t + 4 <= m + 4)
    (hJ1 : a.HeClassicJ1EPrime (2 * t + 2) (by omega))
    (hJ2 : a.HeClassicJ2E (2 * t + 2) (by omega))
    (hTests : a.HeClassicLemma46PublishedTests t) :
    a.HeClassicJ3E (2 * t + 2) (by omega) := by
  unfold HeClassicJ3E
  intro hExtraRaw
  have hExtra : 2 * t + 5 <= m + 4 := by omega
  by_contra hNotBound
  have hNext : 2 * t + 2 + 1 = 2 * t + 3 := by omega
  have hNextTwo : 2 * t + 2 + 2 = 2 * t + 4 := by omega
  have hNotBound' : ¬ (a.order ⟨2 * t + 4, by omega⟩ -
      a.order ⟨2 * t + 3, by omega⟩ <=
        2 * (ramificationIndex K : Int)) := by
    simpa only [hNext, hNextTwo] using hNotBound
  have hLargeGap : 2 * (ramificationIndex K : Int) <
      a.order ⟨2 * t + 4, by omega⟩ -
        a.order ⟨2 * t + 3, by omega⟩ := by
    omega
  let c := ((-1 : Kˣ) ^ (t + 2)) * a.prefixProduct (2 * t + 4)
  have hCases := a.he2022ClassicLemma46_j2_cases t hSource hJ1 hJ2
  have hcOrderEq : ordUnit K c =
      a.order ⟨2 * t + 3, by omega⟩ := by
    simpa only [c] using
      a.he2022ClassicLemma46_signedPrefix_order t hSource hJ1
  have hcOrder : ordUnit K c = 0 ∨ ordUnit K c = 1 := by
    rw [hcOrderEq]
    exact hCases.1
  have hcDefectEq : defectOrder (K := K) c =
      a.truncatedPrefixDefect a ((-1) ^ (t + 2)) 0
        (2 * t + 4) := by
    simpa only [c] using
      a.he2022ClassicLemma46_rawDefect_eq_capped t hSource hExtra
        hJ1 hJ2 hLargeGap
  have hcDefect : defectOrder (K := K) c = (0 : WithTop ℚ) ∨
      defectOrder (K := K) c = (1 : WithTop ℚ) := by
    rw [hcDefectEq]
    exact hCases.2
  have hTestPair := hTests hExtra hLargeGap c hcOrder hcDefect
  let hcNonnegative : 0 <= ordUnit K c := by
    rcases hcOrder with hzero | hone <;> omega
  let hcDomain := heClassicLowDefectSharpDomain c hcDefect
  let cSharp := heHuSharp c hcDomain
  let hcSharpOrder : ordUnit K cSharp = 0 := by
    exact heClassicLowDefectSharp_order c hcDefect
  let bC1 := heClassicEvenC1GoodBONG (K := K) t c hcNonnegative
  let bC2 := heClassicEvenC2GoodBONG (K := K) t c cSharp
    hcNonnegative hcSharpOrder
  have hLongC1 : a.LongRepresentationConditions bC1 := by
    exact hTestPair.1
  have hLongC2 : a.LongRepresentationConditions bC2 := by
    exact hTestPair.2
  have hC1Last : bC1.order ⟨2 * t + 1, by omega⟩ =
      a.order ⟨2 * t + 3, by omega⟩ := by
    calc
      bC1.order ⟨2 * t + 1, by omega⟩ = ordUnit K c := by
        simp only [bC1, heClassicEvenC1GoodBONG,
          heHuExactGoodBONG_order, heClassicEvenC1_order]
        simp
      _ = a.order ⟨2 * t + 3, by omega⟩ := hcOrderEq
  have hC2Last : bC2.order ⟨2 * t + 1, by omega⟩ =
      a.order ⟨2 * t + 3, by omega⟩ := by
    calc
      bC2.order ⟨2 * t + 1, by omega⟩ = ordUnit K c := by
        simp only [bC2, heClassicEvenC2GoodBONG,
          heHuExactGoodBONG_order]
        rw [heClassicEvenC2_order t c cSharp hcSharpOrder]
        simp
      _ = a.order ⟨2 * t + 3, by omega⟩ := hcOrderEq
  have hRepC1 := a.he2022ClassicLemma46_terminalRepresentation t bC1
    hExtra hLargeGap hC1Last hLongC1
  have hRepC2 := a.he2022ClassicLemma46_terminalRepresentation t bC2
    hExtra hLargeGap hC2Last hLongC2
  let source := a.prefixValueUnits (2 * t + 4) (by omega)
  have hRepC1Units : DiagonalRepresents
      (diagonalUnitCoefficients (heClassicEvenC1 (K := K) t c))
      (diagonalUnitCoefficients source) := by
    change DiagonalRepresents
      (diagonalUnitCoefficients
        (bC1.prefixValueUnits (2 * t + 2) le_rfl))
      (diagonalUnitCoefficients source) at hRepC1
    rw [heClassicEvenC1_fullPrefixValueUnits t c hcNonnegative] at hRepC1
    exact hRepC1
  have hRepC2Units : DiagonalRepresents
      (diagonalUnitCoefficients
        (heClassicEvenC2 (K := K) t c cSharp))
      (diagonalUnitCoefficients source) := by
    change DiagonalRepresents
      (diagonalUnitCoefficients
        (bC2.prefixValueUnits (2 * t + 2) le_rfl))
      (diagonalUnitCoefficients source) at hRepC2
    rw [heClassicEvenC2_fullPrefixValueUnits t c cSharp
      hcNonnegative hcSharpOrder] at hRepC2
    exact hRepC2
  have hSourceDet : diagonalUnitDeterminant source =
      a.prefixProduct (2 * t + 4) := by
    simpa only [source] using
      a.diagonalUnitDeterminant_prefixValueUnits (2 * t + 4) (by omega)
  have hC1Det :
      diagonalUnitDeterminant (heClassicEvenC1 (K := K) t c) =
        (-1 : Kˣ) ^ (t + 1) * c := by
    calc
      diagonalUnitDeterminant (heClassicEvenC1 (K := K) t c) =
          diagonalUnitDeterminant
            (bC1.prefixValueUnits (2 * t + 2) le_rfl) := by
        rw [heClassicEvenC1_fullPrefixValueUnits t c hcNonnegative]
      _ = bC1.prefixProduct (2 * t + 2) :=
        bC1.diagonalUnitDeterminant_prefixValueUnits
          (2 * t + 2) le_rfl
      _ = (-1 : Kˣ) ^ (t + 1) * c :=
        heClassicEvenC1_prefixProduct_full (K := K) t c hcNonnegative
  have hDet : IsSquare
      (-diagonalUnitDeterminant source *
        diagonalUnitDeterminant (heClassicEvenC1 (K := K) t c)) := by
    rw [hSourceDet, hC1Det]
    refine ⟨a.prefixProduct (2 * t + 4), ?_⟩
    dsimp only [c]
    have hEven : Even (1 + (t + 1) + (t + 2)) :=
      ⟨t + 2, by omega⟩
    have hSign : (-1 : Kˣ) *
        (((-1 : Kˣ) ^ (t + 1)) * ((-1 : Kˣ) ^ (t + 2))) = 1 := by
      calc
        (-1 : Kˣ) *
            (((-1 : Kˣ) ^ (t + 1)) * ((-1 : Kˣ) ^ (t + 2))) =
            (-1 : Kˣ) ^ (1 + (t + 1) + (t + 2)) := by
              simp only [pow_add, pow_one, mul_assoc]
        _ = 1 := hEven.neg_one_pow
    have hNeg : -a.prefixProduct (2 * t + 4) =
        (-1 : Kˣ) * a.prefixProduct (2 * t + 4) := by
      apply Units.ext
      simp
    rw [hNeg]
    calc
      ((-1 : Kˣ) * a.prefixProduct (2 * t + 4)) *
          ((-1 : Kˣ) ^ (t + 1) *
            ((-1 : Kˣ) ^ (t + 2) *
              a.prefixProduct (2 * t + 4))) =
          ((-1 : Kˣ) *
            (((-1 : Kˣ) ^ (t + 1)) *
              ((-1 : Kˣ) ^ (t + 2)))) *
            (a.prefixProduct (2 * t + 4) *
              a.prefixProduct (2 * t + 4)) := by ac_rfl
      _ = a.prefixProduct (2 * t + 4) *
          a.prefixProduct (2 * t + 4) := by rw [hSign, one_mul]
  have hPair := heClassicEvenC_lowDefectPairProperties t c hcDefect
  have hExactlyOne := heHu2022Lemma313CodimensionTwo
    (heClassicEvenC1 (K := K) t c)
    (heClassicEvenC2 (K := K) t c cSharp)
    hPair source hDet
  rcases hExactlyOne with hFirst | hSecond
  · exact hFirst.2 hRepC2Units
  · exact hSecond.1 hRepC1Units

/-- The last-gap bound `J3_E(n)` makes condition (iv) automatic at every
admissible index.  The two orders immediately after the zero block lie in
`{0,1}` by Lemma 4.4, so the preceding gap is also at most `2e`. -/
theorem he2022ClassicLemma46_all_of_j3
    [QuadraticDefectLaws K]
    {m : Nat} (t : Nat) (a : GoodBONG q L (m + 4))
    (hSource : 2 * t + 4 <= m + 4)
    (hJ1 : a.HeClassicJ1EPrime (2 * t + 2) (by omega))
    (hJ2 : a.HeClassicJ2E (2 * t + 2) (by omega))
    (hJ3 : a.HeClassicJ3E (2 * t + 2) (by omega)) :
    HeClassicAllLongRepresentationConditions.{u, v, w}
      (n := 2 * t + 1) a := by
  intro W _ _ r M b _hClassic
  apply (a.heClassicLongConditions_iff_forall_at b).2
  intro i
  apply a.he2022ClassicLemma31v b i
  have hCases := a.he2022ClassicLemma46_j2_cases t hSource hJ1 hJ2
  have hzero : forall k : Fin (m + 4), k.val <= 2 * t + 2 ->
      a.order k = 0 := by
    intro k hk
    let small : Fin (2 * t + 3) := ⟨k.val, by omega⟩
    have h := hJ1.1 small
    change a.order ⟨k.val, by omega⟩ = 0 at h
    simpa only [Fin.eta] using h
  by_cases hEarly : i.val <= 2 * t + 1
  · have hCurrent :
        a.order ⟨i.val, by have := i.succ_lt_large; omega⟩ = 0 := by
      apply hzero
      change i.val <= 2 * t + 2
      omega
    have hNext : a.order ⟨i.val + 1, i.succ_lt_large⟩ = 0 := by
      apply hzero
      change i.val + 1 <= 2 * t + 2
      omega
    rw [hCurrent, hNext]
    have hePositive := ramificationIndex_pos (K := K)
    omega
  · by_cases hMiddle : i.val = 2 * t + 2
    · have hleft :
          (⟨i.val, by have := i.succ_lt_large; omega⟩ : Fin (m + 4)) =
            ⟨2 * t + 2, by omega⟩ := by
        apply Fin.ext
        exact hMiddle
      have hright : (⟨i.val + 1, i.succ_lt_large⟩ : Fin (m + 4)) =
          ⟨2 * t + 3, by omega⟩ := by
        apply Fin.ext
        change i.val + 1 = 2 * t + 3
        omega
      have hMiddleZero : a.order ⟨2 * t + 2, by omega⟩ = 0 := by
        apply hzero
        change 2 * t + 2 <= 2 * t + 2
        omega
      rw [hleft, hright]
      have hePositive := ramificationIndex_pos (K := K)
      rcases hCases.1 with hNextZero | hNextOne
      · rw [hNextZero, hMiddleZero]
        omega
      · rw [hNextOne, hMiddleZero]
        omega
    · have hLast : i.val = 2 * t + 3 := by
        have := i.le_small_succ
        omega
      have hleft :
          (⟨i.val, by have := i.succ_lt_large; omega⟩ : Fin (m + 4)) =
            ⟨2 * t + 3, by omega⟩ := by
        apply Fin.ext
        exact hLast
      have hTerminalBound : 2 * t + 4 < m + 4 := by
        have hi := i.succ_lt_large
        change i.val + 1 < m + 4 at hi
        omega
      have hright : (⟨i.val + 1, i.succ_lt_large⟩ : Fin (m + 4)) =
          ⟨2 * t + 4, hTerminalBound⟩ := by
        apply Fin.ext
        change i.val + 1 = 2 * t + 4
        omega
      have hStable : 2 * t + 2 + 2 <= m + 3 := by
        have := i.succ_lt_large
        omega
      have hGap := hJ3 hStable
      rw [hleft, hright]
      simpa only [show 2 * t + 2 + 1 = 2 * t + 3 by omega,
        show 2 * t + 2 + 2 = 2 * t + 4 by omega] using hGap

/-- Lemma 4.6, equivalence `(ii) <-> (iii)`. -/
theorem he2022ClassicLemma46_publishedTests_iff_j3
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [DyadicDiscriminantClassLaws K]
    {m : Nat} (t : Nat) (a : GoodBONG q L (m + 4))
    (hSource : 2 * t + 4 <= m + 4)
    (hJ1 : a.HeClassicJ1EPrime (2 * t + 2) (by omega))
    (hJ2 : a.HeClassicJ2E (2 * t + 2) (by omega)) :
    a.HeClassicLemma46PublishedTests t <->
      a.HeClassicJ3E (2 * t + 2) (by omega) := by
  constructor
  · exact a.he2022ClassicLemma46_j3_of_publishedTests t hSource hJ1 hJ2
  · intro hJ3
    have hAll : HeClassicAllLongRepresentationConditions.{u, v, u}
        (n := 2 * t + 1) a :=
      a.he2022ClassicLemma46_all_of_j3 t hSource hJ1 hJ2 hJ3
    exact a.he2022ClassicLemma46_publishedTests_of_all t
      hAll

/-- Lemma 4.6, equivalence `(i) <-> (ii)`. -/
theorem he2022ClassicLemma46_all_iff_publishedTests
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [DyadicDiscriminantClassLaws K]
    {m : Nat} (t : Nat) (a : GoodBONG q L (m + 4))
    (hSource : 2 * t + 4 <= m + 4)
    (hJ1 : a.HeClassicJ1EPrime (2 * t + 2) (by omega))
    (hJ2 : a.HeClassicJ2E (2 * t + 2) (by omega)) :
    HeClassicAllLongRepresentationConditions.{u, v, u}
        (n := 2 * t + 1) a <->
      a.HeClassicLemma46PublishedTests t := by
  constructor
  · exact a.he2022ClassicLemma46_publishedTests_of_all t
  · intro hTests
    exact a.he2022ClassicLemma46_all_of_j3 t hSource hJ1 hJ2
      (a.he2022ClassicLemma46_j3_of_publishedTests t hSource hJ1 hJ2 hTests)

/-- He (2024), Lemma 4.6, in its compact endpoint form `(i) <-> (iii)`.
Together with `he2022ClassicLemma46_all_iff_publishedTests`, this records
all three printed conditions. -/
theorem he2022ClassicLemma46
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [DyadicDiscriminantClassLaws K]
    {m : Nat} (t : Nat) (a : GoodBONG q L (m + 4))
    (hSource : 2 * t + 4 <= m + 4)
    (hJ1 : a.HeClassicJ1EPrime (2 * t + 2) (by omega))
    (hJ2 : a.HeClassicJ2E (2 * t + 2) (by omega)) :
    HeClassicAllLongRepresentationConditions.{u, v, u}
        (n := 2 * t + 1) a <->
      a.HeClassicJ3E (2 * t + 2) (by omega) := by
  constructor
  · intro hAll
    exact a.he2022ClassicLemma46_j3_of_publishedTests t hSource hJ1 hJ2
      (a.he2022ClassicLemma46_publishedTests_of_all t hAll)
  · exact a.he2022ClassicLemma46_all_of_j3 t hSource hJ1 hJ2

end BONG.GoodBONG

end Bong
