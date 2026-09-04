/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2022ClassicLemma55

/-!
# He (2024), Lemma 5.6

The two targets below use `heHuLemma59Target`.  Its coefficient family is the
first-column maximal lattice, and `heClassicOddC1_eq_heHuOddFirst` proves that
this is exactly the publisher's classic row `C₁ⁿ(c)`.  Reusing this canonical
realization keeps the already verified determinant and Hilbert-symbol
obstruction available without changing the mathematical target.
-/

namespace Bong

open Dyadic AlternatingEndpointTower

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG.GoodBONG

/-- Under `J1'_E(N-1)`, the valuation of the first `N=2*k+3`
coefficients is even (indeed, it is zero). -/
theorem he2022ClassicLemma56_sourceInitialPrefixOrder_even
    {m k : Nat} (a : GoodBONG q L (m + 3))
    (hm : 2 * k + 3 <= m)
    (hJ1 : a.HeClassicJ1EPrime (2 * k + 2) (by omega)) :
    Even (ordUnit K (a.prefixProduct (2 * k + 3))) := by
  have hEntries (j : Nat) (hj : j < 2 * k + 3) :
      Even (a.orderSequence.entryOrZero j) := by
    let jf : Fin (m + 3) := ⟨j, by omega⟩
    rw [a.orderSequence_entryOrZero_eq_order jf]
    have hZero := hJ1.1 ⟨j, by omega⟩
    have hIndex : (⟨j, by omega⟩ : Fin (m + 3)) = jf := Fin.ext rfl
    rw [hIndex] at hZero
    rw [hZero]
    exact Even.zero
  rw [a.ordUnit_prefixProduct_eq_orderSequence_prefixSum
    (2 * k + 3) (by omega)]
  exact a.orderSequence.prefixSum_even_of_entries_even (2 * k + 3) hEntries

/-- In the classic case, the signed determinant
`c=(-1)^((N+1)/2)a_(1,N+2)` has the parity of
`R_(N+2)-R_(N+1)`. -/
theorem he2022ClassicLemma56_c_order_sub_gap_even
    {m k : Nat} (a : GoodBONG q L (m + 3))
    (hm : 2 * k + 3 <= m)
    (hJ1 : a.HeClassicJ1EPrime (2 * k + 2) (by omega)) :
    Even (ordUnit K (heHuLemma59C a k) -
      (a.order ⟨2 * k + 4, by omega⟩ -
        a.order ⟨2 * k + 3, by omega⟩)) := by
  have hPrefix :=
    a.he2022ClassicLemma56_sourceInitialPrefixOrder_even (k := k) hm hJ1
  rcases hPrefix with ⟨t, ht⟩
  have hProduct :
      ordUnit K (a.prefixProduct (2 * k + 5)) =
        ordUnit K (a.prefixProduct (2 * k + 3)) +
          a.order ⟨2 * k + 3, by omega⟩ +
          a.order ⟨2 * k + 4, by omega⟩ := by
    calc
      ordUnit K (a.prefixProduct (2 * k + 5)) =
          ordUnit K (a.prefixProduct (2 * k + 4)) +
            a.order ⟨2 * k + 4, by omega⟩ := by
        unfold GoodBONG.prefixProduct
        rw [show 2 * k + 5 = (2 * k + 4) + 1 by omega,
          a.toBONG.prefixProduct_succ (2 * k + 4) (by omega), ordUnit_mul]
        rfl
      _ = ordUnit K (a.prefixProduct (2 * k + 3)) +
            a.order ⟨2 * k + 3, by omega⟩ +
            a.order ⟨2 * k + 4, by omega⟩ := by
        have hStep :
            ordUnit K (a.prefixProduct (2 * k + 4)) =
              ordUnit K (a.prefixProduct (2 * k + 3)) +
                a.order ⟨2 * k + 3, by omega⟩ := by
          unfold GoodBONG.prefixProduct
          rw [show 2 * k + 4 = (2 * k + 3) + 1 by omega,
            a.toBONG.prefixProduct_succ (2 * k + 3) (by omega), ordUnit_mul]
          rfl
        rw [hStep]
  have hCOrder :
      ordUnit K (heHuLemma59C a k) =
        ordUnit K (a.prefixProduct (2 * k + 5)) := by
    unfold heHuLemma59C
    rw [ordUnit_mul, ordUnit_pow, ordUnit_neg_one_eq_zero (K := K)]
    simp only [mul_zero, zero_add]
  refine ⟨t + a.order ⟨2 * k + 3, by omega⟩, ?_⟩
  rw [hCOrder, hProduct, ht]
  ring

/-- Lemma 5.6(i): both first-column tests activate the numerical trigger in
Theorem 2.5(iii). -/
theorem he2022ClassicLemma56i
    [QuadraticDefectLaws K]
    {m k : Nat} (a : GoodBONG q L (m + 3))
    (hm : 2 * k + 3 <= m)
    (hClassic : Lattice.IsClassicIntegral q L)
    (hJ1 : a.HeClassicJ1EPrime (2 * k + 2) (by omega))
    (hJ2 : a.HeClassicJ2E (2 * k + 2) (by omega))
    (hAlphaNext :
      (a.heClassicOddThreshold (2 * k + 3) (by omega) : ℚ) <
        a.alphaValue ⟨2 * k + 4, by omega⟩)
    (hTrigger : a.order ⟨2 * k + 3, by omega⟩ = 1 ∨
      1 < a.order ⟨2 * k + 4, by omega⟩) :
    let cTilde := heHuLemma59CTilde a k
    ∃ hc : HeHuSharpDomain cTilde,
      let u := heHuSharp cTilde hc
      a.centralDefectTrigger
          (heHuLemma59Target (K := K) (heHuLemma59C a k) k)
          (heHuLemma59CentralIndex k hm) ∧
        a.centralDefectTrigger
          (heHuLemma59Target (K := K) (heHuLemma59C a k * u) k)
          (heHuLemma59CentralIndex k hm) := by
  dsimp only
  have h55 := a.he2022ClassicLemma55 (k := k) hm hClassic hJ1 hJ2 hTrigger
  rcases h55 with ⟨hc, hRaw, hUnit, hSharp⟩
  refine ⟨hc, ?_⟩
  let c := heHuLemma59C a k
  let cTilde := heHuLemma59CTilde a k
  let u := heHuSharp cTilde hc
  have hCap := a.he2022ClassicLemma55_nextAlpha_gt (k := k) hm hClassic
    hJ1 hJ2 hTrigger
  have hSourceDefect : (heHuSharpData cTilde hc).sourceDefect =
      ((1 - a.order ⟨2 * k + 3, by omega⟩ : Int) : ℚ) := by
    have hs := (heHuSharpData cTilde hc).source_defectOrder
    rw [hRaw] at hs
    exact WithTop.coe_eq_coe.mp hs.symm
  have hLt :
      ((((1 : Int) - a.order ⟨2 * k + 3, by omega⟩ : Int) : ℚ) :
          WithTop ℚ) <
        ((2 * ramificationIndex K : ℚ) : WithTop ℚ) := by
    have hs := (heHuSharpData cTilde hc).sourceDefect_lt_twoE
    rw [hSourceDefect] at hs
    exact_mod_cast hs
  have hBoundary := a.heHuLemma59_boundaryOrder_gt_gapParity k hm
    hClassic.isIntegral hTrigger
  let gap := a.order ⟨2 * k + 4, by omega⟩ -
    a.order ⟨2 * k + 3, by omega⟩
  have hCDiff : Even (ordUnit K c - gap) := by
    simpa only [c, gap] using
      a.he2022ClassicLemma56_c_order_sub_gap_even (k := k) hm hJ1
  have hCParity : heHuLemma59Parity (K := K) c =
      if Even gap then 0 else 1 :=
    heHuLemma59Parity_eq_gapParity c gap hCDiff
  have hCUDiff : Even (ordUnit K (c * u) - gap) := by
    apply heHuLemma59_mul_unit_order_sub_gap_even c u gap hCDiff
    simpa only [u, cTilde] using hUnit
  have hCUParity : heHuLemma59Parity (K := K) (c * u) =
      if Even gap then 0 else 1 :=
    heHuLemma59Parity_eq_gapParity (c * u) gap hCUDiff
  have hLastC : (heHuLemma59Target (K := K) c k).order
      ⟨2 * k + 2, by omega⟩ = if Even gap then 0 else 1 :=
    (heHuLemma59Target_lastOrder (K := K) c k).trans hCParity
  have hLastCU : (heHuLemma59Target (K := K) (c * u) k).order
      ⟨2 * k + 2, by omega⟩ = if Even gap then 0 else 1 :=
    (heHuLemma59Target_lastOrder (K := K) (c * u) k).trans hCUParity
  have hPreviousC := a.heHuLemma59_centralPreviousDefect_eq k hm
    hRaw hCap hLt c
  have hPreviousCU := a.heHuLemma59_centralPreviousDefect_eq k hm
    hRaw hCap hLt (c * u)
  have hRawC :
      ((a.heHuOddThreshold (2 * k + 3) (by omega) : ℚ) : WithTop ℚ) <
        defectOrder (K := K)
          ((-1 : Kˣ) * a.prefixProduct (2 * k + 5) *
            (heHuLemma59Target (K := K) c k).prefixProduct (2 * k + 3)) := by
    dsimp only [c]
    rw [heHuLemma59_currentMixed_defectOrder_C]
    exact WithTop.coe_lt_top _
  have hCurrentC := a.heHuLemma59_centralCurrentDefect_gt k hm c
    (a.heHuOddThreshold (2 * k + 3) (by omega)) hRawC (by
      simpa only [heClassicOddThreshold] using hAlphaNext)
  have hSharpGt := a.heHuLemma59_sharpDefect_gt_threshold k hm u
    (by simpa only [gap] using hBoundary) (by
      simpa only [u, cTilde] using hSharp)
  have hRawCU :
      ((a.heHuOddThreshold (2 * k + 3) (by omega) : ℚ) : WithTop ℚ) <
        defectOrder (K := K)
          ((-1 : Kˣ) * a.prefixProduct (2 * k + 5) *
            (heHuLemma59Target (K := K) (c * u) k).prefixProduct
              (2 * k + 3)) := by
    dsimp only [c]
    rw [heHuLemma59_currentMixed_defectOrder_C_mul]
    exact hSharpGt
  have hCurrentCU := a.heHuLemma59_centralCurrentDefect_gt k hm (c * u)
    (a.heHuOddThreshold (2 * k + 3) (by omega)) hRawCU (by
      simpa only [heClassicOddThreshold] using hAlphaNext)
  constructor
  · apply a.heHuLemma59_defectTrigger_of_bounds k hm c
    · simpa only [gap] using hLastC
    · exact hBoundary
    · simpa only [c] using hPreviousC
    · simpa only [c] using hCurrentC
  · apply a.heHuLemma59_defectTrigger_of_bounds k hm (c * u)
    · simpa only [gap] using hLastCU
    · exact hBoundary
    · simpa only [c, u] using hPreviousCU
    · simpa only [c, u] using hCurrentCU

/-- Lemma 5.6(ii): the common source prefix cannot represent both test
spaces.  This is the same determinant/Hilbert-symbol obstruction as the
He--Hu lemma because the two `C₁` coefficient families coincide exactly. -/
theorem he2022ClassicLemma56ii
    {m k : Nat} (a : GoodBONG q L (m + 3))
    (hm : 2 * k + 3 <= m)
    (hc : HeHuSharpDomain (heHuLemma59CTilde a k)) :
    ¬(
      DiagonalRepresents
          ((heHuLemma59Target (K := K) (heHuLemma59C a k) k).prefixValues
            (2 * k + 3) (by omega))
          (a.prefixValues (2 * k + 4) (by omega)) ∧
        DiagonalRepresents
          ((heHuLemma59Target (K := K)
              (heHuLemma59C a k *
                heHuSharp (heHuLemma59CTilde a k) hc) k).prefixValues
            (2 * k + 3) (by omega))
          (a.prefixValues (2 * k + 4) (by omega))) :=
  a.heHu2022Lemma59ii k hm hc

/-- He (2024), Lemma 5.6 in the publisher's full logical form: both tests
activate condition (iii), they cannot both be represented, and therefore
condition (iii) fails for at least one of them. -/
theorem he2022ClassicLemma56
    [QuadraticDefectLaws K]
    {m k : Nat} (a : GoodBONG q L (m + 3))
    (hm : 2 * k + 3 <= m)
    (hClassic : Lattice.IsClassicIntegral q L)
    (hJ1 : a.HeClassicJ1EPrime (2 * k + 2) (by omega))
    (hJ2 : a.HeClassicJ2E (2 * k + 2) (by omega))
    (hAlphaNext :
      (a.heClassicOddThreshold (2 * k + 3) (by omega) : ℚ) <
        a.alphaValue ⟨2 * k + 4, by omega⟩)
    (hTrigger : a.order ⟨2 * k + 3, by omega⟩ = 1 ∨
      1 < a.order ⟨2 * k + 4, by omega⟩) :
    ∃ hc : HeHuSharpDomain (heHuLemma59CTilde a k),
      let u := heHuSharp (heHuLemma59CTilde a k) hc
      a.centralDefectTrigger
          (heHuLemma59Target (K := K) (heHuLemma59C a k) k)
          (heHuLemma59CentralIndex k hm) ∧
        a.centralDefectTrigger
          (heHuLemma59Target (K := K) (heHuLemma59C a k * u) k)
          (heHuLemma59CentralIndex k hm) ∧
        ¬(
          DiagonalRepresents
              ((heHuLemma59Target (K := K) (heHuLemma59C a k) k).prefixValues
                (2 * k + 3) (by omega))
              (a.prefixValues (2 * k + 4) (by omega)) ∧
            DiagonalRepresents
              ((heHuLemma59Target (K := K)
                  (heHuLemma59C a k * u) k).prefixValues
                (2 * k + 3) (by omega))
              (a.prefixValues (2 * k + 4) (by omega))) ∧
        (¬a.CentralRepresentationConditionsPrime
            (heHuLemma59Target (K := K) (heHuLemma59C a k) k) ∨
          ¬a.CentralRepresentationConditionsPrime
            (heHuLemma59Target (K := K) (heHuLemma59C a k * u) k)) := by
  rcases a.he2022ClassicLemma56i (k := k) hm hClassic hJ1 hJ2
    hAlphaNext hTrigger with
    ⟨hc, hFirstTrigger, hSecondTrigger⟩
  let u := heHuSharp (heHuLemma59CTilde a k) hc
  have hNot := a.he2022ClassicLemma56ii (k := k) hm hc
  refine ⟨hc, hFirstTrigger, hSecondTrigger, hNot, ?_⟩
  by_cases hPrimeFirst : a.CentralRepresentationConditionsPrime
      (heHuLemma59Target (K := K) (heHuLemma59C a k) k)
  · right
    intro hPrimeSecond
    apply hNot
    constructor
    · apply a.centralRepresentationConditionsPrime_represents_castLengths
        (heHuLemma59Target (K := K) (heHuLemma59C a k) k)
        hPrimeFirst (heHuLemma59CentralIndex k hm) hFirstTrigger
      · simp only [heHuLemma59CentralIndex]
        omega
      · rfl
    · apply a.centralRepresentationConditionsPrime_represents_castLengths
        (heHuLemma59Target (K := K) (heHuLemma59C a k * u) k)
        hPrimeSecond (heHuLemma59CentralIndex k hm) hSecondTrigger
      · simp only [heHuLemma59CentralIndex]
        omega
      · rfl
  · exact Or.inl hPrimeFirst

end BONG.GoodBONG

end Bong
