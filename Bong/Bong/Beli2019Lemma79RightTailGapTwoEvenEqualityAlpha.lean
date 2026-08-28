/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapTwoEvenEqualityNonzero

/-!
# Beli (2019), Lemma 7.9(ii), case 8: excluding zero alpha in equality

If `gamma_(i-1) = 0`, equality in the domination coefficient and oddness of
`beta_i` make `S_(i+1)` congruent to `T_i`.  The known congruence of the two
prefixes of length `i` would then make the signed primary product have even
order, contradicting the odd order obtained from Lemma 7.3(ii).
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V} {n : Nat}

/-- Prefix congruence excludes `gamma_(i-1) = 0` in the even equality
branch. -/
theorem caseEight_gapTwo_even_equality_previousAlpha_ne_zero
    (b : GoodBONG q M (n + 2)) (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (first : Fin (n + 1))
    (hfirstLast : first <= caseEightLastAlphaIndex i)
    (H : CaseEightStrictBetaTailConsequences b first
      (caseEightLastAlphaIndex i))
    (j : Fin (n + 1))
    (hsource : b.order first.castSucc = c.order j.castSucc + 1)
    (hcoefficient :
      ((((c.order j.castSucc -
          c.order (evenTargetPreviousIndex i) : Int) : Rat) +
        c.alphaValue (evenTargetPreviousAlphaIndex i) : Rat) :
          WithTop Rat) =
      ((((b.order first.castSucc - b.order first.succ : Int) : Rat) +
        b.alphaValue first : Rat) : WithTop Rat))
    (hprefix : Int.ModEq 2 (b.orderSequence.prefixSum i.val)
      (c.orderSequence.prefixSum i.val))
    (hodd : Odd (ordUnit K
      ((-1 : Kˣ) * b.prefixProduct (i.val + 1) *
        c.prefixProduct (i.val - 1)))) :
    c.alphaValue (evenTargetPreviousAlphaIndex i) ≠ 0 := by
  intro halphaZero
  rcases H.alpha_odd (caseEightLastAlphaIndex i) hfirstLast le_rfl with
    ⟨z, hzOdd, hz⟩
  have hcoefficientQ :
      ((c.order j.castSucc - c.order (evenTargetPreviousIndex i) : Int) :
          Rat) + c.alphaValue (evenTargetPreviousAlphaIndex i) =
        ((b.order first.castSucc - b.order first.succ : Int) : Rat) +
          b.alphaValue first := by
    exact_mod_cast hcoefficient
  have hcentral := H.centralCoefficient_eq
    (caseEightLastAlphaIndex i) hfirstLast le_rfl
  rw [caseEightLastAlphaIndex_succ i] at hcentral
  have hsourceQ : (b.order first.castSucc : Rat) =
      (c.order j.castSucc : Rat) + 1 := by
    exact_mod_cast hsource
  have hdiffQ :
      (b.order ⟨i.val, i.lt_large⟩ : Rat) -
          (c.order (evenTargetPreviousIndex i) : Rat) =
        (z : Rat) + 1 := by
    rw [halphaZero] at hcoefficientQ
    rw [hz] at hcentral
    push_cast at hcoefficientQ hcentral hsourceQ ⊢
    linarith
  have hdiff : b.order ⟨i.val, i.lt_large⟩ -
        c.order (evenTargetPreviousIndex i) = z + 1 := by
    exact_mod_cast hdiffQ
  have hdiffEven : Even (b.order ⟨i.val, i.lt_large⟩ -
      c.order (evenTargetPreviousIndex i)) := by
    rcases hzOdd with ⟨d, hd⟩
    refine ⟨d + 1, ?_⟩
    rw [hdiff, hd]
    omega
  have hentryMod : Int.ModEq 2
      (b.orderSequence.entryOrZero i.val)
      (c.orderSequence.entryOrZero (i.val - 1)) := by
    have hbEntry : b.orderSequence.entryOrZero i.val =
        b.order ⟨i.val, i.lt_large⟩ := by
      simpa using b.orderSequence_entryOrZero_eq_order
        (⟨i.val, i.lt_large⟩ : Fin (n + 2))
    have hcIndex : (⟨i.val - 1, by
        have hi := i.lt_large
        omega⟩ : Fin (n + 2)) = evenTargetPreviousIndex i := by
      apply Fin.ext
      rfl
    have hcEntry : c.orderSequence.entryOrZero (i.val - 1) =
        c.order (evenTargetPreviousIndex i) := by
      rw [<- hcIndex]
      simpa using c.orderSequence_entryOrZero_eq_order
        (⟨i.val - 1, by
          have hi := i.lt_large
          omega⟩ : Fin (n + 2))
    rw [hbEntry, hcEntry]
    exact int_modEq_two_of_even_sub hdiffEven
  have hsumMod : Int.ModEq 2
      (b.orderSequence.prefixSum (i.val + 1))
      (c.orderSequence.prefixSum (i.val - 1) +
        c.orderSequence.entryOrZero (i.val - 1) +
        c.orderSequence.entryOrZero (i.val - 1)) := by
    have hadd := hprefix.add hentryMod
    rw [b.orderSequence.prefixSum_succ]
    have hcPrefixSucc : c.orderSequence.prefixSum i.val =
        c.orderSequence.prefixSum (i.val - 1) +
          c.orderSequence.entryOrZero (i.val - 1) := by
      have hiDecompose : i.val = (i.val - 1) + 1 := by
        have hiPos := i.pos
        omega
      calc
        c.orderSequence.prefixSum i.val =
            c.orderSequence.prefixSum ((i.val - 1) + 1) := by
          exact congrArg c.orderSequence.prefixSum hiDecompose
        _ = c.orderSequence.prefixSum (i.val - 1) +
            c.orderSequence.entryOrZero (i.val - 1) := by
          rw [c.orderSequence.prefixSum_succ]
    rw [hcPrefixSucc] at hadd
    exact hadd
  have hdoubleZero : Int.ModEq 2
      (c.orderSequence.entryOrZero (i.val - 1) +
        c.orderSequence.entryOrZero (i.val - 1)) 0 := by
    rw [Int.modEq_iff_dvd]
    refine ⟨-(c.orderSequence.entryOrZero (i.val - 1)), ?_⟩
    ring
  have hlongPrevious : Int.ModEq 2
      (b.orderSequence.prefixSum (i.val + 1))
      (c.orderSequence.prefixSum (i.val - 1)) := by
    exact hsumMod.trans (by
      have hbase : Int.ModEq 2
          (c.orderSequence.prefixSum (i.val - 1))
          (c.orderSequence.prefixSum (i.val - 1)) := Int.ModEq.refl _
      simpa only [add_assoc, add_zero] using hbase.add hdoubleZero)
  have htotalZero : Int.ModEq 2
      (b.orderSequence.prefixSum (i.val + 1) +
        c.orderSequence.prefixSum (i.val - 1)) 0 := by
    have hdoublePrevious : Int.ModEq 2
        (c.orderSequence.prefixSum (i.val - 1) +
          c.orderSequence.prefixSum (i.val - 1)) 0 := by
      rw [Int.modEq_iff_dvd]
      refine ⟨-(c.orderSequence.prefixSum (i.val - 1)), ?_⟩
      ring
    exact (hlongPrevious.add (Int.ModEq.refl
      (c.orderSequence.prefixSum (i.val - 1)))).trans hdoublePrevious
  have ordUnit_neg_eq (x : Kˣ) : ordUnit K (-x) = ordUnit K x := by
    apply WithTop.coe_injective
    rw [coe_ordUnit, coe_ordUnit]
    simpa using ord_neg K (x : K)
  have hone : ordUnit K (1 : Kˣ) = 0 := by
    have h := ordUnit_mul K (1 : Kˣ) 1
    simp only [mul_one] at h
    omega
  have hneg : ordUnit K (-1 : Kˣ) = 0 := by
    rw [ordUnit_neg_eq, hone]
  have horder : ordUnit K
        ((-1 : Kˣ) * b.prefixProduct (i.val + 1) *
          c.prefixProduct (i.val - 1)) =
      b.orderSequence.prefixSum (i.val + 1) +
        c.orderSequence.prefixSum (i.val - 1) := by
    rw [ordUnit_mul, ordUnit_mul, hneg, zero_add,
      b.ordUnit_prefixProduct_eq_orderSequence_prefixSum
        (i.val + 1) (by
          have hi := i.lt_large
          omega),
      c.ordUnit_prefixProduct_eq_orderSequence_prefixSum
        (i.val - 1) (by
          have hi := i.lt_large
          omega)]
  rw [horder] at hodd
  rcases hodd with ⟨w, hw⟩
  rw [Int.modEq_iff_dvd] at htotalZero
  rcases htotalZero with ⟨v, hv⟩
  omega

end BONG.GoodBONG

end Bong
