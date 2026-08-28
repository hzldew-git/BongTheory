/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapTwoEvenNonintegral
import Bong.Bong.Beli2019Lemma79EvenTypeIEqualityParity

/-!
# Beli (2019), Lemma 7.9(ii), case 8: parity in the even equality branch

Equality in the domination coefficient forces equality of two comparison
right endpoints.  Lemma 7.3(ii) propagates the resulting parity from the
low witness through the prefix of length `i - 1`.  On the target side, the
constant right-endpoint tail has even length, so the initial gap-two prefix
parity persists through length `i + 1`.  The two prefixes therefore form a
signed product of odd order.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Equality in the low-witness domination chain makes the signed primary
product at an even gap-two tail coordinate have odd order. -/
theorem beli2019Lemma79_typeI_caseEight_gapTwo_even_equality_primaryProduct_odd
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (hfirst : D.profile.first = 0)
    (hgapTwo : b.orderSequence.entryOrZero D.profile.last =
      a.orderSequence.entryOrZero D.profile.last + 2)
    (hlast : D.profile.last < n + 1)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hafter : D.profile.last + 1 <= i.val)
    (H : CaseEightStrictBetaTailConsequences b
      (Fin.mk D.profile.last hlast) (caseEightLastAlphaIndex i))
    (hiEven : Even i.val) (hiTwo : 2 <= i.val)
    (hself : c.truncatedPrefixDefect c ((-1) ^ (i.val / 2)) 0 i.val =
      ((((b.order (Fin.mk D.profile.last hlast).castSucc -
          b.order (Fin.mk D.profile.last hlast).succ : Int) : Rat) +
        b.alphaValue (Fin.mk D.profile.last hlast) : Rat) : WithTop Rat))
    (j : Fin (n + 1)) (hjEven : Even j.val)
    (hjBefore : j.val + 1 < i.val)
    (hlow : c.order j.castSucc <
      b.order (Fin.mk D.profile.last hlast).castSucc)
    (hjPair : c.truncatedPrefixDefect c (-1) j.val (j.val + 2) <=
      ((((b.order (Fin.mk D.profile.last hlast).castSucc -
          b.order (Fin.mk D.profile.last hlast).succ : Int) : Rat) +
        b.alphaValue (Fin.mk D.profile.last hlast) : Rat) : WithTop Rat))
    (hcoefficient :
      ((((c.order j.castSucc -
          c.order (evenTargetPreviousIndex i) : Int) : Rat) +
        c.alphaValue (evenTargetPreviousAlphaIndex i) : Rat) :
          WithTop Rat) =
      ((((b.order (Fin.mk D.profile.last hlast).castSucc -
          b.order (Fin.mk D.profile.last hlast).succ : Int) : Rat) +
        b.alphaValue (Fin.mk D.profile.last hlast) : Rat) : WithTop Rat)) :
    Odd (ordUnit K
      ((-1 : Kˣ) * b.prefixProduct (i.val + 1) *
        c.prefixProduct (i.val - 1))) := by
  rcases beli2019Lemma79_typeI_caseEight_gapTwo_initialData
    a b D hfirst hgapTwo with ⟨I⟩
  let first : Fin (n + 1) := Fin.mk D.profile.last hlast
  let reference : Int := a.orderSequence.entryOrZero D.anchor + 1
  rcases beli2019Lemma79_typeI_caseEight_gapTwo_lowWitness_orders
      a b c D hfirst hgapTwo hlast hnorm j hjEven (by
        simpa only [first] using hlow) with
    ⟨hzero, hjOrder, htarget, _⟩
  have hjOrderCurrent : c.order j.castSucc =
      b.order first.castSucc - 1 := by
    simp only [first, reference] at hjOrder htarget ⊢
    omega
  have hjDefect : c.truncatedPrefixDefect c (-1) j.val (j.val + 2) <=
      c.truncatedPrefixDefect c ((-1) ^ (i.val / 2)) 0 i.val := by
    rw [hself]
    simpa only [first] using hjPair
  have heq : c.truncatedPrefixDefect c ((-1) ^ (i.val / 2)) 0 i.val =
      ((show Rat from
          ((b.order first.castSucc -
            c.order (evenTargetPreviousIndex i) : Int) : Rat) +
          c.alphaValue (evenTargetPreviousAlphaIndex i) - 1) :
        WithTop Rat) := by
    calc
      c.truncatedPrefixDefect c ((-1) ^ (i.val / 2)) 0 i.val =
          ((((b.order first.castSucc - b.order first.succ : Int) : Rat) +
            b.alphaValue first : Rat) : WithTop Rat) := by
        simpa only [first] using hself
      _ = ((((c.order j.castSucc -
            c.order (evenTargetPreviousIndex i) : Int) : Rat) +
          c.alphaValue (evenTargetPreviousAlphaIndex i) : Rat) :
            WithTop Rat) := by
        simpa only [first] using hcoefficient.symm
      _ = ((show Rat from
          ((b.order first.castSucc -
            c.order (evenTargetPreviousIndex i) : Int) : Rat) +
          c.alphaValue (evenTargetPreviousAlphaIndex i) - 1) :
            WithTop Rat) := by
        apply congrArg (fun z : Rat => (z : WithTop Rat))
        rw [hjOrderCurrent]
        push_cast
        ring
  have hendpoint := lemma79_even_rightEndpoint_eq_of_domination_equality
    c i hiTwo j hjBefore (b.order first.castSucc) hjOrderCurrent
      hjDefect heq
  have hfirstLower : reference <= c.orderSequence.entryOrZero 0 := by
    have hzero' : c.order (0 : Fin (n + 2)) = reference := by
      simpa only [reference] using hzero
    have hentry : c.orderSequence.entryOrZero 0 =
        c.order (0 : Fin (n + 2)) := by
      simpa using c.orderSequence_entryOrZero_eq_order
        (0 : Fin (n + 2))
    rw [hentry, hzero']
  have hcPrefix :=
    lemma79_typeI_even_thirdPrefix_modEq_of_rightEndpoint_eq
      c i hiTwo hiEven j hjEven hjBefore reference hfirstLower
        (by simpa only [reference] using hjOrder) hendpoint
  have hiEvenForProduct := hiEven
  have hcountPreviousOne : Int.ModEq 2
      (((i.val - 1 : Nat) : Int)) 1 := by
    rcases hiEven with ⟨d, hd⟩
    have hdPos : 0 < d := by omega
    rw [Int.modEq_iff_dvd]
    refine ⟨-((d - 1 : Nat) : Int), ?_⟩
    omega
  have hc : Int.ModEq 2
      (c.orderSequence.prefixSum (i.val - 1))
      (((i.val - 1 : Nat) : Int) * reference) :=
    hcPrefix.trans (by
      simpa only [one_mul] using
        (hcountPreviousOne.mul_right reference).symm)
  have hstart : first.val + 1 <= i.val + 1 := by
    simp only [first]
    omega
  have hbTail := b.orderSequence.prefixSum_modEq_add_mul_of_tail
    (((first.val + 1 : Nat) : Int) * reference + 1)
      (b.order first.succ) hstart (by
        simpa only [first, reference] using I.target_prefix_last) (by
          intro k hkStart hkEnd
          have hkBound : k < n + 2 := by
            have hi := i.lt_large
            omega
          let r : Fin (n + 1) := ⟨k - 1, by omega⟩
          have hrFirst : first <= r := by
            change first.val <= r.val
            simp only [r]
            omega
          have hrLast : r <= caseEightLastAlphaIndex i := by
            change r.val <= (caseEightLastAlphaIndex i).val
            simp only [r, caseEightLastAlphaIndex_val]
            omega
          have hmod := H.order_modEq r hrFirst hrLast
          have hrSucc : r.succ = (⟨k, hkBound⟩ : Fin (n + 2)) := by
            apply Fin.ext
            simp only [r, Fin.val_succ]
            omega
          calc
            b.orderSequence.entryOrZero k =
                b.order (⟨k, hkBound⟩ : Fin (n + 2)) := by
              simpa using b.orderSequence_entryOrZero_eq_order
                (⟨k, hkBound⟩ : Fin (n + 2))
            _ = b.order r.succ := by rw [hrSucc]
            _ ≡ b.order first.succ [ZMOD 2] := hmod)
  have htailCountEven : Even ((i.val + 1) - (first.val + 1)) := by
    rcases hiEvenForProduct with ⟨d, hd⟩
    rcases I.last_even with ⟨s, hs⟩
    refine ⟨d - s, ?_⟩
    simp only [first]
    omega
  have htailCountZero : Int.ModEq 2
      ((((i.val + 1) - (first.val + 1) : Nat) : Int)) 0 := by
    rcases htailCountEven with ⟨d, hd⟩
    rw [Int.modEq_iff_dvd]
    refine ⟨-(d : Int), ?_⟩
    omega
  have hbInitial : Int.ModEq 2
      (b.orderSequence.prefixSum (i.val + 1))
      (((first.val + 1 : Nat) : Int) * reference + 1) := by
    have hzeroTail := htailCountZero.mul_right (b.order first.succ)
    exact hbTail.trans (by
      simpa only [zero_mul, add_zero] using
        (Int.ModEq.rfl.add hzeroTail))
  have hfirstCountOne : Int.ModEq 2
      (((first.val + 1 : Nat) : Int)) 1 := by
    rcases I.last_even with ⟨d, hd⟩
    rw [Int.modEq_iff_dvd]
    refine ⟨-(d : Int), ?_⟩
    simp only [first]
    omega
  have hbReference : Int.ModEq 2
      (b.orderSequence.prefixSum (i.val + 1)) (reference + 1) :=
    hbInitial.trans (by
      have hmul := hfirstCountOne.mul_right reference
      have hone : Int.ModEq 2 (1 : Int) 1 := Int.ModEq.refl 1
      simpa only [one_mul] using hmul.add hone)
  have hiCountOne : Int.ModEq 2
      (((i.val + 1 : Nat) : Int)) 1 := by
    rcases hiEvenForProduct with ⟨d, hd⟩
    rw [Int.modEq_iff_dvd]
    refine ⟨-(d : Int), ?_⟩
    omega
  have hb : Int.ModEq 2
      (b.orderSequence.prefixSum (i.val + 1))
      (((i.val + 1 : Nat) : Int) * (reference + 1)) :=
    hbReference.trans (by
      simpa only [one_mul] using
        (hiCountOne.mul_right (reference + 1)).symm)
  have hiPrefixBound : i.val + 1 <= n + 2 := by
    have hi := i.lt_large
    omega
  exact lemma79_typeI_even_primaryProduct_odd_of_modEq
    b c i.val hiEvenForProduct hiTwo hiPrefixBound reference hb hc

end BONG.GoodBONG

end Bong
