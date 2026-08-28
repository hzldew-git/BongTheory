/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79RightTailGapTwoOddEqualityEndpoint
import Bong.Bong.Beli2019Lemma79RightTailGapTwoLowWitnessOrders

/-!
# Beli (2019), Lemma 7.9(ii), case 8: exclusion of odd equality

Lemma 7.3(ii) makes all orders after the odd domination witness congruent.
Because the remaining tail has even length, the full comparison prefix stays
in the norm-floor class `T`.  The target prefix is in class `T + 1`, contrary
to the comparison-prefix congruence.  This formalizes lines 5971--5975.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- An even zero-based witness and an odd current index leave an even number
of comparison orders after the witness.  Lemma 7.3(ii) therefore preserves
the witness-prefix congruence through the full prefix of length `i`. -/
theorem lemma79_odd_comparisonPrefix_modEq_of_rightEndpoint_eq
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2)) (hiOdd : Odd i.val)
    (j : Fin (n + 1)) (hjEven : Even j.val)
    (hjBefore : j.val + 1 < i.val - 1) (reference : Int)
    (hbase : Int.ModEq 2
      (c.orderSequence.prefixSum (j.val + 1)) reference)
    (hendpoint : c.alphaRightEndpoint j =
      c.alphaRightEndpoint (evenTargetPreviousAlphaIndex i)) :
    Int.ModEq 2 (c.orderSequence.prefixSum i.val) reference := by
  let p : Fin (n + 1) := evenTargetPreviousAlphaIndex i
  have hpVal : p.val = i.val - 2 := by
    simp only [p, evenTargetPreviousAlphaIndex]
  have hjp : j < p := by
    change j.val < p.val
    rw [hpVal]
    omega
  have h73 := c.beli2019Lemma73_ii j p hjp (by
    simpa only [p] using hendpoint)
  have hstartEnd : j.val + 1 <= i.val := by omega
  have htail := c.orderSequence.prefixSum_modEq_add_mul_of_tail
    reference (c.order j.succ) hstartEnd hbase (by
      intro k hkStart hkEnd
      have hkBound : k < n + 2 := hkEnd.trans i.lt_large
      let r : Fin (n + 1) := ⟨k - 1, by omega⟩
      have hjr : j <= r := by
        change j.val <= r.val
        simp only [r]
        omega
      have hrp : r <= p := by
        change r.val <= p.val
        simp only [r]
        rw [hpVal]
        omega
      have hmod := h73.order_modEq r hjr hrp
      let kFin : Fin (n + 2) := ⟨k, hkBound⟩
      have hrSucc : r.succ = kFin := by
        apply Fin.ext
        simp only [r, kFin, Fin.val_succ]
        omega
      calc
        c.orderSequence.entryOrZero k = c.order kFin := by
          simpa only [kFin] using
            c.orderSequence_entryOrZero_eq_order kFin
        _ = c.order r.succ := by rw [hrSucc]
        _ ≡ c.order j.succ [ZMOD 2] := hmod)
  have htailCountEven : Even (i.val - (j.val + 1)) := by
    rcases hiOdd with ⟨d, hd⟩
    rcases hjEven with ⟨s, hs⟩
    refine ⟨d - s, ?_⟩
    omega
  have htailCountEvenInt : Even
      (((i.val - (j.val + 1) : Nat) : Int)) := by
    rcases htailCountEven with ⟨d, hd⟩
    refine ⟨(d : Int), ?_⟩
    exact_mod_cast hd
  have htailCountZero : Int.ModEq 2
      (((i.val - (j.val + 1) : Nat) : Int)) 0 := by
    apply int_modEq_two_of_even_sub
    simpa only [sub_zero] using htailCountEvenInt
  have htailTermZero : Int.ModEq 2
      (((i.val - (j.val + 1) : Nat) : Int) * c.order j.succ) 0 := by
    simpa only [zero_mul] using htailCountZero.mul_right (c.order j.succ)
  have hreference : Int.ModEq 2
      (reference +
        (((i.val - (j.val + 1) : Nat) : Int) * c.order j.succ))
      reference := by
    simpa only [add_zero] using
      (Int.ModEq.rfl : Int.ModEq 2 reference reference).add htailTermZero
  exact htail.trans hreference

/-- The equality alternative in odd-index capped domination is impossible:
the comparison prefix would be congruent to `T`, while the target prefix and
the global prefix relation force it to be congruent to `T + 1`. -/
theorem beli2019Lemma79_typeI_caseEight_gapTwo_odd_domination_equality_false
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
    (hiOdd : Odd i.val)
    (hprefix : Int.ModEq 2 (b.orderSequence.prefixSum i.val)
      (c.orderSequence.prefixSum i.val))
    (hcomparison : c.truncatedPrefixDefect c
      ((-1) ^ ((i.val - 1) / 2)) 0 (i.val - 1) =
        ((((b.order (Fin.mk D.profile.last hlast).castSucc -
          b.order (Fin.mk D.profile.last hlast).succ : Int) : Rat) +
          b.alphaValue (Fin.mk D.profile.last hlast) : Rat) : WithTop Rat))
    (j : Fin (n + 1)) (hjEven : Even j.val)
    (hjBefore : j.val + 1 < i.val - 1)
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
    False := by
  let first : Fin (n + 1) := Fin.mk D.profile.last hlast
  let reference : Int := a.orderSequence.entryOrZero D.anchor + 1
  have hiTwo : 2 <= i.val := by omega
  rcases beli2019Lemma79_typeI_caseEight_gapTwo_lowWitness_orders
      a b c D hfirst hgapTwo hlast hnorm j hjEven (by
        simpa only [first] using hlow) with
    ⟨_, hjOrder, htargetOrder, hjPrefix⟩
  have hsource : b.order first.castSucc = c.order j.castSucc + 1 := by
    simp only [first, reference] at hjOrder htargetOrder ⊢
    omega
  have hjDefect : c.truncatedPrefixDefect c (-1) j.val (j.val + 2) <=
      c.truncatedPrefixDefect c
        ((-1) ^ ((i.val - 1) / 2)) 0 (i.val - 1) := by
    rw [hcomparison]
    simpa only [first] using hjPair
  have heq : c.truncatedPrefixDefect c
        ((-1) ^ ((i.val - 1) / 2)) 0 (i.val - 1) =
      ((show Rat from
          ((b.order first.castSucc -
            c.order (evenTargetPreviousIndex i) : Int) : Rat) +
            c.alphaValue (evenTargetPreviousAlphaIndex i) - 1) :
        WithTop Rat) := by
    calc
      c.truncatedPrefixDefect c
          ((-1) ^ ((i.val - 1) / 2)) 0 (i.val - 1) =
          ((((b.order first.castSucc - b.order first.succ : Int) : Rat) +
            b.alphaValue first : Rat) : WithTop Rat) := by
              simpa only [first] using hcomparison
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
          have hsourceQ : (b.order first.castSucc : Rat) =
              (c.order j.castSucc : Rat) + 1 := by
            exact_mod_cast hsource
          push_cast at hsourceQ ⊢
          linarith
  have hendpoint := lemma79_odd_rightEndpoint_eq_of_domination_equality
    c i hiTwo j hjBefore (b.order first.castSucc) (by
      omega) hjDefect heq
  have hcomparisonPrefix :=
    lemma79_odd_comparisonPrefix_modEq_of_rightEndpoint_eq
      c i hiOdd j hjEven hjBefore reference (by
        simpa only [reference] using hjPrefix) hendpoint
  have htargetPrefix :=
    beli2019Lemma79_typeI_caseEight_gapTwo_odd_targetPrefix_modEq
      a b D hfirst hgapTwo hlast i hafter H hiOdd
  have hbad : Int.ModEq 2 (reference + 1) reference := by
    have htargetReference :
        a.orderSequence.entryOrZero D.anchor + 2 = reference + 1 := by
      simp only [reference]
      omega
    rw [htargetReference] at htargetPrefix
    exact htargetPrefix.symm.trans (hprefix.trans hcomparisonPrefix)
  rw [Int.modEq_iff_dvd] at hbad
  rcases hbad with ⟨z, hz⟩
  omega

end BONG.GoodBONG

end Bong
