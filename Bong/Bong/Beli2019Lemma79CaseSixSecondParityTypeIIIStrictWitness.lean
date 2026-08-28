/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79CaseSixSecondParityTypeIIIWitness
import Bong.Bong.Beli2019Lemma79EvenTargetDomination

/-!
# Beli (2019), Lemma 7.9(ii), case 6: the strict type-III witness

If the order selected by domination is at least two above the left source
order, its transported coefficient and the two type-III boundary identities
make the primary right cap nonpositive.  Condition 2.1(ii) then follows from
nonnegativity of the target comparison defect.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- A domination witness strictly above the left type-III boundary makes
the primary right cap nonpositive. -/
theorem beli2019Lemma79_typeIII_caseSix_secondParity_of_strictWitness
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : D.outer.transition.firstTwo - 1 ≤ i.val)
    (hthroughLast : i.val ≤ D.outer.last)
    (heven : Even
      (i.val - (D.outer.transition.firstTwo - 1)))
    (hiTwo : 2 ≤ i.val) (j : Fin (n + 1))
    (hcoefficient :
      (((((c.order j.castSucc - c.order (evenTargetPreviousIndex i) : Int) : ℚ) +
          c.alphaValue (evenTargetPreviousAlphaIndex i) : ℚ)) : WithTop ℚ) ≤
        ((((b.orderSequence.entryOrZero D.outer.transition.lastZero -
            a.orderSequence.entryOrZero
              (D.outer.transition.lastZero + 1) : Int) : ℚ)) :
          WithTop ℚ))
    (hstrict : a.orderSequence.entryOrZero D.outer.transition.lastZero + 2 ≤
      c.order j.castSucc) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  let central : Int :=
    b.orderSequence.entryOrZero D.outer.transition.lastZero -
      a.orderSequence.entryOrZero (D.outer.transition.lastZero + 1)
  have hcurrent := D.outer.target_rightEven_eq_boundary
    i.val hright hthroughLast heven
  have hrightIndex : D.outer.transition.firstTwo - 1 =
      D.outer.transition.lastZero + 1 := by
    rw [D.adjacent]
    omega
  have hleftBoundary := D.outer.transition.leftBoundary
  have hrightBoundary := D.outer.transition.rightBoundary
  have hcurrentCentral :
      b.orderSequence.entryOrZero i.val + central ≤ c.order j.castSucc := by
    rw [hrightBoundary, hrightIndex] at hcurrent
    simp only [central]
    omega
  have hcurrentOrder : b.order ⟨i.val, i.lt_large⟩ =
      b.orderSequence.entryOrZero i.val := by
    exact (b.orderSequence_entryOrZero_eq_order ⟨i.val, i.lt_large⟩).symm
  have hcoefficientQ :
      (((c.order j.castSucc - c.order (evenTargetPreviousIndex i) : Int) : ℚ) +
          c.alphaValue (evenTargetPreviousAlphaIndex i) : ℚ) ≤
        (central : ℚ) := by
    exact WithTop.coe_le_coe.mp (by simpa only [central] using hcoefficient)
  let delta : ℚ :=
    ((b.order ⟨i.val, i.lt_large⟩ - c.order j.castSucc : Int) : ℚ)
  have htransported : delta +
      (((c.order j.castSucc - c.order (evenTargetPreviousIndex i) : Int) : ℚ) +
        c.alphaValue (evenTargetPreviousAlphaIndex i)) ≤
      delta + (central : ℚ) :=
    by simpa only [add_comm] using add_le_add_left hcoefficientQ delta
  have hdelta : delta + (central : ℚ) ≤ 0 := by
    have hdeltaInt : b.order ⟨i.val, i.lt_large⟩ -
        c.order j.castSucc + central ≤ 0 := by
      rw [hcurrentOrder]
      omega
    simp only [delta]
    exact_mod_cast hdeltaInt
  have hcapQ :
      (((b.order ⟨i.val, i.lt_large⟩ -
          c.order (evenTargetPreviousIndex i) : Int) : ℚ) +
          c.alphaValue (evenTargetPreviousAlphaIndex i) : ℚ) ≤ 0 := by
    calc
      (((b.order ⟨i.val, i.lt_large⟩ -
          c.order (evenTargetPreviousIndex i) : Int) : ℚ) +
          c.alphaValue (evenTargetPreviousAlphaIndex i) : ℚ) =
          ((b.order ⟨i.val, i.lt_large⟩ - c.order j.castSucc : Int) : ℚ) +
            (((c.order j.castSucc -
              c.order (evenTargetPreviousIndex i) : Int) : ℚ) +
              c.alphaValue (evenTargetPreviousAlphaIndex i)) := by
        push_cast
        ring
      _ ≤ delta + (central : ℚ) := by
        simpa only [delta] using htransported
      _ ≤ 0 := hdelta
  calc
    (b.representationAlphaValue c i : WithTop ℚ) ≤
        (((b.order ⟨i.val, i.lt_large⟩ -
          c.order (evenTargetPreviousIndex i) : Int) : ℚ) : WithTop ℚ) +
          c.prefixAlphaCap (i.val - 1) :=
      lemma79_representationAlphaValue_le_primaryRightCap b c i
    _ = (((((b.order ⟨i.val, i.lt_large⟩ -
          c.order (evenTargetPreviousIndex i) : Int) : ℚ) +
          c.alphaValue (evenTargetPreviousAlphaIndex i) : ℚ)) : WithTop ℚ) :=
      evenTarget_primaryRightCap_eq b c i hiTwo
    _ ≤ 0 := by exact_mod_cast hcapQ
    _ ≤ b.truncatedPrefixDefect c 1 i.val i.val :=
      b.truncatedPrefixDefect_nonneg c 1 i.val i.val

end BONG.GoodBONG

end Bong
