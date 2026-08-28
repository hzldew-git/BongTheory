/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeIRightComplete
import Bong.Bong.Beli2019Lemma72TypeICanonical
import Bong.Bong.Beli2019Lemma79CaseSixSecondParityProfile

/-!
# Beli (2019), Lemma 7.9(ii), case 6: the type-I right-even profile

The published TeX comments out the phrase saying that case 6 also contains
the even type-I interval after `t'`.  This file records the corresponding
canonical profile facts.  On that interval the target current order is one
above the source order, the preceding target alpha is one, and the source
and target prefixes have opposite parity.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The canonical type-I anchor is even after normalizing the first unequal
coordinate to zero. -/
theorem lemma79_typeI_anchor_even
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (hfirst : D.profile.first = 0) :
    Even D.anchor := by
  by_cases heq : D.profile.first = D.anchor
  · rw [← heq, hfirst]
    exact ⟨0, by omega⟩
  · have hlt : D.profile.first < D.anchor :=
      lt_of_le_of_ne D.profile.first_le_anchor heq
    simpa only [hfirst, Nat.sub_zero] using
      (D.profile.leftProfile hlt).1

/-- The last unequal type-I coordinate is even in the nonterminal right
branch. -/
theorem lemma79_typeI_last_even
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last) :
    Even D.profile.last := by
  have hanchorEven := lemma79_typeI_anchor_even a b D hfirst
  have hanchorLast : D.anchor < D.profile.last :=
    C.anchor_le_right.trans_lt hrightLast
  have hdistance := (D.profile.rightProfile hanchorLast).1
  rcases hanchorEven with ⟨d, hd⟩
  rcases hdistance with ⟨e, he⟩
  exact ⟨d + e, by omega⟩

/-- At an even type-I coordinate after the right switch, the target order
is exactly one above the source order. -/
theorem lemma79_typeI_caseSix_current_eq_source_add_one
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : C.rightSwitch < i.val)
    (hthroughLast : i.val ≤ D.profile.last) (hiEven : Even i.val) :
    b.orderSequence.entryOrZero i.val =
      a.orderSequence.entryOrZero i.val + 1 := by
  have hanchorEven := lemma79_typeI_anchor_even a b D hfirst
  have hdistance : Even (i.val - D.anchor) := by
    rcases hiEven with ⟨d, hd⟩
    rcases hanchorEven with ⟨e, he⟩
    exact ⟨d - e, by
      have hanchorRight := C.anchor_le_right
      omega⟩
  have hsource := C.source_after_right i.val hright hthroughLast hdistance
  have htarget := C.target_from_anchor i.val
    (C.anchor_le_right.trans hright.le) hthroughLast hdistance
  have hgap := D.anchor_gap
  omega

/-- The current target order is `R + 2`, where `R` is the canonical source
anchor order. -/
theorem lemma79_typeI_caseSix_current_eq_reference_add_one
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : C.rightSwitch < i.val)
    (hthroughLast : i.val ≤ D.profile.last) (hiEven : Even i.val) :
    b.orderSequence.entryOrZero i.val =
      (a.orderSequence.entryOrZero D.anchor + 1) + 1 := by
  have hanchorEven := lemma79_typeI_anchor_even a b D hfirst
  have hdistance : Even (i.val - D.anchor) := by
    rcases hiEven with ⟨d, hd⟩
    rcases hanchorEven with ⟨e, he⟩
    exact ⟨d - e, by
      have hanchorRight := C.anchor_le_right
      omega⟩
  have htarget := C.target_from_anchor i.val
    (C.anchor_le_right.trans hright.le) hthroughLast hdistance
  have hgap := D.anchor_gap
  omega

/-- Every odd target alpha strictly after the right switch and before the
last unequal coordinate is exactly one. -/
theorem beli2019Remark613_typeI_targetRightAlpha_eq_one
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last)
    (hdefect : a.RepresentationDefectCondition b)
    (k : Nat) (hright : C.rightSwitch < k)
    (hlast : k < D.profile.last) (hkOdd : Odd k) :
    b.alphaValue ⟨k, by
      have hbound := D.profile.lastDifference.bound
      omega⟩ = 1 := by
  let p : Fin (n + 1) := ⟨k, by
    have hbound := D.profile.lastDifference.bound
    omega⟩
  have horders := lemma69_typeI_rightOdd_orders
    a b D C hfirst k hright hlast hkOdd
  have hsourceGap := a.orderGap_ge_neg_two_mul_e p
  have htargetGap : -(2 * (ramificationIndex K : Int)) < b.orderGap p := by
    unfold orderGap at hsourceGap ⊢
    rw [← b.orderSequence_entryOrZero_eq_order p.succ,
      ← b.orderSequence_entryOrZero_eq_order p.castSucc]
    change -(2 * (ramificationIndex K : Int)) <
      b.orderSequence.entryOrZero (k + 1) -
        b.orderSequence.entryOrZero k
    rw [← a.orderSequence_entryOrZero_eq_order p.succ,
      ← a.orderSequence_entryOrZero_eq_order p.castSucc] at hsourceGap
    change -(2 * (ramificationIndex K : Int)) ≤
      a.orderSequence.entryOrZero (k + 1) -
        a.orderSequence.entryOrZero k at hsourceGap
    omega
  have halphaLe := beli2019Lemma69_i_typeI_targetRightTail
    a b D C hfirst hrightLast hdefect k hright hlast hkOdd
  have halphaNe : b.alphaValue p ≠ 0 := by
    intro halphaZero
    have hgapEq := (b.alpha_p2 p).2.mp halphaZero
    exact (ne_of_gt htargetGap) hgapEq
  have halphaOne : (1 : ℚ) ≤ b.alphaValue p :=
    b.one_le_alphaValue_of_ne_zero p halphaNe
  have : b.alphaValue p = 1 := le_antisymm
    (by simpa only [p] using halphaLe) halphaOne
  simpa only [p] using this

/-- On the type-I case-6 parity class, the source and target prefix sums
have opposite parity. -/
theorem beli2019Lemma79_typeI_caseSix_prefix_opposite
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : C.rightSwitch < i.val)
    (hthroughLast : i.val ≤ D.profile.last) (hiEven : Even i.val) :
    Int.ModEq 2 (a.orderSequence.prefixSum i.val + 1)
      (b.orderSequence.prefixSum i.val) := by
  have hsource := lemma72_typeI_source_after_of_canonical
    a b D C hfirst i.val (by omega) (by omega)
  have htarget := lemma72_typeI_target_after_of_canonical
    a b D C hfirst i.val (by
      have hleftRight := C.left_le_anchor.trans C.anchor_le_right
      omega) (by omega)
  have hbridge : Int.ModEq 2
      ((i.val : Int) * (a.orderSequence.entryOrZero D.anchor + 1))
      ((i.val : Int) * (a.orderSequence.entryOrZero D.anchor + 2)) := by
    apply int_modEq_two_of_even_sub
    rcases hiEven with ⟨d, hd⟩
    refine ⟨-(d : Int), ?_⟩
    have hdInt : (i.val : Int) = (d : Int) + (d : Int) := by
      exact_mod_cast hd
    rw [hdInt]
    ring
  have hsourceOne := hsource.add (Int.ModEq.refl 1)
  have hsourceOne' : Int.ModEq 2
      (a.orderSequence.prefixSum i.val + 1)
      ((i.val : Int) * (a.orderSequence.entryOrZero D.anchor + 1)) := by
    simpa only [sub_add_cancel] using hsourceOne
  exact hsourceOne'.trans (hbridge.trans htarget.symm)

/-- The target prefix at an even type-I case-6 coordinate has even order. -/
theorem beli2019Lemma79_typeI_caseSix_targetPrefix_even
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hright : C.rightSwitch < i.val)
    (hthroughLast : i.val ≤ D.profile.last) (hiEven : Even i.val) :
    Even (b.orderSequence.prefixSum i.val) := by
  have htarget := lemma72_typeI_target_after_of_canonical
    a b D C hfirst i.val (by
      have hleftRight := C.left_le_anchor.trans C.anchor_le_right
      omega) (by omega)
  apply caseSix_even_of_modEq_two_of_even htarget
  rcases hiEven with ⟨d, hd⟩
  refine ⟨(d : Int) *
    (a.orderSequence.entryOrZero D.anchor + 2), ?_⟩
  have hdInt : (i.val : Int) = (d : Int) + (d : Int) := by
    exact_mod_cast hd
  rw [hdInt]
  ring

/-- The strict norm comparison puts the type-I case-6 reference below the
first comparison order. -/
theorem beli2019Lemma79_typeI_caseSix_reference_le_thirdFirst
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeI a b)
    (C : Lemma67TypeICanonicalData a b D)
    (_hfirst : D.profile.first = 0)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L) :
    a.orderSequence.entryOrZero D.anchor + 1 ≤
      c.orderSequence.entryOrZero 0 := by
  have hnormOrder := a.toBONG.order_zero_add_one_le_of_normIdeal_lt
    c.toBONG hnorm
  have hfirstOrder : a.orderSequence.entryOrZero 0 + 1 ≤
      c.orderSequence.entryOrZero 0 := by
    calc
      a.orderSequence.entryOrZero 0 + 1 = a.order 0 + 1 := by
        rw [a.orderSequence.entryOrZero_of_lt (by omega)]
        rfl
      _ ≤ c.order 0 := hnormOrder
      _ = c.orderSequence.entryOrZero 0 := by
        rw [c.orderSequence.entryOrZero_of_lt (by omega)]
        rfl
  have hsourceZero := C.source_to_anchor 0
    (Nat.zero_le D.anchor) ⟨0, by omega⟩
  rw [hsourceZero] at hfirstOrder
  exact hfirstOrder

end BONG.GoodBONG

end Bong
