/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma67Classification

/-!
# Beli (2019), Lemma 7.9(ii), case 8: the unchanged suffix

After the last unequal order, equality of the suffix entries transports the
full volume gap to every later prefix.  This is the first common fact in
case 8, before the three Lemma 6.7 types are separated again.
-/

namespace Bong

namespace BeliOrderSequence

variable {Gamma : Type} [AddCommGroup Gamma] [LinearOrder Gamma]
  [IsOrderedAddMonoid Gamma]

omit [IsOrderedAddMonoid Gamma] in
/-- A fixed total gap remains the prefix gap after a common suffix is
removed. -/
theorem prefixSum_add_totalGap_eq_of_suffix_entries_eq {n : Nat}
    (x y : BeliOrderSequence n Gamma) (gap : Gamma)
    (htotal : x.prefixSum n + gap = y.prefixSum n)
    (j : Nat) (hj : j <= n)
    (hsuffix : forall k, j <= k -> k < n ->
      x.entryOrZero k = y.entryOrZero k) :
    x.prefixSum j + gap = y.prefixSum j := by
  have hsums := x.suffixSum_eq_of_entryOrZero_eq_after y j hj hsuffix
  calc
    x.prefixSum j + gap = x.prefixSum n + gap - x.suffixSum j := by
      rw [x.suffixSum_eq_total_sub_prefix j hj]
      abel
    _ = y.prefixSum n - y.suffixSum j := by rw [htotal, hsums]
    _ = y.prefixSum j := by
      rw [y.suffixSum_eq_total_sub_prefix j hj]
      abel

omit [IsOrderedAddMonoid Gamma] in
/-- The preceding prefix-gap result, specialized to an explicitly known
last unequal coordinate. -/
theorem IsLastDifferenceAt.prefixSum_add_totalGap_eq_after {n : Nat}
    {x y : BeliOrderSequence n Gamma} {last : Nat}
    (D : IsLastDifferenceAt x y last) (gap : Gamma)
    (htotal : x.prefixSum n + gap = y.prefixSum n)
    (j : Nat) (hlast : last < j) (hj : j <= n) :
    x.prefixSum j + gap = y.prefixSum j := by
  apply x.prefixSum_add_totalGap_eq_of_suffix_entries_eq y gap htotal j hj
  intro k hjk hkn
  exact D.after k (hlast.trans_le hjk) hkn

end BeliOrderSequence

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- Case 8's prefix-sum identity in type I. -/
theorem beli2019Lemma79_typeI_caseEight_prefixSum
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (j : Nat) (hafter : D.profile.last < j) (hj : j <= n + 2) :
    a.orderSequence.prefixSum j + 2 =
      b.orderSequence.prefixSum j :=
  D.profile.lastDifference.prefixSum_add_totalGap_eq_after
    2 htotal j hafter hj

/-- Case 8's prefix-sum identity in type II. -/
theorem beli2019Lemma79_typeII_caseEight_prefixSum
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeII a b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (j : Nat) (hafter : D.outer.last < j) (hj : j <= n + 2) :
    a.orderSequence.prefixSum j + 2 =
      b.orderSequence.prefixSum j :=
  D.outer.lastDifference.prefixSum_add_totalGap_eq_after
    2 htotal j hafter hj

/-- Case 8's prefix-sum identity in type III. -/
theorem beli2019Lemma79_typeIII_caseEight_prefixSum
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (j : Nat) (hafter : D.outer.last < j) (hj : j <= n + 2) :
    a.orderSequence.prefixSum j + 2 =
      b.orderSequence.prefixSum j :=
  D.outer.lastDifference.prefixSum_add_totalGap_eq_after
    2 htotal j hafter hj

/-- The unchanged suffix required by the generic case-8 assembly in type I. -/
theorem beli2019Lemma79_typeI_caseEight_suffix
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hafter : D.profile.last < i.val) :
    forall k, i.val <= k -> k < n + 2 ->
      a.orderSequence.entryOrZero k = b.orderSequence.entryOrZero k := by
  intro k hik hkn
  exact D.profile.lastDifference.after k (hafter.trans_le hik) hkn

/-- The unchanged suffix required by the generic case-8 assembly in type II. -/
theorem beli2019Lemma79_typeII_caseEight_suffix
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeII a b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hafter : D.outer.last < i.val) :
    forall k, i.val <= k -> k < n + 2 ->
      a.orderSequence.entryOrZero k = b.orderSequence.entryOrZero k := by
  intro k hik hkn
  exact D.outer.lastDifference.after k (hafter.trans_le hik) hkn

/-- The unchanged suffix required by the generic case-8 assembly in type III. -/
theorem beli2019Lemma79_typeIII_caseEight_suffix
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeIII a b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hafter : D.outer.last < i.val) :
    forall k, i.val <= k -> k < n + 2 ->
      a.orderSequence.entryOrZero k = b.orderSequence.entryOrZero k := by
  intro k hik hkn
  exact D.outer.lastDifference.after k (hafter.trans_le hik) hkn

end BONG.GoodBONG

end Bong
