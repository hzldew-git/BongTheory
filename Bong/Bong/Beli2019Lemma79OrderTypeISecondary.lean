/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79OrderCandidateExtraction
import Bong.Bong.Beli2019Lemma79OrderTypeIHalfGap

/-!
# Beli (2019), Lemma 7.9(i): the type-I secondary candidate

At a difficult even type-I coordinate, the next source pair is the
corresponding target pair.  Two-step monotonicity of the target BONG places
the current target pair below it.  Consequently a nonpositive secondary
candidate gives exactly the adjacent-pair alternative in condition 2.1(i).
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}
  [Beli2006AlphaLaws.{u, v} K]

/-- The current target pair is bounded by the following source pair at every
nonterminal difficult even type-I coordinate. -/
theorem lemma79_typeI_even_targetPair_le_sourceNextPair
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (k : Nat) (hkTwo : k + 2 < n + 2) (hkEven : Even k)
    (hleft : C.leftSwitch ≤ k) :
    b.orderSequence.entryOrZero k +
        b.orderSequence.entryOrZero (k + 1) ≤
      a.orderSequence.entryOrZero (k + 1) +
        a.orderSequence.entryOrZero (k + 2) := by
  have hpair : a.orderSequence.entryOrZero (k + 1) +
      a.orderSequence.entryOrZero (k + 2) =
        b.orderSequence.entryOrZero (k + 1) +
          b.orderSequence.entryOrZero (k + 2) := by
    by_cases hcentral : k + 1 < C.rightSwitch
    · exact lemma69_v_typeI_adjacent_entry_sum_eq
        a b D C hfirst (k + 1) (by omega) hcentral
    · have hright : C.rightSwitch ≤ k := by
        rcases hkEven with ⟨d, hd⟩
        rcases C.right_even with ⟨e, he⟩
        omega
      have hanchorEven : Even D.anchor := by
        by_cases heq : D.profile.first = D.anchor
        · rw [← heq, hfirst]
          exact ⟨0, by omega⟩
        · have hlt : D.profile.first < D.anchor :=
            lt_of_le_of_ne D.profile.first_le_anchor heq
          simpa only [hfirst, Nat.sub_zero] using
            (D.profile.leftProfile hlt).1
      have hpairParity : Even ((k + 1) - (D.anchor + 1)) := by
        rcases hkEven with ⟨d, hd⟩
        rcases hanchorEven with ⟨e, he⟩
        exact ⟨d - e, by omega⟩
      exact D.profile.rightPairEq (k + 1) (by
        have hanchorRight := C.anchor_le_right
        omega) (by omega) hpairParity
  have htwoStep := b.orderSequence.twoStep k hkTwo
  have hk : k < n + 2 := by omega
  have hkOne : k + 1 < n + 2 := by omega
  change b.orderSequence.entry k hk ≤
    b.orderSequence.entry (k + 2) hkTwo at htwoStep
  calc
    b.orderSequence.entryOrZero k +
        b.orderSequence.entryOrZero (k + 1) ≤
      b.orderSequence.entryOrZero (k + 1) +
        b.orderSequence.entryOrZero (k + 2) := by
      rw [b.orderSequence.entryOrZero_of_lt hk,
        b.orderSequence.entryOrZero_of_lt hkOne,
        b.orderSequence.entryOrZero_of_lt hkTwo]
      omega
    _ = a.orderSequence.entryOrZero (k + 1) +
        a.orderSequence.entryOrZero (k + 2) := hpair.symm

/-- A nonpositive secondary candidate proves the adjacent-pair alternative
for the new type-I target. -/
theorem lemma79_typeI_even_pair_of_secondary_le_zero
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (k : Nat) (hk : k < n + 2) (hkNext : k + 1 < n + 2)
    (hkEven : Even k) (hleft : C.leftSwitch ≤ k)
    (hi : 1 < k + 1 ∧ k + 1 + 1 < n + 2)
    (hsecondary : a.representationSecondaryDefect c {
      val := k + 1
      pos := by omega
      lt_large := hkNext
      le_small := hkNext.le } hi ≤ 0) :
    b.orderSequence.entry k hk +
        b.orderSequence.entry (k + 1) hkNext ≤
      c.orderSequence.entry (k - 1) (by omega) +
        c.orderSequence.entry k hk := by
  let i : RepresentationIndex (n + 2) (n + 2) := {
    val := k + 1
    pos := by omega
    lt_large := hkNext
    le_small := hkNext.le }
  have hsourcePair := a.sourcePair_le_targetPair_of_secondary_le_zero
    c i hi (by simpa only [i] using hsecondary)
  have hsourcePair' : a.orderSequence.entryOrZero (k + 1) +
      a.orderSequence.entryOrZero (k + 2) ≤
        c.orderSequence.entryOrZero (k - 1) +
          c.orderSequence.entryOrZero k := by
    rw [a.orderSequence_entryOrZero_eq_order ⟨k + 1, hkNext⟩,
      a.orderSequence_entryOrZero_eq_order ⟨k + 2, hi.2⟩,
      c.orderSequence_entryOrZero_eq_order ⟨k - 1, by omega⟩,
      c.orderSequence_entryOrZero_eq_order ⟨k, hk⟩]
    convert hsourcePair using 1
    congr 1
  have htargetPair := lemma79_typeI_even_targetPair_le_sourceNextPair
    a b D C hfirst k hi.2 hkEven hleft
  calc
    b.orderSequence.entry k hk +
        b.orderSequence.entry (k + 1) hkNext =
      b.orderSequence.entryOrZero k +
        b.orderSequence.entryOrZero (k + 1) := by
      rw [b.orderSequence.entryOrZero_of_lt hk,
        b.orderSequence.entryOrZero_of_lt hkNext]
    _ ≤ a.orderSequence.entryOrZero (k + 1) +
        a.orderSequence.entryOrZero (k + 2) := htargetPair
    _ ≤ c.orderSequence.entryOrZero (k - 1) +
        c.orderSequence.entryOrZero k := hsourcePair'
    _ = c.orderSequence.entry (k - 1) (by omega) +
        c.orderSequence.entry k hk := by
      rw [c.orderSequence.entryOrZero_of_lt (by omega),
        c.orderSequence.entryOrZero_of_lt hk]

end BONG.GoodBONG

end Bong
