/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79OrderTransfer

/-!
# Beli (2019), Lemma 7.9: reduction of condition (i)

Lemma 6.7 supplies a last differing coordinate in each of its three cases.
The order condition for the third lattice therefore only has to be checked
through that coordinate.  The common suffix is discharged by the generic
transport theorem in the preceding file.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Condition 2.1(i) in Lemma 7.9 reduces, case by case, to the altered
finite interval of the index-`p` pair. -/
theorem beli2019Lemma79_orderCondition_of_type_interiors
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (D : Lemma67Classification a b)
    (hac : a.RepresentationOrderCondition c le_rfl)
    (typeI : ∀ E : Lemma67TypeI a b,
      ∀ (i : Nat) (hi : i < n + 1), i ≤ E.profile.last →
        b.orderSequence.entry i hi ≤ c.orderSequence.entry i hi ∨
          ∃ (hi0 : 0 < i) (hiNext : i + 1 < n + 1),
            b.orderSequence.entry i hi +
                b.orderSequence.entry (i + 1) hiNext ≤
              c.orderSequence.entry (i - 1) (by omega) +
                c.orderSequence.entry i hi)
    (typeII : ∀ E : Lemma67TypeII a b,
      ∀ (i : Nat) (hi : i < n + 1), i ≤ E.outer.last →
        b.orderSequence.entry i hi ≤ c.orderSequence.entry i hi ∨
          ∃ (hi0 : 0 < i) (hiNext : i + 1 < n + 1),
            b.orderSequence.entry i hi +
                b.orderSequence.entry (i + 1) hiNext ≤
              c.orderSequence.entry (i - 1) (by omega) +
                c.orderSequence.entry i hi)
    (typeIII : ∀ E : Lemma67TypeIII a b,
      ∀ (i : Nat) (hi : i < n + 1), i ≤ E.outer.last →
        b.orderSequence.entry i hi ≤ c.orderSequence.entry i hi ∨
          ∃ (hi0 : 0 < i) (hiNext : i + 1 < n + 1),
            b.orderSequence.entry i hi +
                b.orderSequence.entry (i + 1) hiNext ≤
              c.orderSequence.entry (i - 1) (by omega) +
                c.orderSequence.entry i hi) :
    b.RepresentationOrderCondition c le_rfl := by
  have hacSequence :=
    (a.representationOrderCondition_iff c le_rfl).mp hac
  apply (b.representationOrderCondition_iff c le_rfl).mpr
  cases D with
  | typeI E =>
      exact BeliOrderLE.of_compare_through_lastDifference
        hacSequence E.profile.lastDifference (typeI E)
  | typeII E =>
      exact BeliOrderLE.of_compare_through_lastDifference
        hacSequence E.outer.lastDifference (typeII E)
  | typeIII E =>
      exact BeliOrderLE.of_compare_through_lastDifference
        hacSequence E.outer.lastDifference (typeIII E)

end BONG.GoodBONG

end Bong
