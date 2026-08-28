/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019OrderSequence

/-!
# M120 Beli 2019, Definitions 2--3 and Lemmas 1.6--1.8 smoke tests
-/

namespace BongTest.M120

open Bong

variable {l m n : Nat}
  {x : BeliOrderSequence l} {y : BeliOrderSequence m}
  {z : BeliOrderSequence n}

example (x : BeliOrderSequence n) : BeliOrderLE x x :=
  BeliOrderLE.refl x

example (hxy : BeliOrderLE x y) (hyz : BeliOrderLE y z) :
    BeliOrderLE x z :=
  hxy.trans hyz

example (hxy : BeliOrderLE x y) (i : Nat) (hi : i + 1 < m) :
    x.entry i (Nat.lt_of_lt_of_le (by omega) hxy.rank) +
        x.entry (i + 1) (hi.trans_le hxy.rank) ≤
      y.entry i (by omega) + y.entry (i + 1) hi :=
  hxy.pairSum_le i hi

example (hxy : BeliOrderLE x y) (i : Nat) (hi0 : 0 < i) (hi : i < m)
    (hiNext : i + 1 < l)
    (hnext : y.entry (i - 1) (by omega) ≤ x.entry (i + 1) hiNext) :
    x.entry i (hi.trans_le hxy.rank) ≤ y.entry i hi :=
  hxy.current_le_of_next_ge_previous i hi0 hi hiNext hnext

example {κ : Int} (hxy : BeliOrderLE x y)
    (hx : x.IsKappaBounded κ) (hy : y.IsKappaBounded κ)
    (i : Nat) (hi : i < m) (hiNext : i + 1 < l)
    (hgap : κ ≤ x.entry (i + 1) hiNext - y.entry i hi) :
    x.entry i (hi.trans_le hxy.rank) ≤ y.entry i hi ∧
      ∀ hiSmallNext : i + 1 < m,
        x.entry (i + 1) (hiSmallNext.trans_le hxy.rank) ≤
          y.entry (i + 1) hiSmallNext :=
  x.le_pair_of_large_crossGap hxy hx hy i hi hiNext hgap

example (x : BeliOrderSequence n) :
    let sequence : BeliOrderFamily := ⟨n, x⟩
    sequence ≤ sequence := by
  exact le_rfl

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

example (a : BONG.GoodBONG q L (l + 1))
    (b : BONG.GoodBONG r M (m + 1)) (hRank : m ≤ l) :
    a.RepresentationOrderCondition b hRank ↔
      BeliOrderLE a.orderSequence b.orderSequence :=
  a.representationOrderCondition_iff b hRank

#print axioms Bong.BeliOrderLE.pairSum_le
#print axioms Bong.BeliOrderLE.next_gt_previous_of_pair_gt
#print axioms Bong.BeliOrderLE.current_le_of_next_ge_previous
#print axioms Bong.BeliOrderLE.trans
#print axioms Bong.BeliOrderLE.antisymm
#print axioms Bong.BeliOrderSequence.le_pair_of_large_crossGap
#print axioms Bong.BONG.GoodBONG.representationOrderCondition_iff

end BongTest.M120
