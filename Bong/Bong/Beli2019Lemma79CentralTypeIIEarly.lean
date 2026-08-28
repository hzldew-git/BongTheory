/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79CentralOuterEarly
import Bong.Bong.Beli2019Lemma69TypeIICoreAlpha

/-!
# Beli (2019), Lemma 7.9(iii): early type II

This is case 1 together with the early part of case 7.  Odd first
alternatives use the common endpoint-tower construction.  Even boundaries,
strictly early second alternatives, and the transition-boundary second
alternative are impossible.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- At the first type-II transition boundary both alphas in the second
alternative are one, so their sum cannot exceed `2e`. -/
theorem lemma79Central_typeIIEarly_boundary_second_not
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeII a b) (hfirst : D.outer.first = 0)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hboundary : i.val = D.outer.transition.lastZero + 1)
    (hcurrent :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        b.prefixAlphaCap i.val + b.centralCurrentDefect c i) : False := by
  have hiNext : i.val + 1 < n + 2 := by
    have hbound := D.outer.transition.firstTwo_le_rank
    have hlong := D.long
    omega
  have hsum := b.lemma79Central_secondAlternative_targetAlphaSum
    c i hiNext hcurrent
  have hprevious := a.beli2019Lemma69_i_typeII_targetCore_eq_one
    b D hfirst (i.val - 1) (by omega) (by
      have hlong := D.long
      omega)
  have hnext := a.beli2019Lemma69_i_typeII_targetCore_eq_one
    b D hfirst i.val (by omega) (by
      have hlong := D.long
      omega)
  rw [hprevious, hnext] at hsum
  have hePos := ramificationIndex_pos (K := K)
  norm_num at hsum
  exact (Nat.ne_of_gt hePos) hsum

/-- The first Lemma 2.18 alternative throughout the early type-II
interval. -/
theorem lemma79CentralWitness_typeIIEarly_firstAlternative
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [DyadicDiscriminantClassLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeII a b) (hfirst : D.outer.first = 0)
    (hdefectBC : b.RepresentationDefectCondition c)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hearly : i.val ≤ D.outer.transition.lastZero + 1)
    (hiOdd : Odd i.val)
    (hprevious :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        b.prefixAlphaCap i.val + b.representationAlpha c i.previous) :
    Lemma79CentralWitness a b c i := by
  apply Lemma79CentralWitness.direct
  have hpreviousEven : Even (i.val - 1) := by
    rcases hiOdd with ⟨d, hd⟩
    exact ⟨d, by omega⟩
  have hbetaCurrent := a.beli2019Lemma69_i_typeII_targetLeftTail
    b D hfirst (i.val - 1) (by omega) hpreviousEven
  exact lemma79Central_outerEarly_first_odd_direct
    a b c D.outer hfirst D.no_gap_two hdefectBC hnorm i hearly hiOdd
      hbetaCurrent hprevious

/-- The second Lemma 2.18 alternative is impossible on the complete early
type-II interval. -/
theorem lemma79Central_typeIIEarly_second_not
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeII a b) (hfirst : D.outer.first = 0)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hearly : i.val ≤ D.outer.transition.lastZero + 1)
    (hiOdd : Odd i.val)
    (hcurrent :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        b.prefixAlphaCap i.val + b.centralCurrentDefect c i) : False := by
  by_cases hstrict : i.val < D.outer.transition.lastZero + 1
  · exact lemma79Central_outerEarly_odd_second_not_of_lt
      a b c D.outer hfirst D.no_gap_two i hiOdd hstrict hcurrent
  · have hboundary : i.val = D.outer.transition.lastZero + 1 := by
      omega
    exact lemma79Central_typeIIEarly_boundary_second_not
      a b c D hfirst i hboundary hcurrent

/-- Complete type-II witness family on the early interval. -/
theorem lemma79CentralWitness_typeIIEarly
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [DyadicDiscriminantClassLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeII a b) (hfirst : D.outer.first = 0)
    (hdefectBC : b.RepresentationDefectCondition c)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hearly : i.val ≤ D.outer.transition.lastZero + 1)
    (htrigger : b.centralAlphaTrigger c i) :
    Lemma79CentralWitness a b c i := by
  rcases Nat.even_or_odd i.val with hiEven | hiOdd
  · exact False.elim (lemma79Central_outerEarly_even_trigger_not
      a b c D.outer hfirst D.no_gap_two hnorm i hearly hiEven htrigger)
  · rcases b.beli2019Lemma218_target c hdefectBC i htrigger with
      hprevious | hcurrent
    · exact lemma79CentralWitness_typeIIEarly_firstAlternative
        a b c D hfirst hdefectBC hnorm i hearly hiOdd hprevious
    · exact False.elim (lemma79Central_typeIIEarly_second_not
        a b c D hfirst hnorm i hearly hiOdd hcurrent)

end BONG.GoodBONG

end Bong
