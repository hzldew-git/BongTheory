/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79CentralTypeIIIEarlyBoundary

/-!
# Beli (2019), Lemma 7.9(iii): early type III

This file assembles cases 1 and 8 on the complete early type-III interval.
Even active indices are excluded by the common outer order profile.  At odd
indices the first Lemma 2.18 alternative gives the endpoint-tower
representation, while the second alternative is excluded either before or
at the transition boundary.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The first Lemma 2.18 alternative throughout the early type-III
interval. -/
theorem lemma79CentralWitness_typeIIIEarly_firstAlternative
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [DyadicDiscriminantClassLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
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
  have hbetaCurrent := a.beli2019Lemma69_i_typeIII_targetLeftTail_local
    b D hfirst horderAB hdefectAB htotal (i.val - 1) (by omega)
      hpreviousEven
  exact lemma79Central_outerEarly_first_odd_direct
    a b c D.outer hfirst D.no_gap_two hdefectBC hnorm i hearly hiOdd
      hbetaCurrent hprevious

/-- The second Lemma 2.18 alternative is impossible on the complete early
type-III interval. -/
theorem lemma79Central_typeIIIEarly_second_not
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hearly : i.val ≤ D.outer.transition.lastZero + 1)
    (hiOdd : Odd i.val)
    (htrigger : b.centralAlphaTrigger c i)
    (hcurrent :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        b.prefixAlphaCap i.val + b.centralCurrentDefect c i) : False := by
  by_cases hstrict : i.val < D.outer.transition.lastZero + 1
  · exact lemma79Central_outerEarly_odd_second_not_of_lt
      a b c D.outer hfirst D.no_gap_two i hiOdd hstrict hcurrent
  · have hboundary : i.val = D.outer.transition.lastZero + 1 := by
      omega
    exact a.lemma79Central_typeIIIEarly_boundary_second_not
      b c D hfirst horderAB hdefectAB htotal hinitial hnorm i hboundary
        htrigger hcurrent

/-- Complete type-III witness family on the early interval. -/
theorem lemma79CentralWitness_typeIIIEarly
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [DyadicDiscriminantClassLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeIII a b) (hfirst : D.outer.first = 0)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by
        have hbound := D.outer.transition.firstTwo_le_rank
        rw [D.adjacent] at hbound
        omega⟩)
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
    · exact lemma79CentralWitness_typeIIIEarly_firstAlternative
        a b c D hfirst horderAB hdefectAB htotal hdefectBC hnorm i
          hearly hiOdd hprevious
    · exact False.elim (lemma79Central_typeIIIEarly_second_not
        a b c D hfirst horderAB hdefectAB htotal hinitial hnorm i
          hearly hiOdd htrigger hcurrent)

end BONG.GoodBONG

end Bong
