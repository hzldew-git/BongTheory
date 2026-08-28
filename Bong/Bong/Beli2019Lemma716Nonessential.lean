/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma716TailDefect
import Bong.Bong.Beli2019Lemma213Nonessential

/-!
# Beli (2019), Lemma 7.16: nonessential interior boundaries

Before checking conditions 2.1(ii) and 2.1(iii), the paper removes most of
the alternating prefix by showing that its boundaries are not essential.
This module formalizes that reduction.  Lemma 2.13 then makes condition
2.1(ii) automatic whenever the two essential endpoints adjacent to an
ordinary representation index both lie in the removed range.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- A reversed first order crossing already rules out essentiality. -/
theorem not_isEssentialFor_of_next_le_previous
    (b : GoodBONG q M (n + 3)) (c : GoodBONG q N (n + 3))
    (i : Fin (n + 3)) (hiPos : 0 < i.val)
    (hiNext : i.val + 1 < n + 3)
    (hcross : b.order ⟨i.val + 1, hiNext⟩ ≤
      c.order ⟨i.val - 1, by omega⟩) :
    ¬b.IsEssentialFor c i := by
  intro hessential
  have hstrict := hessential.1 hiPos hiNext
  simp only [orderSequence_at] at hstrict
  exact (not_lt_of_ge hcross) hstrict

variable [Beli2006AlphaLaws.{u, v} K]

/-- Every paper index `1 < i ≤ s - 3` is nonessential in the type-I
branch.  In zero-based essential coordinates this is the range displayed
below. -/
theorem lemma716_typeI_not_essential
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData a R s)
    (hfirst : a.order 0 = R)
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (hvalues : ∀ j, b.valueUnit j =
      lemma714TypeITargetValues a s D.two_le D.le_rank j)
    (i : Fin (n + 3)) (hiPos : 0 < i.val)
    (hiRange : i.val + 1 ≤ s - 3) :
    ¬b.IsEssentialFor c i := by
  have hiNext : i.val + 1 < n + 3 := by
    have := D.le_rank
    omega
  apply b.not_isEssentialFor_of_next_le_previous c i hiPos hiNext
  let previous : Fin (n + 3) := ⟨i.val - 1, by omega⟩
  let next : Fin (n + 3) := ⟨i.val + 1, hiNext⟩
  change b.order next ≤ c.order previous
  have hnextPrefix : next.val < s - 2 := by
    change i.val + 1 < s - 2
    omega
  rcases Nat.even_or_odd i.val with hiEven | hiOdd
  · rcases hiEven with ⟨d, hd⟩
    have hpreviousOdd : Odd previous.val := by
      change Odd (i.val - 1)
      refine ⟨d - 1, ?_⟩
      omega
    have hnextOdd : Odd next.val := by
      change Odd (i.val + 1)
      exact Even.add_one ⟨d, hd⟩
    have hcomparison := a.lemma716_comparison_odd_order_ge c R hfirst
      hnorm previous hpreviousOdd
    have htarget := a.lemma716_typeI_prefix_order_eq_low b R s D hthird
      hvalues next hnextPrefix hnextOdd
    rw [htarget]
    exact hcomparison
  · rcases hiOdd with ⟨d, hd⟩
    have hpreviousEven : Even previous.val := by
      change Even (i.val - 1)
      refine ⟨d, ?_⟩
      omega
    have hnextEven : Even next.val := by
      change Even (i.val + 1)
      exact Odd.add_one ⟨d, hd⟩
    have hcomparison := a.lemma716_comparison_even_order_ge c R hfirst
      hnorm previous hpreviousEven
    have htarget := a.lemma716_typeI_prefix_order_eq_high b R s D hthird
      hvalues next hnextPrefix hnextEven
    rw [htarget]
    exact hcomparison

/-- Lemma 2.13 removes all type-I condition 2.1(ii) boundaries in the
paper's range `1 < i ≤ s - 4`. -/
theorem lemma716_typeI_representationDefectAt_of_interior
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData a R s)
    (hfirst : a.order 0 = R)
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (hvalues : ∀ j, b.valueUnit j =
      lemma714TypeITargetValues a s D.two_le D.le_rank j)
    (i : RepresentationIndex (n + 3) (n + 3))
    (hiTwo : 1 < i.val) (hiRange : i.val ≤ s - 4) :
    b.RepresentationDefectAt c i := by
  apply b.representationDefectAt_of_not_essential c i
  · apply a.lemma716_typeI_not_essential b c R s D hfirst hthird hnorm
      hvalues (currentEssentialIndex i) (by
        simp only [currentEssentialIndex]
        omega)
    simp only [currentEssentialIndex]
    omega
  · apply a.lemma716_typeI_not_essential b c R s D hfirst hthird hnorm
      hvalues (nextEssentialIndex i) (by
        simp only [nextEssentialIndex]
        omega)
    simp only [nextEssentialIndex]
    omega

variable [DyadicDiscriminantClassLaws K]

/-- Every paper index `1 < i ≤ s - 2` is nonessential in the type-II
branch.  The last even coefficient is handled by the explicit left-boundary
order formula; all earlier coefficients use the shifted plateau. -/
theorem lemma716_typeII_not_essential
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData a R s)
    (hfirst : a.order 0 = R)
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (hII : Lemma714IsTypeII a R s) (epsilon eta : Kˣ)
    (hepsilonUnit : IsValuationUnit K (epsilon : K))
    (hetaUnit : IsValuationUnit K (eta : K))
    (hvalues : ∀ j, b.valueUnit j =
      lemma714TypeIITargetValues a s D.two_le
        (Classical.choose hII) epsilon eta j)
    (i : Fin (n + 3)) (hiPos : 0 < i.val)
    (hiRange : i.val + 1 ≤ s - 2) :
    ¬b.IsEssentialFor c i := by
  have hiNext : i.val + 1 < n + 3 := by
    have := D.le_rank
    omega
  apply b.not_isEssentialFor_of_next_le_previous c i hiPos hiNext
  let previous : Fin (n + 3) := ⟨i.val - 1, by omega⟩
  let next : Fin (n + 3) := ⟨i.val + 1, hiNext⟩
  change b.order next ≤ c.order previous
  rcases Nat.even_or_odd i.val with hiEven | hiOdd
  · rcases hiEven with ⟨d, hd⟩
    have hpreviousOdd : Odd previous.val := by
      change Odd (i.val - 1)
      refine ⟨d - 1, ?_⟩
      omega
    have hnextOdd : Odd next.val := by
      change Odd (i.val + 1)
      exact Even.add_one ⟨d, hd⟩
    have hnextPrefix : next.val < s - 2 := by
      rcases D.even with ⟨t, ht⟩
      change i.val + 1 < s - 2
      omega
    have hcomparison := a.lemma716_comparison_odd_order_ge c R hfirst
      hnorm previous hpreviousOdd
    have htarget := a.lemma716_typeII_prefix_order_eq_low b R s D hthird
      hII epsilon eta hvalues next hnextPrefix hnextOdd
    rw [htarget]
    exact hcomparison
  · rcases hiOdd with ⟨d, hd⟩
    have hpreviousEven : Even previous.val := by
      change Even (i.val - 1)
      refine ⟨d, ?_⟩
      omega
    have hnextEven : Even next.val := by
      change Even (i.val + 1)
      exact Odd.add_one ⟨d, hd⟩
    have hcomparison := a.lemma716_comparison_even_order_ge c R hfirst
      hnorm previous hpreviousEven
    by_cases hboundary : next.val = s - 2
    · have htarget : b.order next = R + 1 := by
        have h := a.lemma716_typeII_leftBoundary_order_eq b R s D hII
          epsilon eta hepsilonUnit hetaUnit hvalues
        have hindex : next = ⟨s - 2, by
            have := D.le_rank
            omega⟩ := Fin.ext hboundary
        simpa only [hindex] using h
      rw [htarget]
      exact hcomparison
    · have hnextPrefix : next.val < s - 2 := by
        have hboundary' : i.val + 1 ≠ s - 2 := by
          intro heq
          apply hboundary
          change i.val + 1 = s - 2
          exact heq
        change i.val + 1 < s - 2
        omega
      have htarget := a.lemma716_typeII_prefix_order_eq_high b R s D hthird
        hII epsilon eta hvalues next hnextPrefix hnextEven
      rw [htarget]
      exact hcomparison

/-- Lemma 2.13 removes all type-II condition 2.1(ii) boundaries in the
paper's range `1 < i ≤ s - 3`. -/
theorem lemma716_typeII_representationDefectAt_of_interior
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData a R s)
    (hfirst : a.order 0 = R)
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (hII : Lemma714IsTypeII a R s) (epsilon eta : Kˣ)
    (hepsilonUnit : IsValuationUnit K (epsilon : K))
    (hetaUnit : IsValuationUnit K (eta : K))
    (hvalues : ∀ j, b.valueUnit j =
      lemma714TypeIITargetValues a s D.two_le
        (Classical.choose hII) epsilon eta j)
    (i : RepresentationIndex (n + 3) (n + 3))
    (hiTwo : 1 < i.val) (hiRange : i.val ≤ s - 3) :
    b.RepresentationDefectAt c i := by
  apply b.representationDefectAt_of_not_essential c i
  · apply a.lemma716_typeII_not_essential b c R s D hfirst hthird hnorm
      hII epsilon eta hepsilonUnit hetaUnit hvalues
      (currentEssentialIndex i) (by
        simp only [currentEssentialIndex]
        omega)
    simp only [currentEssentialIndex]
    omega
  · apply a.lemma716_typeII_not_essential b c R s D hfirst hthird hnorm
      hII epsilon eta hepsilonUnit hetaUnit hvalues
      (nextEssentialIndex i) (by
        simp only [nextEssentialIndex]
        omega)
    simp only [nextEssentialIndex]
    omega

end BONG.GoodBONG

end Bong
