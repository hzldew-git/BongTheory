/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma716TypeIISMinusOneCentral

/-!
# Beli (2019), Lemma 7.16: condition (iii')

This file assembles the revised central representation condition.  In type I
the only exceptional paper indices are `s - 2`, `s - 1`, and `s`; in type II
only `s - 1` is exceptional.  Lemma 2.13 makes every earlier trigger
impossible, while Lemma 7.15 transports every index at least `s + 1`.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

variable [Beli2006AlphaLaws.{u, v} K]
variable [Beli2009AlphaParityLaws.{u, v} K]
variable [laws : DyadicDiscriminantClassLaws K]
variable [DyadicAlternatingEndpointTowerRepresentationLaws K]

private theorem centralRepresentationIndex_eq_of_val_eq
    {m n : Nat} {i j : CentralRepresentationIndex m n}
    (h : i.val = j.val) : i = j := by
  cases i
  cases j
  simp_all

/-- Under conditions (i) and (ii), Lemmas 2.16 and 2.13 rule out a revised
central trigger at a nonessential boundary. -/
theorem centralDefectTrigger_false_of_not_essential
    (b : GoodBONG q M (n + 3)) (c : GoodBONG q N (n + 3))
    (horder : b.RepresentationOrderCondition c le_rfl)
    (hdefect : b.RepresentationDefectCondition c)
    (i : CentralRepresentationIndex (n + 3) (n + 3))
    (hnot : ¬ b.IsEssentialFor c ⟨i.val - 1, by
      have := i.lt_large
      omega⟩) :
    ¬ b.centralDefectTrigger c i := by
  intro htrigger
  have halpha : b.centralAlphaTrigger c i :=
    ((b.beli2019Lemma216 c le_rfl horder hdefect) i).mpr htrigger
  exact hnot (b.isEssentialFor_of_centralAlphaTrigger c i halpha)

/-- In type II the paper index `s` is nonessential: the next constructed
coefficient and the preceding comparison coefficient are both bounded by
the scale `R + 1` in the required direction. -/
theorem lemma716_typeII_s_not_essential
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData a R s)
    (hfirst : a.order 0 = R)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (hII : Lemma714IsTypeII a R s) (epsilon eta : Kˣ)
    (hepsilonUnit : IsValuationUnit K (epsilon : K))
    (hetaUnit : IsValuationUnit K (eta : K))
    (hvalues : ∀ j, b.valueUnit j =
      lemma714TypeIITargetValues a s D.two_le
        (Classical.choose hII) epsilon eta j) :
    ¬ b.IsEssentialFor c ⟨s - 1, by
      have := Classical.choose hII
      omega⟩ := by
  let boundary : Fin (n + 3) := ⟨s - 1, by
    have := Classical.choose hII
    omega⟩
  have hboundary : 0 < boundary.val := by
    dsimp only [boundary]
    have := D.two_le
    omega
  have hnext : boundary.val + 1 < n + 3 := by
    dsimp only [boundary]
    have := Classical.choose hII
    omega
  apply b.not_isEssentialFor_of_next_le_previous c boundary hboundary hnext
  let previous : Fin (n + 3) := ⟨boundary.val - 1, by omega⟩
  let next : Fin (n + 3) := ⟨boundary.val + 1, hnext⟩
  change b.order next ≤ c.order previous
  have hnextOrder : b.order next = R + 1 := by
    have hindex : next = ⟨s, Classical.choose hII⟩ := by
      apply Fin.ext
      change (s - 1) + 1 = s
      have := D.two_le
      omega
    rw [hindex]
    exact a.lemma716_typeII_tailBoundary_order_eq b R s D hII epsilon eta
      hepsilonUnit hetaUnit hvalues
  have hpreviousEven : Even previous.val := by
    rcases D.even with ⟨d, hd⟩
    exact ⟨d - 1, by dsimp only [previous, boundary]; omega⟩
  have hpreviousLower : R + 1 ≤ c.order previous :=
    a.lemma716_comparison_even_order_ge c R hfirst hnorm previous
      hpreviousEven
  rw [hnextOrder]
  exact hpreviousLower

/-- Complete revised condition (iii') in the type-I branch. -/
theorem lemma716_typeI_centralRepresentationConditionsPrime
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData a R s)
    (hfirst : a.order 0 = R)
    (hsecond : a.order 1 =
      R - 2 * (ramificationIndex K : Int))
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (hac : RepresentationConditionsPrime a c le_rfl)
    (hI : Lemma714IsTypeI a R s)
    (hdiscriminant : a.toBONG.adjacentUnitSquareClass
      (0 : Fin (n + 3)) (by simp) = unitSquareClass K
        (lemma712DiscriminantParameter (K := K)))
    (hvalues : ∀ j, b.valueUnit j =
      lemma714TypeITargetValues a s D.two_le D.le_rank j)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hdefectBC : b.RepresentationDefectCondition c)
    (horders : ∀ j, s ≤ j.val → a.order j = b.order j)
    (halphas : ∀ j, s ≤ j.val → a.alphaValue j = b.alphaValue j)
    (hprefix : ∀ (k : Nat), s ≤ k → (hk : k ≤ n + 3) →
      (a.prefixDiagonalSpace k hk).IsIsometric
        (b.prefixDiagonalSpace k hk)) :
    b.CentralRepresentationConditionsPrime c := by
  intro i htrigger
  by_cases hsTwo : s = 2
  · by_cases hiS : i.val = s
    · have hsInterior : s < n + 3 := by
        rw [← hiS]
        exact i.lt_large
      let j : CentralRepresentationIndex (n + 3) (n + 3) :=
        { val := s
          one_lt := by omega
          lt_large := hsInterior
          le_small_succ := by omega }
      have hij : i = j := centralRepresentationIndex_eq_of_val_eq hiS
      rw [hij] at htrigger ⊢
      simpa only [j] using
        a.lemma716_typeI_s_centralRepresentationAt b c R s D hsecond hthird
          hac hI hvalues horders halphas hprefix hsInterior htrigger
    · have htail : s + 1 ≤ i.val := by
        have := i.one_lt
        omega
      exact a.lemma716_tail_centralRepresentationAt b c s hac horders halphas
        (fun k hsk hk ↦ hprefix k (by omega) hk) i htail htrigger
  · have hsFour : 4 ≤ s := by
      rcases D.even with ⟨d, hd⟩
      have := D.two_le
      omega
    by_cases hiEarly : i.val ≤ s - 3
    · let boundary : Fin (n + 3) := ⟨i.val - 1, by
          have := i.lt_large
          omega⟩
      have hnot := a.lemma716_typeI_not_essential b c R s D hfirst hthird
        hnorm hvalues boundary (by
          dsimp only [boundary]
          have := i.one_lt
          omega) (by
          dsimp only [boundary]
          omega)
      exact (b.centralDefectTrigger_false_of_not_essential c horderBC
        hdefectBC i (by simpa only [boundary] using hnot) htrigger).elim
    · by_cases hiMinusTwo : i.val = s - 2
      · let j : CentralRepresentationIndex (n + 3) (n + 3) :=
          { val := s - 2
            one_lt := by omega
            lt_large := by have := D.le_rank; omega
            le_small_succ := by have := D.le_rank; omega }
        have hij : i = j := centralRepresentationIndex_eq_of_val_eq hiMinusTwo
        rw [hij] at htrigger ⊢
        have hrep :=
          a.lemma716_typeI_sMinusTwo_centralRepresentationAt b c R s D
            hfirst hsecond hthird hnorm hvalues horderBC hdefectBC hsFour
              htrigger
        exact prefixRepresents_cast c b (by
          dsimp only [j]
          omega) rfl hrep
      · by_cases hiMinusOne : i.val = s - 1
        · let j : CentralRepresentationIndex (n + 3) (n + 3) :=
            { val := s - 1
              one_lt := by omega
              lt_large := by have := D.le_rank; omega
              le_small_succ := by have := D.le_rank; omega }
          have hij : i = j := centralRepresentationIndex_eq_of_val_eq hiMinusOne
          rw [hij] at htrigger ⊢
          have hrep :=
            a.lemma716_typeI_sMinusOne_centralRepresentationAt b c R s D
              hfirst hsecond hthird hnorm hac hI hdiscriminant hvalues hsFour
                htrigger
          exact prefixRepresents_cast c b (by
            dsimp only [j]
            omega) rfl hrep
        · by_cases hiS : i.val = s
          · have hsInterior : s < n + 3 := by
              rw [← hiS]
              exact i.lt_large
            let j : CentralRepresentationIndex (n + 3) (n + 3) :=
              { val := s
                one_lt := by omega
                lt_large := hsInterior
                le_small_succ := by omega }
            have hij : i = j := centralRepresentationIndex_eq_of_val_eq hiS
            rw [hij] at htrigger ⊢
            simpa only [j] using
              a.lemma716_typeI_s_centralRepresentationAt b c R s D hsecond
                hthird hac hI hvalues horders halphas hprefix hsInterior
                  htrigger
          · have htail : s + 1 ≤ i.val := by omega
            exact a.lemma716_tail_centralRepresentationAt b c s hac horders
              halphas (fun k hsk hk ↦ hprefix k (by omega) hk) i htail
                htrigger

/-- Complete revised condition (iii') in the type-II branch. -/
theorem lemma716_typeII_centralRepresentationConditionsPrime
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData a R s)
    (hfirst : a.order 0 = R)
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (hac : RepresentationConditionsPrime a c le_rfl)
    (hII : Lemma714IsTypeII a R s) (epsilon eta : Kˣ)
    (hepsilonUnit : IsValuationUnit K (epsilon : K))
    (hetaUnit : IsValuationUnit K (eta : K))
    (hvalues : ∀ j, b.valueUnit j =
      lemma714TypeIITargetValues a s D.two_le
        (Classical.choose hII) epsilon eta j)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hdefectBC : b.RepresentationDefectCondition c)
    (horders : ∀ j, s ≤ j.val → a.order j = b.order j)
    (halphas : ∀ j, s ≤ j.val → a.alphaValue j = b.alphaValue j)
    (hprefix : ∀ (k : Nat), s + 1 ≤ k → (hk : k ≤ n + 3) →
      (a.prefixDiagonalSpace k hk).IsIsometric
        (b.prefixDiagonalSpace k hk)) :
    b.CentralRepresentationConditionsPrime c := by
  intro i htrigger
  by_cases hiEarly : i.val ≤ s - 2
  · let boundary : Fin (n + 3) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
    have hnot := a.lemma716_typeII_not_essential b c R s D hfirst hthird
      hnorm hII epsilon eta hepsilonUnit hetaUnit hvalues boundary (by
        dsimp only [boundary]
        have := i.one_lt
        omega) (by
        dsimp only [boundary]
        have := i.one_lt
        omega)
    exact (b.centralDefectTrigger_false_of_not_essential c horderBC hdefectBC
      i (by simpa only [boundary] using hnot) htrigger).elim
  · by_cases hiMinusOne : i.val = s - 1
    · have hsFour : 4 ≤ s := by
        rcases D.even with ⟨d, hd⟩
        have := i.one_lt
        omega
      let j : CentralRepresentationIndex (n + 3) (n + 3) :=
        { val := s - 1
          one_lt := by omega
          lt_large := by have := D.le_rank; omega
          le_small_succ := by have := D.le_rank; omega }
      have hij : i = j := centralRepresentationIndex_eq_of_val_eq hiMinusOne
      rw [hij] at htrigger ⊢
      have hrep :=
        a.lemma716_typeII_sMinusOne_centralRepresentationAt b c R s D hfirst
          hthird hnorm hII epsilon eta hepsilonUnit hetaUnit hvalues horderBC
            hdefectBC hsFour htrigger
      exact prefixRepresents_cast c b (by
        dsimp only [j]
        omega) rfl hrep
    · by_cases hiS : i.val = s
      · let boundary : Fin (n + 3) := ⟨i.val - 1, by
            have := i.lt_large
            omega⟩
        have hnot := a.lemma716_typeII_s_not_essential b c R s D hfirst
          hnorm hII epsilon eta hepsilonUnit hetaUnit hvalues
        exact (b.centralDefectTrigger_false_of_not_essential c horderBC
          hdefectBC i (by
            have hindex : boundary = ⟨s - 1, by
                have := Classical.choose hII
                omega⟩ := by
              apply Fin.ext
              dsimp only [boundary]
              omega
            simpa only [boundary, hindex] using hnot) htrigger).elim
      · have htail : s + 1 ≤ i.val := by omega
        exact a.lemma716_tail_centralRepresentationAt b c s hac horders halphas
          hprefix i htail htrigger

end BONG.GoodBONG

end Bong
