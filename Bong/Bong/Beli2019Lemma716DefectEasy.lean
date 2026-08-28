/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma716Nonessential

/-!
# Beli (2019), Lemma 7.16(ii): nonpositive half-gap cases

Several finite boundary cases in the paper end with `B_i ≤ 0`.  Since every
capped quadratic defect is nonnegative, all such cases share one short
formal proof.  The second theorem translates the displayed integral order
inequality into the required nonpositive half-gap estimate.
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

/-- A nonpositive half-gap candidate makes condition 2.1(ii) automatic. -/
theorem representationDefectAt_of_halfGap_le_zero
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (i : RepresentationIndex (n + 1) (n + 1))
    (hhalf : a.representationHalfGap b i ≤ 0) :
    a.RepresentationDefectAt b i := by
  unfold RepresentationDefectAt
  calc
    a.representationAlpha b i ≤ a.representationHalfGap b i :=
      a.representationAlpha_le_halfGap b i
    _ ≤ 0 := hhalf
    _ ≤ a.truncatedPrefixDefect b 1 i.val i.val :=
      a.truncatedPrefixDefect_nonneg b 1 i.val i.val

/-- If the comparison order preceding the boundary is at least `2e` above
the current source order, then the half-gap candidate is nonpositive. -/
theorem representationHalfGap_le_zero_of_add_twoE_le
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (i : RepresentationIndex (n + 1) (n + 1))
    (horder : a.order ⟨i.val, i.lt_large⟩ +
        2 * (ramificationIndex K : Int) ≤
      b.order ⟨i.val - 1,
        (Nat.sub_le i.val 1).trans_lt i.lt_large⟩) :
    a.representationHalfGap b i ≤ 0 := by
  unfold representationHalfGap
  apply WithTop.coe_le_coe.mpr
  have hq :
      ((a.order ⟨i.val, i.lt_large⟩ : ℚ) +
          2 * (ramificationIndex K : ℚ)) ≤
        (b.order ⟨i.val - 1,
          (Nat.sub_le i.val 1).trans_lt i.lt_large⟩ : ℚ) := by
    exact_mod_cast horder
  push_cast at hq ⊢
  linarith

/-- Order-only form of the recurring `B_i ≤ 0` argument. -/
theorem representationDefectAt_of_add_twoE_le
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (i : RepresentationIndex (n + 1) (n + 1))
    (horder : a.order ⟨i.val, i.lt_large⟩ +
        2 * (ramificationIndex K : Int) ≤
      b.order ⟨i.val - 1,
        (Nat.sub_le i.val 1).trans_lt i.lt_large⟩) :
    a.RepresentationDefectAt b i :=
  a.representationDefectAt_of_halfGap_le_zero b i
    (a.representationHalfGap_le_zero_of_add_twoE_le b i horder)

/-- The first ordinary boundary in Lemma 7.16 is automatic whenever the
constructed second order is `R - 2e + 1` and the comparison norm forces its
first order to be at least `R + 1`. -/
theorem lemma716_first_representationDefectAt
    (b : GoodBONG q L (n + 3)) (c : GoodBONG q M (n + 3))
    (R : Int)
    (hsecond : b.order (1 : Fin (n + 3)) =
      R - 2 * (ramificationIndex K : Int) + 1)
    (hcomparison : R + 1 ≤ c.order (0 : Fin (n + 3))) :
    b.RepresentationDefectAt c
      { val := 1
        pos := by omega
        lt_large := by omega
        le_small := by omega } := by
  let i : RepresentationIndex (n + 3) (n + 3) :=
    { val := 1
      pos := by omega
      lt_large := by omega
      le_small := by omega }
  apply b.representationDefectAt_of_add_twoE_le c i
  change b.order (1 : Fin (n + 3)) +
      2 * (ramificationIndex K : Int) ≤ c.order (0 : Fin (n + 3))
  rw [hsecond]
  omega

/-- The `i = 1` calculation in the type-I branch when `s > 2`. -/
theorem lemma716_typeI_first_representationDefectAt_of_gt_two
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData a R s)
    (hfirst : a.order 0 = R)
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (hvalues : ∀ j, b.valueUnit j =
      lemma714TypeITargetValues a s D.two_le D.le_rank j)
    (hs : 2 < s) :
    b.RepresentationDefectAt c
      { val := 1
        pos := by omega
        lt_large := by omega
        le_small := by omega } := by
  have hodd : Odd (1 : Nat) := ⟨0, by omega⟩
  have hprefix : (1 : Nat) < s - 2 := by
    rcases D.even with ⟨d, hd⟩
    omega
  have hsecond := a.lemma716_typeI_prefix_order_eq_low b R s D hthird
    hvalues (1 : Fin (n + 3)) hprefix hodd
  have hcomparison := a.lemma716_comparison_order_zero_ge c R hfirst hnorm
  exact b.lemma716_first_representationDefectAt c R hsecond hcomparison

variable [DyadicDiscriminantClassLaws K]

/-- The same `i = 1` calculation in the type-II branch when `s > 2`. -/
theorem lemma716_typeII_first_representationDefectAt_of_gt_two
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData a R s)
    (hfirst : a.order 0 = R)
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (hII : Lemma714IsTypeII a R s) (epsilon eta : Kˣ)
    (hvalues : ∀ j, b.valueUnit j =
      lemma714TypeIITargetValues a s D.two_le
        (Classical.choose hII) epsilon eta j)
    (hs : 2 < s) :
    b.RepresentationDefectAt c
      { val := 1
        pos := by omega
        lt_large := by omega
        le_small := by omega } := by
  have hodd : Odd (1 : Nat) := ⟨0, by omega⟩
  have hprefix : (1 : Nat) < s - 2 := by
    rcases D.even with ⟨d, hd⟩
    omega
  have hsecond := a.lemma716_typeII_prefix_order_eq_low b R s D hthird
    hII epsilon eta hvalues (1 : Fin (n + 3)) hprefix hodd
  have hcomparison := a.lemma716_comparison_order_zero_ge c R hfirst hnorm
  exact b.lemma716_first_representationDefectAt c R hsecond hcomparison

/-- The last elementary type-I point `i = s - 3` also has nonpositive
half-gap. -/
theorem lemma716_typeI_sMinusThree_representationDefectAt
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData a R s)
    (hfirst : a.order 0 = R)
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (hvalues : ∀ j, b.valueUnit j =
      lemma714TypeITargetValues a s D.two_le D.le_rank j)
    (hsFour : 4 ≤ s) :
    b.RepresentationDefectAt c
      { val := s - 3
        pos := by omega
        lt_large := by have := D.le_rank; omega
        le_small := by have := D.le_rank; omega } := by
  let i : RepresentationIndex (n + 3) (n + 3) :=
    { val := s - 3
      pos := by omega
      lt_large := by have := D.le_rank; omega
      le_small := by have := D.le_rank; omega }
  let previous : Fin (n + 3) := ⟨s - 4, by
    have := D.le_rank
    omega⟩
  let current : Fin (n + 3) := ⟨s - 3, by
    have := D.le_rank
    omega⟩
  rcases D.even with ⟨d, hd⟩
  have hcurrentOdd : Odd current.val := by
    change Odd (s - 3)
    exact ⟨d - 2, by omega⟩
  have hpreviousEven : Even previous.val := by
    change Even (s - 4)
    exact ⟨d - 2, by omega⟩
  have hsource := a.lemma716_typeI_prefix_order_eq_low b R s D hthird
    hvalues current (by change s - 3 < s - 2; omega) hcurrentOdd
  have htarget := a.lemma716_comparison_even_order_ge c R hfirst hnorm
    previous hpreviousEven
  apply b.representationDefectAt_of_add_twoE_le c i
  change b.order current + 2 * (ramificationIndex K : Int) ≤
    c.order previous
  rw [hsource]
  convert htarget using 1 <;> ring

end BONG.GoodBONG

end Bong
