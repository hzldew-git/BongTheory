/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma716DefectEasy
import Bong.Bong.Beli2019Lemma715AlphaCommon

/-!
# Beli (2019), Lemma 7.16(ii): alpha values at the exceptional block

The type-II ternary block has consecutive order gaps `2 - 2e` and
`2e - 2`.  Beli (2009/2010), Corollary 2.9(i), therefore computes its two
alpha values as `1` and `2e - 1`.  Recording these consequences explicitly
avoids repeating the same local calculation in the three boundary cases of
condition 2.1(ii).
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

variable [DyadicDiscriminantClassLaws K]
variable [Beli2006AlphaLaws.{u, v} K]
variable [Beli2009AlphaParityLaws.{u, v} K]

/-- The first alpha in the exceptional type-II ternary block is `1`. -/
theorem lemma716_typeII_leftBoundary_alphaValue_eq_one
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) (D : Lemma714StoppingData a R s)
    (hII : Lemma714IsTypeII a R s) (epsilon eta : Kˣ)
    (hεUnit : IsValuationUnit K (epsilon : K))
    (hηUnit : IsValuationUnit K (eta : K))
    (hvalues : ∀ j, b.valueUnit j =
      lemma714TypeIITargetValues a s D.two_le
        (Classical.choose hII) epsilon eta j) :
    b.alphaValue ⟨s - 2, by
      have := D.le_rank
      omega⟩ = 1 := by
  let i : Fin (n + 2) := ⟨s - 2, by
    have := D.le_rank
    omega⟩
  have hleft := a.lemma716_typeII_leftBoundary_order_eq b R s D hII
    epsilon eta hεUnit hηUnit hvalues
  have hright := a.lemma716_typeII_rightBoundary_order_eq b R s D hII
    epsilon eta hεUnit hηUnit hvalues
  have hgap' : b.order ⟨s - 1, by
        have := D.le_rank
        omega⟩ -
      b.order ⟨s - 2, by
        have := D.le_rank
        omega⟩ = 2 - 2 * (ramificationIndex K : Int) := by
    rw [hright, hleft]
    ring
  have hgap : b.orderGap i =
      2 - 2 * (ramificationIndex K : Int) := by
    unfold orderGap
    rw [show i.succ = (⟨s - 1, by
        have := D.le_rank
        omega⟩ : Fin (n + 3)) by
      apply Fin.ext
      simp only [i, Fin.val_succ, Fin.val_mk]
      have hsTwo := D.two_le
      omega]
    rw [show i.castSucc = (⟨s - 2, by
        have := D.le_rank
        omega⟩ : Fin (n + 3)) by
      apply Fin.ext
      rfl]
    exact hgap'
  have halpha := b.beli2009Corollary29_i i
    (Or.inr (Or.inr (Or.inl hgap)))
  rw [halpha]
  unfold halfGapValue
  rw [hgap]
  push_cast
  ring

/-- The second alpha in the exceptional type-II ternary block is
`2e - 1`. -/
theorem lemma716_typeII_rightBoundary_alphaValue_eq_twoE_sub_one
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) (D : Lemma714StoppingData a R s)
    (hII : Lemma714IsTypeII a R s) (epsilon eta : Kˣ)
    (hεUnit : IsValuationUnit K (epsilon : K))
    (hηUnit : IsValuationUnit K (eta : K))
    (hvalues : ∀ j, b.valueUnit j =
      lemma714TypeIITargetValues a s D.two_le
        (Classical.choose hII) epsilon eta j) :
    b.alphaValue ⟨s - 1, by
      have hs : s < n + 3 := Classical.choose hII
      omega⟩ =
      2 * (ramificationIndex K : ℚ) - 1 := by
  let i : Fin (n + 2) := ⟨s - 1, by
    have hs : s < n + 3 := Classical.choose hII
    omega⟩
  have hleft := a.lemma716_typeII_rightBoundary_order_eq b R s D hII
    epsilon eta hεUnit hηUnit hvalues
  have hright := a.lemma716_typeII_tailBoundary_order_eq b R s D hII
    epsilon eta hεUnit hηUnit hvalues
  have hgap' : b.order ⟨s, Classical.choose hII⟩ -
      b.order ⟨s - 1, by
        have := D.le_rank
        omega⟩ = 2 * (ramificationIndex K : Int) - 2 := by
    rw [hright, hleft]
    ring
  have hgap : b.orderGap i =
      2 * (ramificationIndex K : Int) - 2 := by
    unfold orderGap
    rw [show i.succ = (⟨s, Classical.choose hII⟩ : Fin (n + 3)) by
      apply Fin.ext
      simp only [i, Fin.val_succ, Fin.val_mk]
      have hsTwo := D.two_le
      omega]
    rw [show i.castSucc = (⟨s - 1, by
        have := D.le_rank
        omega⟩ : Fin (n + 3)) by
      apply Fin.ext
      rfl]
    exact hgap'
  have halpha := b.beli2009Corollary29_i i
    (Or.inr (Or.inr (Or.inr hgap)))
  rw [halpha]
  unfold halfGapValue
  rw [hgap]
  push_cast
  ring

/-- At the last type-I exceptional coefficient, the next unchanged source
coefficient creates a gap of at least `2e`; hence the boundary alpha is at
least `2e`. -/
theorem lemma716_typeI_rightBoundary_alphaValue_ge_twoE
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) (D : Lemma714StoppingData a R s)
    (hsecond : a.order 1 =
      R - 2 * (ramificationIndex K : Int))
    (hI : Lemma714IsTypeI a R s)
    (hvalues : ∀ j, b.valueUnit j =
      lemma714TypeITargetValues a s D.two_le D.le_rank j)
    (horders : ∀ j, s ≤ j.val → a.order j = b.order j)
    (hsInterior : s < n + 3) :
    2 * (ramificationIndex K : ℚ) ≤
      b.alphaValue ⟨s - 1, by omega⟩ := by
  let i : Fin (n + 2) := ⟨s - 1, by omega⟩
  have hprevious := a.lemma716_typeI_rightBoundary_order_eq b R s D
    hsecond hvalues
  have hnextSource := a.lemma714_typeI_nextOrder_ge R s hI hsInterior
  have hnext : R + 2 ≤ b.order ⟨s, hsInterior⟩ := by
    rw [← horders ⟨s, hsInterior⟩ le_rfl]
    exact hnextSource
  have hgap' : 2 * (ramificationIndex K : Int) ≤
      b.order ⟨s, hsInterior⟩ -
        b.order ⟨s - 1, by omega⟩ := by
    rw [hprevious]
    omega
  have hgap : 2 * (ramificationIndex K : Int) ≤ b.orderGap i := by
    unfold orderGap
    rw [show i.succ = (⟨s, hsInterior⟩ : Fin (n + 3)) by
      apply Fin.ext
      simp only [i, Fin.val_succ, Fin.val_mk]
      have hsTwo := D.two_le
      omega]
    rw [show i.castSucc = (⟨s - 1, by omega⟩ : Fin (n + 3)) by
      apply Fin.ext
      rfl]
    exact hgap'
  rw [b.beli2009Lemma27_ii i hgap]
  unfold halfGapValue
  have hgapQ : 2 * (ramificationIndex K : ℚ) ≤
      (b.orderGap i : ℚ) := by
    exact_mod_cast hgap
  linarith

end BONG.GoodBONG

end Bong
