/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma716CentralTail

/-!
# Beli (2019), Lemma 7.16(iii'): the type-I boundary `i = s`

At this boundary the length-`s` source prefixes are isometric, but their
caps use the preceding alpha values, which need not be equal.  The original
preceding coefficient has strictly smaller order than its replacement,
while the following coefficient is unchanged.  Lemma 2.7 therefore makes
the original alpha strictly larger.  This is exactly the capped-defect
comparison used in the printed proof of condition 2.1(iii).
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
variable [DyadicDiscriminantClassLaws K]

/-- At the type-I boundary, the alpha cap of the constructed prefix is no
larger than the cap of the original prefix. -/
theorem lemma716_typeI_boundary_prefixAlphaCap_le
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (R : Int) (s : Nat) (D : Lemma714StoppingData a R s)
    (hsecond : a.order 1 =
      R - 2 * (ramificationIndex K : Int))
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (hI : Lemma714IsTypeI a R s)
    (hvalues : ∀ j, b.valueUnit j =
      lemma714TypeITargetValues a s D.two_le D.le_rank j)
    (horders : ∀ j, s ≤ j.val → a.order j = b.order j)
    (hsInterior : s < n + 3) :
    b.prefixAlphaCap s ≤ a.prefixAlphaCap s := by
  let boundary : Fin (n + 2) := ⟨s - 1, by omega⟩
  let previous : Fin (n + 3) := ⟨s - 1, by omega⟩
  let next : Fin (n + 3) := ⟨s, hsInterior⟩
  have hpreviousTarget : b.order previous =
      R - 2 * (ramificationIndex K : Int) + 2 := by
    simpa only [previous] using
      a.lemma716_typeI_rightBoundary_order_eq b R s D hsecond hvalues
  have hpreviousLt : a.order previous < b.order previous := by
    by_cases hsTwo : s = 2
    · have hsource : a.order previous =
          R - 2 * (ramificationIndex K : Int) := by
        have hindex : previous = (1 : Fin (n + 3)) := by
          apply Fin.ext
          simp only [previous, Fin.val_mk, Fin.val_one]
          omega
        rw [hindex, hsecond]
      rw [hsource, hpreviousTarget]
      omega
    · have hsFour : 4 ≤ s := by
        rcases D.even with ⟨d, hd⟩
        have := D.two_le
        omega
      have P := a.beli2019Lemma714_i R s D.toLemma714MinimalityData
        hsFour hthird
      have hodd : Odd (s - 1) := by
        rcases D.even with ⟨d, hd⟩
        exact ⟨d - 1, by omega⟩
      have hsource : a.order previous =
          R - 2 * (ramificationIndex K : Int) + 1 := by
        simpa only [previous] using
          P.low_positions (s - 1) (by omega) (by omega) hodd
      rw [hsource, hpreviousTarget]
      omega
  have hnext : a.order next = b.order next := by
    exact horders next (by
      change s ≤ s
      exact le_rfl)
  have hcast : boundary.castSucc = previous := by
    apply Fin.ext
    rfl
  have hsucc : boundary.succ = next := by
    apply Fin.ext
    simp only [boundary, next, Fin.val_succ]
    have hsTwo := D.two_le
    omega
  have hgapLt : b.orderGap boundary < a.orderGap boundary := by
    unfold orderGap
    rw [hcast, hsucc, hnext]
    omega
  have htargetGap : 2 * (ramificationIndex K : Int) ≤
      b.orderGap boundary := by
    have hnextLower : R + 2 ≤ b.order next := by
      rw [← hnext]
      exact a.lemma714_typeI_nextOrder_ge R s hI hsInterior
    unfold orderGap
    rw [hcast, hsucc, hpreviousTarget]
    omega
  have hsourceGap : 2 * (ramificationIndex K : Int) ≤
      a.orderGap boundary := by omega
  have halphaLt : b.alphaValue boundary < a.alphaValue boundary := by
    rw [b.beli2009Lemma27_ii boundary htargetGap,
      a.beli2009Lemma27_ii boundary hsourceGap]
    unfold halfGapValue
    have hgapQ : (b.orderGap boundary : ℚ) <
        (a.orderGap boundary : ℚ) := by
      exact_mod_cast hgapLt
    linarith
  have hsPos : 0 < s := lt_of_lt_of_le (by omega) D.two_le
  rw [b.prefixAlphaCap_of_internal hsPos hsInterior,
    a.prefixAlphaCap_of_internal hsPos hsInterior]
  exact_mod_cast halphaLt.le

/-- The mixed capped defect occurring at `i = s` for the original BONG is
at least the corresponding defect for the constructed BONG. -/
theorem lemma716_typeI_s_previousDefect_le
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData a R s)
    (hsecond : a.order 1 =
      R - 2 * (ramificationIndex K : Int))
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (hI : Lemma714IsTypeI a R s)
    (hvalues : ∀ j, b.valueUnit j =
      lemma714TypeITargetValues a s D.two_le D.le_rank j)
    (horders : ∀ j, s ≤ j.val → a.order j = b.order j)
    (hprefix : ∀ (k : Nat), s ≤ k → (hk : k ≤ n + 3) →
      (a.prefixDiagonalSpace k hk).IsIsometric
        (b.prefixDiagonalSpace k hk))
    (hsInterior : s < n + 3) :
    b.truncatedPrefixDefect c (-1) s (s - 2) ≤
      a.truncatedPrefixDefect c (-1) s (s - 2) := by
  have hcap := a.lemma716_typeI_boundary_prefixAlphaCap_le b R s D
    hsecond hthird hI hvalues horders hsInterior
  have hraw := a.defectOrder_mixedPrefix_eq_of_prefix_isometric b c
    (-1) s (s - 2) D.le_rank (hprefix s le_rfl D.le_rank)
  unfold truncatedPrefixDefect
  rw [hraw]
  exact min_le_min le_rfl (min_le_min hcap le_rfl)

/-- Condition (iii') at the type-I boundary with paper index `s`. -/
theorem lemma716_typeI_s_centralRepresentationAt
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData a R s)
    (hsecond : a.order 1 =
      R - 2 * (ramificationIndex K : Int))
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (hac : RepresentationConditionsPrime a c le_rfl)
    (hI : Lemma714IsTypeI a R s)
    (hvalues : ∀ j, b.valueUnit j =
      lemma714TypeITargetValues a s D.two_le D.le_rank j)
    (horders : ∀ j, s ≤ j.val → a.order j = b.order j)
    (halphas : ∀ j, s ≤ j.val → a.alphaValue j = b.alphaValue j)
    (hprefix : ∀ (k : Nat), s ≤ k → (hk : k ≤ n + 3) →
      (a.prefixDiagonalSpace k hk).IsIsometric
        (b.prefixDiagonalSpace k hk))
    (hsInterior : s < n + 3)
    (htrigger : b.centralDefectTrigger c
      { val := s
        one_lt := by have := D.two_le; omega
        lt_large := hsInterior
        le_small_succ := by omega }) :
    DiagonalRepresents
      (c.prefixValues (s - 1) (by omega))
      (b.prefixValues s D.le_rank) := by
  let i : CentralRepresentationIndex (n + 3) (n + 3) :=
    { val := s
      one_lt := by have := D.two_le; omega
      lt_large := hsInterior
      le_small_succ := by omega }
  have hprevious : b.centralPreviousDefect c i ≤
      a.centralPreviousDefect c i := by
    unfold centralPreviousDefect
    simpa only [i] using
      a.lemma716_typeI_s_previousDefect_le b c R s D hsecond hthird hI
        hvalues horders hprefix hsInterior
  have hcurrent : b.centralCurrentDefect c i =
      a.centralCurrentDefect c i := by
    unfold centralCurrentDefect
    symm
    exact a.lemma716_tail_truncatedPrefixDefect_eq b c s halphas
      (fun k hsk hk ↦ hprefix k (by omega) hk)
      (-1) (s + 1) (s - 1) (by omega) hsInterior
  have horder : a.order ⟨s, hsInterior⟩ = b.order ⟨s, hsInterior⟩ :=
    horders ⟨s, hsInterior⟩ le_rfl
  have hsourceTrigger : a.centralDefectTrigger c i := by
    unfold centralDefectTrigger at htrigger ⊢
    dsimp only [i] at htrigger ⊢
    constructor
    · rw [horder]
      exact htrigger.1
    · rw [horder]
      exact htrigger.2.trans_le
        (add_le_add hprevious (le_of_eq hcurrent))
  have hsource := hac.centralRepresentations i hsourceTrigger
  have htransport := diagonalRepresents_prefixValues_of_prefix_isometric
    a b s D.le_rank (hprefix s le_rfl D.le_rank)
  simpa only [i] using hsource.trans htransport

end BONG.GoodBONG

end Bong
