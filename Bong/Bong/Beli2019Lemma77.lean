/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma76TypeI
import Bong.Bong.Beli2019OddPrefixDefect

/-!
# Beli (2019), Lemma 7.7: prefix-defect lower bounds

This file isolates the two numerical branches used in Lemma 7.7.  A
nonpositive required bound follows from nonnegativity of quadratic defect.
On a same-parity order plateau, Lemma 7.4(i) gives the stronger bound with
the preceding alpha invariant.  The canonical type-I profile supplies the
plateau equality through the right switch.
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}

/-- The defect `d[(-1)^(i/2) a_(1,i)]` used throughout Section 7. -/
noncomputable def alternatingPrefixDefect
    (b : GoodBONG q L n) (i : Nat) : WithTop ℚ :=
  defectOrder (K := K) ((-1) ^ (i / 2) * b.prefixProduct i)

/-- Removing the two endpoint caps can only increase the self-comparison
prefix defect. -/
theorem truncatedPrefixDefect_self_le_alternating
    (b : GoodBONG q L (n + 1)) (i : Nat) :
    b.truncatedPrefixDefect b ((-1) ^ (i / 2)) 0 i ≤
      b.alternatingPrefixDefect i := by
  have h := b.truncatedPrefixDefect_le_defect b
    ((-1) ^ (i / 2)) 0 i
  simpa only [alternatingPrefixDefect, prefixProduct,
    BONG.prefixProduct_zero, mul_one] using h

/-- The immediate branch of Lemma 7.7 when its integral lower bound is
nonpositive. -/
theorem beli2019Lemma77_of_nonpositive
    (b : GoodBONG q L (n + 2)) (i : Nat)
    (hiTwo : 2 ≤ i) (hiBound : i ≤ n + 2)
    (hnonpositive :
      b.order ⟨i - 2, by omega⟩ - b.order ⟨i - 1, by omega⟩ + 2 ≤ 0) :
    (((((b.order ⟨i - 2, by omega⟩ -
          b.order ⟨i - 1, by omega⟩ : Int) : ℚ) + 2 : ℚ)) :
        WithTop ℚ) ≤ b.alternatingPrefixDefect i := by
  have hbound :
      ((b.order ⟨i - 2, by omega⟩ -
          b.order ⟨i - 1, by omega⟩ : Int) : ℚ) + 2 ≤ 0 := by
    exact_mod_cast hnonpositive
  exact (WithTop.coe_le_coe.mpr hbound).trans
    (defectOrder_nonneg ((-1) ^ (i / 2) * b.prefixProduct i))

/-- The plateau branch of Lemma 7.7: Lemma 7.4(i), followed by removal of
the caps, replaces `alpha_(i-1) >= 2` by the required constant two. -/
theorem beli2019Lemma77_of_plateau
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q L (n + 2)) (i : Nat)
    (hiTwo : 2 ≤ i) (hiBound : i ≤ n + 2) (hiEven : Even i)
    (horder : b.order (0 : Fin (n + 2)) =
      b.order ⟨i - 2, by omega⟩)
    (halpha : 2 ≤ b.alphaValue ⟨i - 2, by omega⟩) :
    (((((b.order ⟨i - 2, by omega⟩ -
          b.order ⟨i - 1, by omega⟩ : Int) : ℚ) + 2 : ℚ)) :
        WithTop ℚ) ≤ b.alternatingPrefixDefect i := by
  let first : Fin (n + 1) := ⟨0, by omega⟩
  let last : Fin (n + 1) := ⟨i - 2, by omega⟩
  have hfirstLast : first ≤ last := by
    change 0 ≤ i - 2
    omega
  have hlastEven : Even (last.val - first.val) := by
    rcases hiEven with ⟨d, hd⟩
    exact ⟨d - 1, by
      simp only [first, last]
      omega⟩
  have horder' : b.order first.castSucc = b.order last.castSucc := by
    change b.order (0 : Fin (n + 2)) =
      b.order ⟨i - 2, by omega⟩
    exact horder
  have h74 := b.beli2019Lemma74_i first last hfirstLast hlastEven horder'
  have hlastCast :
      last.castSucc = (⟨i - 2, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have hlastSucc :
      last.succ = (⟨i - 1, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [last, Fin.val_succ]
    omega
  rw [hlastCast, hlastSucc] at h74
  have h74' :
      (((((b.order ⟨i - 2, by omega⟩ -
            b.order ⟨i - 1, by omega⟩ : Int) : ℚ) +
          b.alphaValue ⟨i - 2, by omega⟩ : ℚ)) : WithTop ℚ) ≤
        b.truncatedPrefixDefect b ((-1) ^ (i / 2)) 0 i := by
    simpa only [first, last, Nat.sub_zero,
      show i - 2 + 2 = i by omega,
      show (i - 2 + 2) / 2 = i / 2 by omega] using h74
  have hcritical :
      ((b.order ⟨i - 2, by omega⟩ -
            b.order ⟨i - 1, by omega⟩ : Int) : ℚ) + 2 ≤
        ((b.order ⟨i - 2, by omega⟩ -
            b.order ⟨i - 1, by omega⟩ : Int) : ℚ) +
          b.alphaValue ⟨i - 2, by omega⟩ := by
    linarith
  exact (WithTop.coe_le_coe.mpr hcritical).trans
    (h74'.trans (b.truncatedPrefixDefect_self_le_alternating i))

/-- In the canonical type-I region, every even source order through the
right switch equals the first source order. -/
theorem lemma77_typeI_source_plateau
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0) (i : Nat)
    (hiTwo : 2 ≤ i) (hiBound : i ≤ n + 2) (hiEven : Even i)
    (hright : i - 2 ≤ C.rightSwitch) :
    a.order (0 : Fin (n + 2)) = a.order ⟨i - 2, by omega⟩ := by
  have hanchorEven : Even D.anchor := by
    by_cases heq : D.profile.first = D.anchor
    · rw [← heq, hfirst]
      exact ⟨0, by omega⟩
    · have hlt : D.profile.first < D.anchor :=
        lt_of_le_of_ne D.profile.first_le_anchor heq
      simpa only [hfirst, Nat.sub_zero] using
        (D.profile.leftProfile hlt).1
  have hlastEven : Even (i - 2) := by
    rcases hiEven with ⟨d, hd⟩
    exact ⟨d - 1, by omega⟩
  have hzero := C.source_to_anchor 0 (Nat.zero_le D.anchor) ⟨0, by omega⟩
  have hlast : a.orderSequence.entryOrZero (i - 2) =
      a.orderSequence.entryOrZero D.anchor := by
    by_cases hleft : i - 2 ≤ D.anchor
    · exact C.source_to_anchor (i - 2) hleft hlastEven
    · have hanchor : D.anchor ≤ i - 2 := Nat.le_of_lt (lt_of_not_ge hleft)
      have heven : Even (i - 2 - D.anchor) := by
        rcases hlastEven with ⟨d, hd⟩
        rcases hanchorEven with ⟨e, he⟩
        exact ⟨d - e, by omega⟩
      exact C.source_to_right (i - 2) hanchor hright heven
  calc
    a.order (0 : Fin (n + 2)) = a.orderSequence.entryOrZero 0 := by
      symm
      exact a.orderSequence_entryOrZero_eq_order 0
    _ = a.orderSequence.entryOrZero (i - 2) := hzero.trans hlast.symm
    _ = a.order ⟨i - 2, by omega⟩ :=
      a.orderSequence_entryOrZero_eq_order ⟨i - 2, by omega⟩

/-- Lemma 7.7 on the canonical type-I plateau, conditional only on the
`alpha_(i-1) >= 2` conclusion supplied later by Lemma 6.9(v)/6.13. -/
theorem beli2019Lemma77_typeI_of_alpha_ge_two
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0) (i : Nat)
    (hiTwo : 2 ≤ i) (hiBound : i ≤ n + 2) (hiEven : Even i)
    (hright : i - 2 ≤ C.rightSwitch)
    (halpha : 2 ≤ a.alphaValue ⟨i - 2, by omega⟩) :
    (((((a.order ⟨i - 2, by omega⟩ -
          a.order ⟨i - 1, by omega⟩ : Int) : ℚ) + 2 : ℚ)) :
        WithTop ℚ) ≤ a.alternatingPrefixDefect i := by
  apply a.beli2019Lemma77_of_plateau i hiTwo hiBound hiEven
  · exact lemma77_typeI_source_plateau a b D C hfirst i
      hiTwo hiBound hiEven hright
  · exact halpha

end BONG.GoodBONG

end Bong
