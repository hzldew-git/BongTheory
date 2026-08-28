/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma77
import Bong.Bong.Beli2019WeightSequence

/-!
# Beli (2019), Lemma 6.9(v) in the type-I middle interval

The even coordinates of the `W`-sequence are `R_i + alpha_i`.  On the
canonical type-I middle interval, the target order is the source order plus
two.  Equality of the corresponding `W`-coordinates therefore gives
`alpha_i = beta_i + 2`, and property P2 gives `alpha_i >= 2`.  This is the
numerical input used in the middle branch of Lemma 7.7.
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

/-- Equality of a type-I left endpoint of the `W`-sequence identifies the
two alpha values up to the order jump. -/
theorem alpha_eq_add_two_of_leftEndpoint_eq
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (k : Fin (n + 1))
    (hgap : b.order k.castSucc = a.order k.castSucc + 2)
    (hweight : a.alphaLeftEndpoint k = b.alphaLeftEndpoint k) :
    a.alphaValue k = b.alphaValue k + 2 := by
  unfold alphaLeftEndpoint at hweight
  have hgapQ := congrArg (fun z : Int => (z : ℚ)) hgap
  push_cast at hgapQ
  linarith

/-- Every even order position between the two canonical type-I switches has
target order exactly two above the source order. -/
theorem lemma69_v_typeI_order_gap_two
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0) (i : Nat)
    (hiTwo : 2 ≤ i) (hiBound : i ≤ n + 2) (hiEven : Even i)
    (hleft : C.leftSwitch ≤ i - 2)
    (hright : i - 2 ≤ C.rightSwitch) :
    b.order ⟨i - 2, by omega⟩ = a.order ⟨i - 2, by omega⟩ + 2 := by
  have hkEven : Even (i - 2) := by
    rcases hiEven with ⟨d, hd⟩
    exact ⟨d - 1, by omega⟩
  have hanchorEven : Even D.anchor := by
    by_cases heq : D.profile.first = D.anchor
    · rw [← heq, hfirst]
      exact ⟨0, by omega⟩
    · have hlt : D.profile.first < D.anchor :=
        lt_of_le_of_ne D.profile.first_le_anchor heq
      simpa only [hfirst, Nat.sub_zero] using
        (D.profile.leftProfile hlt).1
  have hentry : b.orderSequence.entryOrZero (i - 2) =
      a.orderSequence.entryOrZero (i - 2) + 2 := by
    by_cases hkAnchor : i - 2 ≤ D.anchor
    · have ha := C.source_to_anchor (i - 2) hkAnchor hkEven
      have hb := C.target_from_left (i - 2) hleft hkAnchor hkEven
      omega
    · have hanchorK : D.anchor ≤ i - 2 :=
        Nat.le_of_lt (lt_of_not_ge hkAnchor)
      have hdistance : Even (i - 2 - D.anchor) := by
        rcases hkEven with ⟨d, hd⟩
        rcases hanchorEven with ⟨e, he⟩
        exact ⟨d - e, by omega⟩
      have ha := C.source_to_right (i - 2) hanchorK hright hdistance
      have hb := C.target_from_anchor (i - 2) hanchorK
        (hright.trans C.right_le_last) hdistance
      have hgapAnchor := D.anchor_gap
      omega
  calc
    b.order ⟨i - 2, by omega⟩ =
        b.orderSequence.entryOrZero (i - 2) := by
      symm
      exact b.orderSequence_entryOrZero_eq_order ⟨i - 2, by omega⟩
    _ = a.orderSequence.entryOrZero (i - 2) + 2 := hentry
    _ = a.order ⟨i - 2, by omega⟩ + 2 := by
      rw [a.orderSequence_entryOrZero_eq_order ⟨i - 2, by omega⟩]

/-- The type-I instance of Lemma 6.9(v), reduced to equality of the
corresponding even coordinate of the two `W`-sequences. -/
theorem lemma69_v_typeI_alpha_ge_two_of_leftEndpoint_eq
    [Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0) (i : Nat)
    (hiTwo : 2 ≤ i) (hiBound : i ≤ n + 2) (hiEven : Even i)
    (hleft : C.leftSwitch ≤ i - 2)
    (hright : i - 2 ≤ C.rightSwitch)
    (hweight :
      a.alphaLeftEndpoint ⟨i - 2, by omega⟩ =
        b.alphaLeftEndpoint ⟨i - 2, by omega⟩) :
    2 ≤ a.alphaValue ⟨i - 2, by omega⟩ := by
  let k : Fin (n + 1) := ⟨i - 2, by omega⟩
  have hweight' : a.alphaLeftEndpoint k = b.alphaLeftEndpoint k := by
    simpa only [k] using hweight
  have hgap : b.order k.castSucc = a.order k.castSucc + 2 := by
    have hkCast : k.castSucc =
        (⟨i - 2, by omega⟩ : Fin (n + 2)) := by
      apply Fin.ext
      rfl
    rw [hkCast]
    exact lemma69_v_typeI_order_gap_two a b D C hfirst i hiTwo
      hiBound hiEven hleft hright
  have halpha := alpha_eq_add_two_of_leftEndpoint_eq a b k hgap hweight'
  have hbeta := (b.alpha_p2 k).1
  simpa only [k] using (show 2 ≤ a.alphaValue k by linarith)

/-- The middle branch of Lemma 7.7 with its `alpha >= 2` premise discharged
by the matching `W`-coordinate from Lemma 6.9(v). -/
theorem beli2019Lemma77_typeI_of_leftEndpoint_eq
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0) (i : Nat)
    (hiTwo : 2 ≤ i) (hiBound : i ≤ n + 2) (hiEven : Even i)
    (hleft : C.leftSwitch ≤ i - 2)
    (hright : i - 2 ≤ C.rightSwitch)
    (hweight :
      a.alphaLeftEndpoint ⟨i - 2, by omega⟩ =
        b.alphaLeftEndpoint ⟨i - 2, by omega⟩) :
    (((((a.order ⟨i - 2, by omega⟩ -
          a.order ⟨i - 1, by omega⟩ : Int) : ℚ) + 2 : ℚ)) :
        WithTop ℚ) ≤ a.alternatingPrefixDefect i := by
  have halpha : 2 ≤ a.alphaValue ⟨i - 2, by omega⟩ := by
    letI : Beli2006AlphaLaws.{u, w} K := alphaW
    exact lemma69_v_typeI_alpha_ge_two_of_leftEndpoint_eq
      a b D C hfirst i hiTwo hiBound hiEven hleft hright hweight
  letI : Beli2006AlphaLaws.{u, v} K := alphaV
  exact a.beli2019Lemma77_typeI_of_alpha_ge_two b D C hfirst i
    hiTwo hiBound hiEven hright halpha

end BONG.GoodBONG

end Bong
