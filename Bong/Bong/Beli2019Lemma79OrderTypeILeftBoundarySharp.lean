/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79OrderTypeILeftBoundaryDefect
import Bong.Bong.Beli2019CappedDefectSharp

/-!
# Beli (2019), Lemma 7.9(i): sharp contradiction at the type-I left boundary

The secondary candidate bounds the exceptional mixed prefix by the order
cut.  Lemma 7.7 puts the corresponding source self-prefix strictly above
that cut.  Sharp capped-defect multiplication therefore identifies the
short third self-prefix with the mixed prefix, contradicting the domination
lower bound from the preceding file.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Once the Lemma 7.7 source-prefix bound is available, failure of both
order alternatives at the exceptional predecessor is impossible. -/
theorem lemma79_typeI_leftPredecessor_failure_false_of_sourcePrefix
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0) (hleftPos : 0 < C.leftSwitch)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (hinterior : C.leftSwitch + 1 < n + 2)
    (F : Lemma79TypeILeftPredecessorFailureData a c C.leftSwitch)
    (hsource :
      (((((a.order
          ⟨C.leftSwitch, C.left_le_anchor.trans_lt D.anchor_bound⟩ -
        a.order ⟨C.leftSwitch + 1, hinterior⟩ : Int) : ℚ) + 1 : ℚ) :
          WithTop ℚ) <
        a.truncatedPrefixDefect a
          ((-1) ^ ((C.leftSwitch + 2) / 2)) 0
            (C.leftSwitch + 2))) : False := by
  have hleftTwo : 2 ≤ C.leftSwitch := by
    rcases C.left_even with ⟨d, hd⟩
    omega
  have hleftBound : C.leftSwitch < n + 2 :=
    C.left_le_anchor.trans_lt D.anchor_bound
  have hsecondary := lemma79_typeI_leftPredecessor_secondary_le_sourceCut
    a b c D C hfirst hleftPos hdefectAB hdefectAC F hinterior
  have hmixedLe := lemma79_typeI_leftPredecessor_mixed_le_orderCut
    a c C.leftSwitch hleftTwo hleftBound hinterior F hsecondary
  let mixed : WithTop ℚ :=
    a.truncatedPrefixDefect c 1 (C.leftSwitch + 2)
      (C.leftSwitch - 2)
  have hmixedSource : mixed <
      a.truncatedPrefixDefect a
        ((-1) ^ ((C.leftSwitch + 2) / 2)) 0
          (C.leftSwitch + 2) := by
    have hmixedCut : mixed ≤
        (((((a.order ⟨C.leftSwitch, hleftBound⟩ -
            a.order ⟨C.leftSwitch + 1, hinterior⟩ : Int) : ℚ) + 1 : ℚ) :
          WithTop ℚ)) := by
      simpa only [mixed] using hmixedLe
    exact hmixedCut.trans_lt hsource
  have hseparation :
      c.truncatedPrefixDefect a 1 (C.leftSwitch - 2)
          (C.leftSwitch + 2) <
        a.truncatedPrefixDefect a
          ((-1) ^ ((C.leftSwitch + 2) / 2)) (C.leftSwitch + 2) 0 := by
    rw [c.truncatedPrefixDefect_comm a 1
        (C.leftSwitch - 2) (C.leftSwitch + 2),
      a.truncatedPrefixDefect_comm a
        ((-1) ^ ((C.leftSwitch + 2) / 2))
          (C.leftSwitch + 2) 0]
    simpa only [mixed] using hmixedSource
  have hsharp := c.truncatedPrefixDefect_mul_eq_left_of_lt_right
    a a 1 ((-1) ^ ((C.leftSwitch + 2) / 2))
      (C.leftSwitch - 2) (C.leftSwitch + 2) 0 hseparation
  have hsign :
      ((-1 : Kˣ) ^ ((C.leftSwitch + 2) / 2)) =
        (-1) ^ ((C.leftSwitch - 2) / 2) := by
    rcases C.left_even with ⟨d, hd⟩
    have hleftHalf : (C.leftSwitch - 2) / 2 = d - 1 := by omega
    have hrightHalf : (C.leftSwitch + 2) / 2 = d + 1 := by omega
    rw [hleftHalf, hrightHalf]
    have hdPos : 0 < d := by omega
    rw [show d + 1 = (d - 1) + 2 by omega, pow_add]
    norm_num
  have hthirdEq :
      c.truncatedPrefixDefect c
          ((-1) ^ ((C.leftSwitch - 2) / 2)) 0
            (C.leftSwitch - 2) = mixed := by
    calc
      c.truncatedPrefixDefect c
          ((-1) ^ ((C.leftSwitch - 2) / 2)) 0
            (C.leftSwitch - 2) =
          c.truncatedPrefixDefect c
            ((-1) ^ ((C.leftSwitch - 2) / 2))
              (C.leftSwitch - 2) 0 :=
        c.truncatedPrefixDefect_comm c
          ((-1) ^ ((C.leftSwitch - 2) / 2)) 0
            (C.leftSwitch - 2)
      _ = c.truncatedPrefixDefect a
          ((-1) ^ ((C.leftSwitch - 2) / 2))
            (C.leftSwitch - 2) 0 :=
        (c.truncatedPrefixDefect_zero_right_eq_self a
          ((-1) ^ ((C.leftSwitch - 2) / 2))
            (C.leftSwitch - 2)).symm
      _ = c.truncatedPrefixDefect a
          ((-1) ^ ((C.leftSwitch + 2) / 2))
            (C.leftSwitch - 2) 0 := by rw [hsign]
      _ = c.truncatedPrefixDefect a
          (1 * ((-1) ^ ((C.leftSwitch + 2) / 2)))
            (C.leftSwitch - 2) 0 := by rw [one_mul]
      _ = c.truncatedPrefixDefect a 1
          (C.leftSwitch - 2) (C.leftSwitch + 2) := hsharp
      _ = a.truncatedPrefixDefect c 1
          (C.leftSwitch + 2) (C.leftSwitch - 2) :=
        c.truncatedPrefixDefect_comm a 1
          (C.leftSwitch - 2) (C.leftSwitch + 2)
      _ = mixed := rfl
  have hmixedUpper : mixed ≤
      (((((a.order ⟨C.leftSwitch, hleftBound⟩ -
          a.order ⟨C.leftSwitch + 1, hinterior⟩ : Int) : ℚ) + 1 : ℚ) :
        WithTop ℚ)) := by
    simpa only [mixed] using hmixedLe
  by_cases hleftFour : 4 ≤ C.leftSwitch
  · have hthirdLower :=
      lemma79_typeI_leftPredecessor_thirdPrefix_ge_orderCut_add_two
        a b c D C hfirst hnorm hleftFour hinterior F
    rw [hthirdEq] at hthirdLower
    have hfalse :
        (((((a.order ⟨C.leftSwitch, hleftBound⟩ -
            a.order ⟨C.leftSwitch + 1, hinterior⟩ : Int) : ℚ) + 3 : ℚ) :
          WithTop ℚ)) ≤
        (((((a.order ⟨C.leftSwitch, hleftBound⟩ -
            a.order ⟨C.leftSwitch + 1, hinterior⟩ : Int) : ℚ) + 1 : ℚ) :
          WithTop ℚ)) := hthirdLower.trans hmixedUpper
    norm_cast at hfalse
    linarith
  · have hleftEq : C.leftSwitch = 2 := by
      rcases C.left_even with ⟨d, hd⟩
      omega
    have hthirdTop :
        c.truncatedPrefixDefect c
            ((-1) ^ ((C.leftSwitch - 2) / 2)) 0
              (C.leftSwitch - 2) = ⊤ := by
      rw [hleftEq]
      norm_num
      unfold truncatedPrefixDefect
      rw [c.prefixAlphaCap_zero]
      simp only [inf_top_eq]
      rw [show (1 : Kˣ) * c.prefixProduct 0 * c.prefixProduct 0 = 1 by
        simp [GoodBONG.prefixProduct]]
      rw [defectOrder_eq_top_of_isSquare]
      exact IsSquare.one
    have htopLe : (⊤ : WithTop ℚ) ≤
        (((((a.order ⟨C.leftSwitch, hleftBound⟩ -
            a.order ⟨C.leftSwitch + 1, hinterior⟩ : Int) : ℚ) + 1 : ℚ) :
          WithTop ℚ)) := by
      calc
        (⊤ : WithTop ℚ) = mixed := hthirdTop.symm.trans hthirdEq
        _ ≤ _ := hmixedUpper
    exact (not_lt_of_ge htopLe) (WithTop.coe_lt_top _)

end BONG.GoodBONG

end Bong
