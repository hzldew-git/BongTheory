/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79OrderTypeILeftBoundarySharp

/-!
# Beli (2019), Lemma 7.9(i): complete exceptional type-I predecessor

The endpoint branch is already impossible at the level of the auxiliary
invariant: there is no secondary candidate, while the primary candidate is
strictly above the source cut.  In the interior branch the sharp-defect
contradiction applies.  This file packages the two arguments as the desired
order alternative at the predecessor of the first type-I switch.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- If the exceptional auxiliary index has no following source coordinate,
its sole primary candidate contradicts the source-alpha bound. -/
theorem lemma79_typeI_leftPredecessor_failure_false_of_not_interior
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0) (hleftPos : 0 < C.leftSwitch)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (F : Lemma79TypeILeftPredecessorFailureData a c C.leftSwitch)
    (hnotInterior : ¬ C.leftSwitch + 1 < n + 2) : False := by
  have hleftTwo : 2 ≤ C.leftSwitch := by
    rcases C.left_even with ⟨d, hd⟩
    omega
  have hleftBound : C.leftSwitch < n + 2 :=
    C.left_le_anchor.trans_lt D.anchor_bound
  let idx : RepresentationIndex (n + 2) (n + 2) :=
    ⟨C.leftSwitch, hleftPos, hleftBound, hleftBound.le⟩
  have hprime := lemma79_typeI_leftPredecessor_alphaPrime_le_sourceCut
    a b c D C hfirst hleftPos hdefectAB hdefectAC F
  have hprimary := lemma79_typeI_leftPredecessor_sourceCut_lt_primary
    a c C.leftSwitch hleftTwo hleftBound F
  have hendpoint := a.representationAlphaPrime_eq_primary_of_not_interior
    c idx (by
      simp only [idx]
      omega)
  rw [hendpoint] at hprime
  exact (not_le_of_gt hprimary) (by simpa only [idx] using hprime)

/-- Condition 2.1(i) at the exceptional predecessor, assuming the exact
Lemma 7.7 source-prefix estimate used by the sharp contradiction. -/
theorem beli2019Lemma79_i_typeI_leftPredecessor_of_sourcePrefix
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0) (hleftPos : 0 < C.leftSwitch)
    (hac : a.RepresentationOrderCondition c le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (hsource : ∀ hinterior : C.leftSwitch + 1 < n + 2,
      (((((a.order
          ⟨C.leftSwitch, C.left_le_anchor.trans_lt D.anchor_bound⟩ -
        a.order ⟨C.leftSwitch + 1, hinterior⟩ : Int) : ℚ) + 1 : ℚ) :
          WithTop ℚ) <
        a.truncatedPrefixDefect a
          ((-1) ^ ((C.leftSwitch + 2) / 2)) 0
            (C.leftSwitch + 2))) :
    b.orderSequence.entry (C.leftSwitch - 1) (by
        have hbound := C.left_le_anchor.trans_lt D.anchor_bound
        omega) ≤
        c.orderSequence.entry (C.leftSwitch - 1) (by
          have hbound := C.left_le_anchor.trans_lt D.anchor_bound
          omega) ∨
      ∃ (hk0 : 0 < C.leftSwitch - 1)
          (hkNext : C.leftSwitch - 1 + 1 < n + 2),
        b.orderSequence.entry (C.leftSwitch - 1) (by omega) +
            b.orderSequence.entry (C.leftSwitch - 1 + 1) hkNext ≤
          c.orderSequence.entry (C.leftSwitch - 1 - 1) (by omega) +
            c.orderSequence.entry (C.leftSwitch - 1) (by omega) := by
  have hleftTwo : 2 ≤ C.leftSwitch := by
    rcases C.left_even with ⟨d, hd⟩
    omega
  have hleftBound : C.leftSwitch < n + 2 :=
    C.left_le_anchor.trans_lt D.anchor_bound
  by_cases hdirect :
      b.orderSequence.entryOrZero (C.leftSwitch - 1) ≤
        c.orderSequence.entryOrZero (C.leftSwitch - 1)
  · left
    rw [b.orderSequence.entryOrZero_of_lt
        (i := C.leftSwitch - 1) (by omega),
      c.orderSequence.entryOrZero_of_lt
        (i := C.leftSwitch - 1) (by omega)] at hdirect
    exact hdirect
  · by_cases hpair :
        b.orderSequence.entryOrZero (C.leftSwitch - 1) +
            b.orderSequence.entryOrZero C.leftSwitch ≤
          c.orderSequence.entryOrZero (C.leftSwitch - 2) +
            c.orderSequence.entryOrZero (C.leftSwitch - 1)
    · right
      refine ⟨by omega, by omega, ?_⟩
      rw [b.orderSequence.entryOrZero_of_lt
          (i := C.leftSwitch - 1) (by omega),
        b.orderSequence.entryOrZero_of_lt
          (i := C.leftSwitch) hleftBound,
        c.orderSequence.entryOrZero_of_lt
          (i := C.leftSwitch - 2) (by omega),
        c.orderSequence.entryOrZero_of_lt
          (i := C.leftSwitch - 1) (by omega)] at hpair
      simpa only [show C.leftSwitch - 1 + 1 = C.leftSwitch by omega,
        show C.leftSwitch - 1 - 1 = C.leftSwitch - 2 by omega] using hpair
    · have F := lemma79_typeI_leftPredecessor_failureData
        a b c D C hfirst hleftPos hac hdirect hpair
      by_cases hinterior : C.leftSwitch + 1 < n + 2
      · exact False.elim
          (lemma79_typeI_leftPredecessor_failure_false_of_sourcePrefix
            a b c D C hfirst hleftPos hdefectAB hdefectAC hnorm
              hinterior F (hsource hinterior))
      · exact False.elim
          (lemma79_typeI_leftPredecessor_failure_false_of_not_interior
            a b c D C hfirst hleftPos hdefectAB hdefectAC F hinterior)

end BONG.GoodBONG

end Bong
