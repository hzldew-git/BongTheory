/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79EvenSourcePlateau

/-!
# Beli (2019), Lemma 7.9(ii), case 3: assembling the left profiles

The normalized type-II, type-III, and early type-I profiles all give a
constant even source-order plateau.  This file combines that plateau, the
capped target estimates, and the scalar inequality `B_i <= beta_i`.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The complete even case-3 implication on a normalized no-gap left
outer interval, conditional only on the paper's scalar beta estimate. -/
theorem lemma79_ii_of_noGap_leftOuter_beta
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (O : BeliOrderLE.NoGapTwoOuterConsequences
      a.orderSequence b.orderSequence)
    (hfirst : O.first = 0)
    (hnoTwo : ∀ k, k < n + 2 →
      b.orderSequence.entryOrZero k <
        a.orderSequence.entryOrZero k + 2)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiTwo : 2 ≤ i.val) (hiNext : i.val + 1 < n + 2)
    (hiEven : Even i.val)
    (hleft : i.val ≤ O.transition.lastZero)
    (hbeta : b.representationAlphaValue c i ≤
      b.alphaValue ⟨i.val - 1, by omega⟩) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hzero := O.target_leftEven_eq_first_add_one
    hfirst hnoTwo 0 (Nat.zero_le _) ⟨0, by omega⟩
  have hcurrent := O.target_leftEven_eq_first_add_one
    hfirst hnoTwo i.val hleft hiEven
  have hplateau : b.orderSequence.entryOrZero 0 =
      b.orderSequence.entryOrZero i.val := hzero.trans hcurrent.symm
  have hsource := b.lemma79_even_sourceCapped_of_plateau
    c i hiTwo hiNext hiEven hplateau hbeta
  have htarget := lemma79_even_targetCapped_of_noGap_leftOuter
    a b c O hfirst hnoTwo hnorm i hiTwo hiEven hleft
  exact lemma79_ii_of_even_selfCapped_bounds b c i hsource htarget

/-- Type II, case 3 on the even left interval. -/
theorem beli2019Lemma79_ii_typeII_even_left_of_beta
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeII a b)
    (hfirst : D.outer.first = 0)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiTwo : 2 ≤ i.val) (hiNext : i.val + 1 < n + 2)
    (hiEven : Even i.val)
    (hleft : i.val ≤ D.outer.transition.lastZero)
    (hbeta : b.representationAlphaValue c i ≤
      b.alphaValue ⟨i.val - 1, by omega⟩) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  exact lemma79_ii_of_noGap_leftOuter_beta
    a b c D.outer hfirst D.no_gap_two hnorm i hiTwo hiNext hiEven
      hleft hbeta

/-- Type III, case 3 on the even left interval. -/
theorem beli2019Lemma79_ii_typeIII_even_left_of_beta
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiTwo : 2 ≤ i.val) (hiNext : i.val + 1 < n + 2)
    (hiEven : Even i.val)
    (hleft : i.val ≤ D.outer.transition.lastZero)
    (hbeta : b.representationAlphaValue c i ≤
      b.alphaValue ⟨i.val - 1, by omega⟩) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  exact lemma79_ii_of_noGap_leftOuter_beta
    a b c D.outer hfirst D.no_gap_two hnorm i hiTwo hiNext hiEven
      hleft hbeta

/-- Type I, case 3 before the first canonical switch. -/
theorem beli2019Lemma79_ii_typeI_even_left_of_beta
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeI a b)
    (C : Lemma67TypeICanonicalData a b D)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiTwo : 2 ≤ i.val) (hiNext : i.val + 1 < n + 2)
    (hiEven : Even i.val) (hbefore : i.val < C.leftSwitch)
    (hbeta : b.representationAlphaValue c i ≤
      b.alphaValue ⟨i.val - 1, by omega⟩) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect c 1 i.val i.val := by
  have hzero := C.target_before_left 0 (by omega) ⟨0, by omega⟩
  have hcurrent := C.target_before_left i.val hbefore hiEven
  have hplateau : b.orderSequence.entryOrZero 0 =
      b.orderSequence.entryOrZero i.val := hzero.trans hcurrent.symm
  have hsource := b.lemma79_even_sourceCapped_of_plateau
    c i hiTwo hiNext hiEven hplateau hbeta
  have htarget := beli2019Lemma79_ii_typeI_even_leftTargetCapped
    a b c D C hnorm i hiTwo hiEven hbefore
  exact lemma79_ii_of_even_selfCapped_bounds b c i hsource htarget

end BONG.GoodBONG

end Bong
