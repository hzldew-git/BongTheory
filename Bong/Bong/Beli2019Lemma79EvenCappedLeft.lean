/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma67TypeICanonical
import Bong.Bong.Beli2019Lemma79EvenCappedNormFloor
import Bong.Bong.Beli2019Lemma79OrderLeftOuter

/-!
# Beli (2019), Lemma 7.9(ii), case 3: complete capped left branch

The exact norm-floor order occurs throughout the even type-II/type-III left
outer interval and before the first canonical type-I switch.  The capped
norm-floor theorem therefore closes the target self-prefix part of case 3
on all of these intervals.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The capped target-prefix bound on a normalized no-gap left outer
interval. -/
theorem lemma79_even_targetCapped_of_noGap_leftOuter
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
    (hiTwo : 2 ≤ i.val) (hiEven : Even i.val)
    (hleft : i.val ≤ O.transition.lastZero) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      c.truncatedPrefixDefect c ((-1) ^ (i.val / 2)) 0 i.val := by
  have hsourceNextRaw := O.target_leftEven_eq_first_add_one
    hfirst hnoTwo i.val hleft hiEven
  have hsourceNext :
      b.order ⟨i.val, i.lt_large⟩ = a.order 0 + 1 := by
    rw [← b.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order]
    exact hsourceNextRaw
  exact lemma79_even_targetCapped_of_sourceNext_eq_normFloor
    a b c hnorm i hiTwo hiEven hsourceNext

/-- The capped target-prefix part of case 3 on the type-II left interval. -/
theorem beli2019Lemma79_ii_typeII_even_leftTargetCapped
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeII a b)
    (hfirst : D.outer.first = 0)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiTwo : 2 ≤ i.val) (hiEven : Even i.val)
    (hleft : i.val ≤ D.outer.transition.lastZero) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      c.truncatedPrefixDefect c ((-1) ^ (i.val / 2)) 0 i.val := by
  exact lemma79_even_targetCapped_of_noGap_leftOuter
    a b c D.outer hfirst D.no_gap_two hnorm i hiTwo hiEven hleft

/-- The capped target-prefix part of case 3 on the type-III left interval. -/
theorem beli2019Lemma79_ii_typeIII_even_leftTargetCapped
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeIII a b)
    (hfirst : D.outer.first = 0)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiTwo : 2 ≤ i.val) (hiEven : Even i.val)
    (hleft : i.val ≤ D.outer.transition.lastZero) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      c.truncatedPrefixDefect c ((-1) ^ (i.val / 2)) 0 i.val := by
  exact lemma79_even_targetCapped_of_noGap_leftOuter
    a b c D.outer hfirst D.no_gap_two hnorm i hiTwo hiEven hleft

/-- The capped target-prefix part of case 3 before the first canonical
type-I switch. -/
theorem beli2019Lemma79_ii_typeI_even_leftTargetCapped
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeI a b)
    (C : Lemma67TypeICanonicalData a b D)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiTwo : 2 ≤ i.val) (hiEven : Even i.val)
    (hbefore : i.val < C.leftSwitch) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      c.truncatedPrefixDefect c ((-1) ^ (i.val / 2)) 0 i.val := by
  have htarget := C.target_before_left i.val hbefore hiEven
  have hsourceZero := C.source_to_anchor 0 (Nat.zero_le _) (by
    exact ⟨0, by omega⟩)
  have hsourceNextRaw :
      b.orderSequence.entryOrZero i.val =
        a.orderSequence.entryOrZero 0 + 1 := by
    rw [hsourceZero]
    exact htarget
  have hsourceNext :
      b.order ⟨i.val, i.lt_large⟩ = a.order 0 + 1 := by
    rw [← b.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order]
    exact hsourceNextRaw
  exact lemma79_even_targetCapped_of_sourceNext_eq_normFloor
    a b c hnorm i hiTwo hiEven hsourceNext

end BONG.GoodBONG

end Bong
