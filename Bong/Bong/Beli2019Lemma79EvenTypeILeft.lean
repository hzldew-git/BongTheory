/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma67TypeICanonical
import Bong.Bong.Beli2019Lemma79EvenNormFloor

/-!
# Beli (2019), Lemma 7.9(ii), case 3: the early type-I interval

Before the first canonical type-I switch, every even target order is the
first source order plus one.  The norm-floor branch therefore proves the
target defect inequality on the entire early type-I interval.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Case 3 on the even coordinates strictly before the first canonical
type-I switch. -/
theorem beli2019Lemma79_ii_typeI_even_beforeLeftSwitch
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) (D : Lemma67TypeI a b)
    (C : Lemma67TypeICanonicalData a b D)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiTwo : 2 ≤ i.val) (hiEven : Even i.val)
    (hbefore : i.val < C.leftSwitch) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      c.alternatingPrefixDefect i.val := by
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
  exact lemma79_even_targetDefect_of_sourceNext_eq_normFloor
    a b c hnorm i hiTwo hiEven hsourceNext

end BONG.GoodBONG

end Bong
