/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79EvenTypeICentralCandidates

/-!
# Beli (2019), Lemma 7.9(ii), case 3: central type-I beta estimate

The exact central alpha shift and the three candidate comparisons assemble
to the scalar estimate `B_i <= beta_i`.  This covers strict even interior
coordinates whose secondary candidate remains in the canonical interval.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

set_option maxHeartbeats 5000000 in
-- Candidate assembly carries dependent representation indices through four lemmas.
/-- In the strict central type-I interval, the representation alpha is
bounded by the preceding target alpha. -/
theorem beli2019Lemma79_typeI_central_even_beta
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last)
    (horderAB : a.RepresentationOrderCondition b le_rfl)
    (hdefectAB : a.RepresentationDefectCondition b)
    (hdefectAC : a.RepresentationDefectCondition c)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hiEven : Even i.val)
    (hiLeft : C.leftSwitch < i.val)
    (hfarRight : i.val + 2 ≤ C.rightSwitch) :
    b.representationAlphaValue c i ≤
      b.alphaValue ⟨i.val - 1, by omega⟩ := by
  have halpha := beli2019Lemma79_typeI_central_even_alphaShift
    a b D C hfirst hrightLast horderAB hdefectAB i hiEven
      (by omega) (by omega)
  have hhalf := lemma79_typeI_central_even_halfGap_le_add_two
    a b c D C hfirst i hiEven hiLeft.le (by omega)
  have hprimary := beli2019Lemma79_typeI_central_even_primary
    a b c D C hfirst hrightLast horderAB hdefectAB i hi.2
      hiEven hiLeft.le (by omega)
  have hsecondary : ∀
      (hi' : 1 < i.val ∧ i.val + 1 < n + 2),
      b.representationSecondaryDefect c i hi' ≤
        a.representationSecondaryDefect c i hi' +
          ((2 : ℚ) : WithTop ℚ) := by
    intro hi'
    exact beli2019Lemma79_typeI_central_even_secondary
      a b c D C hfirst hrightLast horderAB hdefectAB i hi'
        hiEven hiLeft.le hfarRight
  exact lemma79_even_beta_bound_of_candidate_shifts
    a b c hdefectAC i halpha hhalf hprimary hsecondary

end BONG.GoodBONG

end Bong
