/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma76TypeICentralComplete
import Bong.Bong.Beli2019Lemma79EvenTypeICentralBeta

/-!
# Beli (2019), Lemma 7.9(ii), case 3: central type-I source prefix

The constant even target plateau bounds the preceding target gap by `2e`.
Condition 2.1(i) transfers that bound to the cross gap, so the completed
central form of Lemma 7.6 applies to the scalar beta estimate.
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
-- The proof reuses the complete candidate and Lemma 7.6 assemblies.
/-- The source capped-prefix bound at strict central even type-I
coordinates. -/
theorem beli2019Lemma79_typeI_central_even_sourceCapped
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
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : 1 < i.val ∧ i.val + 1 < n + 2)
    (hiEven : Even i.val)
    (hiLeft : C.leftSwitch < i.val)
    (hfarRight : i.val + 2 ≤ C.rightSwitch) :
    (b.representationAlphaValue c i : WithTop ℚ) ≤
      b.truncatedPrefixDefect b ((-1) ^ (i.val / 2)) 0 i.val := by
  have hiTwo : 2 ≤ i.val := by omega
  have hpreviousEven : Even (i.val - 2) := by
    rcases hiEven with ⟨d, hd⟩
    exact ⟨d - 1, by omega⟩
  have hpreviousLeft : C.leftSwitch ≤ i.val - 2 := by
    rcases hiEven with ⟨d, hd⟩
    rcases C.left_even with ⟨e, he⟩
    omega
  have hpreviousRaw := lemma76_typeI_target_even_order_eq_left
    a b D C hfirst (i.val - 2) hpreviousLeft (by omega) hpreviousEven
  have hcurrentRaw := lemma76_typeI_target_even_order_eq_left
    a b D C hfirst i.val hiLeft.le (by omega) hiEven
  have htwo : b.order ⟨i.val - 2, by omega⟩ =
      b.order ⟨i.val, i.lt_large⟩ := by
    rw [← b.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    exact hpreviousRaw.symm.trans hcurrentRaw
  have hsourceGap := b.orderGap_previous_le_twoE_of_twoStep
    i hiTwo htwo
  have hcross :=
    crossGap_le_twoE_of_representationOrder_of_sourceGap_le_twoE
      b c horderBC i hsourceGap
  have hbeta := beli2019Lemma79_typeI_central_even_beta
    a b c D C hfirst hrightLast horderAB hdefectAB hdefectAC
      i hi hiEven hiLeft hfarRight
  exact beli2019Lemma76_typeI_central_sourceCapped_complete
    a b c D C hfirst i hi.2 hiEven hiLeft (by omega) hcross hbeta

end BONG.GoodBONG

end Bong
