/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeICentralSeedsComplete
import Bong.Bong.Beli2019Lemma79EvenTypeILeftComplete

/-!
# Beli (2019), Lemma 7.9(ii), case 3: central type-I alpha shift

Lemma 6.9(v) identifies the source and target left endpoints throughout a
nonterminal canonical type-I interval.  At an odd order coordinate the
source order is two larger, so the corresponding target alpha is exactly
the source alpha plus two.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- The paper's identity `beta_i = alpha_i + 2` at an even central type-I
representation boundary. -/
theorem beli2019Lemma79_typeI_central_even_alphaShift
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (hrightLast : C.rightSwitch < D.profile.last)
    (horder : a.RepresentationOrderCondition b le_rfl)
    (hdefect : a.RepresentationDefectCondition b)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiEven : Even i.val)
    (hiLeft : C.leftSwitch ≤ i.val - 1)
    (hiRight : i.val - 1 < C.rightSwitch) :
    b.alphaValue ⟨i.val - 1, by
        have hi := i.lt_large
        omega⟩ =
      a.alphaValue ⟨i.val - 1, by
        have hi := i.lt_large
        omega⟩ + 2 := by
  have hodd : Odd (i.val - 1) := by
    rcases hiEven with ⟨d, hd⟩
    have hip := i.pos
    exact ⟨d - 1, by omega⟩
  have hweight := beli2019Lemma69_v_typeI_of_rightSwitch_lt_last
    a b D C hfirst hrightLast horder hdefect (i.val - 1)
      hiLeft hiRight
  have hentry := lemma69_v_typeI_odd_entry_gap_two
    a b D C hfirst (i.val - 1) hodd hiLeft hiRight.le
  let p : Fin (n + 1) := ⟨i.val - 1, by
    have hi := i.lt_large
    omega⟩
  have hweight' : a.alphaLeftEndpoint p = b.alphaLeftEndpoint p := by
    simpa only [p] using hweight
  have horderShift : a.order p.castSucc = b.order p.castSucc + 2 := by
    rw [← a.orderSequence_entryOrZero_eq_order,
      ← b.orderSequence_entryOrZero_eq_order]
    change a.orderSequence.entryOrZero (i.val - 1) =
      b.orderSequence.entryOrZero (i.val - 1) + 2
    exact hentry
  have horderShiftQ : (a.order p.castSucc : ℚ) =
      (b.order p.castSucc : ℚ) + 2 := by
    exact_mod_cast horderShift
  unfold alphaLeftEndpoint at hweight'
  have hresult : b.alphaValue p = a.alphaValue p + 2 := by
    rw [horderShiftQ] at hweight'
    linarith
  simpa only [p] using hresult

end BONG.GoodBONG

end Bong
