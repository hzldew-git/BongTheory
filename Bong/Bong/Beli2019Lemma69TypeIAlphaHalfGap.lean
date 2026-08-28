/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeIAlphaPrimary

/-!
# Beli (2019), Lemma 6.9(ii): type-I source-alpha half-gap

At an even central boundary the preceding target order is two below the
source order.  Hence the representation half-gap is larger than the source
half-gap that already bounds the source alpha.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- The source alpha is below Definition 4's half-gap candidate at an even
central type-I boundary. -/
theorem lemma69_typeI_alpha_le_halfGap
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (i : RepresentationIndex (n + 2) (n + 2))
    (heven : Even i.val) (hiTwo : 1 < i.val)
    (hleft : C.leftSwitch < i.val - 1)
    (hright : i.val - 1 < C.rightSwitch) :
    (a.alphaValue ⟨i.val - 1, by
      have hi := i.lt_large
      omega⟩ : WithTop ℚ) ≤
      a.representationHalfGap b i := by
  have hiPrevious : i.val - 1 < n + 2 := by
    have hi := i.lt_large
    omega
  have hiAlpha : i.val - 1 < n + 1 := by
    have hi := i.lt_large
    omega
  let p : Fin (n + 1) := ⟨i.val - 1, hiAlpha⟩
  rcases heven with ⟨d, hd⟩
  have hpreviousOdd : Odd (i.val - 1) := ⟨d - 1, by omega⟩
  have hgapEntries := lemma69_v_typeI_odd_entry_gap_two
    a b D C hfirst (i.val - 1) hpreviousOdd (by omega) hright.le
  have hpCast : p.castSucc =
      (⟨i.val - 1, hiPrevious⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl
  have hpSucc : p.succ =
      (⟨i.val, i.lt_large⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [p, Fin.val_succ]
    omega
  have htargetPrevious : b.order p.castSucc =
      a.order p.castSucc - 2 := by
    rw [hpCast]
    rw [← b.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order]
    have hgap : b.orderSequence.entryOrZero (i.val - 1) =
        a.orderSequence.entryOrZero (i.val - 1) - 2 := by
      omega
    simpa only using hgap
  have halpha := a.alphaValue_le_halfGapValue p
  unfold halfGapValue orderGap at halpha
  rw [hpSucc] at halpha
  have hfinite : a.alphaValue p ≤
      ((a.order ⟨i.val, i.lt_large⟩ -
        b.order ⟨i.val - 1, hiPrevious⟩ : Int) : ℚ) / 2 +
        (ramificationIndex K : ℚ) := by
    rw [← hpCast, htargetPrevious]
    push_cast at halpha ⊢
    linarith
  unfold representationHalfGap
  exact_mod_cast hfinite

end BONG.GoodBONG

end Bong
