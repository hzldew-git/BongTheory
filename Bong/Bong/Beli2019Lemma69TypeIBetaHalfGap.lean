/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma69TypeIBetaSecondary

/-!
# Beli (2019), Lemma 6.9(ii): type-I beta half-gap candidate

The even entry immediately before an odd type-I boundary differs by two.
The common weight endpoint therefore translates the source alpha bound into
the half-gap bound required for the target alpha.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- At an odd central type-I boundary, the target alpha is no larger than
the half-gap candidate in Definition 4. -/
theorem lemma69_typeI_beta_le_halfGap
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hfirst : D.profile.first = 0)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hodd : Odd i.val) (hiTwo : 1 < i.val)
    (hleft : C.leftSwitch ≤ i.val - 1)
    (hright : i.val - 1 < C.rightSwitch)
    (hweight : a.alphaLeftEndpoint ⟨i.val - 1, by
        have hi := i.lt_large
        omega⟩ =
      b.alphaLeftEndpoint ⟨i.val - 1, by
        have hi := i.lt_large
        omega⟩) :
    (b.alphaValue ⟨i.val - 1, by
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
  rcases hodd with ⟨d, hd⟩
  have hpEven : Even p.val := ⟨d, by simp only [p]; omega⟩
  have hgapEntries := lemma69_v_typeI_even_entry_gap_two
    a b D C hfirst p.val hpEven (by simpa only [p] using hleft) (by
      simp only [p]
      omega)
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
      a.order p.castSucc + 2 := by
    rw [hpCast]
    rw [← b.orderSequence_entryOrZero_eq_order,
      ← a.orderSequence_entryOrZero_eq_order]
    simpa only [p] using hgapEntries
  have hbetaSource : b.alphaValue p = a.alphaValue p - 2 := by
    unfold alphaLeftEndpoint at hweight
    change (a.order p.castSucc : ℚ) + a.alphaValue p =
      (b.order p.castSucc : ℚ) + b.alphaValue p at hweight
    rw [htargetPrevious] at hweight
    push_cast at hweight ⊢
    linarith
  have halpha := a.alphaValue_le_halfGapValue p
  unfold halfGapValue orderGap at halpha
  rw [hpSucc] at halpha
  have hfinite : b.alphaValue p ≤
      ((a.order ⟨i.val, i.lt_large⟩ -
        b.order ⟨i.val - 1, hiPrevious⟩ : Int) : ℚ) / 2 +
        (ramificationIndex K : ℚ) := by
    rw [← hpCast, htargetPrevious]
    push_cast at halpha ⊢
    linarith [hbetaSource]
  unfold representationHalfGap
  exact_mod_cast hfinite

end BONG.GoodBONG

end Bong
