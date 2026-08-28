/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019CanonicalApproximation
import Bong.Bong.Beli2019Corollary311
import Bong.Bong.Beli2019OddPrefixDefect
import Bong.Bong.DiagonalCodimensionOneCancellation

/-!
# Beli (2019), the long-prefix replacements in Lemma 3.10

The inequalities in condition (iv) force the relevant order gaps, and hence
the corresponding alpha values, strictly above `2e`.  The determinant of an
approximating space therefore has the same square class as the BONG prefix.
Its right-approximation clause embeds it in the next prefix, so generic Witt
cancellation identifies the two equal-rank diagonal spaces.
-/

namespace Bong

open Dyadic

universe u v w

/-- A defect strictly beyond the dyadic threshold has square class one. -/
theorem isSquare_of_two_mul_e_lt_defectOrder
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] [HilbertSymbolLaws K]
    {x : Kˣ}
    (h : (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
      BONG.GoodBONG.defectOrder (K := K) x) :
    IsSquare x := by
  apply HilbertSymbolLaws.nondegenerate
  intro y
  apply hilbertSymbol_eq_one_of_defectOrder_add_gt_two_mul_e
  exact h.trans_le
    (le_add_of_nonneg_right (BONG.GoodBONG.defectOrder_nonneg y))

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K] [HilbertSymbolLaws K]
  [DiagonalCodimensionOneCancellationLaws K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {m n : Nat}

/-- The target-space replacement in Lemma 3.10(iv). -/
theorem longTarget_iff_of_cancellation
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : LongRepresentationIndex (m + 1) (n + 1))
    (htrigger : a.longRepresentationTrigger b i)
    (c : Fin (i.val + 1) → Kˣ)
    (hc : a.IsSpaceApproximation
      ⟨i.val, by have := i.succ_lt_large; omega⟩ c) :
    DiagonalRepresents
        (b.prefixValues (i.val - 1) (by
          have := i.le_small_succ
          omega))
        (a.prefixValues (i.val + 1) (by
          have := i.succ_lt_large
          omega)) ↔
      DiagonalRepresents
        (b.prefixValues (i.val - 1) (by
          have := i.le_small_succ
          omega))
        (diagonalUnitCoefficients c) := by
  have hilarge := i.succ_lt_large
  unfold longRepresentationTrigger at htrigger
  rcases htrigger with ⟨_, hmiddle, hleft⟩
  let ia : Fin m := ⟨i.val, by omega⟩
  have hchain :
      a.order ⟨i.val, by omega⟩ +
          2 * (ramificationIndex K : Int) <
        a.order ⟨i.val + 1, by omega⟩ := by
    omega
  have hgap : 2 * (ramificationIndex K : Int) < a.orderGap ia := by
    unfold orderGap
    have hsucc : ia.succ = ⟨i.val + 1, by omega⟩ := by
      apply Fin.ext
      rfl
    have hcast : ia.castSucc = ⟨i.val, by omega⟩ := by
      apply Fin.ext
      rfl
    rw [hsucc, hcast]
    omega
  have halpha : 2 * (ramificationIndex K : ℚ) < a.alphaValue ia :=
    (a.alpha_p5 ia).2.2.mpr hgap
  have hcap : a.prefixAlphaCap (i.val + 1) =
      (a.alphaValue ia : WithTop ℚ) := by
    rw [a.prefixAlphaCap_of_internal (by omega) (by omega)]
    congr 2
  have hdetBound :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        defectOrder (K := K)
          (diagonalUnitDeterminant c * a.prefixProduct (i.val + 1)) := by
    have halphaTop :
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
          (a.alphaValue ia : WithTop ℚ) := by
      exact_mod_cast halpha
    apply halphaTop.trans_le
    rw [← hcap]
    exact hc.1.1
  have hsquareRaw : IsSquare
      (diagonalUnitDeterminant c * a.prefixProduct (i.val + 1)) :=
    Bong.isSquare_of_two_mul_e_lt_defectOrder hdetBound
  have hrightCaps :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        a.prefixAlphaCap (i.val + 1) +
          a.prefixAlphaCap (i.val + 2) := by
    have hfirst :
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
          a.prefixAlphaCap (i.val + 1) := by
      rw [hcap]
      exact_mod_cast halpha
    exact hfirst.trans_le
      (le_add_of_nonneg_right (a.prefixAlphaCap_nonneg (i.val + 2)))
  have hright : a.rightApproximationTrigger ia :=
    a.rightApproximationTrigger_of_prefixCaps ia (by
      simpa only [ia] using hrightCaps)
  let base := a.prefixValueUnits (i.val + 1) (by omega)
  let extended := a.prefixValueUnits (i.val + 2) (by omega)
  have hrepExtended : DiagonalRepresents
      (diagonalUnitCoefficients c)
      (diagonalUnitCoefficients extended) := by
    simpa only [extended, diagonalUnitCoefficients_prefixValueUnits] using
      hc.2.2 hright
  have hprefix : diagonalUnitPrefix extended = base := by
    simpa only [extended, base] using
      a.diagonalUnitPrefix_prefixValueUnits (i.val + 1) (by omega)
  have hsquare : IsSquare
      (diagonalUnitDeterminant c * diagonalUnitDeterminant base) := by
    simpa only [base, diagonalUnitDeterminant_prefixValueUnits] using
      hsquareRaw
  have hcaUnits : DiagonalRepresents
      (diagonalUnitCoefficients c) (diagonalUnitCoefficients base) :=
    DiagonalCodimensionOneCancellationLaws.cancel
      base c extended hprefix hrepExtended hsquare
  have hacUnits := DiagonalRepresents.symm_of_sameRank hcaUnits
  have hca : DiagonalRepresents (diagonalUnitCoefficients c)
      (a.prefixValues (i.val + 1) (by omega)) := by
    simpa only [base, diagonalUnitCoefficients_prefixValueUnits] using hcaUnits
  have hac : DiagonalRepresents
      (a.prefixValues (i.val + 1) (by omega))
      (diagonalUnitCoefficients c) := by
    simpa only [base, diagonalUnitCoefficients_prefixValueUnits] using hacUnits
  exact ⟨fun h ↦ h.trans hac, fun h ↦ h.trans hca⟩

/-- The source-space replacement in Lemma 3.10(iv). -/
theorem longSource_iff_of_cancellation
    [targetLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i : LongRepresentationIndex (m + 1) (n + 1))
    (htrigger : a.longRepresentationTrigger b i)
    (hsource : i.val - 1 < n + 1)
    (c : Fin (i.val + 1) → Kˣ)
    (d : Fin ((i.val - 2) + 1) → Kˣ)
    (_hc : a.IsSpaceApproximation
      ⟨i.val, by have := i.succ_lt_large; omega⟩ c)
    (hd : b.IsSpaceApproximation
      ⟨i.val - 2, by
        have := i.one_lt
        have := hsource
        omega⟩ d) :
    DiagonalRepresents
        (b.prefixValues (i.val - 1) (by
          have := i.le_small_succ
          omega))
        (diagonalUnitCoefficients c) ↔
      DiagonalRepresents (diagonalUnitCoefficients d)
        (diagonalUnitCoefficients c) := by
  have hsmall := i.le_small_succ
  have hone := i.one_lt
  have hi : i.val ≤ n + 1 := by omega
  unfold longRepresentationTrigger at htrigger
  rcases htrigger with ⟨hupper, hmiddle, _⟩
  have hupper' :
      a.order ⟨i.val + 1, i.succ_lt_large⟩ ≤
        b.order ⟨i.val - 1, by omega⟩ := by
    simpa only [dif_pos hi] using hupper
  let ib : Fin n := ⟨i.val - 2, by omega⟩
  have hchain :
      b.order ⟨i.val - 2, by omega⟩ +
          2 * (ramificationIndex K : Int) <
        b.order ⟨i.val - 1, by omega⟩ :=
    hmiddle.trans_le hupper'
  have hgap : 2 * (ramificationIndex K : Int) < b.orderGap ib := by
    unfold orderGap
    have hsucc : ib.succ = ⟨i.val - 1, by omega⟩ := by
      apply Fin.ext
      change i.val - 2 + 1 = i.val - 1
      omega
    have hcast : ib.castSucc = ⟨i.val - 2, by omega⟩ := by
      apply Fin.ext
      rfl
    rw [hsucc, hcast]
    omega
  have hbeta : 2 * (ramificationIndex K : ℚ) < b.alphaValue ib :=
    (b.alpha_p5 ib).2.2.mpr hgap
  have hcap : b.prefixAlphaCap (ib.val + 1) =
      (b.alphaValue ib : WithTop ℚ) := by
    rw [b.prefixAlphaCap_of_internal (by omega) (by omega)]
    congr 2
  have hdetBound :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        defectOrder (K := K)
          (diagonalUnitDeterminant d * b.prefixProduct (ib.val + 1)) := by
    have hbetaTop :
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
          (b.alphaValue ib : WithTop ℚ) := by
      exact_mod_cast hbeta
    apply hbetaTop.trans_le
    rw [← hcap]
    exact hd.1.1
  have hsquareRaw : IsSquare
      (diagonalUnitDeterminant d * b.prefixProduct (ib.val + 1)) :=
    Bong.isSquare_of_two_mul_e_lt_defectOrder hdetBound
  have hrightCaps :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        b.prefixAlphaCap (ib.val + 1) +
          b.prefixAlphaCap (ib.val + 2) := by
    have hfirst :
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
          b.prefixAlphaCap (ib.val + 1) := by
      rw [hcap]
      exact_mod_cast hbeta
    exact hfirst.trans_le
      (le_add_of_nonneg_right (b.prefixAlphaCap_nonneg (ib.val + 2)))
  have hright : b.rightApproximationTrigger ib :=
    b.rightApproximationTrigger_of_prefixCaps ib hrightCaps
  let base := b.prefixValueUnits (ib.val + 1) (by omega)
  let extended := b.prefixValueUnits (ib.val + 2) (by omega)
  have hrepExtended : DiagonalRepresents
      (diagonalUnitCoefficients d)
      (diagonalUnitCoefficients extended) := by
    simpa only [extended, diagonalUnitCoefficients_prefixValueUnits] using
      hd.2.2 hright
  have hprefix : diagonalUnitPrefix extended = base := by
    simpa only [extended, base] using
      b.diagonalUnitPrefix_prefixValueUnits (ib.val + 1) (by omega)
  have hsquare : IsSquare
      (diagonalUnitDeterminant d * diagonalUnitDeterminant base) := by
    simpa only [base, diagonalUnitDeterminant_prefixValueUnits] using
      hsquareRaw
  have hdbUnits : DiagonalRepresents
      (diagonalUnitCoefficients d) (diagonalUnitCoefficients base) :=
    DiagonalCodimensionOneCancellationLaws.cancel
      base d extended hprefix hrepExtended hsquare
  have hbdUnits := DiagonalRepresents.symm_of_sameRank hdbUnits
  have hi0 : ib.val + 1 = i.val - 1 := by
    dsimp only [ib]
    omega
  have hdbRaw : DiagonalRepresents (diagonalUnitCoefficients d)
      (b.prefixValues (ib.val + 1) (by omega)) := by
    simpa only [base, diagonalUnitCoefficients_prefixValueUnits] using hdbUnits
  have hbdRaw : DiagonalRepresents
      (b.prefixValues (ib.val + 1) (by omega))
      (diagonalUnitCoefficients d) := by
    simpa only [base, diagonalUnitCoefficients_prefixValueUnits] using hbdUnits
  have hdb : DiagonalRepresents (diagonalUnitCoefficients d)
      (b.prefixValues (i.val - 1) (by omega)) :=
    targetPrefixRepresents_cast (diagonalUnitCoefficients d) b hi0 hdbRaw
  have hbd : DiagonalRepresents
      (b.prefixValues (i.val - 1) (by omega))
      (diagonalUnitCoefficients d) :=
    sourcePrefixRepresents_cast b (diagonalUnitCoefficients d) hi0 hbdRaw
  exact ⟨fun h ↦ hdb.trans h, fun h ↦ hbd.trans h⟩

end BONG.GoodBONG

end Bong
