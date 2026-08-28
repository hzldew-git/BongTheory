/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019CanonicalApproximation
import Bong.Bong.Beli2019Lemma218

/-!
# Beli (2019), the central replacements in Lemma 3.10

The two replacements are derived from Lemma 2.18's scalar alternatives,
Definition 10's approximation clauses, the quadratic-defect criterion for the
Hilbert symbol, and the three generic parity cycles of Lemma 1.5.
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K] [HilbertSymbolLaws K]
  [DiagonalRepresentationParityLaws K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {m n : Nat}

/-- The target-space replacement in Lemma 3.10(iii), proved from Lemmas 1.5
and 2.18. -/
theorem centralTarget_iff_of_lemma218
    [sourceLaws : Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (m + 1) (n + 1))
    (htrigger : a.centralAlphaTrigger b i)
    (c : Fin ((i.val - 1) + 1) → Kˣ)
    (hc : a.IsSpaceApproximation
      ⟨i.val - 1, by
        have := i.one_lt
        have := i.lt_large
        omega⟩ c) :
    DiagonalRepresents
        (b.prefixValues (i.val - 1) (by
          have := i.le_small_succ
          omega))
        (a.prefixValues i.val (by
          have := i.lt_large
          omega)) ↔
      DiagonalRepresents
        (b.prefixValues (i.val - 1) (by
          have := i.le_small_succ
          omega))
        (diagonalUnitCoefficients c) := by
  let ia : Fin m := ⟨i.val - 1, by
    have := i.one_lt
    have := i.lt_large
    omega⟩
  let ai := a.prefixValueUnits ((i.val - 1) + 1) (by
    have := i.lt_large
    omega)
  let bs := b.prefixValueUnits (i.val - 1) (by
    have := i.le_small_succ
    omega)
  have hi1 : (i.val - 1) + 1 = i.val := by
    have := i.one_lt
    omega
  have originalToUnits
      (hrep : DiagonalRepresents
        (b.prefixValues (i.val - 1) (by
          have := i.le_small_succ
          omega))
        (a.prefixValues i.val (by
          have := i.lt_large
          omega))) :
      DiagonalRepresents (diagonalUnitCoefficients bs)
        (diagonalUnitCoefficients ai) := by
    have hcast : DiagonalRepresents
        (b.prefixValues (i.val - 1) (by
          have := i.le_small_succ
          omega))
        (a.prefixValues ((i.val - 1) + 1) (by
          have := i.lt_large
          omega)) :=
      prefixRepresents_cast b a rfl hi1.symm hrep
    simpa only [bs, ai, diagonalUnitCoefficients_prefixValueUnits] using hcast
  have unitsToOriginal
      (hrep : DiagonalRepresents (diagonalUnitCoefficients bs)
        (diagonalUnitCoefficients ai)) :
      DiagonalRepresents
        (b.prefixValues (i.val - 1) (by
          have := i.le_small_succ
          omega))
        (a.prefixValues i.val (by
          have := i.lt_large
          omega)) := by
    have hcast : DiagonalRepresents
        (b.prefixValues (i.val - 1) (by
          have := i.le_small_succ
          omega))
        (a.prefixValues ((i.val - 1) + 1) (by
          have := i.lt_large
          omega)) := by
      simpa only [bs, ai, diagonalUnitCoefficients_prefixValueUnits] using hrep
    exact prefixRepresents_cast b a rfl hi1 hcast
  have happrox := hc.1.1
  unfold IsPrefixApproximation at happrox
  have hAraw := hdefect i.previous
  rw [a.coe_representationAlphaValue b i.previous] at hAraw
  have hAcap : a.representationAlpha b i.previous ≤
      a.prefixAlphaCap (i.val - 1) :=
    hAraw.trans
      (a.truncatedPrefixDefect_le_leftCap b 1
        i.previous.val i.previous.val)
  have hAdefect : a.representationAlpha b i.previous ≤
      defectOrder (K := K)
        (diagonalUnitDeterminant
            (diagonalUnitTake ai (i.val - 1) (by omega)) *
          diagonalUnitDeterminant bs) := by
    have hraw := hAraw.trans
      (a.truncatedPrefixDefect_le_defect b 1
        i.previous.val i.previous.val)
    simpa only [ai, bs, diagonalUnitTake_prefixValueUnits,
      diagonalUnitDeterminant_prefixValueUnits, one_mul,
      CentralRepresentationIndex.previous] using hraw
  rcases a.beli2019Lemma218_target (sourceLaws := sourceLaws)
      b hdefect i htrigger with hleft | hright
  · have hleftCaps :
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
          a.prefixAlphaCap (i.val - 1) + a.prefixAlphaCap i.val := by
      calc
        _ < a.prefixAlphaCap i.val +
              a.representationAlpha b i.previous := hleft
        _ ≤ a.prefixAlphaCap i.val + a.prefixAlphaCap (i.val - 1) :=
          add_le_add_right hAcap _
        _ = a.prefixAlphaCap (i.val - 1) + a.prefixAlphaCap i.val :=
          add_comm _ _
    have hleftTrigger : a.leftApproximationTrigger ia :=
      a.leftApproximationTrigger_of_prefixCaps ia (by
        simpa only [ia, hi1] using hleftCaps)
    have hp : DiagonalRepresents
        (diagonalUnitCoefficients
          (diagonalUnitTake ai (i.val - 1) (by omega)))
        (diagonalUnitCoefficients c) := by
      simpa only [ai, ia, diagonalUnitTake_prefixValueUnits,
        diagonalUnitCoefficients_prefixValueUnits] using
          hc.1.2 hleftTrigger
    have hAlphaDefect : a.prefixAlphaCap i.val ≤
        defectOrder (K := K)
          (diagonalUnitDeterminant c * diagonalUnitDeterminant ai) := by
      simpa only [ai, hi1, diagonalUnitDeterminant_prefixValueUnits] using
        happrox
    have hs : hilbertSymbol K
        (diagonalUnitDeterminant c * diagonalUnitDeterminant ai)
        (diagonalUnitDeterminant
            (diagonalUnitTake ai (i.val - 1) (by omega)) *
          diagonalUnitDeterminant bs) = 1 :=
      hilbertSymbol_eq_one_of_defectOrder_add_gt_two_mul_e
        (hleft.trans_le (add_le_add hAlphaDefect hAdefect))
    have hpar := EvenTruthParity.second_iff_third_of_first_fourth
      (DiagonalRepresentationParityLaws.caseI c ai bs rfl rfl) hp hs
    constructor
    · intro hrep
      have hq := originalToUnits hrep
      have hr := hpar.mp hq
      simpa only [bs, diagonalUnitCoefficients_prefixValueUnits] using hr
    · intro hrep
      have hr : DiagonalRepresents
          (diagonalUnitCoefficients bs)
          (diagonalUnitCoefficients c) := by
        simpa only [bs, diagonalUnitCoefficients_prefixValueUnits] using hrep
      have hq := hpar.mpr hr
      exact unitsToOriginal hq
  · let aiPlus := a.prefixValueUnits ((i.val - 1) + 2) (by
      have := i.lt_large
      omega)
    have hi2 : (i.val - 1) + 2 = i.val + 1 := by
      have := i.one_lt
      omega
    have hcurrentCap : a.centralCurrentDefect b i ≤
        a.prefixAlphaCap (i.val + 1) :=
      a.truncatedPrefixDefect_le_leftCap b (-1)
        (i.val + 1) (i.val - 1)
    have hrightCaps :
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
          a.prefixAlphaCap i.val + a.prefixAlphaCap (i.val + 1) :=
      hright.trans_le (add_le_add_right hcurrentCap _)
    have hrightTrigger : a.rightApproximationTrigger ia :=
      a.rightApproximationTrigger_of_prefixCaps ia (by
        simpa only [ia, hi1, hi2] using hrightCaps)
    have hp : DiagonalRepresents
        (diagonalUnitCoefficients c)
        (diagonalUnitCoefficients aiPlus) := by
      simpa only [aiPlus, ia, hi2,
        diagonalUnitCoefficients_prefixValueUnits] using
          hc.2.2 hrightTrigger
    have hAlphaDefect : a.prefixAlphaCap i.val ≤
        defectOrder (K := K)
          (diagonalUnitDeterminant
              (diagonalUnitTake aiPlus ((i.val - 1) + 1) (by omega)) *
            diagonalUnitDeterminant c) := by
      simpa only [aiPlus, hi1, diagonalUnitTake_prefixValueUnits,
        diagonalUnitDeterminant_prefixValueUnits, mul_comm] using happrox
    have hCurrentDefect : a.centralCurrentDefect b i ≤
        defectOrder (K := K)
          (-diagonalUnitDeterminant aiPlus * diagonalUnitDeterminant bs) := by
      have hraw := a.truncatedPrefixDefect_le_defect b (-1)
        (i.val + 1) (i.val - 1)
      simpa only [centralCurrentDefect, aiPlus, bs, hi2,
        diagonalUnitDeterminant_prefixValueUnits, neg_mul, one_mul] using hraw
    have hs : hilbertSymbol K
        (diagonalUnitDeterminant
            (diagonalUnitTake aiPlus ((i.val - 1) + 1) (by omega)) *
          diagonalUnitDeterminant c)
        (-diagonalUnitDeterminant aiPlus * diagonalUnitDeterminant bs) = 1 :=
      hilbertSymbol_eq_one_of_defectOrder_add_gt_two_mul_e
        (hright.trans_le (add_le_add hAlphaDefect hCurrentDefect))
    have hpar := EvenTruthParity.second_iff_third_of_first_fourth
      (DiagonalRepresentationParityLaws.caseII aiPlus c bs rfl rfl) hp hs
    constructor
    · intro hrep
      have hrepUnits := originalToUnits hrep
      have hr : DiagonalRepresents
          (diagonalUnitCoefficients bs)
          (diagonalUnitCoefficients
            (diagonalUnitTake aiPlus ((i.val - 1) + 1) (by omega))) := by
        simpa only [ai, aiPlus,
          diagonalUnitTake_prefixValueUnits,
          diagonalUnitCoefficients_prefixValueUnits] using hrepUnits
      have hq := hpar.mpr hr
      simpa only [bs, diagonalUnitCoefficients_prefixValueUnits] using hq
    · intro hrep
      have hq : DiagonalRepresents
          (diagonalUnitCoefficients bs)
          (diagonalUnitCoefficients c) := by
        simpa only [bs, diagonalUnitCoefficients_prefixValueUnits] using hrep
      have hr := hpar.mp hq
      apply unitsToOriginal
      simpa only [ai, aiPlus, diagonalUnitTake_prefixValueUnits,
        diagonalUnitCoefficients_prefixValueUnits] using hr

/-- The source-space replacement in Lemma 3.10(iii), proved from Lemmas 1.5
and 2.18. -/
theorem centralSource_iff_of_lemma218
    [targetLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (m + 1) (n + 1))
    (htrigger : a.centralAlphaTrigger b i)
    (hsource : i.val - 1 < n + 1)
    (c : Fin ((i.val - 1) + 1) → Kˣ)
    (d : Fin ((i.val - 2) + 1) → Kˣ)
    (hc : a.IsSpaceApproximation
      ⟨i.val - 1, by
        have := i.one_lt
        have := i.lt_large
        omega⟩ c)
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
  let ia : Fin m := ⟨i.val - 1, by
    have := i.one_lt
    have := i.lt_large
    omega⟩
  let ib : Fin n := ⟨i.val - 2, by
    have := i.one_lt
    have := hsource
    omega⟩
  let bi := b.prefixValueUnits ((i.val - 1) + 1) (by
    have := hsource
    omega)
  let bp := b.prefixValueUnits (i.val - 1) (by
    have := i.le_small_succ
    omega)
  have hi0 : (i.val - 2) + 1 = i.val - 1 := by
    have := i.one_lt
    omega
  have hi1 : (i.val - 1) + 1 = i.val := by
    have := i.one_lt
    omega
  have hi2 : (i.val - 2) + 2 = (i.val - 1) + 1 := by
    have := i.one_lt
    omega
  have hcDet : a.IsPrefixApproximation i.val
      (diagonalUnitDeterminant c) := by
    simpa only [ia, hi1] using hc.1.1
  have hdDet : b.IsPrefixApproximation (i.val - 1)
      (diagonalUnitDeterminant d) := by
    simpa only [ib, hi0] using hd.1.1
  have hAraw := hdefect (i.current (by omega))
  rw [a.coe_representationAlphaValue b (i.current (by omega))] at hAraw
  change a.representationAlpha b (i.current (by omega)) ≤
    a.truncatedPrefixDefect b 1 i.val i.val at hAraw
  have hAcap : a.representationAlpha b (i.current (by omega)) ≤
      b.prefixAlphaCap i.val :=
    hAraw.trans
      (a.truncatedPrefixDefect_le_rightCap b 1 i.val i.val)
  have hAdefect : a.representationAlpha b (i.current (by omega)) ≤
      defectOrder (K := K)
        (diagonalUnitDeterminant c * diagonalUnitDeterminant bi) := by
    have heq := a.truncatedPrefixDefect_eq_of_approximations b 1
      i.val i.val (diagonalUnitDeterminant c) (b.prefixProduct i.val)
      hcDet (b.isPrefixApproximation_prefixProduct i.val)
    have hraw : a.representationAlpha b (i.current (by omega)) ≤
        defectOrder (K := K)
          (1 * diagonalUnitDeterminant c * b.prefixProduct i.val) := by
      rw [heq] at hAraw
      exact hAraw.trans (min_le_left _ _)
    simpa only [bi, hi1, diagonalUnitDeterminant_prefixValueUnits,
      one_mul] using hraw
  have hbeta : b.prefixAlphaCap (i.val - 1) ≤
      defectOrder (K := K)
        (diagonalUnitDeterminant d * b.prefixProduct (i.val - 1)) := by
    unfold IsPrefixApproximation at hdDet
    exact hdDet
  rcases a.beli2019Lemma218_source (targetLaws := targetLaws)
      b hdefect i htrigger hsource with hright | hleft
  · have hrightCaps :
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
          b.prefixAlphaCap (i.val - 1) + b.prefixAlphaCap i.val :=
      hright.trans_le (add_le_add_right hAcap _)
    have hrightTrigger : b.rightApproximationTrigger ib :=
      b.rightApproximationTrigger_of_prefixCaps ib (by
        simpa only [ib, hi0, hi1, hi2] using hrightCaps)
    have hqRaw := hd.2.2 hrightTrigger
    have hqCast : DiagonalRepresents (diagonalUnitCoefficients d)
        (b.prefixValues ((i.val - 1) + 1) (by
          have := hsource
          omega)) :=
      targetPrefixRepresents_cast (diagonalUnitCoefficients d) b hi2 hqRaw
    have hq : DiagonalRepresents (diagonalUnitCoefficients d)
        (diagonalUnitCoefficients bi) := by
      simpa only [bi, diagonalUnitCoefficients_prefixValueUnits] using hqCast
    have hbetaDefect : b.prefixAlphaCap (i.val - 1) ≤
        defectOrder (K := K)
          (diagonalUnitDeterminant
              (diagonalUnitTake bi ((i.val - 2) + 1) (by omega)) *
            diagonalUnitDeterminant d) := by
      simpa only [bi, hi0, diagonalUnitTake_prefixValueUnits,
        diagonalUnitDeterminant_prefixValueUnits, mul_comm] using hbeta
    have hs : hilbertSymbol K
        (diagonalUnitDeterminant c * diagonalUnitDeterminant bi)
        (diagonalUnitDeterminant
            (diagonalUnitTake bi ((i.val - 2) + 1) (by omega)) *
          diagonalUnitDeterminant d) = 1 :=
      hilbertSymbol_eq_one_of_defectOrder_add_gt_two_mul_e
        (by
          rw [add_comm]
          exact hright.trans_le (add_le_add hbetaDefect hAdefect))
    have hpar := EvenTruthParity.first_iff_third_of_second_fourth
      (DiagonalRepresentationParityLaws.caseI c bi d rfl hi2) hq hs
    constructor
    · intro hrep
      have hpCast : DiagonalRepresents
          (b.prefixValues ((i.val - 2) + 1) (by
            have := i.le_small_succ
            omega))
          (diagonalUnitCoefficients c) :=
        sourcePrefixRepresents_cast b (diagonalUnitCoefficients c)
          hi0.symm hrep
      have hp : DiagonalRepresents
          (diagonalUnitCoefficients
            (diagonalUnitTake bi ((i.val - 2) + 1) (by omega)))
          (diagonalUnitCoefficients c) := by
        simpa only [bi, diagonalUnitTake_prefixValueUnits,
          diagonalUnitCoefficients_prefixValueUnits] using hpCast
      exact hpar.mp hp
    · intro hrep
      have hp := hpar.mpr hrep
      have hpCast : DiagonalRepresents
          (b.prefixValues ((i.val - 2) + 1) (by
            have := i.le_small_succ
            omega))
          (diagonalUnitCoefficients c) := by
        simpa only [bi, diagonalUnitTake_prefixValueUnits,
          diagonalUnitCoefficients_prefixValueUnits] using hp
      exact sourcePrefixRepresents_cast b (diagonalUnitCoefficients c)
        hi0 hpCast
  · have hpreviousCap : a.centralPreviousDefect b i ≤
        b.prefixAlphaCap (i.val - 2) :=
      a.truncatedPrefixDefect_le_rightCap b (-1)
        i.val (i.val - 2)
    have hleftCaps :
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
          b.prefixAlphaCap (i.val - 2) +
            b.prefixAlphaCap (i.val - 1) := by
      calc
        _ < b.prefixAlphaCap (i.val - 1) +
              a.centralPreviousDefect b i := hleft
        _ ≤ b.prefixAlphaCap (i.val - 1) +
              b.prefixAlphaCap (i.val - 2) :=
          add_le_add_right hpreviousCap _
        _ = b.prefixAlphaCap (i.val - 2) +
              b.prefixAlphaCap (i.val - 1) := add_comm _ _
    have hleftTrigger : b.leftApproximationTrigger ib :=
      b.leftApproximationTrigger_of_prefixCaps ib (by
        simpa only [ib, hi0] using hleftCaps)
    have hqRaw := hd.1.2 hleftTrigger
    have hq : DiagonalRepresents
        (diagonalUnitCoefficients
          (diagonalUnitTake bp (i.val - 2) (by omega)))
        (diagonalUnitCoefficients d) := by
      simpa only [bp, ib, diagonalUnitTake_prefixValueUnits,
        diagonalUnitCoefficients_prefixValueUnits] using hqRaw
    have hbetaDefect : b.prefixAlphaCap (i.val - 1) ≤
        defectOrder (K := K)
          (diagonalUnitDeterminant d * diagonalUnitDeterminant bp) := by
      simpa only [bp, diagonalUnitDeterminant_prefixValueUnits] using hbeta
    have hPreviousDefect : a.centralPreviousDefect b i ≤
        defectOrder (K := K)
          (-diagonalUnitDeterminant c *
            diagonalUnitDeterminant
              (diagonalUnitTake bp (i.val - 2) (by omega))) := by
      have heq := a.truncatedPrefixDefect_eq_of_approximations b (-1)
        i.val (i.val - 2) (diagonalUnitDeterminant c)
        (b.prefixProduct (i.val - 2)) hcDet
        (b.isPrefixApproximation_prefixProduct (i.val - 2))
      unfold centralPreviousDefect
      rw [heq]
      unfold truncatedApproximationDefect
      refine (min_le_left _ _).trans ?_
      simp only [bp, diagonalUnitTake_prefixValueUnits,
        diagonalUnitDeterminant_prefixValueUnits, neg_mul, one_mul]
      exact le_rfl
    have hs : hilbertSymbol K
        (diagonalUnitDeterminant d * diagonalUnitDeterminant bp)
        (-diagonalUnitDeterminant c *
          diagonalUnitDeterminant
            (diagonalUnitTake bp (i.val - 2) (by omega))) = 1 :=
      hilbertSymbol_eq_one_of_defectOrder_add_gt_two_mul_e
        (hleft.trans_le (add_le_add hbetaDefect hPreviousDefect))
    have hba : ((i.val - 2) + 1) + 1 = (i.val - 1) + 1 := by omega
    have hcb : i.val - 1 = (i.val - 2) + 1 := hi0.symm
    have hlc : (i.val - 2) + 1 = i.val - 1 := hi0
    have hpar := EvenTruthParity.first_iff_third_of_second_fourth
      (DiagonalRepresentationParityLaws.caseIII c d bp hba hcb hlc) hq hs
    constructor
    · intro hrep
      have hr : DiagonalRepresents (diagonalUnitCoefficients bp)
          (diagonalUnitCoefficients c) := by
        simpa only [bp, diagonalUnitCoefficients_prefixValueUnits] using hrep
      exact hpar.mpr hr
    · intro hrep
      have hr := hpar.mp hrep
      simpa only [bp, diagonalUnitCoefficients_prefixValueUnits] using hr

end BONG.GoodBONG

end Bong
