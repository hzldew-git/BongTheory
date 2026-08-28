/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma912TypeIAssembly
import Bong.Bong.Beli2019Corollary811
import Bong.Bong.Beli2019Lemma814HigherRankUnequal
import Bong.Bong.Beli2019Lemma99Sufficiency
import Bong.Bong.Beli2019Lemma711
import Bong.Bong.Beli2019Lemma73

/-!
# Beli (2019), Lemma 9.12: normalization of the type-III branch

In the remaining branch of Lemma 9.12, the first and third orders agree and
the second alpha is one.  The paper first changes the initial ternary BONG so
that its second literal adjacent defect is the first alpha.  This file carries
out that normalization inside the original lattice.

The construction uses Corollary 8.11 to realize the first alpha literally,
Lemma 9.9 (including its `moreover` clause) to realize the second literal
defect, Lemma 7.11 to identify the two ternary lattices, and Lemma 4.9 to put
the normalized ternary segment back into the ambient BONG.  The resulting
boundary equality is exactly the hypothesis needed for Lemma 9.11.
-/

namespace Bong

open Dyadic
open Module

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {N : Nat}

/-- The normalized source BONG in the type-III branch.  Its lattice is
literally the original lattice, its order and alpha sequences are unchanged,
and the second adjacent pair satisfies the boundary equation of Lemma 9.11. -/
structure Beli2019Lemma912TypeIIINormalizationData
    (a : GoodBONG q L (N + 5)) where
  transformed : GoodBONG q L (N + 5)
  sameOrders : a.SameOrders transformed
  sameAlphas : a.SameAlphas transformed
  pairBoundary :
    (((transformed.orderGap (1 : Fin (N + 4)) : Int) : ℚ) : WithTop ℚ) +
        transformed.adjacentDefect (1 : Fin (N + 4)) = 1

/-- In the type-III branch, equality of the first alphas forces the source
second order to be exactly one above the target second order.  This is the
`T₂ = R₂ + 1` assertion used in the paper before invoking Lemma 9.11. -/
theorem beli2019Lemma912_sourceSecond_eq_add_one_of_typeIII
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    [parityW : Beli2009AlphaParityLaws.{u, w} K]
    (a : GoodBONG q L (N + 5)) (c : GoodBONG r M (N + 5))
    (profile : Beli2019Lemma912InitialProfile a c)
    (hfirst : a.order (0 : Fin (N + 5)) =
      c.order (0 : Fin (N + 5)))
    (hparams : Beli2019Lemma912TypeIIIParameters a c) :
    c.order (1 : Fin (N + 5)) = a.order (1 : Fin (N + 5)) + 1 := by
  letI : Beli2006AlphaLaws.{u, v} K := alphaV
  have hremark := a.beli2019Remark87 (0 : Fin (N + 3)) profile.firstThird_eq
  have hformula := hremark.previousAlpha_eq
  change a.alphaValue (0 : Fin (N + 4)) =
    ((a.order (1 : Fin (N + 5)) - a.order (2 : Fin (N + 5)) : Int) : ℚ) +
      a.alphaValue (1 : Fin (N + 4)) at hformula
  rw [← profile.firstThird_eq, hparams.2.2] at hformula
  have hsourceAlpha : c.alphaValue (0 : Fin (N + 4)) =
      a.alphaValue (0 : Fin (N + 4)) := hparams.2.1.symm
  have hcAlphaLe : c.alphaValue (0 : Fin (N + 4)) ≤
      2 * (ramificationIndex K : ℚ) := by
    rw [hsourceAlpha, hformula]
    have hgap := profile.firstGap_le_twoE_sub_two
    unfold orderGap at hgap
    change a.order (1 : Fin (N + 5)) - a.order (0 : Fin (N + 5)) ≤
      2 * (ramificationIndex K : Int) - 2 at hgap
    push_cast
    exact_mod_cast (show
      a.order (1 : Fin (N + 5)) - a.order (0 : Fin (N + 5)) + 1 ≤
        2 * (ramificationIndex K : Int) by omega)
  letI : Beli2006AlphaLaws.{u, w} K := alphaW
  letI : Beli2009AlphaParityLaws.{u, w} K := parityW
  have hcGapLe : c.orderGap (0 : Fin (N + 4)) ≤
      2 * (ramificationIndex K : Int) :=
    (c.alphaValue_le_twoE_iff_orderGap_le_twoE
      (0 : Fin (N + 4))).mp hcAlphaLe
  have hcGapAlpha := (c.alpha_p3 (0 : Fin (N + 4)) hcGapLe).1
  have hgapUpper : c.orderGap (0 : Fin (N + 4)) ≤
      a.orderGap (0 : Fin (N + 4)) + 1 := by
    rw [hsourceAlpha, hformula] at hcGapAlpha
    unfold orderGap at hcGapAlpha ⊢
    exact_mod_cast hcGapAlpha
  unfold orderGap at hgapUpper
  change c.order (1 : Fin (N + 5)) - c.order (0 : Fin (N + 5)) ≤
    (a.order (1 : Fin (N + 5)) - a.order (0 : Fin (N + 5))) + 1 at hgapUpper
  rw [← hfirst] at hgapUpper
  have hlower := profile.second_lt_sourceSecond
  omega

/-- Consequently the fifth target order is strictly above the first in the
type-III branch, as required for the two-step goodness inequality after the
third coefficient is shifted. -/
theorem beli2019Lemma912_first_lt_fifth_of_typeIII
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [alphaW : Beli2006AlphaLaws.{u, w} K]
    [parityW : Beli2009AlphaParityLaws.{u, w} K]
    (a : GoodBONG q L (N + 5)) (c : GoodBONG r M (N + 5))
    (profile : Beli2019Lemma912InitialProfile a c)
    (hfirst : a.order (0 : Fin (N + 5)) =
      c.order (0 : Fin (N + 5)))
    (hparams : Beli2019Lemma912TypeIIIParameters a c) :
    a.order (0 : Fin (N + 5)) < a.order (4 : Fin (N + 5)) :=
  profile.sourceSecond_eq_add_one_imp_first_lt_fifth
    (beli2019Lemma912_sourceSecond_eq_add_one_of_typeIII
      (alphaV := alphaV) (alphaW := alphaW) (parityW := parityW)
      a c profile hfirst hparams)

set_option maxHeartbeats 4000000 in
/-- Type-III normalization in the proof of Beli (2019), Lemma 9.12.

The comparison BONG occurs only through the initial profile; all changes are
performed on the target BONG `a`. -/
theorem exists_beli2019Lemma912TypeIIINormalizationData
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [DyadicDiagonalClassificationLaws K]
    (a : GoodBONG q L (N + 5)) (c : GoodBONG r M (N + 5))
    (profile : Beli2019Lemma912InitialProfile a c)
    (hsecond : a.alphaValue (1 : Fin (N + 4)) = 1) :
    Nonempty (Beli2019Lemma912TypeIIINormalizationData a) := by
  rcases a.beli2019Corollary811 (0 : Fin (N + 4)) with ⟨C⟩
  let a₀ := C.transformed
  have horders₀ : a.SameOrders a₀ := a.order_invariant a₀
  have halphas₀ : a.SameAlphas a₀ := a.alpha_invariant a₀
  have hfirstBinary : a₀.firstBinaryAlpha =
      (a₀.alphaValue (0 : Fin (N + 4)) : WithTop ℚ) := by
    rw [← a₀.adjacentBinaryAlpha_zero]
    exact C.adjacentBinaryAlpha_eq
  let s := a₀.lemma814InitialThree
  have hsFirst : s.alphaValue (0 : Fin 2) =
      a₀.alphaValue (0 : Fin (N + 4)) :=
    a₀.lemma814InitialThree_firstAlpha_eq hfirstBinary
  have houter₀ : a₀.order (0 : Fin (N + 5)) =
      a₀.order (2 : Fin (N + 5)) := by
    calc
      a₀.order (0 : Fin (N + 5)) = a.order 0 := (horders₀ 0).symm
      _ = a.order 2 := profile.firstThird_eq
      _ = a₀.order (2 : Fin (N + 5)) := horders₀ 2
  have hsecond₀ : a₀.alphaValue (1 : Fin (N + 4)) = 1 :=
    (halphas₀ 1).symm.trans hsecond
  have hsOuter : s.order (0 : Fin 3) = s.order (2 : Fin 3) := by
    rw [a₀.lemma814InitialThree_order_eq,
      a₀.lemma814InitialThree_order_eq]
    exact houter₀
  have hsSecond : s.alphaValue (1 : Fin 2) =
      a₀.alphaValue (1 : Fin (N + 4)) := by
    have hg := a₀.beli2019Remark87 (0 : Fin (N + 3)) houter₀
    have hl := s.beli2019Remark87 (0 : Fin 1) hsOuter
    have hg' := hg.previousAlpha_eq
    have hl' := hl.previousAlpha_eq
    change a₀.alphaValue (0 : Fin (N + 4)) =
      ((a₀.order (1 : Fin (N + 5)) -
        a₀.order (2 : Fin (N + 5)) : Int) : ℚ) +
        a₀.alphaValue (1 : Fin (N + 4)) at hg'
    change s.alphaValue (0 : Fin 2) =
      ((s.order (1 : Fin 3) - s.order (2 : Fin 3) : Int) : ℚ) +
        s.alphaValue (1 : Fin 2) at hl'
    rw [hsFirst,
      a₀.lemma814InitialThree_order_eq (1 : Fin 3),
      a₀.lemma814InitialThree_order_eq (2 : Fin 3)] at hl'
    have hone : (⟨(1 : Fin 3).1, by omega⟩ : Fin (N + 5)) =
        (1 : Fin (N + 5)) := by
      apply Fin.ext
      rfl
    have htwo : (⟨(2 : Fin 3).1, by omega⟩ : Fin (N + 5)) =
        (2 : Fin (N + 5)) := by
      apply Fin.ext
      rfl
    rw [hone, htwo] at hl'
    linarith
  let R₁ : Int := a₀.order (0 : Fin (N + 5))
  let R₂ : Int := a₀.order (1 : Fin (N + 5))
  let A : Int := R₂ - R₁ + 1
  have hfirstFormula : a₀.alphaValue (0 : Fin (N + 4)) = (A : ℚ) := by
    have hg := a₀.beli2019Remark87 (0 : Fin (N + 3)) houter₀
    have hg' := hg.previousAlpha_eq
    change a₀.alphaValue (0 : Fin (N + 4)) =
      ((a₀.order (1 : Fin (N + 5)) -
        a₀.order (2 : Fin (N + 5)) : Int) : ℚ) +
        a₀.alphaValue (1 : Fin (N + 4)) at hg'
    rw [houter₀.symm, hsecond₀] at hg'
    dsimp only [A, R₁, R₂]
    push_cast at hg' ⊢
    linarith
  have hsFirstFormula : s.alphaValue (0 : Fin 2) = (A : ℚ) :=
    hsFirst.trans hfirstFormula
  have hgapEven₀ : Even (R₂ - R₁) := by
    have hgapEven := profile.firstGap_even
    unfold orderGap at hgapEven
    change Even
      (a.order (1 : Fin (N + 5)) - a.order (0 : Fin (N + 5))) at hgapEven
    simpa only [R₁, R₂, horders₀ (0 : Fin (N + 5)),
      horders₀ (1 : Fin (N + 5))] using hgapEven
  have hAOdd : Odd A := by
    rcases hgapEven₀ with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    dsimp only [A]
    omega
  have hrefOrders : ∀ i : Fin 3, s.order i = ![R₁, R₂, R₁] i := by
    intro i
    fin_cases i <;>
      simp [s, R₁, R₂, a₀.lemma814InitialThree_order_eq, houter₀]
    apply congrArg a₀.order
    apply Fin.ext
    rfl
  have C₉₉ := Beli2019Lemma99Conditions.ofReferenceInvariants.{u, v}
    s R₁ R₂ A hrefOrders hsFirstFormula
  rcases beli2019Lemma99_moreover s R₁ R₂ R₁ A rfl hAOdd C₉₉ with
    ⟨D, hDDefect⟩
  have hsameOrders : s.SameOrders D.bong := by
    intro i
    rw [hrefOrders i, D.orders i]
  have hfirstSD : s.alphaValue (0 : Fin 2) =
      D.bong.alphaValue (0 : Fin 2) :=
    hsFirstFormula.trans D.firstAlpha.symm
  rcases (s.beli2019Lemma711 D.bong hsameOrders hsOuter).2 hfirstSD with ⟨f⟩
  let t : GoodBONG
      (q.restrict a₀.lemma814InitialThreeSegment.carrier
        a₀.lemma814InitialThreeSegment.nondegenerate)
      a₀.lemma814InitialThreeSegment.lattice 3 :=
    D.bong.mapLatticeIsometry f.symm
  have htValues : ∀ i, t.valueUnit i = D.bong.valueUnit i := by
    intro i
    apply Units.ext
    change (D.bong.toBONG.mapLatticeIsometry f.symm).value i =
      D.bong.toBONG.value i
    exact BONG.value_mapLatticeIsometry f.symm D.bong.toBONG i
  have htDefect : t.adjacentDefect (1 : Fin 2) =
      ((A : ℚ) : WithTop ℚ) := by
    unfold adjacentDefect adjacentProduct
    rw [htValues, htValues]
    simpa only [adjacentDefect, adjacentProduct] using hDDefect
  rcases a₀.toBONG.beliLemma49_ii a₀.good
      a₀.lemma814InitialThreeSegment t.toBONG t.good with ⟨R⟩
  let transformed : GoodBONG q L (N + 5) := ⟨R.bong, R.good⟩
  have hinsideValue (i : Fin 3) :
      transformed.valueUnit (⟨i.val, by omega⟩ : Fin (N + 5)) =
        t.valueUnit i := by
    apply Units.ext
    change R.bong.value ⟨i.val, by omega⟩ = t.toBONG.value i
    rw [← R.bong.quadratic_ambientVector,
      ← t.toBONG.quadratic_ambientVector]
    change q.quadratic (R.bong.ambientVector ⟨i.val, by omega⟩) =
      q.quadratic (t.toBONG.ambientVector i : V)
    simpa only [zero_add] using congrArg q.quadratic (R.inside_eq i)
  have htransformedDefect :
      transformed.adjacentDefect (1 : Fin (N + 4)) =
        ((A : ℚ) : WithTop ℚ) := by
    unfold adjacentDefect adjacentProduct
    have hcast : (Fin.castSucc (1 : Fin (N + 4))) =
        (⟨((1 : Fin 2).castSucc).val, by omega⟩ : Fin (N + 5)) := by
      apply Fin.ext
      rfl
    have hsucc : (Fin.succ (1 : Fin (N + 4))) =
        (⟨((1 : Fin 2).succ).val, by omega⟩ : Fin (N + 5)) := by
      apply Fin.ext
      rfl
    rw [hcast, hsucc, hinsideValue (1 : Fin 2).castSucc,
      hinsideValue (1 : Fin 2).succ]
    simpa only [adjacentDefect, adjacentProduct] using htDefect
  have hordersFinal : a.SameOrders transformed := a.order_invariant transformed
  have halphasFinal : a.SameAlphas transformed := a.alpha_invariant transformed
  have hpairGap : transformed.orderGap (1 : Fin (N + 4)) = R₁ - R₂ := by
    unfold orderGap
    change transformed.order (2 : Fin (N + 5)) -
      transformed.order (1 : Fin (N + 5)) = R₁ - R₂
    rw [← hordersFinal (1 : Fin (N + 5)),
      ← hordersFinal (2 : Fin (N + 5)),
      horders₀ (1 : Fin (N + 5)), horders₀ (2 : Fin (N + 5))]
    dsimp only [R₁, R₂]
    rw [← houter₀]
  refine ⟨{
    transformed := transformed
    sameOrders := hordersFinal
    sameAlphas := halphasFinal
    pairBoundary := ?_
  }⟩
  rw [hpairGap, htransformedDefect]
  change (((((R₁ - R₂ : Int) : ℚ) + (A : ℚ)) : ℚ) : WithTop ℚ) =
    ((1 : ℚ) : WithTop ℚ)
  congr 1
  dsimp only [A]
  push_cast
  ring

end BONG.GoodBONG

end Bong
