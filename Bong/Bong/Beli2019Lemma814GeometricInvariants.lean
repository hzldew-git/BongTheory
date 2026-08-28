/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.DiagonalHasseSymbol
import Bong.Bong.Beli2019Lemma814Invariants
import Bong.Bong.Beli2019Remark87

/-!
# Beli (2019), Lemma 8.14: geometric change-of-BONG invariants

This file formalizes the Hilbert-symbol comparison in the first geometric
part of the proof of Lemma 8.14.  When `R₁ = R₃` and
`α₂ + α₃ > 2e`, classification condition (iv) embeds the first two
values of a second good BONG in the first ternary prefix.  Determinant
completion and the defect criterion then show that the two ternary prefixes
have the same isotropy behaviour.

The separate Hasse-symbol comparison for the ternary complement
`[a₁,a₂,a₃,a₄] \top [b₁]` is left to the next substage.
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {N : Nat}

set_option maxHeartbeats 800000 in
-- The determinant-completion comparison contains several dependent prefix
-- casts and a concrete three-coordinate Hilbert-symbol calculation.
/-- The ternary isotropy condition in Lemma 8.14(a)--(b) is independent of
the chosen good BONG in target rank at least four. -/
theorem lemma814FirstThreeIsotropic_changeBONG_iff_of_alphaSum
    [QuadraticDefectLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DiagonalCodimensionOneCancellationLaws K]
    [HilbertSymbolLaws K]
    (a a' : GoodBONG q L (N + 3))
    (hfour : 4 ≤ N + 3)
    (houter : a.order (0 : Fin (N + 3)) = a.order (2 : Fin (N + 3)))
    (hsum : 2 * (ramificationIndex K : ℚ) <
      a.alphaValue (1 : Fin (N + 2)) +
        a.alphaValue (⟨2, by omega⟩ : Fin (N + 2))) :
    a.Lemma814FirstThreeIsotropic ↔
      a'.Lemma814FirstThreeIsotropic := by
  let base := a.prefixValueUnits 3 (by omega)
  let head := a'.prefixValueUnits 2 (by omega)
  let other := a'.prefixValueUnits 3 (by omega)
  let d := diagonalUnitDeterminant base * diagonalUnitDeterminant head
  let candidate : Fin 3 → Kˣ := Fin.snoc head d
  have hinter := a.internalRepresentationConditions_sameLattice a'
  have hheadRepValues : DiagonalRepresents
      (a'.prefixValues 2 (by omega))
      (a.prefixValues 3 (by omega)) := by
    apply hinter (⟨2, by omega⟩ : Fin (N + 2)) (by norm_num)
    simpa using hsum
  have hheadRep : DiagonalRepresents
      (diagonalUnitCoefficients head)
      (diagonalUnitCoefficients base) := by
    simpa [head, base] using hheadRepValues
  have hcandidateRep : DiagonalRepresents
      (diagonalUnitCoefficients candidate)
      (diagonalUnitCoefficients base) := by
    simpa [candidate, d] using
      determinantCompletion_represents_base base head hheadRep
  have hbaseCandidate :
      DiagonalIsotropic (diagonalUnitCoefficients base) ↔
        DiagonalIsotropic (diagonalUnitCoefficients candidate) := by
    constructor
    · exact hcandidateRep.symm_of_sameRank.isotropic_of
    · exact hcandidateRep.isotropic_of
  have hcandidateZero : candidate (0 : Fin 3) = head (0 : Fin 2) := by
    simp [candidate]
  have hcandidateOne : candidate (1 : Fin 3) = head (1 : Fin 2) := by
    change (Fin.snoc head d : Fin 3 → Kˣ) 1 = head 1
    rw [show (1 : Fin 3) = (1 : Fin 2).castSucc by rfl,
      Fin.snoc_castSucc]
  have hcandidateTwo : candidate (2 : Fin 3) = d := by
    change (Fin.snoc head d : Fin 3 → Kˣ) 2 = d
    rw [show (2 : Fin 3) = Fin.last 2 by rfl, Fin.snoc_last]
  have hotherZero : other (0 : Fin 3) = head (0 : Fin 2) := by
    rfl
  have hotherOne : other (1 : Fin 3) = head (1 : Fin 2) := by
    rfl
  let firstArgument : Kˣ := -(head 0 * head 1)
  let candidateSecond : Kˣ := -(candidate 1 * candidate 2)
  let otherSecond : Kˣ := -(other 1 * other 2)
  have hsecondProduct :
      candidateSecond * otherSecond =
        (a.prefixProduct 3 * a'.prefixProduct 3) * (head 1) ^ 2 := by
    rw [← a.diagonalUnitDeterminant_prefixValueUnits 3 (by omega),
      ← a'.diagonalUnitDeterminant_prefixValueUnits 3 (by omega)]
    change candidateSecond * otherSecond =
      (diagonalUnitDeterminant base * diagonalUnitDeterminant other) *
        (head 1) ^ 2
    dsimp only [candidateSecond, otherSecond]
    rw [hcandidateOne, hcandidateTwo, hotherOne]
    simp only [d, diagonalUnitDeterminant,
      Fin.prod_univ_two, Fin.prod_univ_three]
    rw [hotherZero, hotherOne]
    simp only [neg_mul_neg, pow_two]
    ac_rfl
  have horders := a.order_invariant a'
  have houter' :
      a'.order (0 : Fin (N + 3)) = a'.order (2 : Fin (N + 3)) :=
    (horders 0).symm.trans (houter.trans (horders 2))
  have hremark := a'.beli2019Remark87 (0 : Fin (N + 1)) houter'
  have hfirstArgument :
      firstArgument = a'.adjacentProduct (0 : Fin (N + 2)) := by
    simp [firstArgument, head, prefixValueUnits, adjacentProduct]
  have hfirstDefect :
      (a'.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) ≤
        defectOrder (K := K) firstArgument := by
    rw [hfirstArgument]
    rw [a'.coe_alphaValue]
    have hraw := hremark.currentAlpha_le_previousRawDefect
    unfold adjacentDefect at hraw
    rw [a'.coe_alphaValue] at hraw
    have hcurrent :
        remark87CurrentAlpha (0 : Fin (N + 1)) =
          (1 : Fin (N + 2)) := by
      apply Fin.ext
      rfl
    have hprevious :
        remark87PreviousAlpha (0 : Fin (N + 1)) =
          (0 : Fin (N + 2)) := by
      apply Fin.ext
      rfl
    rw [hcurrent, hprevious] at hraw
    exact hraw
  have hcomparisonDefect :
      (a.alphaValue (⟨2, by omega⟩ : Fin (N + 2)) : WithTop ℚ) ≤
        defectOrder (K := K)
          (a.prefixProduct 3 * a'.prefixProduct 3) := by
    have hbound := a.prefixChangeDefectBound_of_classification a' 3
    rw [a.prefixAlphaCap_of_internal (by omega) (by omega)] at hbound
    simpa only using hbound
  have hsecondDefect :
      (a.alphaValue (⟨2, by omega⟩ : Fin (N + 2)) : WithTop ℚ) ≤
        defectOrder (K := K) (candidateSecond * otherSecond) := by
    rw [hsecondProduct, defectOrder_mul_square]
    exact hcomparisonDefect
  have halphas := a.alpha_invariant a'
  have hsum' : 2 * (ramificationIndex K : ℚ) <
      a'.alphaValue (1 : Fin (N + 2)) +
        a.alphaValue (⟨2, by omega⟩ : Fin (N + 2)) := by
    rw [← halphas (1 : Fin (N + 2))]
    exact hsum
  have hdefectSum :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        defectOrder (K := K) firstArgument +
          defectOrder (K := K) (candidateSecond * otherSecond) := by
    have hsumTop :
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
          (a'.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) +
            (a.alphaValue (⟨2, by omega⟩ : Fin (N + 2)) : WithTop ℚ) := by
      exact_mod_cast hsum'
    exact hsumTop.trans_le (add_le_add hfirstDefect hsecondDefect)
  have hproductHilbert :
      hilbertSymbol K firstArgument (candidateSecond * otherSecond) = 1 :=
    hilbertSymbol_eq_one_of_defectOrder_add_gt_two_mul_e hdefectSum
  have hsecondHilbert :
      hilbertSymbol K firstArgument candidateSecond =
        hilbertSymbol K firstArgument otherSecond :=
    hilbertSymbol_eq_of_mul_right_eq_one firstArgument candidateSecond
      otherSecond hproductHilbert
  have hcandidateOther :
      DiagonalIsotropic (diagonalUnitCoefficients candidate) ↔
        DiagonalIsotropic (diagonalUnitCoefficients other) := by
    rw [diagonalUnitTernary_isotropic_iff_adjacentHilbertOne,
      diagonalUnitTernary_isotropic_iff_adjacentHilbertOne]
    rw [hcandidateZero, hcandidateOne, hotherZero, hotherOne]
    change hilbertSymbol K firstArgument candidateSecond = 1 ↔
      hilbertSymbol K firstArgument otherSecond = 1
    rw [hsecondHilbert]
  have haBase :
      a.Lemma814FirstThreeIsotropic ↔
        DiagonalIsotropic (diagonalUnitCoefficients base) := by
    rfl
  have haOther :
      a'.Lemma814FirstThreeIsotropic ↔
        DiagonalIsotropic (diagonalUnitCoefficients other) := by
    rfl
  exact haBase.trans (hbaseCandidate.trans (hcandidateOther.trans haOther.symm))

/-- The strict defect inequality in exception (a) implies the strict
`α₂ + α₃ > 2e` inequality needed by the Hilbert-symbol comparison. -/
theorem alphaTwo_add_alphaThree_strict_of_lemma814ExceptionA
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (hfour : 4 ≤ N + 3) (A : a.Beli2019Lemma814ExceptionA b) :
    2 * (ramificationIndex K : ℚ) <
      a.alphaValue (1 : Fin (N + 2)) +
        a.alphaValue (⟨2, by omega⟩ : Fin (N + 2)) := by
  have hcap := a.truncatedPrefixDefect_le_leftCap b (-1) 3 1
  change a.lemma814FirstThirdCappedDefect b ≤
    a.prefixAlphaCap 3 at hcap
  rw [a.prefixAlphaCap_of_internal (by omega) (by omega)] at hcap
  have hcap' : a.lemma814FirstThirdCappedDefect b ≤
      (a.alphaValue (⟨2, by omega⟩ : Fin (N + 2)) : WithTop ℚ) := by
    simpa only using hcap
  have hsumLe :
      (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) +
          a.lemma814FirstThirdCappedDefect b ≤
        (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) +
          (a.alphaValue (⟨2, by omega⟩ : Fin (N + 2)) : WithTop ℚ) := by
    exact add_le_add_right hcap' _
  have htop :
      ((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) <
        (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) +
          (a.alphaValue (⟨2, by omega⟩ : Fin (N + 2)) : WithTop ℚ) :=
    A.defectSum_strict.trans_le hsumLe
  exact_mod_cast htop

/-- Exception (a) supplies all hypotheses of the high-rank ternary
isotropy comparison. -/
theorem lemma814FirstThreeIsotropic_changeBONG_iff_of_exceptionA
    [QuadraticDefectLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DiagonalCodimensionOneCancellationLaws K]
    [HilbertSymbolLaws K]
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (a a' : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (hfour : 4 ≤ N + 3) (A : a.Beli2019Lemma814ExceptionA b) :
    a.Lemma814FirstThreeIsotropic ↔
      a'.Lemma814FirstThreeIsotropic := by
  apply a.lemma814FirstThreeIsotropic_changeBONG_iff_of_alphaSum a' hfour
    A.firstThirdOrders_eq
  exact a.alphaTwo_add_alphaThree_strict_of_lemma814ExceptionA b hfour A

/-- Exception (b) states the strict alpha sum explicitly whenever the target
rank is at least four. -/
theorem lemma814FirstThreeIsotropic_changeBONG_iff_of_exceptionB
    [QuadraticDefectLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DiagonalCodimensionOneCancellationLaws K]
    [HilbertSymbolLaws K]
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (a a' : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (hfour : 4 ≤ N + 3) (B : a.Beli2019Lemma814ExceptionB b) :
    a.Lemma814FirstThreeIsotropic ↔
      a'.Lemma814FirstThreeIsotropic := by
  exact a.lemma814FirstThreeIsotropic_changeBONG_iff_of_alphaSum a' hfour
    B.firstThirdOrders_eq (B.laterAlphaSum_strict hfour)

/-- In rank at least four, exception (a) transports with no separate
geometric hypothesis: its strict defect inequality supplies the Hilbert
comparison. -/
theorem lemma814ExceptionA_of_changeBONG_ge_four
    [QuadraticDefectLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    [DiagonalCodimensionOneCancellationLaws K]
    [HilbertSymbolLaws K]
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (a a' : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (hfour : 4 ≤ N + 3) (A : a.Beli2019Lemma814ExceptionA b) :
    a'.Beli2019Lemma814ExceptionA b := by
  letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
  have hisotropy :=
    a.lemma814FirstThreeIsotropic_changeBONG_iff_of_exceptionA
      a' b hfour A
  have hnotIsotropic : ¬a'.Lemma814FirstThreeIsotropic := by
    intro h
    exact a.not_firstThreeIsotropic_of_anisotropic A.firstThree_anisotropic
      (hisotropy.mpr h)
  apply a.lemma814ExceptionA_of_changeBONG
    (classificationV := classificationV) (classificationW := classificationW)
    (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
    a' b A
  exact (a'.not_firstThreeIsotropic_iff_anisotropic).mp hnotIsotropic

/-- In rank at least four, exception (b) likewise transports without an
extra geometric assumption. -/
theorem lemma814ExceptionB_of_changeBONG_ge_four
    [QuadraticDefectLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    [DiagonalCodimensionOneCancellationLaws K]
    [HilbertSymbolLaws K]
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (a a' : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (hfour : 4 ≤ N + 3) (B : a.Beli2019Lemma814ExceptionB b) :
    a'.Beli2019Lemma814ExceptionB b := by
  letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
  have hisotropy :=
    a.lemma814FirstThreeIsotropic_changeBONG_iff_of_exceptionB
      a' b hfour B
  apply a.lemma814ExceptionB_of_changeBONG
    (classificationV := classificationV) (classificationW := classificationW)
    (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
    a' b B
  exact hisotropy.mp B.firstThree_isotropic

/-- The disjunction of exceptions (a) and (b) is fully invariant in target
rank at least four. -/
theorem lemma814ExceptionAB_changeBONG_iff_ge_four
    [QuadraticDefectLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    [DiagonalCodimensionOneCancellationLaws K]
    [HilbertSymbolLaws K]
    {W : Type w} [AddCommGroup W] [Module K W]
    {r : QuadraticSpace K W} {M : Lattice K W}
    (a a' : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (hfour : 4 ≤ N + 3) :
    (a.Beli2019Lemma814ExceptionA b ∨ a.Beli2019Lemma814ExceptionB b) ↔
      (a'.Beli2019Lemma814ExceptionA b ∨
        a'.Beli2019Lemma814ExceptionB b) := by
  letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
  constructor
  · rintro (A | B)
    · exact Or.inl (a.lemma814ExceptionA_of_changeBONG_ge_four
        (classificationV := classificationV)
        (classificationW := classificationW)
        (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
        a' b hfour A)
    · exact Or.inr (a.lemma814ExceptionB_of_changeBONG_ge_four
        (classificationV := classificationV)
        (classificationW := classificationW)
        (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
        a' b hfour B)
  · rintro (A | B)
    · exact Or.inl (a'.lemma814ExceptionA_of_changeBONG_ge_four
        (classificationV := classificationV)
        (classificationW := classificationW)
        (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
        a b hfour A)
    · exact Or.inr (a'.lemma814ExceptionB_of_changeBONG_ge_four
        (classificationV := classificationV)
        (classificationW := classificationW)
        (prefixChangeV := prefixChangeV) (prefixChangeW := prefixChangeW)
        a b hfour B)

end BONG.GoodBONG

end Bong
