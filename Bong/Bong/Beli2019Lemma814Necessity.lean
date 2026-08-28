/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Corollary810
import Bong.Bong.Beli2019Lemma814ComplementInvariants

/-!
# Beli (2019), Lemma 8.14: necessity

This file proves that a good BONG whose first value is the prescribed unary
value cannot satisfy any of the three exceptional alternatives in Lemma 8.14.
The proof follows Beli's normalization by Corollary 8.10 before treating the
three Hilbert-symbol contradictions.
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {N : Nat}

/-- Exception (a) is independent of the chosen good BONG in every target
rank in which Lemma 8.14 is stated. -/
theorem lemma814ExceptionA_changeBONG_iff
    [QuadraticDefectLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    [DiagonalCodimensionOneCancellationLaws K]
    [HilbertSymbolLaws K]
    (a a' : GoodBONG q L (N + 3)) (b : GoodBONG r M 1) :
    a.Beli2019Lemma814ExceptionA b ↔
      a'.Beli2019Lemma814ExceptionA b := by
  cases N with
  | zero =>
      constructor
      · intro A
        apply a.lemma814ExceptionA_of_changeBONG
          (classificationV := classificationV)
          (classificationW := classificationW)
          (prefixChangeV := prefixChangeV)
          (prefixChangeW := prefixChangeW) a' b A
        exact (a.lemma814FirstThreeAnisotropic_changeBONG_iff_rankThree a').mp
          A.firstThree_anisotropic
      · intro A
        apply a'.lemma814ExceptionA_of_changeBONG
          (classificationV := classificationV)
          (classificationW := classificationW)
          (prefixChangeV := prefixChangeV)
          (prefixChangeW := prefixChangeW) a b A
        exact (a.lemma814FirstThreeAnisotropic_changeBONG_iff_rankThree a').mpr
          A.firstThree_anisotropic
  | succ N =>
      constructor
      · exact fun A ↦ a.lemma814ExceptionA_of_changeBONG_ge_four
          (classificationV := classificationV)
          (classificationW := classificationW)
          (prefixChangeV := prefixChangeV)
          (prefixChangeW := prefixChangeW) a' b (by omega) A
      · exact fun A ↦ a'.lemma814ExceptionA_of_changeBONG_ge_four
          (classificationV := classificationV)
          (classificationW := classificationW)
          (prefixChangeV := prefixChangeV)
          (prefixChangeW := prefixChangeW) a b (by omega) A

/-- Exception (b) is likewise independent of the chosen good BONG in every
target rank. -/
theorem lemma814ExceptionB_changeBONG_iff
    [QuadraticDefectLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    [DiagonalCodimensionOneCancellationLaws K]
    [HilbertSymbolLaws K]
    (a a' : GoodBONG q L (N + 3)) (b : GoodBONG r M 1) :
    a.Beli2019Lemma814ExceptionB b ↔
      a'.Beli2019Lemma814ExceptionB b := by
  cases N with
  | zero =>
      constructor
      · intro B
        apply a.lemma814ExceptionB_of_changeBONG
          (classificationV := classificationV)
          (classificationW := classificationW)
          (prefixChangeV := prefixChangeV)
          (prefixChangeW := prefixChangeW) a' b B
        exact (a.lemma814FirstThreeIsotropic_changeBONG_iff_rankThree a').mp
          B.firstThree_isotropic
      · intro B
        apply a'.lemma814ExceptionB_of_changeBONG
          (classificationV := classificationV)
          (classificationW := classificationW)
          (prefixChangeV := prefixChangeV)
          (prefixChangeW := prefixChangeW) a b B
        exact (a.lemma814FirstThreeIsotropic_changeBONG_iff_rankThree a').mpr
          B.firstThree_isotropic
  | succ N =>
      constructor
      · exact fun B ↦ a.lemma814ExceptionB_of_changeBONG_ge_four
          (classificationV := classificationV)
          (classificationW := classificationW)
          (prefixChangeV := prefixChangeV)
          (prefixChangeW := prefixChangeW) a' b (by omega) B
      · exact fun B ↦ a'.lemma814ExceptionB_of_changeBONG_ge_four
          (classificationV := classificationV)
          (classificationW := classificationW)
          (prefixChangeV := prefixChangeV)
          (prefixChangeW := prefixChangeW) a b (by omega) B

/-- The complete exceptional disjunction is invariant under changing the
good BONG. -/
theorem lemma814Exceptional_changeBONG_iff_full
    [QuadraticDefectLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [HilbertSymbolLaws K]
    [DyadicQuaternaryComplementLaws K]
    (a a' : GoodBONG q L (N + 3)) (b : GoodBONG r M 1) :
    a.Beli2019Lemma814Exceptional b ↔
      a'.Beli2019Lemma814Exceptional b := by
  unfold Beli2019Lemma814Exceptional
  rw [a.lemma814ExceptionA_changeBONG_iff
      (classificationV := classificationV)
      (classificationW := classificationW)
      (prefixChangeV := prefixChangeV)
      (prefixChangeW := prefixChangeW) a' b,
    a.lemma814ExceptionB_changeBONG_iff
      (classificationV := classificationV)
      (classificationW := classificationW)
      (prefixChangeV := prefixChangeV)
      (prefixChangeW := prefixChangeW) a' b,
    a.lemma814ExceptionC_changeBONG_iff
      (classificationV := classificationV)
      (classificationW := classificationW)
      (prefixChangeV := prefixChangeV)
      (prefixChangeW := prefixChangeW) a' b]

/-- In Corollary 8.10 normal form, equal first and third orders identify the
first raw adjacent defect with the second alpha. -/
theorem adjacentDefect_zero_eq_secondAlpha_of_firstBinary
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 3))
    (hbinary : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin (N + 2)) : WithTop ℚ))
    (houter : a.order (0 : Fin (N + 3)) =
      a.order (2 : Fin (N + 3)))
    (hstrict : a.alphaValue (0 : Fin (N + 2)) <
      a.halfGapValue (0 : Fin (N + 2))) :
    a.adjacentDefect (0 : Fin (N + 2)) =
      (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) := by
  have hstrictTop :
      (a.alphaValue (0 : Fin (N + 2)) : WithTop ℚ) <
        a.halfGapCandidate (0 : Fin (N + 2)) := by
    rw [← a.coe_halfGapValue]
    exact_mod_cast hstrict
  have hleftlt :
      a.leftDefectCandidate (0 : Fin (N + 2)) (0 : Fin (N + 2)) <
        a.halfGapCandidate (0 : Fin (N + 2)) := by
    by_contra hnot
    have hhalfLe : a.halfGapCandidate (0 : Fin (N + 2)) ≤
        a.leftDefectCandidate (0 : Fin (N + 2)) (0 : Fin (N + 2)) :=
      le_of_not_gt hnot
    have hmin := hbinary
    unfold firstBinaryAlpha at hmin
    rw [min_eq_left hhalfLe] at hmin
    exact (ne_of_lt hstrictTop) hmin.symm
  have hleft :
      a.leftDefectCandidate (0 : Fin (N + 2)) (0 : Fin (N + 2)) =
        (a.alphaValue (0 : Fin (N + 2)) : WithTop ℚ) := by
    have hmin := hbinary
    unfold firstBinaryAlpha at hmin
    rw [min_eq_right hleftlt.le] at hmin
    exact hmin
  have houter' :
      a.order (remark87PreviousValue (0 : Fin (N + 1))) =
        a.order (remark87NextValue (0 : Fin (N + 1))) := by
    convert houter using 1 <;> apply congrArg a.order <;> apply Fin.ext <;> rfl
  have hremark := a.beli2019Remark87 (0 : Fin (N + 1)) houter'
  have hcurrent :
      a.alphaValue (1 : Fin (N + 2)) =
        ((a.order (0 : Fin (N + 3)) -
          a.order (1 : Fin (N + 3)) : Int) : ℚ) +
            a.alphaValue (0 : Fin (N + 2)) := by
    simpa [remark87PreviousAlpha, remark87CurrentAlpha,
      remark87PreviousValue, remark87MiddleValue] using
        hremark.currentAlpha_eq
  have hgap :
      (a.orderGap (0 : Fin (N + 2)) : ℚ) +
          a.alphaValue (1 : Fin (N + 2)) =
        a.alphaValue (0 : Fin (N + 2)) := by
    have hsucc : (0 : Fin (N + 2)).succ = (1 : Fin (N + 3)) := by
      apply Fin.ext
      rfl
    have hcast : (0 : Fin (N + 2)).castSucc = (0 : Fin (N + 3)) := by
      apply Fin.ext
      rfl
    unfold orderGap
    rw [hsucc, hcast]
    push_cast at hcurrent ⊢
    linarith
  have hgapTop :
      ((a.orderGap (0 : Fin (N + 2)) : ℚ) : WithTop ℚ) +
          (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) =
        (a.alphaValue (0 : Fin (N + 2)) : WithTop ℚ) := by
    exact_mod_cast hgap
  apply WithTop.add_left_cancel WithTop.coe_ne_top
  calc
    ((a.orderGap (0 : Fin (N + 2)) : ℚ) : WithTop ℚ) +
          a.adjacentDefect (0 : Fin (N + 2)) =
        (a.alphaValue (0 : Fin (N + 2)) : WithTop ℚ) := by
      simpa only [leftDefectCandidate, orderGap] using hleft
    _ = ((a.orderGap (0 : Fin (N + 2)) : ℚ) : WithTop ℚ) +
        (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) := hgapTop.symm

/-- Once the first values agree, the raw mixed defect in Lemma 8.14 is the
second adjacent defect of the target BONG. -/
theorem lemma814FirstThirdRawDefect_eq_adjacentDefect_of_firstValue_eq
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (hfirst : a.valueUnit (0 : Fin (N + 3)) =
      b.valueUnit (0 : Fin 1)) :
    defectOrder (K := K)
        ((-1) * a.prefixProduct 3 * b.prefixProduct 1) =
      a.adjacentDefect (1 : Fin (N + 2)) := by
  have haProduct : a.prefixProduct 1 =
      a.valueUnit (0 : Fin (N + 3)) := by
    unfold GoodBONG.prefixProduct GoodBONG.valueUnit
    have h := a.toBONG.prefixProduct_succ 0 (by omega)
    rw [a.toBONG.prefixProduct_zero, one_mul] at h
    convert h using 1
    apply congrArg a.toBONG.valueUnit
    apply Fin.ext
    rfl
  have hbProduct : b.prefixProduct 1 = b.valueUnit (0 : Fin 1) := by
    unfold GoodBONG.prefixProduct GoodBONG.valueUnit
    have h := b.toBONG.prefixProduct_succ 0 (by omega)
    rw [b.toBONG.prefixProduct_zero, one_mul] at h
    convert h using 1
    apply congrArg b.toBONG.valueUnit
    apply Fin.ext
    rfl
  have hunit :
      (-1 : Kˣ) * a.prefixProduct 3 * b.prefixProduct 1 =
        (-1) * a.prefixProduct 1 * a.prefixProduct 3 := by
    rw [haProduct, hbProduct, ← hfirst]
    ac_rfl
  rw [hunit]
  exact a.defectOrder_prefixPair_eq_adjacentDefect
    (1 : Fin (N + 2))

/-- With aligned first values, the bracketed first-third defect is the raw
second adjacent defect capped only at the target prefix boundary. -/
theorem lemma814FirstThirdCappedDefect_eq_min_of_firstValue_eq
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (hfirst : a.valueUnit (0 : Fin (N + 3)) =
      b.valueUnit (0 : Fin 1)) :
    a.lemma814FirstThirdCappedDefect b =
      min (a.adjacentDefect (1 : Fin (N + 2)))
        (a.prefixAlphaCap 3) := by
  have hraw :=
    a.lemma814FirstThirdRawDefect_eq_adjacentDefect_of_firstValue_eq b hfirst
  unfold lemma814FirstThirdCappedDefect truncatedPrefixDefect
  rw [b.prefixAlphaCap_last, hraw]
  simp only [min_top_right]

/-- The bracketed quaternary determinant defect is its raw defect capped at
the fourth target prefix boundary. -/
theorem lemma814FirstFourCappedDefect_eq_min
    (a : GoodBONG q L (N + 3)) (hfour : 4 ≤ N + 3) :
    a.lemma814FirstFourCappedDefect hfour =
      min (defectOrder (K := K) (a.prefixProduct 4))
        (a.prefixAlphaCap 4) := by
  unfold lemma814FirstFourCappedDefect truncatedPrefixDefect
  rw [show a.prefixProduct 0 = 1 by exact a.toBONG.prefixProduct_zero,
    a.prefixAlphaCap_zero]
  simp only [mul_one, one_mul, min_top_right]

/-- If a binary minimum lies strictly below its right entry, it is its left
entry. -/
theorem eq_left_of_eq_min_lt_right {x raw cap : WithTop ℚ}
    (heq : x = min raw cap) (hlt : x < cap) : x = raw := by
  have hraw : raw ≤ cap := by
    by_contra hnot
    have hcap : cap ≤ raw := le_of_not_ge hnot
    have hmin : min raw cap = cap := min_eq_right hcap
    have hlt' : min raw cap < cap := by
      rw [← heq]
      exact hlt
    rw [hmin] at hlt'
    exact (lt_irrefl _ hlt').elim
  rw [heq, min_eq_left hraw]

/-- The first ternary prefix is isotropic exactly when the Hilbert symbol of
its two adjacent products is one. -/
theorem lemma814FirstThreeIsotropic_iff_adjacentHilbertOne
    (a : GoodBONG q L (N + 3)) :
    a.Lemma814FirstThreeIsotropic ↔
      hilbertSymbol K
        (a.adjacentProduct (0 : Fin (N + 2)))
        (a.adjacentProduct (1 : Fin (N + 2))) = 1 := by
  change DiagonalIsotropic
      (diagonalUnitCoefficients (a.prefixValueUnits 3 (by omega))) ↔ _
  rw [diagonalUnitTernary_isotropic_iff_adjacentHilbertOne]
  have hzero :
      -(a.prefixValueUnits 3 (by omega) 0 *
          a.prefixValueUnits 3 (by omega) 1) =
        a.adjacentProduct (0 : Fin (N + 2)) := by
    unfold prefixValueUnits adjacentProduct
    congr 2
  have hone :
      -(a.prefixValueUnits 3 (by omega) 1 *
          a.prefixValueUnits 3 (by omega) 2) =
        a.adjacentProduct (1 : Fin (N + 2)) := by
    unfold prefixValueUnits adjacentProduct
    congr 2
  rw [hzero, hone]

/-- If the prescribed unary value is already the first BONG value, exception
(a) would force the first ternary prefix to be both isotropic and anisotropic. -/
theorem not_lemma814ExceptionA_of_firstValue_eq
    [Beli2006AlphaLaws.{u, v} K]
    [HilbertSymbolLaws K]
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (hfirst : a.valueUnit (0 : Fin (N + 3)) =
      b.valueUnit (0 : Fin 1)) :
    ¬a.Beli2019Lemma814ExceptionA b := by
  intro A
  have houter :
      a.order (remark87PreviousValue (0 : Fin (N + 1))) =
        a.order (remark87NextValue (0 : Fin (N + 1))) := by
    convert A.firstThirdOrders_eq using 1 <;>
      apply congrArg a.order <;> apply Fin.ext <;> rfl
  have hremark := a.beli2019Remark87 (0 : Fin (N + 1)) houter
  have hfirstDefect :
      (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) ≤
        a.adjacentDefect (0 : Fin (N + 2)) := by
    simpa [remark87CurrentAlpha, remark87PreviousAlpha] using
      hremark.currentAlpha_le_previousRawDefect
  have hsecondDefect :
      a.lemma814FirstThirdCappedDefect b ≤
        a.adjacentDefect (1 : Fin (N + 2)) := by
    have hraw := a.truncatedPrefixDefect_le_defect b (-1) 3 1
    rw [a.lemma814FirstThirdRawDefect_eq_adjacentDefect_of_firstValue_eq
      b hfirst] at hraw
    exact hraw
  have hsum :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        a.adjacentDefect (0 : Fin (N + 2)) +
          a.adjacentDefect (1 : Fin (N + 2)) := by
    have hsum' := A.defectSum_strict.trans_le
      (add_le_add hfirstDefect hsecondDefect)
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hsum'
  have hone :
      hilbertSymbol K
        (a.adjacentProduct (0 : Fin (N + 2)))
        (a.adjacentProduct (1 : Fin (N + 2))) = 1 := by
    apply hilbertSymbol_eq_one_of_defectOrder_add_gt_two_mul_e
    simpa only [adjacentDefect] using hsum
  have hisotropic : a.Lemma814FirstThreeIsotropic := by
    exact (a.lemma814FirstThreeIsotropic_iff_adjacentHilbertOne).mpr hone
  exact a.not_firstThreeIsotropic_of_anisotropic
    A.firstThree_anisotropic hisotropic

/-- In exception (b), alignment of the first value removes the remaining
prefix cap, so the second adjacent defect is exactly the bracketed defect. -/
theorem adjacentDefect_one_eq_capped_of_lemma814ExceptionB
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (hfirst : a.valueUnit (0 : Fin (N + 3)) =
      b.valueUnit (0 : Fin 1))
    (B : a.Beli2019Lemma814ExceptionB b) :
    a.adjacentDefect (1 : Fin (N + 2)) =
      a.lemma814FirstThirdCappedDefect b := by
  have hmin :=
    a.lemma814FirstThirdCappedDefect_eq_min_of_firstValue_eq b hfirst
  by_cases hfour : 4 ≤ N + 3
  · let secondAlpha : Fin (N + 2) := 1
    let thirdAlpha : Fin (N + 2) := ⟨2, by omega⟩
    have hlater := B.laterAlphaSum_strict hfour
    have hlaterTop :
        (((2 * (ramificationIndex K : ℚ) : ℚ)) : WithTop ℚ) <
          (a.alphaValue secondAlpha : WithTop ℚ) +
            (a.alphaValue thirdAlpha : WithTop ℚ) := by
      rw [← WithTop.coe_add]
      apply WithTop.coe_lt_coe.mpr
      simpa only [secondAlpha, thirdAlpha] using hlater
    have hsumLt :
        (a.alphaValue secondAlpha : WithTop ℚ) +
            a.lemma814FirstThirdCappedDefect b <
          (a.alphaValue secondAlpha : WithTop ℚ) +
            (a.alphaValue thirdAlpha : WithTop ℚ) := by
      have heq := B.defectSum_eq
      simpa only [secondAlpha] using heq.trans_lt hlaterTop
    have hcapLt :
        a.lemma814FirstThirdCappedDefect b <
          (a.alphaValue thirdAlpha : WithTop ℚ) :=
      (WithTop.add_lt_add_iff_left WithTop.coe_ne_top).mp hsumLt
    rw [a.prefixAlphaCap_of_internal (i := 3) (by omega) (by omega)] at hmin
    have hindex :
        (⟨3 - 1, by omega⟩ : Fin (N + 2)) = thirdAlpha := by
      apply Fin.ext
      rfl
    rw [hindex] at hmin
    exact (eq_left_of_eq_min_lt_right hmin hcapLt).symm
  · have hN : N = 0 := by omega
    subst N
    rw [a.prefixAlphaCap_last, min_top_right] at hmin
    exact hmin.symm

/-- In Corollary 8.10 normal form, exception (b) makes the adjacent Hilbert
symbol simultaneously one (by isotropy) and non-one (by the residue-two
boundary criterion). -/
theorem not_lemma814ExceptionB_of_firstValue_eq_of_firstBinary
    [Beli2006AlphaLaws.{u, v} K]
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (hfirst : a.valueUnit (0 : Fin (N + 3)) =
      b.valueUnit (0 : Fin 1))
    (hbinary : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin (N + 2)) : WithTop ℚ)) :
    ¬a.Beli2019Lemma814ExceptionB b := by
  intro B
  have hfirstDefect :=
    a.adjacentDefect_zero_eq_secondAlpha_of_firstBinary hbinary
      B.firstThirdOrders_eq B.firstAlpha_strict
  have hsecondDefect :=
    a.adjacentDefect_one_eq_capped_of_lemma814ExceptionB b hfirst B
  have hsum' :
      a.adjacentDefect (0 : Fin (N + 2)) +
          a.adjacentDefect (1 : Fin (N + 2)) =
        (((2 * (ramificationIndex K : ℚ) : ℚ)) : WithTop ℚ) := by
    rw [hfirstDefect, hsecondDefect]
    exact B.defectSum_eq
  have hsum :
      defectOrder (K := K) (a.adjacentProduct (0 : Fin (N + 2))) +
          defectOrder (K := K) (a.adjacentProduct (1 : Fin (N + 2))) =
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
    simpa only [adjacentDefect, Nat.cast_mul, Nat.cast_ofNat] using hsum'
  have hne :
      hilbertSymbol K
        (a.adjacentProduct (0 : Fin (N + 2)))
        (a.adjacentProduct (1 : Fin (N + 2))) ≠ 1 :=
    hilbertSymbol_ne_one_of_residue_two_of_defectOrder_add_eq_twoE
      B.residueTwo _ _ hsum
  have hone :
      hilbertSymbol K
        (a.adjacentProduct (0 : Fin (N + 2)))
        (a.adjacentProduct (1 : Fin (N + 2))) = 1 :=
    (a.lemma814FirstThreeIsotropic_iff_adjacentHilbertOne).mp
      B.firstThree_isotropic
  exact hne hone

/-- When the prescribed line is literally the first BONG line, cancellation
identifies its ternary complement with the three-term tail
`[a₂,a₃,a₄]`.  Thus anisotropy of the complement transfers to that tail. -/
theorem lemma814TailFirstThreeAnisotropic_of_firstValue_eq
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (hfirst : a.valueUnit (0 : Fin (N + 3)) =
      b.valueUnit (0 : Fin 1))
    (C : a.Beli2019Lemma814ExceptionC b)
    (hthree : 3 ≤ N + 2) :
    a.tail.Lemma88FirstThreeAnisotropic hthree := by
  rcases C.firstFourComplement_anisotropic with
    ⟨complement, hrep, hanisotropic⟩
  have hhead : a.value (0 : Fin (N + 3)) = b.value (0 : Fin 1) := by
    simpa only [GoodBONG.coe_valueUnit] using
      congrArg (fun z : Kˣ ↦ (z : K)) hfirst
  have hprefix :
      a.prefixValues 4 C.rank_four =
        Fin.cons (a.value (0 : Fin (N + 3)))
          (a.tail.prefixValues 3 hthree) := by
    simpa only [show 3 + 1 = 4 by omega] using
      a.prefixValues_succ_eq_cons_head_tail 3 hthree
  have hrep' : DiagonalRepresents
      (Fin.cons (a.value (0 : Fin (N + 3))) complement)
      (Fin.cons (a.value (0 : Fin (N + 3)))
        (a.tail.prefixValues 3 hthree)) := by
    rw [← hprefix, hhead]
    exact hrep
  have htailRep : DiagonalRepresents complement
      (a.tail.prefixValues 3 hthree) := by
    apply DiagonalRepresents.cancel_common_head
      (a.value (0 : Fin (N + 3))) complement
        (a.tail.prefixValues 3 hthree)
    · exact a.toBONG.value_ne_zero _
    · intro i
      exact diagonalAnisotropic_coefficient_ne_zero
        complement hanisotropic i
    · intro i
      change a.tail.toBONG.value
        ⟨i.val, i.isLt.trans_le hthree⟩ ≠ 0
      exact a.tail.toBONG.value_ne_zero _
    · exact hrep'
  have htailAnisotropic : DiagonalAnisotropic
      (a.tail.prefixValues 3 hthree) :=
    (DiagonalRepresents.symm_of_sameRank htailRep).anisotropic_of
      hanisotropic
  change DiagonalAnisotropic (a.tail.lemma88FirstThreeValues hthree)
  have hvalues : a.tail.lemma88FirstThreeValues hthree =
      a.tail.prefixValues 3 hthree := by
    funext i
    rfl
  rw [hvalues]
  exact htailAnisotropic

/-- Exception (c) removes the fourth-prefix cap: in rank four the cap is
terminal, while in higher rank its `α₄` value is strictly larger. -/
theorem lemma814FirstFourRawDefect_eq_secondAlpha_of_exceptionC
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (C : a.Beli2019Lemma814ExceptionC b) :
    defectOrder (K := K) (a.prefixProduct 4) =
      (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) := by
  have hmin := a.lemma814FirstFourCappedDefect_eq_min C.rank_four
  by_cases hfive : 5 ≤ N + 3
  · let fourthAlpha : Fin (N + 2) := ⟨3, by omega⟩
    rw [a.prefixAlphaCap_of_internal (i := 4) (by omega) (by omega)] at hmin
    have hindex :
        (⟨4 - 1, by omega⟩ : Fin (N + 2)) = fourthAlpha := by
      apply Fin.ext
      rfl
    rw [hindex] at hmin
    have hltQ :
        a.alphaValue (1 : Fin (N + 2)) <
          a.alphaValue fourthAlpha := by
      rw [C.secondAlpha_eq_complement]
      simpa only [fourthAlpha] using C.laterAlpha_strict hfive
    have hlt :
        a.lemma814FirstFourCappedDefect C.rank_four <
          (a.alphaValue fourthAlpha : WithTop ℚ) := by
      rw [C.firstFourDefect_eq_secondAlpha]
      exact WithTop.coe_lt_coe.mpr hltQ
    have hcappedRaw := eq_left_of_eq_min_lt_right hmin hlt
    exact hcappedRaw.symm.trans C.firstFourDefect_eq_secondAlpha
  · have hfour := C.rank_four
    have hlast : 4 = N + 3 := by omega
    have hcap : a.prefixAlphaCap 4 = ⊤ := by
      rw [hlast]
      exact a.prefixAlphaCap_last
    rw [hcap, min_top_right] at hmin
    exact hmin.symm.trans C.firstFourDefect_eq_secondAlpha

/-- The two middle alphas in exception (c) lie exactly on the `2e`
boundary. -/
theorem secondAlpha_add_thirdAlpha_eq_twoE_of_lemma814ExceptionC
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (C : a.Beli2019Lemma814ExceptionC b) (hthree : 3 ≤ N + 2) :
    a.alphaValue (1 : Fin (N + 2)) +
        a.alphaValue (⟨2, by omega⟩ : Fin (N + 2)) =
      2 * (ramificationIndex K : ℚ) := by
  let thirdAlpha : Fin (N + 2) := ⟨2, by omega⟩
  have hthird : a.alphaValue thirdAlpha =
      a.halfGapValue thirdAlpha := by
    simpa only [thirdAlpha] using C.thirdAlpha_eq_halfGap
  have hboundary :
      a.lemma814ThirdComplementaryDefect C.rank_four +
          a.halfGapValue thirdAlpha =
        2 * (ramificationIndex K : ℚ) := by
    simpa only [thirdAlpha] using
      a.lemma814ThirdComplementaryDefect_add_halfGap C.rank_four
  calc
    a.alphaValue (1 : Fin (N + 2)) +
          a.alphaValue (⟨2, by omega⟩ : Fin (N + 2)) =
        a.lemma814ThirdComplementaryDefect C.rank_four +
          a.halfGapValue thirdAlpha := by
      rw [C.secondAlpha_eq_complement]
      simpa only [thirdAlpha] using congrArg
        (fun x : ℚ ↦ a.lemma814ThirdComplementaryDefect C.rank_four + x)
        hthird
    _ = 2 * (ramificationIndex K : ℚ) := hboundary

/-- The order inequality in exception (c) puts the second alpha strictly
below its half gap. -/
theorem secondAlpha_lt_halfGap_of_lemma814ExceptionC
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (C : a.Beli2019Lemma814ExceptionC b) :
    a.alphaValue (1 : Fin (N + 2)) <
      a.halfGapValue (1 : Fin (N + 2)) := by
  have hfour := C.rank_four
  let secondValue : Fin (N + 3) := ⟨1, by omega⟩
  let thirdValue : Fin (N + 3) := ⟨2, by omega⟩
  let fourthValue : Fin (N + 3) := ⟨3, by omega⟩
  rw [C.secondAlpha_eq_complement]
  change (ramificationIndex K : ℚ) -
      ((a.order fourthValue - a.order thirdValue : Int) : ℚ) / 2 <
    ((a.order thirdValue - a.order secondValue : Int) : ℚ) / 2 +
      (ramificationIndex K : ℚ)
  have horderInt : a.order secondValue < a.order fourthValue := by
    convert C.secondFourthOrders_lt using 1 <;>
      apply congrArg a.order <;> apply Fin.ext <;> rfl
  have horderQ :
      (a.order secondValue : ℚ) < (a.order fourthValue : ℚ) := by
    exact_mod_cast horderInt
  push_cast at horderQ ⊢
  linarith

/-- Remark 8.7 transports the preceding strict half-gap inequality to the
first alpha. -/
theorem firstAlpha_lt_halfGap_of_lemma814ExceptionC
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (C : a.Beli2019Lemma814ExceptionC b) :
    a.alphaValue (0 : Fin (N + 2)) <
      a.halfGapValue (0 : Fin (N + 2)) := by
  have houter :
      a.order (remark87PreviousValue (0 : Fin (N + 1))) =
        a.order (remark87NextValue (0 : Fin (N + 1))) := by
    convert C.firstThirdOrders_eq using 1 <;>
      apply congrArg a.order <;> apply Fin.ext <;> rfl
  have hremark := a.beli2019Remark87 (0 : Fin (N + 1)) houter
  have hhalfIff :
      a.AttainsHalfGap (0 : Fin (N + 2)) ↔
        a.AttainsHalfGap (1 : Fin (N + 2)) := by
    simpa [remark87PreviousAlpha, remark87CurrentAlpha] using
      hremark.attainsHalfGap_iff
  have hsecondStrict := a.secondAlpha_lt_halfGap_of_lemma814ExceptionC b C
  have hnotSecond : ¬a.AttainsHalfGap (1 : Fin (N + 2)) := by
    intro h
    exact (ne_of_lt hsecondStrict) h
  have hnotFirst : ¬a.AttainsHalfGap (0 : Fin (N + 2)) :=
    fun h ↦ hnotSecond (hhalfIff.mp h)
  apply lt_of_le_of_ne (a.alphaValue_le_halfGapValue 0)
  simpa only [AttainsHalfGap] using hnotFirst

/-- Lemma 8.1(ii) applied to the first adjacent product and the quaternary
determinant makes the third adjacent defect strictly larger than `α₂`. -/
theorem secondAlpha_lt_adjacentDefect_two_of_lemma814ExceptionC
    [Beli2006AlphaLaws.{u, v} K]
    [QuadraticDefectLaws K]
    [DyadicResidueDefectProductLaws K]
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (hbinary : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin (N + 2)) : WithTop ℚ))
    (C : a.Beli2019Lemma814ExceptionC b) (hfour : 4 ≤ N + 3) :
    (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) <
      a.adjacentDefect (⟨2, by omega⟩ : Fin (N + 2)) := by
  let thirdAdjacent : Fin (N + 2) := ⟨2, by omega⟩
  let x := a.adjacentProduct (0 : Fin (N + 2))
  let z := a.prefixProduct 4
  have hfirstStrict := a.firstAlpha_lt_halfGap_of_lemma814ExceptionC b C
  have hx : defectOrder (K := K) x =
      (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) := by
    change a.adjacentDefect (0 : Fin (N + 2)) = _
    exact a.adjacentDefect_zero_eq_secondAlpha_of_firstBinary hbinary
      C.firstThirdOrders_eq hfirstStrict
  have hz : defectOrder (K := K) z =
      (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) := by
    exact a.lemma814FirstFourRawDefect_eq_secondAlpha_of_exceptionC b C
  have hdefectEq : quadraticDefect K x = quadraticDefect K z :=
    quadraticDefect_eq_of_defectOrder_eq x z (hx.trans hz.symm)
  have hxFinite : quadraticDefect K x ≠ ⊤ :=
    quadraticDefect_ne_top_of_defectOrder_eq_coe x
      (a.alphaValue (1 : Fin (N + 2))) hx
  have hstrict := beli2019Lemma81_ii_strict
    C.residueTwo x z hdefectEq hxFinite
  have hstrictOrder := defectOrder_lt_of_quadraticDefect_lt x (x * z) hstrict
  have hproduct :
      x * z = a.adjacentProduct thirdAdjacent *
        (a.valueUnit (0 : Fin (N + 3)) *
          a.valueUnit (1 : Fin (N + 3))) ^ 2 := by
    unfold x z
    rw [a.prefixProduct_add_two 2 (by omega),
      a.prefixProduct_add_two 0 (by omega)]
    rw [show a.prefixProduct 0 = 1 by exact a.toBONG.prefixProduct_zero]
    unfold adjacentProduct
    have hzeroCast : (0 : Fin (N + 2)).castSucc =
        (⟨0, by omega⟩ : Fin (N + 3)) := by
      apply Fin.ext
      rfl
    have hzeroSucc : (0 : Fin (N + 2)).succ =
        (⟨1, by omega⟩ : Fin (N + 3)) := by
      apply Fin.ext
      rfl
    have hthirdCast : thirdAdjacent.castSucc =
        (⟨2, by omega⟩ : Fin (N + 3)) := by
      apply Fin.ext
      rfl
    have hthirdSucc : thirdAdjacent.succ =
        (⟨3, by omega⟩ : Fin (N + 3)) := by
      apply Fin.ext
      rfl
    have hzero : (0 : Fin (N + 3)) =
        (⟨0, by omega⟩ : Fin (N + 3)) := by
      apply Fin.ext
      rfl
    have hone : (1 : Fin (N + 3)) =
        (⟨1, by omega⟩ : Fin (N + 3)) := by
      apply Fin.ext
      rfl
    apply Units.ext
    simp only [Units.val_mul, Units.val_neg, Units.val_pow_eq_pow_val,
      Units.val_one, one_mul, Nat.zero_add]
    rw [hzeroCast, hzeroSucc, hthirdCast, hthirdSucc, hzero, hone]
    ring
  rw [hproduct, defectOrder_mul_square, hx] at hstrictOrder
  simpa only [x, thirdAdjacent, adjacentDefect] using hstrictOrder

/-- In Corollary 8.10 normal form, exception (c) contradicts anisotropy of
the aligned ternary complement: Lemma 8.1(ii) forces the adjacent defect sum
strictly above `2e`, hence forces its Hilbert symbol to be one. -/
theorem not_lemma814ExceptionC_of_firstValue_eq_of_firstBinary
    [Beli2006AlphaLaws.{u, v} K]
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (hfirst : a.valueUnit (0 : Fin (N + 3)) =
      b.valueUnit (0 : Fin 1))
    (hbinary : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin (N + 2)) : WithTop ℚ)) :
    ¬a.Beli2019Lemma814ExceptionC b := by
  intro C
  have hfour := C.rank_four
  have hthree : 3 ≤ N + 2 := by omega
  let thirdAlpha : Fin (N + 2) := ⟨2, by omega⟩
  let thirdAdjacent : Fin (N + 2) := ⟨2, by omega⟩
  have htailAnisotropic :=
    a.lemma814TailFirstThreeAnisotropic_of_firstValue_eq
      b hfirst C hthree
  have hneTail :=
    a.tail.hilbertSymbol_firstAdjacent_secondAdjacent_ne_one
      hthree htailAnisotropic
  have hne :
      hilbertSymbol K
        (a.adjacentProduct (1 : Fin (N + 2)))
        (a.adjacentProduct thirdAdjacent) ≠ 1 := by
    simp only [a.adjacentProduct_tail] at hneTail
    let tailFirst : Fin (N + 1) := ⟨0, by omega⟩
    let tailSecond : Fin (N + 1) := ⟨1, by omega⟩
    have hneTail' :
        hilbertSymbol K (a.adjacentProduct tailFirst.succ)
          (a.adjacentProduct tailSecond.succ) ≠ 1 := by
      simpa only [tailFirst, tailSecond] using hneTail
    have hfirstIndex : tailFirst.succ =
        (1 : Fin (N + 2)) := by
      apply Fin.ext
      rfl
    have hsecondIndex : tailSecond.succ =
        thirdAdjacent := by
      apply Fin.ext
      rfl
    rw [hfirstIndex, hsecondIndex] at hneTail'
    exact hneTail'
  have hfirstThirdRaw := a.truncatedPrefixDefect_le_defect b (-1) 3 1
  rw [a.lemma814FirstThirdRawDefect_eq_adjacentDefect_of_firstValue_eq
    b hfirst] at hfirstThirdRaw
  have hsecondLower :
      (a.alphaValue thirdAlpha : WithTop ℚ) ≤
        a.adjacentDefect (1 : Fin (N + 2)) := by
    calc
      (a.alphaValue thirdAlpha : WithTop ℚ) =
          a.lemma814FirstThirdCappedDefect b := by
        simpa only [thirdAlpha] using C.firstThirdDefect_eq_alpha.symm
      _ ≤ a.adjacentDefect (1 : Fin (N + 2)) := hfirstThirdRaw
  have hthirdStrict :
      (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) <
        a.adjacentDefect thirdAdjacent := by
    simpa only [thirdAdjacent] using
      a.secondAlpha_lt_adjacentDefect_two_of_lemma814ExceptionC
        b hbinary C hfour
  have hsumQ :=
    a.secondAlpha_add_thirdAlpha_eq_twoE_of_lemma814ExceptionC
      b C hthree
  have hboundaryQ :
      ((2 * ramificationIndex K : Nat) : ℚ) =
        a.alphaValue thirdAlpha +
          a.alphaValue (1 : Fin (N + 2)) := by
    push_cast
    rw [add_comm]
    simpa only [thirdAlpha] using hsumQ.symm
  have hboundary :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) =
        (a.alphaValue thirdAlpha : WithTop ℚ) +
          (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) := by
    rw [← WithTop.coe_add]
    exact congrArg (fun x : ℚ ↦ (x : WithTop ℚ)) hboundaryQ
  have hdefectSum :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        a.adjacentDefect (1 : Fin (N + 2)) +
          a.adjacentDefect thirdAdjacent := by
    calc
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) =
          (a.alphaValue thirdAlpha : WithTop ℚ) +
            (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) := hboundary
      _ < a.adjacentDefect (1 : Fin (N + 2)) +
          a.adjacentDefect thirdAdjacent :=
        WithTop.add_lt_add_of_le_of_lt WithTop.coe_ne_top
          hsecondLower hthirdStrict
  have hone :
      hilbertSymbol K
        (a.adjacentProduct (1 : Fin (N + 2)))
        (a.adjacentProduct thirdAdjacent) = 1 := by
    apply hilbertSymbol_eq_one_of_defectOrder_add_gt_two_mul_e
    simpa only [adjacentDefect] using hdefectSum
  exact hne hone

/-- A good BONG whose first value already equals the prescribed unary value
cannot satisfy the exceptional alternative.  Corollary 8.10 first changes its
tail to the normal form used in the proofs of (b) and (c). -/
theorem not_lemma814Exceptional_of_firstValue_eq
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
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (hfirst : a.valueUnit (0 : Fin (N + 3)) =
      b.valueUnit (0 : Fin 1)) :
    ¬a.Beli2019Lemma814Exceptional b := by
  letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
  rcases a.beli2019Corollary810 with ⟨D⟩
  have hfirst' : D.transformed.valueUnit (0 : Fin (N + 3)) =
      b.valueUnit (0 : Fin 1) := D.headValue_eq.trans hfirst
  have hinvariant := a.lemma814Exceptional_changeBONG_iff_full
    (classificationV := classificationV)
    (classificationW := classificationW)
    (prefixChangeV := prefixChangeV)
    (prefixChangeW := prefixChangeW) D.transformed b
  intro E
  rcases hinvariant.mp E with A | B | C
  · exact D.transformed.not_lemma814ExceptionA_of_firstValue_eq
      b hfirst' A
  · exact D.transformed.not_lemma814ExceptionB_of_firstValue_eq_of_firstBinary
      b hfirst' D.firstBinaryAlpha_eq B
  · exact D.transformed.not_lemma814ExceptionC_of_firstValue_eq_of_firstBinary
      b hfirst' D.firstBinaryAlpha_eq C

/-- Necessity in Beli (2019), Lemma 8.14: every good-BONG transform with
prescribed first value rules out all three exceptional alternatives. -/
theorem beli2019Lemma814_necessity
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
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1) :
    Nonempty (a.Beli2019PrescribedFirstValueTransform b) →
      ¬a.Beli2019Lemma814Exceptional b := by
  rintro ⟨T⟩ E
  have hinvariant := a.lemma814Exceptional_changeBONG_iff_full
    (classificationV := classificationV)
    (classificationW := classificationW)
    (prefixChangeV := prefixChangeV)
    (prefixChangeW := prefixChangeW) T.transformed b
  apply T.transformed.not_lemma814Exceptional_of_firstValue_eq
    (classificationV := classificationV)
    (classificationW := classificationW)
    (prefixChangeV := prefixChangeV)
    (prefixChangeW := prefixChangeW) b T.firstValue_eq
  exact hinvariant.mp E

end BONG.GoodBONG

end Bong
