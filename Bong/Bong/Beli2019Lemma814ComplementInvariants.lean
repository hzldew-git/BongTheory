/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma814GeometricInvariants
import Bong.Bong.DiagonalQuaternaryComplement

/-!
# Beli (2019), Lemma 8.14(c): complement invariance

This file formalizes the Hasse-symbol comparison for the ternary complement
in exception (c).  The comparison itself is derived from the numerical
conditions in (c).  Existence of a complement for the second quaternary
prefix is kept as a separate witness: anisotropy is then forced by the
comparison.  This distinction mirrors the logical split between orthogonal
complement existence and Hasse-invariant classification.
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

/-- A unit-valued ternary complement of `[b_1]` in the quaternary prefix.
This is the nondegenerate presentation used by the Hasse calculation. -/
noncomputable def Lemma814FirstFourUnitComplement
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (hfour : 4 ≤ N + 3) : Prop :=
  ∃ complement : Fin 3 → Kˣ,
    DiagonalRepresents
      (diagonalUnitCoefficients
        (Fin.cons (b.valueUnit (0 : Fin 1)) complement))
      (diagonalUnitCoefficients (a.prefixValueUnits 4 hfour))

/-- Quaternary universality supplies the complement whose existence is
implicit in Beli's notation `V \top [b₁]`. -/
theorem lemma814FirstFourUnitComplement_of_quaternaryLaws
    [DyadicQuaternaryComplementLaws K]
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (hfour : 4 ≤ N + 3) :
    a.Lemma814FirstFourUnitComplement b hfour := by
  exact diagonalQuaternary_hasComplement
    (b.valueUnit (0 : Fin 1)) (a.prefixValueUnits 4 hfour)

/-- An anisotropic field-valued complement canonically yields a
unit-valued complement. -/
theorem lemma814FirstFourUnitComplement_of_anisotropic
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (hfour : 4 ≤ N + 3)
    (h : a.Lemma814FirstFourComplementAnisotropic b hfour) :
    ∃ complement : Fin 3 → Kˣ,
      DiagonalRepresents
        (diagonalUnitCoefficients
          (Fin.cons (b.valueUnit (0 : Fin 1)) complement))
        (diagonalUnitCoefficients (a.prefixValueUnits 4 hfour)) ∧
      DiagonalAnisotropic (diagonalUnitCoefficients complement) := by
  rcases h with ⟨complement, hrep, hanisotropic⟩
  have hne : ∀ i, complement i ≠ 0 := by
    intro i
    exact diagonalAnisotropic_coefficient_ne_zero
      complement hanisotropic i
  let complementUnits := diagonalUnitization complement hne
  refine ⟨complementUnits, ?_, ?_⟩
  · simpa only [complementUnits,
      diagonalUnitCoefficients_cons,
      diagonalUnitCoefficients_unitization,
      diagonalUnitCoefficients_prefixValueUnits,
      GoodBONG.coe_valueUnit] using hrep
  · change DiagonalAnisotropic complement
    exact hanisotropic

/-- A unit-valued complement together with its anisotropy gives the literal
field-valued complement predicate in Lemma 8.14(c). -/
theorem lemma814FirstFourComplementAnisotropic_of_unit
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (hfour : 4 ≤ N + 3) (complement : Fin 3 → Kˣ)
    (hrep : DiagonalRepresents
      (diagonalUnitCoefficients
        (Fin.cons (b.valueUnit (0 : Fin 1)) complement))
      (diagonalUnitCoefficients (a.prefixValueUnits 4 hfour)))
    (hanisotropic :
      DiagonalAnisotropic (diagonalUnitCoefficients complement)) :
    a.Lemma814FirstFourComplementAnisotropic b hfour := by
  refine ⟨diagonalUnitCoefficients complement, ?_, hanisotropic⟩
  simpa only [diagonalUnitCoefficients_cons,
    diagonalUnitCoefficients_prefixValueUnits,
    GoodBONG.coe_valueUnit] using hrep

/-- The complementary defect at the third gap and its half-gap add to
`2e`. -/
theorem lemma814ThirdComplementaryDefect_add_halfGap
    (a : GoodBONG q L (N + 3)) (hfour : 4 ≤ N + 3) :
    a.lemma814ThirdComplementaryDefect hfour +
        a.halfGapValue (⟨2, by omega⟩ : Fin (N + 2)) =
      2 * (ramificationIndex K : ℚ) := by
  unfold lemma814ThirdComplementaryDefect halfGapValue
  ring

set_option maxHeartbeats 600000 in
-- Dependent finite-index proof terms in the two exception fields require
-- additional normalization during elaboration.
/-- In rank at least five, exception (c) implies the strict inequality
`alpha_3 + alpha_4 > 2e` used by classification condition (iv). -/
theorem alphaThree_add_alphaFour_strict_of_lemma814ExceptionC
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (C : a.Beli2019Lemma814ExceptionC b) (hfive : 5 ≤ N + 3) :
    2 * (ramificationIndex K : ℚ) <
      a.alphaValue (⟨2, by omega⟩ : Fin (N + 2)) +
        a.alphaValue (⟨3, by omega⟩ : Fin (N + 2)) := by
  have hcomplement :=
    a.lemma814ThirdComplementaryDefect_add_halfGap C.rank_four
  have hthird := C.thirdAlpha_eq_halfGap
  have hlater := C.laterAlpha_strict hfive
  linarith

/-- Classification condition (iv) embeds the first ternary prefix of the
second BONG into the first quaternary prefix of the first BONG. -/
theorem lemma814FirstThree_represents_firstFour_of_exceptionC
    [GoodBONGClassificationLaws.{u, v, v} K]
    (a a' : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (C : a.Beli2019Lemma814ExceptionC b) (hfive : 5 ≤ N + 3) :
    DiagonalRepresents
      (diagonalUnitCoefficients (a'.prefixValueUnits 3 (by omega)))
      (diagonalUnitCoefficients (a.prefixValueUnits 4 C.rank_four)) := by
  have hinter := a.internalRepresentationConditions_sameLattice a'
  have hvalues : DiagonalRepresents
      (a'.prefixValues 3 (by omega))
      (a.prefixValues 4 C.rank_four) := by
    apply hinter (⟨3, by omega⟩ : Fin (N + 2)) (by norm_num)
    exact a.alphaThree_add_alphaFour_strict_of_lemma814ExceptionC
      b C hfive
  simpa only [diagonalUnitCoefficients_prefixValueUnits] using hvalues

/-- The two defect bounds in exception (c) force the residual Hilbert symbol
in Beli's quaternary-complement comparison to be one. -/
theorem lemma814ComplementResidual_hilbert_eq_one
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    [HilbertSymbolLaws K]
    (a a' : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (C : a.Beli2019Lemma814ExceptionC b) (hfive : 5 ≤ N + 3) :
    hilbertSymbol K
      (a.prefixProduct 4 * a'.prefixProduct 4)
      (-(a'.prefixProduct 3 * b.valueUnit (0 : Fin 1))) = 1 := by
  letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
  let thirdAlpha : Fin (N + 2) := ⟨2, by omega⟩
  let fourthAlpha : Fin (N + 2) := ⟨3, by omega⟩
  have hfourthDefect :
      (a.alphaValue fourthAlpha : WithTop ℚ) ≤
        defectOrder (K := K)
          (a.prefixProduct 4 * a'.prefixProduct 4) := by
    have hbound := a.prefixChangeDefectBound_of_classification a' 4
    rw [a.prefixAlphaCap_of_internal (by omega) (by omega)] at hbound
    simpa only [fourthAlpha] using hbound
  have hbProduct : b.prefixProduct 1 = b.valueUnit (0 : Fin 1) := by
    unfold GoodBONG.prefixProduct GoodBONG.valueUnit
    have h := b.toBONG.prefixProduct_succ 0 (by omega)
    rw [b.toBONG.prefixProduct_zero, one_mul] at h
    convert h using 1
    apply congrArg b.toBONG.valueUnit
    apply Fin.ext
    rfl
  have hthirdDefect :
      (a.alphaValue thirdAlpha : WithTop ℚ) ≤
        defectOrder (K := K)
          (-(a'.prefixProduct 3 * b.valueUnit (0 : Fin 1))) := by
    calc
      (a.alphaValue thirdAlpha : WithTop ℚ) =
          a.lemma814FirstThirdCappedDefect b := by
        simpa only [thirdAlpha] using C.firstThirdDefect_eq_alpha.symm
      _ = a'.lemma814FirstThirdCappedDefect b :=
        a.lemma814FirstThirdCappedDefect_invariant
          (classificationV := classificationV)
          (classificationW := classificationW)
          (prefixChangeV := prefixChangeV)
          (prefixChangeW := prefixChangeW) a' b
      _ ≤ defectOrder (K := K)
          (-(a'.prefixProduct 3 * b.valueUnit (0 : Fin 1))) := by
        have hraw := a'.truncatedPrefixDefect_le_defect b (-1) 3 1
        simpa only [lemma814FirstThirdCappedDefect, hbProduct,
          neg_mul, one_mul] using hraw
  have hsum : 2 * (ramificationIndex K : ℚ) <
      a.alphaValue fourthAlpha + a.alphaValue thirdAlpha := by
    have h := a.alphaThree_add_alphaFour_strict_of_lemma814ExceptionC
      b C hfive
    rw [add_comm]
    simpa only [thirdAlpha, fourthAlpha] using h
  have hsumTop :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        (a.alphaValue fourthAlpha : WithTop ℚ) +
          (a.alphaValue thirdAlpha : WithTop ℚ) := by
    exact_mod_cast hsum
  exact hilbertSymbol_eq_one_of_defectOrder_add_gt_two_mul_e
    (hsumTop.trans_le (add_le_add hfourthDefect hthirdDefect))

set_option maxHeartbeats 800000 in
-- The proof aligns two dependent four-term prefixes before applying the
-- generic ternary-complement Hasse comparison.
/-- In rank at least five, any ternary complement for the second quaternary
prefix is anisotropic whenever exception (c) holds for the first BONG. -/
theorem lemma814FirstFourComplementAnisotropic_of_changeBONG_ge_five
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [HilbertSymbolLaws K]
    (a a' : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (C : a.Beli2019Lemma814ExceptionC b) (hfive : 5 ≤ N + 3)
    (hunit' : a'.Lemma814FirstFourUnitComplement b C.rank_four) :
    a'.Lemma814FirstFourComplementAnisotropic b C.rank_four := by
  letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
  rcases a.lemma814FirstFourUnitComplement_of_anisotropic b C.rank_four
      C.firstFourComplement_anisotropic with
    ⟨complement, hcomplementRaw, hanisotropic⟩
  rcases hunit' with ⟨complement', hcomplementRaw'⟩
  let base := a.prefixValueUnits 4 C.rank_four
  let head := a'.prefixValueUnits 3 (by omega)
  let last := a'.valueUnit (⟨3, by omega⟩ : Fin (N + 3))
  have hother : a'.prefixValueUnits 4 C.rank_four =
      Fin.snoc head last := by
    simpa only [head, last] using
      a'.prefixValueUnits_succ_eq_snoc 3 C.rank_four
  have hheadRep : DiagonalRepresents
      (diagonalUnitCoefficients head)
      (diagonalUnitCoefficients base) := by
    simpa only [head, base] using
      a.lemma814FirstThree_represents_firstFour_of_exceptionC
        a' b C hfive
  have hcomplement : DiagonalRepresents
      (diagonalUnitCoefficients
        (Fin.cons (b.valueUnit (0 : Fin 1)) complement))
      (diagonalUnitCoefficients base) := by
    simpa only [base] using hcomplementRaw
  have hcomplement' : DiagonalRepresents
      (diagonalUnitCoefficients
        (Fin.cons (b.valueUnit (0 : Fin 1)) complement'))
      (diagonalUnitCoefficients (Fin.snoc head last)) := by
    rw [← hother]
    exact hcomplementRaw'
  have hbaseDet : diagonalUnitDeterminant base = a.prefixProduct 4 := by
    simpa only [base] using
      a.diagonalUnitDeterminant_prefixValueUnits 4 C.rank_four
  have hheadDet : diagonalUnitDeterminant head = a'.prefixProduct 3 := by
    simpa only [head] using
      a'.diagonalUnitDeterminant_prefixValueUnits 3 (by omega)
  have hotherDet :
      diagonalUnitDeterminant (Fin.snoc head last) =
        a'.prefixProduct 4 := by
    rw [← hother]
    exact a'.diagonalUnitDeterminant_prefixValueUnits 4 C.rank_four
  have hresidual : hilbertSymbol K
      (diagonalUnitDeterminant base *
        diagonalUnitDeterminant (Fin.snoc head last))
      (-(diagonalUnitDeterminant head *
        b.valueUnit (0 : Fin 1))) = 1 := by
    simpa only [hbaseDet, hheadDet, hotherDet] using
      a.lemma814ComplementResidual_hilbert_eq_one
        (classificationV := classificationV)
        (classificationW := classificationW)
        (prefixChangeV := prefixChangeV)
        (prefixChangeW := prefixChangeW) a' b C hfive
  have hanisotropic' :
      DiagonalAnisotropic (diagonalUnitCoefficients complement') :=
    (diagonalTernaryComplementAnisotropic_iff_of_hilbert
      base head (b.valueUnit (0 : Fin 1)) last complement complement'
      hheadRep hcomplement hcomplement' hresidual).mp hanisotropic
  exact a'.lemma814FirstFourComplementAnisotropic_of_unit
    b C.rank_four complement' hcomplementRaw' hanisotropic'

/-- All fields of exception (c), including complement anisotropy, transport
to another good BONG in rank at least five. -/
theorem lemma814ExceptionC_of_changeBONG_ge_five
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [HilbertSymbolLaws K]
    [DyadicQuaternaryComplementLaws K]
    (a a' : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (C : a.Beli2019Lemma814ExceptionC b) (hfive : 5 ≤ N + 3) :
    a'.Beli2019Lemma814ExceptionC b := by
  apply a.lemma814ExceptionC_of_changeBONG
    (classificationV := classificationV)
    (classificationW := classificationW)
    (prefixChangeV := prefixChangeV)
    (prefixChangeW := prefixChangeW) a' b C
  apply a.lemma814FirstFourComplementAnisotropic_of_changeBONG_ge_five
    (classificationV := classificationV)
    (classificationW := classificationW)
    (prefixChangeV := prefixChangeV)
    (prefixChangeW := prefixChangeW) a' b C hfive
  exact a'.lemma814FirstFourUnitComplement_of_quaternaryLaws
    b C.rank_four

/-- Exception (c) is independent of the chosen good BONG in every rank in
which it can occur.  Rank four uses whole-space isometry; rank at least five
uses the complement Hasse comparison above. -/
theorem lemma814ExceptionC_changeBONG_iff
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [HilbertSymbolLaws K]
    [DyadicQuaternaryComplementLaws K]
    (a a' : GoodBONG q L (N + 3)) (b : GoodBONG r M 1) :
    a.Beli2019Lemma814ExceptionC b ↔
      a'.Beli2019Lemma814ExceptionC b := by
  constructor
  · intro C
    by_cases hfive : 5 ≤ N + 3
    · exact a.lemma814ExceptionC_of_changeBONG_ge_five
        (classificationV := classificationV)
        (classificationW := classificationW)
        (prefixChangeV := prefixChangeV)
        (prefixChangeW := prefixChangeW) a' b C hfive
    · have hfour := C.rank_four
      have hN : N = 1 := by omega
      subst N
      exact (a.lemma814ExceptionC_changeBONG_iff_rankFour
        (classificationV := classificationV)
        (classificationW := classificationW)
        (prefixChangeV := prefixChangeV)
        (prefixChangeW := prefixChangeW) a' b).mp C
  · intro C
    by_cases hfive : 5 ≤ N + 3
    · exact a'.lemma814ExceptionC_of_changeBONG_ge_five
        (classificationV := classificationV)
        (classificationW := classificationW)
        (prefixChangeV := prefixChangeV)
        (prefixChangeW := prefixChangeW) a b C hfive
    · have hfour := C.rank_four
      have hN : N = 1 := by omega
      subst N
      exact (a.lemma814ExceptionC_changeBONG_iff_rankFour
        (classificationV := classificationV)
        (classificationW := classificationW)
        (prefixChangeV := prefixChangeV)
        (prefixChangeW := prefixChangeW) a' b).mpr C

end BONG.GoodBONG

end Bong
