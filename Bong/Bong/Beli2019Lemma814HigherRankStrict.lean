/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma814HigherRankSegments

/-!
# Beli (2019), Lemma 8.14: the `R₃ < R₅` branch

Lemma 8.8 changes the first value of `[a₄, ..., aₙ]`.  Lemma 4.9(ii)
inserts that suffix back into the ambient BONG, and Lemma 8.1(ii) raises
the raw defect of the first four values.  This destroys local exception
(c).
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

/-- The ambient coordinate change obtained by inserting a successful
Lemma 8.8 transformation of `[a₄, ..., aₙ]`. -/
structure Beli2019Lemma814TailScalingData
    (a : GoodBONG q L (N + 5)) where
  epsilon : Kˣ
  epsilon_isValuationUnit : IsValuationUnit K (epsilon : K)
  epsilon_defect : defectOrder (K := K) epsilon =
    (a.alphaValue (1 : Fin (N + 4)) : WithTop ℚ)
  transformed : GoodBONG q L (N + 5)
  firstValue_eq : transformed.valueUnit (0 : Fin (N + 5)) =
    a.valueUnit (0 : Fin (N + 5))
  secondValue_eq : transformed.valueUnit (1 : Fin (N + 5)) =
    a.valueUnit (1 : Fin (N + 5))
  thirdValue_eq : transformed.valueUnit (⟨2, by omega⟩ : Fin (N + 5)) =
    a.valueUnit (⟨2, by omega⟩ : Fin (N + 5))
  fourthValue_eq : transformed.valueUnit (⟨3, by omega⟩ : Fin (N + 5)) =
    epsilon * a.valueUnit (⟨3, by omega⟩ : Fin (N + 5))

/-- Insert a chosen suffix transformation by Beli (2003), Lemma 4.9(ii). -/
theorem lemma814TailScalingData_of_transform
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    (a : GoodBONG q L (N + 5))
    (D : a.Beli2019Lemma814HigherRankAlphaData (by omega))
    (hthirdFifth : a.order (⟨2, by omega⟩ : Fin (N + 5)) <
      a.order (⟨4, by omega⟩ : Fin (N + 5)))
    (T : a.lemma814Tail.Beli2019FirstValueTransform) :
    Nonempty a.Beli2019Lemma814TailScalingData := by
  rcases a.toBONG.beliLemma49_ii a.good a.lemma814TailSegment
      T.transformed.toBONG T.transformed.good with ⟨replacement⟩
  let transformed : GoodBONG q L (N + 5) :=
    ⟨replacement.bong, replacement.good⟩
  have beforeValue_eq (i : Fin (N + 5)) (hi : i.1 < 3) :
      transformed.valueUnit i = a.valueUnit i := by
    apply Units.ext
    change replacement.bong.value i = a.toBONG.value i
    rw [← replacement.bong.quadratic_ambientVector,
      ← a.toBONG.quadratic_ambientVector]
    exact congrArg q.quadratic (replacement.before_eq i hi)
  have hfourthLocal : transformed.valueUnit
      (⟨3, by omega⟩ : Fin (N + 5)) =
        T.transformed.valueUnit (0 : Fin (N + 2)) := by
    apply Units.ext
    change replacement.bong.value ⟨3, by omega⟩ =
      T.transformed.toBONG.value 0
    rw [← replacement.bong.quadratic_ambientVector,
      ← T.transformed.toBONG.quadratic_ambientVector]
    change q.quadratic (replacement.bong.ambientVector ⟨3, by omega⟩) =
      q.quadratic (T.transformed.toBONG.ambientVector 0 : V)
    exact congrArg q.quadratic (replacement.inside_eq (0 : Fin (N + 2)))
  have htailFirst : a.lemma814Tail.valueUnit (0 : Fin (N + 2)) =
      a.valueUnit (⟨3, by omega⟩ : Fin (N + 5)) := by
    have h := a.lemma814Tail_valueUnit_eq (0 : Fin (N + 2))
    convert h using 1
    congr 1
  have halpha :=
    a.lemma814Tail_alpha_zero_eq_fourthAlpha_of_third_lt_fifth
      D hthirdFifth
  have hepsilon : defectOrder (K := K) T.epsilon =
      (a.alphaValue (1 : Fin (N + 4)) : WithTop ℚ) :=
    T.epsilon_defect.trans <|
      (congrArg (fun x : ℚ ↦ (x : WithTop ℚ)) halpha).trans <|
        congrArg (fun x : ℚ ↦ (x : WithTop ℚ)) D.fourth_eq_second
  exact ⟨{
    epsilon := T.epsilon
    epsilon_isValuationUnit := T.epsilon_isValuationUnit
    epsilon_defect := hepsilon
    transformed := transformed
    firstValue_eq := beforeValue_eq (0 : Fin (N + 5)) (by norm_num)
    secondValue_eq := beforeValue_eq (1 : Fin (N + 5)) (by norm_num)
    thirdValue_eq := beforeValue_eq (⟨2, by omega⟩ : Fin (N + 5))
      (by norm_num)
    fourthValue_eq := hfourthLocal.trans <| T.firstValue_eq.trans <|
      congrArg (T.epsilon * ·) htailFirst
  }⟩

/-- The complete construction of the suffix scaling in the strict-order
branch. -/
theorem exists_lemma814TailScalingData_of_third_lt_fifth
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
    (a : GoodBONG q L (N + 5))
    (D : a.Beli2019Lemma814HigherRankAlphaData (by omega))
    (hthirdFifth : a.order (⟨2, by omega⟩ : Fin (N + 5)) <
      a.order (⟨4, by omega⟩ : Fin (N + 5))) :
    Nonempty a.Beli2019Lemma814TailScalingData := by
  rcases a.exists_lemma814TailFirstValueTransform_of_third_lt_fifth
      D hthirdFifth with ⟨T⟩
  exact a.lemma814TailScalingData_of_transform D hthirdFifth T

namespace Beli2019Lemma814TailScalingData

variable {a : GoodBONG q L (N + 5)}

/-- The first-four product is multiplied by the suffix multiplier. -/
theorem prefixProduct_four_eq (D : a.Beli2019Lemma814TailScalingData) :
    D.transformed.prefixProduct 4 = D.epsilon * a.prefixProduct 4 := by
  unfold GoodBONG.prefixProduct
  rw [D.transformed.toBONG.prefixProduct_succ 3 (by omega),
    D.transformed.toBONG.prefixProduct_succ 2 (by omega),
    D.transformed.toBONG.prefixProduct_succ 1 (by omega),
    D.transformed.toBONG.prefixProduct_succ 0 (by omega),
    a.toBONG.prefixProduct_succ 3 (by omega),
    a.toBONG.prefixProduct_succ 2 (by omega),
    a.toBONG.prefixProduct_succ 1 (by omega),
    a.toBONG.prefixProduct_succ 0 (by omega)]
  simp only [BONG.prefixProduct_zero, one_mul]
  have hfirst := D.firstValue_eq
  change D.transformed.toBONG.valueUnit ⟨0, by omega⟩ =
    a.toBONG.valueUnit ⟨0, by omega⟩ at hfirst
  have hsecond := D.secondValue_eq
  change D.transformed.toBONG.valueUnit ⟨1, by omega⟩ =
    a.toBONG.valueUnit ⟨1, by omega⟩ at hsecond
  have hthird := D.thirdValue_eq
  change D.transformed.toBONG.valueUnit ⟨2, by omega⟩ =
    a.toBONG.valueUnit ⟨2, by omega⟩ at hthird
  have hfourth := D.fourthValue_eq
  change D.transformed.toBONG.valueUnit ⟨3, by omega⟩ =
    D.epsilon * a.toBONG.valueUnit ⟨3, by omega⟩ at hfourth
  rw [hfirst, hsecond, hthird, hfourth]
  ac_rfl

/-- Equal finite defects of the multiplier and the old quaternary product
are raised strictly by Lemma 8.1(ii). -/
theorem firstFourRawDefect_lt_of_eq
    [QuadraticDefectLaws K]
    [DyadicResidueDefectProductLaws K]
    (D : a.Beli2019Lemma814TailScalingData)
    (hresidueTwo :
      ¬HasResidueFieldMoreThanTwoElements (K := K))
    (hraw : defectOrder (K := K) (a.prefixProduct 4) =
      (a.alphaValue (1 : Fin (N + 4)) : WithTop ℚ)) :
    (a.alphaValue (1 : Fin (N + 4)) : WithTop ℚ) <
      defectOrder (K := K) (D.transformed.prefixProduct 4) := by
  let x := a.prefixProduct 4
  have heq : quadraticDefect K D.epsilon = quadraticDefect K x :=
    quadraticDefect_eq_of_defectOrder_eq D.epsilon x
      (D.epsilon_defect.trans hraw.symm)
  have hfinite : quadraticDefect K D.epsilon ≠ ⊤ :=
    quadraticDefect_ne_top_of_defectOrder_eq_coe D.epsilon
      (a.alphaValue (1 : Fin (N + 4))) D.epsilon_defect
  have hstrictRaw := beli2019Lemma81_ii_strict hresidueTwo D.epsilon
    x heq hfinite
  have hstrict := defectOrder_lt_of_quadraticDefect_lt
    D.epsilon (D.epsilon * x) hstrictRaw
  rw [D.prefixProduct_four_eq]
  exact D.epsilon_defect ▸ hstrict

/-- After the suffix scaling, the initial quaternary segment cannot still
satisfy exception (c): that exception would force its raw determinant
defect back down to `α₂`, contradicting Lemma 8.1(ii). -/
theorem initialFour_not_exceptionC
    [QuadraticDefectLaws K]
    [DyadicResidueDefectProductLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [classification : GoodBONGClassificationLaws.{u, v, v} K]
    (D : a.Beli2019Lemma814TailScalingData)
    (A : a.Beli2019Lemma814HigherRankAlphaData (by omega))
    (b : GoodBONG r M 1)
    (hresidueTwo :
      ¬HasResidueFieldMoreThanTwoElements (K := K))
    (hraw : defectOrder (K := K) (a.prefixProduct 4) =
      (a.alphaValue (1 : Fin (N + 4)) : WithTop ℚ)) :
    ¬Beli2019Lemma814ExceptionC
      (D.transformed.lemma814InitialFour (by omega)) b := by
  letI : GoodBONGClassificationLaws.{u, v, v} K := classification
  have halphas := a.alpha_invariant D.transformed
  have hhalf := a.halfGapValue_invariant
    (classificationV := classification) D.transformed
      (⟨2, by omega⟩ : Fin (N + 4))
  have hthirdHalf : D.transformed.alphaValue
      (⟨2, by omega⟩ : Fin (N + 4)) =
        D.transformed.halfGapValue
          (⟨2, by omega⟩ : Fin (N + 4)) := by
    calc
      D.transformed.alphaValue (⟨2, by omega⟩ : Fin (N + 4)) =
          a.alphaValue (⟨2, by omega⟩ : Fin (N + 4)) :=
        (halphas _).symm
      _ = a.halfGapValue (⟨2, by omega⟩ : Fin (N + 4)) :=
        A.third_eq_halfGap
      _ = D.transformed.halfGapValue
          (⟨2, by omega⟩ : Fin (N + 4)) := hhalf
  have hbinary :=
    D.transformed.adjacentBinaryAlpha_eq_alpha_of_attainsHalfGap
      (⟨2, by omega⟩ : Fin (N + 4)) hthirdHalf
  have hlocalAlphas :=
    D.transformed.lemma814InitialFour_alphas_eq (by omega) hbinary
  intro C
  have hrawTransformed :=
    lemma814FirstFourRawDefect_eq_secondAlpha_of_initialFour_exceptionC
      D.transformed b (by omega) hlocalAlphas C
  have hstrict := D.firstFourRawDefect_lt_of_eq hresidueTwo hraw
  have halphaOne := halphas (1 : Fin (N + 4))
  rw [← halphaOne] at hrawTransformed
  rw [hrawTransformed] at hstrict
  exact (lt_irrefl _ hstrict)

end Beli2019Lemma814TailScalingData

end BONG.GoodBONG

end Bong
