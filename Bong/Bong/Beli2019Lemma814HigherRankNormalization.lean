/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma814HigherRank

/-!
# Beli (2019), Lemma 8.14: second higher-rank normalization

After a local exception (c) has forced the numerical boundary data, the
paper applies Corollary 8.11 once more to the initial quaternary lattice.
This file inserts that normalized quaternary BONG back into the ambient
lattice and records precisely the invariant consequences used by the two
higher-rank order branches.
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

namespace Beli2019Lemma814HigherRankAlphaData

/-- The numerical alpha package is invariant under a change of good BONG
of the same ambient lattice. -/
theorem changeBONG
    [Beli2006AlphaLaws.{u, v} K]
    [classification : GoodBONGClassificationLaws.{u, v, v} K]
    {a : GoodBONG q L (N + 5)}
    (A : a.Beli2019Lemma814HigherRankAlphaData (by omega))
    (a' : GoodBONG q L (N + 5)) :
    a'.Beli2019Lemma814HigherRankAlphaData (by omega) := by
  letI : GoodBONGClassificationLaws.{u, v, v} K := classification
  have halphas := a.alpha_invariant a'
  have hhalf := a.halfGapValue_invariant
    (classificationV := classification) a'
      (⟨2, by omega⟩ : Fin (N + 4))
  refine {
    first_odd := ?_
    second_odd := ?_
    third_odd := ?_
    first_lt_twoE := ?_
    second_lt_twoE := ?_
    third_lt_twoE := ?_
    second_third_sum := ?_
    third_eq_halfGap := ?_
    fourth_eq_second := ?_
  }
  · simpa only [halphas (0 : Fin (N + 4))] using A.first_odd
  · simpa only [halphas (1 : Fin (N + 4))] using A.second_odd
  · simpa only [halphas (⟨2, by omega⟩ : Fin (N + 4))] using A.third_odd
  · simpa only [halphas (0 : Fin (N + 4))] using A.first_lt_twoE
  · simpa only [halphas (1 : Fin (N + 4))] using A.second_lt_twoE
  · simpa only [halphas (⟨2, by omega⟩ : Fin (N + 4))] using A.third_lt_twoE
  · simpa only [halphas (1 : Fin (N + 4)),
      halphas (⟨2, by omega⟩ : Fin (N + 4))] using A.second_third_sum
  · calc
      a'.alphaValue (⟨2, by omega⟩ : Fin (N + 4)) =
          a.alphaValue (⟨2, by omega⟩ : Fin (N + 4)) :=
        (halphas _).symm
      _ = a.halfGapValue (⟨2, by omega⟩ : Fin (N + 4)) :=
        A.third_eq_halfGap
      _ = a'.halfGapValue (⟨2, by omega⟩ : Fin (N + 4)) := hhalf
  · calc
      a'.alphaValue (⟨3, by omega⟩ : Fin (N + 4)) =
          a.alphaValue (⟨3, by omega⟩ : Fin (N + 4)) :=
        (halphas _).symm
      _ = a.alphaValue (1 : Fin (N + 4)) := A.fourth_eq_second
      _ = a'.alphaValue (1 : Fin (N + 4)) := halphas _

end Beli2019Lemma814HigherRankAlphaData

/-- The ambient output of normalizing the first binary pair inside the
initial quaternary lattice. -/
structure Beli2019Lemma814HigherRankFirstBinaryData
    (a : GoodBONG q L (N + 5)) where
  transformed : GoodBONG q L (N + 5)
  alphaData : transformed.Beli2019Lemma814HigherRankAlphaData (by omega)
  firstFourRawDefect_eq_secondAlpha :
    defectOrder (K := K) (transformed.prefixProduct 4) =
      (transformed.alphaValue (1 : Fin (N + 4)) : WithTop ℚ)
  secondAlpha_lt_thirdAdjacentDefect :
    (transformed.alphaValue (1 : Fin (N + 4)) : WithTop ℚ) <
      transformed.adjacentDefect (⟨2, by omega⟩ : Fin (N + 4))

/-- Corollary 8.11 on the initial four entries, followed by Lemma 4.9(ii),
produces the ambient first-binary normal form used in the final two cases of
the higher-rank proof. -/
theorem exists_lemma814HigherRankFirstBinaryData
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
    [BONGStructuralLaws.{u, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    (a : GoodBONG q L (N + 5)) (b : GoodBONG r M 1)
    (A : a.Beli2019Lemma814HigherRankAlphaData (by omega))
    (halphas : ∀ i : Fin 3,
      (a.lemma814InitialFour (by omega)).alphaValue i =
        a.alphaValue ⟨i.1, by omega⟩)
    (C : Beli2019Lemma814ExceptionC
      (a.lemma814InitialFour (by omega)) b) :
    Nonempty a.Beli2019Lemma814HigherRankFirstBinaryData := by
  classical
  letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
  let s := a.lemma814InitialFour (by omega)
  rcases s.beli2019Corollary811 (0 : Fin 3) with ⟨D⟩
  let c := D.transformed
  have hbinary : c.firstBinaryAlpha =
      (c.alphaValue (0 : Fin 3) : WithTop ℚ) := by
    simpa only [c, adjacentBinaryAlpha_zero] using D.adjacentBinaryAlpha_eq
  have Cc : c.Beli2019Lemma814ExceptionC b :=
    (s.lemma814ExceptionC_changeBONG_iff_rankFour
      (classificationV := classificationV)
      (classificationW := classificationW)
      (prefixChangeV := prefixChangeV)
      (prefixChangeW := prefixChangeW) c b).mp C
  have hcRaw : defectOrder (K := K) (c.prefixProduct 4) =
      (c.alphaValue (1 : Fin 3) : WithTop ℚ) :=
    c.lemma814FirstFourRawDefect_eq_secondAlpha_of_exceptionC b Cc
  have hcStrict : (c.alphaValue (1 : Fin 3) : WithTop ℚ) <
      c.adjacentDefect (2 : Fin 3) :=
    c.secondAlpha_lt_adjacentDefect_two_of_lemma814ExceptionC
      b hbinary Cc (by omega)
  rcases a.toBONG.beliLemma49_ii a.good
      (a.lemma814InitialFourSegment (by omega)) c.toBONG c.good with
    ⟨replacement⟩
  let transformed : GoodBONG q L (N + 5) :=
    ⟨replacement.bong, replacement.good⟩
  have hinsValue (i : Fin 4) :
      transformed.valueUnit ⟨i.1, by omega⟩ = c.valueUnit i := by
    apply Units.ext
    change replacement.bong.value ⟨i.1, by omega⟩ = c.toBONG.value i
    rw [← replacement.bong.quadratic_ambientVector,
      ← c.toBONG.quadratic_ambientVector]
    change q.quadratic (replacement.bong.ambientVector ⟨i.1, by omega⟩) =
      q.quadratic (c.toBONG.ambientVector i : V)
    simpa only [Nat.zero_add] using congrArg q.quadratic
      (replacement.inside_eq i)
  have hprefix (k : Nat) (hk : k ≤ 4) :
      transformed.prefixProduct k = c.prefixProduct k := by
    induction k with
    | zero =>
        simp only [GoodBONG.prefixProduct, BONG.prefixProduct_zero]
    | succ k ih =>
        have hkFour : k < 4 := by omega
        have hkAmbient : k < N + 5 := by omega
        unfold GoodBONG.prefixProduct
        rw [transformed.toBONG.prefixProduct_succ k hkAmbient,
          c.toBONG.prefixProduct_succ k hkFour]
        have ih' := ih (by omega)
        change transformed.toBONG.prefixProduct k =
          c.toBONG.prefixProduct k at ih'
        rw [ih']
        congr 1
        exact hinsValue ⟨k, hkFour⟩
  have hadjacent : transformed.adjacentDefect
      (⟨2, by omega⟩ : Fin (N + 4)) = c.adjacentDefect (2 : Fin 3) := by
    have htwo : transformed.valueUnit
        (⟨2, by omega⟩ : Fin (N + 4)).castSucc =
          c.valueUnit (2 : Fin 3).castSucc := by
      simpa using hinsValue (2 : Fin 4)
    have hthree : transformed.valueUnit
        (⟨2, by omega⟩ : Fin (N + 4)).succ =
          c.valueUnit (2 : Fin 3).succ := by
      simpa using hinsValue (3 : Fin 4)
    unfold adjacentDefect adjacentProduct
    rw [htwo, hthree]
  have hlocalAlphas := s.alpha_invariant c
  have hglobalAlphas := a.alpha_invariant transformed
  have halphaOne : s.alphaValue (1 : Fin 3) =
      a.alphaValue (1 : Fin (N + 4)) := by
    have h := halphas (1 : Fin 3)
    convert h using 1
    congr 1
  have hraw : defectOrder (K := K) (transformed.prefixProduct 4) =
      (transformed.alphaValue (1 : Fin (N + 4)) : WithTop ℚ) := by
    calc
      defectOrder (K := K) (transformed.prefixProduct 4) =
          defectOrder (K := K) (c.prefixProduct 4) := by rw [hprefix 4 (by omega)]
      _ = (c.alphaValue (1 : Fin 3) : WithTop ℚ) := hcRaw
      _ = (s.alphaValue (1 : Fin 3) : WithTop ℚ) := by
        exact congrArg (fun x : ℚ ↦ (x : WithTop ℚ))
          (hlocalAlphas (1 : Fin 3)).symm
      _ = (a.alphaValue (1 : Fin (N + 4)) : WithTop ℚ) := by
        exact congrArg (fun x : ℚ ↦ (x : WithTop ℚ)) halphaOne
      _ = (transformed.alphaValue (1 : Fin (N + 4)) : WithTop ℚ) :=
        congrArg (fun x : ℚ ↦ (x : WithTop ℚ))
          (hglobalAlphas (1 : Fin (N + 4)))
  have hstrict :
      (transformed.alphaValue (1 : Fin (N + 4)) : WithTop ℚ) <
        transformed.adjacentDefect (⟨2, by omega⟩ : Fin (N + 4)) := by
    calc
      (transformed.alphaValue (1 : Fin (N + 4)) : WithTop ℚ) =
          (c.alphaValue (1 : Fin 3) : WithTop ℚ) := by
        exact congrArg (fun x : ℚ ↦ (x : WithTop ℚ)) <| by
          rw [← hglobalAlphas (1 : Fin (N + 4))]
          calc
            a.alphaValue (1 : Fin (N + 4)) = s.alphaValue (1 : Fin 3) :=
              halphaOne.symm
            _ = c.alphaValue (1 : Fin 3) := hlocalAlphas (1 : Fin 3)
      _ < c.adjacentDefect (2 : Fin 3) := hcStrict
      _ = transformed.adjacentDefect
          (⟨2, by omega⟩ : Fin (N + 4)) := hadjacent.symm
  exact ⟨{
    transformed := transformed
    alphaData := A.changeBONG transformed
    firstFourRawDefect_eq_secondAlpha := hraw
    secondAlpha_lt_thirdAdjacentDefect := hstrict
  }⟩

end BONG.GoodBONG

end Bong
