/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.DiagonalTernaryScaling
import Bong.Bong.Beli2019Lemma711

/-!
# Diagonal ternary scaling with equal outer orders

This file packages the lattice-theoretic claim in the `R₁ = R₃`,
rank-three part of Beli (2019), Lemma 8.14.  Lemma 8.6 constructs a good
BONG with scaled values.  One of the three explicit alpha witnesses from
the paper then fixes its first alpha, and Lemma 7.11 identifies the new
lattice with the original one.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- The three alternatives in condition (2) of the rank-three,
equal-outer-order construction in Lemma 8.14. -/
def TernaryEqualOuterAlphaCriterion
    (a : GoodBONG q L 3) (ε η : Kˣ) : Prop :=
  a.AttainsHalfGap (0 : Fin 2) ∨
    defectOrder (K := K)
        (-(ε * a.valueUnit (1 : Fin 3) * a.valueUnit (2 : Fin 3))) =
      (a.alphaValue (0 : Fin 2) : WithTop ℚ) ∨
    defectOrder (K := K)
        (-(η * a.valueUnit (0 : Fin 3) * a.valueUnit (1 : Fin 3))) =
      (a.alphaValue (1 : Fin 2) : WithTop ℚ)

/-- Given the defect, alpha, and Hasse witnesses displayed in the paper,
the ternary scaling `[a₁,a₂,a₃] ↦ [εa₁,εηa₂,ηa₃]` is realized by a
good BONG of the original equal-outer-order lattice. -/
theorem exists_goodBONG_ternaryScaledValues_of_equalOuter
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicDiagonalClassificationLaws K]
    (a : GoodBONG q L 3) (ε η : Kˣ)
    (hεUnit : IsValuationUnit K (ε : K))
    (hηUnit : IsValuationUnit K (η : K))
    (hεDefect : (a.alphaValue (0 : Fin 2) : WithTop ℚ) ≤
      defectOrder (K := K) ε)
    (hηDefect : (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
      defectOrder (K := K) η)
    (hadjacent :
      hilbertSymbol K
          (-(η * a.valueUnit (0 : Fin 3) * a.valueUnit (1 : Fin 3)))
          (-(ε * a.valueUnit (1 : Fin 3) * a.valueUnit (2 : Fin 3))) =
        hilbertSymbol K
          (-(a.valueUnit (0 : Fin 3) * a.valueUnit (1 : Fin 3)))
          (-(a.valueUnit (1 : Fin 3) * a.valueUnit (2 : Fin 3))))
    (houter : a.order (0 : Fin 3) = a.order (2 : Fin 3))
    (halpha : a.TernaryEqualOuterAlphaCriterion ε η) :
    ∃ c : GoodBONG q L 3,
      ∀ i, c.valueUnit i = a.ternaryScaledValues ε η i := by
  rcases a.exists_ternaryScaledOrthogonalBasis ε η hadjacent with
    ⟨X, hvalues⟩
  have hordersX : X.SameOrders a :=
    a.ternaryScaled_sameOrders X ε η hεUnit hηUnit hvalues
  have hprefixX : X.PrefixDefectBounds a :=
    a.ternaryScaled_prefixDefectBounds X ε η hvalues hεDefect hηDefect
  have hfullX : IsSquare (X.comparisonPrefixUnit a 3) :=
    a.ternaryScaled_fullComparisonSquare X ε η hvalues
  rcases BONG.OrthogonalBasisData.beli2019Lemma86_i
      a X hordersX hprefixX hfullX with
    ⟨M, c₀, hreal, hgood⟩
  let c : GoodBONG q M 3 := ⟨c₀, hgood⟩
  have horders : a.SameOrders c := by
    intro i
    calc
      a.order i = X.order i := (hordersX i).symm
      _ = c.order i := X.order_eq_of_isRealizedBy hreal i
  have houterC : c.order (0 : Fin 3) = c.order (2 : Fin 3) :=
    (horders 0).symm.trans (houter.trans (horders 2))
  have hprefix : a.PrefixDefectBounds c :=
    X.prefixDefectBounds_of_isRealizedBy a hreal hprefixX
  have hfull : IsSquare (comparisonPrefixUnit a c 3) := by
    change IsSquare (a.prefixProduct 3 * c.prefixProduct 3)
    rw [← BONG.OrthogonalBasisData.prefixProduct_eq_of_isRealizedBy
      (b := c) hreal 3]
    exact hfullX
  have halphaLower :
      a.alphaValue (0 : Fin 2) ≤ c.alphaValue (0 : Fin 2) :=
    a.beli2019Lemma86_ii c horders hprefix hfull (0 : Fin 2)
  have hadjacentZero : c.adjacentDefect (0 : Fin 2) =
      defectOrder (K := K)
        (-(η * a.valueUnit (0 : Fin 3) * a.valueUnit (1 : Fin 3))) := by
    calc
      c.adjacentDefect (0 : Fin 2) =
          X.adjacentDefect (0 : Fin 2) :=
        (X.adjacentDefect_eq_of_isRealizedBy hreal 0).symm
      _ = defectOrder (K := K)
          (-(η * a.valueUnit (0 : Fin 3) * a.valueUnit (1 : Fin 3))) :=
        a.ternaryScaled_adjacentDefect_zero X ε η hvalues
  have hadjacentOne : c.adjacentDefect (1 : Fin 2) =
      defectOrder (K := K)
        (-(ε * a.valueUnit (1 : Fin 3) * a.valueUnit (2 : Fin 3))) := by
    calc
      c.adjacentDefect (1 : Fin 2) =
          X.adjacentDefect (1 : Fin 2) :=
        (X.adjacentDefect_eq_of_isRealizedBy hreal 1).symm
      _ = defectOrder (K := K)
          (-(ε * a.valueUnit (1 : Fin 3) * a.valueUnit (2 : Fin 3))) :=
        a.ternaryScaled_adjacentDefect_one X ε η hvalues
  have halphaUpper :
      c.alphaValue (0 : Fin 2) ≤ a.alphaValue (0 : Fin 2) := by
    rcases halpha with hhalf | hsecond | hfirst
    · have hhalfC : c.halfGapValue (0 : Fin 2) =
          a.halfGapValue (0 : Fin 2) := by
        unfold halfGapValue orderGap
        rw [← horders (0 : Fin 2).succ,
          ← horders (0 : Fin 2).castSucc]
      calc
        c.alphaValue (0 : Fin 2) ≤ c.halfGapValue (0 : Fin 2) :=
          c.alphaValue_le_halfGapValue 0
        _ = a.halfGapValue (0 : Fin 2) := hhalfC
        _ = a.alphaValue (0 : Fin 2) := hhalf.symm
    · have hbound := c.alpha_le_rightDefectCandidate
          (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by decide)
      rw [← c.coe_alphaValue] at hbound
      change
        (c.alphaValue (0 : Fin 2) : WithTop ℚ) ≤
          ((((c.order (2 : Fin 3) - c.order (0 : Fin 3) : Int) : ℚ) :
              WithTop ℚ) + c.adjacentDefect (1 : Fin 2)) at hbound
      rw [houterC, sub_self, Int.cast_zero, WithTop.coe_zero, zero_add,
        hadjacentOne, hsecond] at hbound
      exact_mod_cast hbound
    · have hremark := a.beli2019Remark87 (0 : Fin 1) (by
          simpa [remark87PreviousValue, remark87NextValue] using houter)
      have hrelation :
          a.alphaValue (0 : Fin 2) =
            ((a.order (1 : Fin 3) - a.order (0 : Fin 3) : Int) : ℚ) +
              a.alphaValue (1 : Fin 2) := by
        have h := hremark.previousAlpha_eq
        change a.alphaValue (0 : Fin 2) =
          ((a.order (1 : Fin 3) - a.order (2 : Fin 3) : Int) : ℚ) +
            a.alphaValue (1 : Fin 2) at h
        rw [← houter] at h
        exact h
      have hbound := c.alpha_le_leftDefectCandidate
          (i := (0 : Fin 2)) (j := (0 : Fin 2)) le_rfl
      rw [← c.coe_alphaValue] at hbound
      change
        (c.alphaValue (0 : Fin 2) : WithTop ℚ) ≤
          ((((c.order (1 : Fin 3) - c.order (0 : Fin 3) : Int) : ℚ) :
              WithTop ℚ) + c.adjacentDefect (0 : Fin 2)) at hbound
      rw [hadjacentZero, hfirst] at hbound
      have hrelationTop :
          (((c.order (1 : Fin 3) - c.order (0 : Fin 3) : Int) : ℚ) :
              WithTop ℚ) +
            (a.alphaValue (1 : Fin 2) : WithTop ℚ) =
          (a.alphaValue (0 : Fin 2) : WithTop ℚ) := by
        rw [← horders (1 : Fin 3), ← horders (0 : Fin 3)]
        exact_mod_cast hrelation.symm
      rw [hrelationTop] at hbound
      exact_mod_cast hbound
  have halphaEq :
      a.alphaValue (0 : Fin 2) = c.alphaValue (0 : Fin 2) :=
    le_antisymm halphaLower halphaUpper
  have hisometric : Lattice.IsIsometric q q L M :=
    (a.beli2019Lemma711 c horders houter).2 halphaEq
  rcases hisometric with ⟨f⟩
  let transformed := c.mapLatticeIsometry f.symm
  refine ⟨transformed, ?_⟩
  intro i
  apply Units.ext
  change (c.toBONG.mapLatticeIsometry f.symm).value i =
    (a.ternaryScaledValues ε η i : K)
  rw [BONG.value_mapLatticeIsometry]
  have hvalue := X.value_eq_of_isRealizedBy hreal i
  have hscaledValue := congrArg Units.val (hvalues i)
  change c₀.value i = (a.ternaryScaledValues ε η i : K)
  rw [← hvalue]
  simpa using hscaledValue

/-- First-coordinate projection of the value-preserving equal-outer ternary
scaling construction. -/
theorem exists_goodBONG_ternaryScaled_of_equalOuter
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicDiagonalClassificationLaws K]
    (a : GoodBONG q L 3) (ε η : Kˣ)
    (hεUnit : IsValuationUnit K (ε : K))
    (hηUnit : IsValuationUnit K (η : K))
    (hεDefect : (a.alphaValue (0 : Fin 2) : WithTop ℚ) ≤
      defectOrder (K := K) ε)
    (hηDefect : (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
      defectOrder (K := K) η)
    (hadjacent :
      hilbertSymbol K
          (-(η * a.valueUnit (0 : Fin 3) * a.valueUnit (1 : Fin 3)))
          (-(ε * a.valueUnit (1 : Fin 3) * a.valueUnit (2 : Fin 3))) =
        hilbertSymbol K
          (-(a.valueUnit (0 : Fin 3) * a.valueUnit (1 : Fin 3)))
          (-(a.valueUnit (1 : Fin 3) * a.valueUnit (2 : Fin 3))))
    (houter : a.order (0 : Fin 3) = a.order (2 : Fin 3))
    (halpha : a.TernaryEqualOuterAlphaCriterion ε η) :
    ∃ c : GoodBONG q L 3,
      c.valueUnit (0 : Fin 3) = ε * a.valueUnit (0 : Fin 3) := by
  rcases a.exists_goodBONG_ternaryScaledValues_of_equalOuter
      ε η hεUnit hηUnit hεDefect hηDefect hadjacent houter halpha with
    ⟨c, hc⟩
  exact ⟨c, (hc 0).trans (a.ternaryScaledValues_zero ε η)⟩

end BONG.GoodBONG

end Bong
