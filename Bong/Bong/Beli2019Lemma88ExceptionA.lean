/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma88Quaternary
import Bong.Dyadic.UnramifiedNorm

/-!
# Beli (2019), Lemma 8.8: the discriminant endpoint branch

When exception (a) occurs for the projected tail in the critical half-gap
configuration, the complementary unit defect is missing from the unit-defect
spectrum.  The global first alpha is nevertheless realized.  The parity and
spectrum laws therefore force the global alpha to be the endpoint `2e`.
The distinguished discriminant unit realizes that endpoint, and its Hilbert
character is trivial on the even-order first adjacent product.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {N : Nat}

/-- The distinguished discriminant unit realizes the endpoint unit defect
`2e`. -/
theorem isValuationUnitDefect_twoE
    [laws : DyadicDiscriminantClassLaws K] :
    IsValuationUnitDefect (K := K)
      (2 * (ramificationIndex K : ℚ)) := by
  refine ⟨laws.discriminantUnit,
    laws.discriminant_isValuationUnit, ?_⟩
  unfold defectOrder
  rw [laws.discriminant_defect]
  norm_cast

/-- If the projected tail misses its complementary unit defect while the
global first alpha is realized, then that first alpha is the discriminant
endpoint `2e`. -/
theorem firstAlpha_eq_twoE_of_tailExceptionA
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (b : GoodBONG q L (N + 3))
    (hhalf : b.AttainsHalfGap (0 : Fin (N + 2)))
    (hnotA : ¬b.Beli2019Lemma88ExceptionA)
    (htailAlpha : b.tail.alphaValue (0 : Fin (N + 1)) =
      b.lemma88ComplementaryDefect)
    (Atail : b.tail.Beli2019Lemma88ExceptionA) :
    b.alphaValue (0 : Fin (N + 2)) =
      2 * (ramificationIndex K : ℚ) := by
  have hrealized : IsValuationUnitDefect (K := K)
      (b.alphaValue (0 : Fin (N + 2))) := by
    by_contra hnot
    exact hnotA hnot
  rcases hrealized with ⟨u, hu, huDefect⟩
  have hglobalNonnegative :
      0 ≤ b.alphaValue (0 : Fin (N + 2)) :=
    (b.beli2009Lemma27_i (0 : Fin (N + 2))).1
  have htailNonnegative :
      0 ≤ b.tail.alphaValue (0 : Fin (N + 1)) :=
    (b.tail.beli2009Lemma27_i (0 : Fin (N + 1))).1
  have hsum :
      b.alphaValue (0 : Fin (N + 2)) +
          b.tail.alphaValue (0 : Fin (N + 1)) =
        2 * (ramificationIndex K : ℚ) := by
    calc
      b.alphaValue (0 : Fin (N + 2)) +
            b.tail.alphaValue (0 : Fin (N + 1)) =
          b.halfGapValue (0 : Fin (N + 2)) +
            b.lemma88ComplementaryDefect := by rw [hhalf, htailAlpha]
      _ = b.lemma88ComplementaryDefect +
          b.halfGapValue (0 : Fin (N + 2)) := add_comm _ _
      _ = 2 * (ramificationIndex K : ℚ) :=
        b.lemma88ComplementaryDefect_add_halfGap
  by_contra hendpoint
  have hglobalLe : b.alphaValue (0 : Fin (N + 2)) ≤
      2 * (ramificationIndex K : ℚ) := by linarith
  have hglobalLt : b.alphaValue (0 : Fin (N + 2)) <
      2 * (ramificationIndex K : ℚ) :=
    lt_of_le_of_ne hglobalLe hendpoint
  have hglobalNeZero :
      b.alphaValue (0 : Fin (N + 2)) ≠ 0 := by
    intro hzero
    apply Atail
    have htailEndpoint : b.tail.alphaValue (0 : Fin (N + 1)) =
        2 * (ramificationIndex K : ℚ) := by linarith
    rw [htailEndpoint]
    exact isValuationUnitDefect_twoE (K := K)
  have hglobalPositive :
      0 < b.alphaValue (0 : Fin (N + 2)) :=
    lt_of_le_of_ne hglobalNonnegative (Ne.symm hglobalNeZero)
  cases huQuadratic : quadraticDefect K u with
  | top =>
      unfold defectOrder at huDefect
      rw [huQuadratic] at huDefect
      exact WithTop.top_ne_coe huDefect
  | coe m =>
      have hmAlpha : (m : ℚ) =
          b.alphaValue (0 : Fin (N + 2)) := by
        unfold defectOrder at huDefect
        rw [huQuadratic] at huDefect
        change ((m : ℚ) : WithTop ℚ) =
          (b.alphaValue (0 : Fin (N + 2)) : WithTop ℚ) at huDefect
        exact WithTop.coe_eq_coe.mp huDefect
      have hmLt : m < 2 * ramificationIndex K := by
        exact_mod_cast (hmAlpha.symm ▸ hglobalLt)
      have huQuadraticLt : quadraticDefect K u <
          ((2 * ramificationIndex K : Nat) : ℕ∞) := by
        rw [huQuadratic]
        exact_mod_cast hmLt
      have hmOdd : Odd m := by
        simpa [huQuadratic] using
          quadraticDefect_toNat_odd_of_unit_of_lt_two_mul_e
            (K := K) u hu huQuadraticLt
      let c : Nat := 2 * ramificationIndex K - m
      have hcOdd : Odd c := by
        rcases hmOdd with ⟨k, hk⟩
        refine ⟨ramificationIndex K - k - 1, ?_⟩
        dsimp only [c]
        omega
      have htailEq : b.tail.alphaValue (0 : Fin (N + 1)) =
          (c : ℚ) := by
        have hmLe : m ≤ 2 * ramificationIndex K := hmLt.le
        have hcCast : (c : ℚ) =
            (2 * ramificationIndex K : Nat) - (m : ℚ) := by
          dsimp only [c]
          rw [Nat.cast_sub hmLe]
        rw [hcCast, hmAlpha]
        push_cast
        linarith
      have htailOdd : IsOddRationalInteger
          (b.tail.alphaValue (0 : Fin (N + 1))) := by
        refine ⟨(c : Int), ?_, ?_⟩
        · exact_mod_cast hcOdd
        · rw [htailEq]
          norm_cast
      have htailLt : b.tail.alphaValue (0 : Fin (N + 1)) <
          2 * (ramificationIndex K : ℚ) := by linarith
      apply Atail
      rcases DyadicUnitDefectSpectrumLaws.exists_unit_of_odd_rational_defect
          (b.tail.alphaValue (0 : Fin (N + 1))) htailOdd
          htailNonnegative htailLt with ⟨η, hηUnit, hηDefect⟩
      exact ⟨η, hηUnit, hηDefect⟩

/-- At the half-gap endpoint `α₁ = 2e`, the first adjacent product has
even valuation. -/
theorem firstAdjacentOrder_even_of_halfGap_alpha_eq_twoE
    (b : GoodBONG q L (N + 2))
    (hhalf : b.AttainsHalfGap (0 : Fin (N + 1)))
    (halpha : b.alphaValue (0 : Fin (N + 1)) =
      2 * (ramificationIndex K : ℚ)) :
    Even (ordUnit K (b.adjacentProduct (0 : Fin (N + 1)))) := by
  have hgap : b.orderGap (0 : Fin (N + 1)) =
      2 * (ramificationIndex K : Int) := by
    unfold AttainsHalfGap halfGapValue at hhalf
    rw [halpha] at hhalf
    have hgapQ : (b.orderGap (0 : Fin (N + 1)) : ℚ) =
        2 * (ramificationIndex K : ℚ) := by linarith
    exact_mod_cast hgapQ
  have hadjacentOrder : ordUnit K
      (b.adjacentProduct (0 : Fin (N + 1))) =
        b.order (0 : Fin (N + 2)) +
          b.order (1 : Fin (N + 2)) := by
    have hordNeg (z : Kˣ) : ordUnit K (-z) = ordUnit K z := by
      apply WithTop.coe_injective
      rw [coe_ordUnit, coe_ordUnit]
      change ord K (-(z : K)) = ord K (z : K)
      exact ord_neg K (z : K)
    have horderUnit (i : Fin (N + 2)) :
        ordUnit K (b.valueUnit i) = b.order i :=
      (b.toBONG.order_eq_ordUnit i).symm
    unfold adjacentProduct
    rw [hordNeg, ordUnit_mul, horderUnit, horderUnit]
    congr 1
  rw [hadjacentOrder]
  refine ⟨b.order (0 : Fin (N + 2)) +
    (ramificationIndex K : Int), ?_⟩
  unfold orderGap at hgap
  change b.order (1 : Fin (N + 2)) -
    b.order (0 : Fin (N + 2)) = _ at hgap
  omega

/-- The completed projected-tail exception-(a) branch.  The discriminant
unit has defect `2e`; the critical half-gap identity makes the first order
gap `2e`, hence the first adjacent product has even valuation and pairs
trivially with that discriminant unit. -/
theorem beli2019Lemma88_critical_of_tailExceptionA
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [discriminant : DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    (b : GoodBONG q L (N + 3))
    (hhalf : b.AttainsHalfGap (0 : Fin (N + 2)))
    (hnotA : ¬b.Beli2019Lemma88ExceptionA)
    (htailAlpha : b.tail.alphaValue (0 : Fin (N + 1)) =
      b.lemma88ComplementaryDefect)
    (Atail : b.tail.Beli2019Lemma88ExceptionA) :
    Nonempty b.Beli2019FirstValueTransform := by
  have halpha := b.firstAlpha_eq_twoE_of_tailExceptionA
    hhalf hnotA htailAlpha Atail
  have hadjacentEven : Even
      (ordUnit K (b.adjacentProduct (0 : Fin (N + 2)))) :=
    b.firstAdjacentOrder_even_of_halfGap_alpha_eq_twoE hhalf halpha
  have hhilbert : hilbertSymbol K discriminant.discriminantUnit
      (b.adjacentProduct (0 : Fin (N + 2))) = 1 :=
    (hilbertSymbol_discriminant_eq_one_iff_even_order
      (b.adjacentProduct (0 : Fin (N + 2)))).2 hadjacentEven
  have hdefect : defectOrder (K := K) discriminant.discriminantUnit =
      (b.alphaValue (0 : Fin (N + 2)) : WithTop ℚ) := by
    rw [halpha]
    unfold defectOrder
    rw [discriminant.discriminant_defect]
    norm_cast
  have hbinary := b.firstBinaryAlpha_eq_alpha_of_halfGap hhalf
  exact b.firstValueTransform_of_firstBinaryAlpha
    discriminant.discriminantUnit
    discriminant.discriminant_isValuationUnit hdefect hbinary hhilbert

end BONG.GoodBONG

end Bong
