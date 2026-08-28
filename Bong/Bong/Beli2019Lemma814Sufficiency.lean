/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma814Necessity
import Bong.Bong.Beli2019Corollary311
import Bong.Bong.DiagonalBinaryRepresentation
import Bong.Bong.DiagonalTernaryScaling
import Bong.Bong.DiagonalTernaryEqualOuter
import Bong.Bong.Beli2019ComplementaryHilbertChoice
import Bong.Bong.Beli2019OddPrefixDefect
import Bong.Bong.Beli2019EvenClassMultiplier

/-!
# Beli (2019), Lemma 8.14: sufficiency

This file follows the rank-stratified converse proof of Lemma 8.14.  The
initial layer records the prescribed multiplier and discharges the direct
binary norm branch from the generalized binary scaling theorem.
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

/-- The multiplier `ε = b₁ / a₁` used throughout the converse proof. -/
noncomputable def lemma814Epsilon
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1) : Kˣ :=
  b.valueUnit (0 : Fin 1) *
    (a.valueUnit (0 : Fin (N + 3)))⁻¹

/-- Multiplying the first target value by the prescribed multiplier gives
the unary source value. -/
theorem lemma814Epsilon_mul_firstValue
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1) :
    a.lemma814Epsilon b * a.valueUnit (0 : Fin (N + 3)) =
      b.valueUnit (0 : Fin 1) := by
  unfold lemma814Epsilon
  simp

/-- Equal first orders make the prescribed multiplier a valuation unit. -/
theorem lemma814Epsilon_isValuationUnit
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (horder : a.order (0 : Fin (N + 3)) = b.order (0 : Fin 1)) :
    IsValuationUnit K (a.lemma814Epsilon b : K) := by
  rw [isValuationUnit_iff_ordUnit_eq_zero]
  unfold lemma814Epsilon
  rw [ordUnit_mul, ordUnit_inv]
  change ordUnit K (b.toBONG.valueUnit 0) +
      -ordUnit K (a.toBONG.valueUnit 0) = 0
  rw [← b.toBONG.order_eq_ordUnit, ← a.toBONG.order_eq_ordUnit,
    show b.toBONG.order 0 = a.toBONG.order 0 by exact horder.symm]
  simp

/-- The uncapped first comparison defect is exactly the defect of `ε`, since
the omitted factor is the square `a₁²`. -/
theorem lemma813RawDefect_eq_lemma814Epsilon
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1) :
    a.lemma813RawDefect b =
      defectOrder (K := K) (a.lemma814Epsilon b) := by
  have hproduct :
      a.valueUnit (0 : Fin (N + 3)) * b.valueUnit (0 : Fin 1) =
        a.lemma814Epsilon b *
          (a.valueUnit (0 : Fin (N + 3))) ^ 2 := by
    unfold lemma814Epsilon
    rw [pow_two]
    simp [mul_comm]
  unfold lemma813RawDefect
  rw [hproduct, defectOrder_mul_square]

/-- Lemma 8.13(a) gives the defect bound on the prescribed multiplier. -/
theorem alpha_le_lemma814EpsilonDefect
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (conditions : a.Lemma813Conditions b) :
    (a.alphaValue (0 : Fin (N + 2)) : WithTop ℚ) ≤
      defectOrder (K := K) (a.lemma814Epsilon b) := by
  have hraw := (a.lemma813_defectEquality_iff_raw b).mp
    conditions.defectEquality
  rw [a.lemma813RawDefect_eq_lemma814Epsilon b] at hraw
  exact hraw

/-- The first binary prefix represents the prescribed unary value exactly
when the Hilbert symbol used in the proof of Lemma 8.14 is positive. -/
theorem lemma814BinaryRepresentation_iff_hilbertSymbol_one
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1) :
    DiagonalRepresents
        (b.prefixValues 1 (Nat.le_refl _))
        (a.prefixValues 2 (by omega)) ↔
      hilbertSymbol K (a.lemma814Epsilon b)
        (a.adjacentProduct (0 : Fin (N + 2))) = 1 := by
  have H := DiagonalRepresents.unary_binary_iff_hilbertSymbol_one
    (a.valueUnit (0 : Fin (N + 3)))
    (a.valueUnit (1 : Fin (N + 3)))
    (b.valueUnit (0 : Fin 1))
  change _ ↔ hilbertSymbol K
    (b.valueUnit (0 : Fin 1) * (a.valueUnit (0 : Fin (N + 3)))⁻¹)
      (-(a.valueUnit (0 : Fin (N + 3)) *
        a.valueUnit (1 : Fin (N + 3)))) = 1
  have hb : b.prefixValues 1 (Nat.le_refl _) =
      (fun _ : Fin 1 ↦ (b.valueUnit (0 : Fin 1) : K)) := by
    funext i
    rw [Fin.eq_zero i]
    rfl
  have ha : a.prefixValues 2 (by omega) =
      Fin.cons (a.valueUnit (0 : Fin (N + 3)) : K)
        (fun _ : Fin 1 ↦ (a.valueUnit (1 : Fin (N + 3)) : K)) := by
    funext i
    refine Fin.cases rfl (fun j ↦ ?_) i
    rw [Fin.eq_zero j]
    rfl
  rw [hb, ha]
  exact H

/-- The numerical alternative in the `R₁ < R₃` branch of Lemma 8.14,
written without subtraction in `WithTop ℚ`. -/
def Lemma814UnequalOuterBound
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1) : Prop :=
  a.order (0 : Fin (N + 3)) < a.order (2 : Fin (N + 3)) ∧
    (a.alphaValue (0 : Fin (N + 2)) : WithTop ℚ) +
        ((((a.order (2 : Fin (N + 3)) : Int) : ℚ) : WithTop ℚ) +
          a.truncatedPrefixDefect b (-1) 3 1) ≤
      ((2 * (ramificationIndex K : ℚ) +
        (a.order (1 : Fin (N + 3)) : ℚ) : ℚ) : WithTop ℚ)

/-- If the prescribed unary value is not represented by the first binary
prefix, Lemma 8.13(b) leaves exactly the two outer-order cases used in the
paper: `R₁ = R₃`, or `R₁ < R₃` together with its displayed defect bound. -/
theorem lemma814_outerCases_of_hilbert_neg_one
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (conditions : a.Lemma813Conditions b)
    (hhilbert : hilbertSymbol K (a.lemma814Epsilon b)
      (a.adjacentProduct (0 : Fin (N + 2))) = -1) :
    a.order (0 : Fin (N + 3)) = a.order (2 : Fin (N + 3)) ∨
      a.Lemma814UnequalOuterBound b := by
  have hnotRepresentation : ¬DiagonalRepresents
      (b.prefixValues 1 (Nat.le_refl _))
      (a.prefixValues 2 (by omega)) := by
    intro hrepresentation
    have hone :=
      (a.lemma814BinaryRepresentation_iff_hilbertSymbol_one b).mp
        hrepresentation
    rw [hhilbert] at hone
    norm_num at hone
  have hnotTrigger :
      ¬a.lemma813CentralTrigger b (by omega) := by
    intro htrigger
    exact hnotRepresentation
      (conditions.binaryHigher (by omega) htrigger)
  by_cases houter :
      a.order (0 : Fin (N + 3)) = a.order (2 : Fin (N + 3))
  · exact Or.inl houter
  · right
    have hle : a.order (0 : Fin (N + 3)) ≤
        a.order (2 : Fin (N + 3)) := by
      convert a.order_zero_le_two using 1 <;>
        apply congrArg a.order <;>
        apply Fin.ext <;>
        rfl
    have hlt : a.order (0 : Fin (N + 3)) <
        a.order (2 : Fin (N + 3)) := lt_of_le_of_ne hle houter
    refine ⟨hlt, ?_⟩
    by_contra hnotLe
    apply hnotTrigger
    refine ⟨hlt, ?_⟩
    exact lt_of_not_ge hnotLe

/-- In target rank three, the full bracketed defect from Lemma 8.14 is the
defect of `ε` times the second adjacent product.  The omitted factor is the
square `a₁²`. -/
theorem lemma814TernaryFullDefect_eq_epsilon_mul_secondAdjacent
    [QuadraticDefectLaws K]
    (a : GoodBONG q L 3) (b : GoodBONG r M 1) :
    a.truncatedPrefixDefect b (-1) 3 1 =
      defectOrder (K := K)
        (a.lemma814Epsilon b * a.adjacentProduct (1 : Fin 2)) := by
  have hproduct :
      (-1 : Kˣ) * a.prefixProduct 3 * b.prefixProduct 1 =
        (a.lemma814Epsilon b * a.adjacentProduct (1 : Fin 2)) *
          (a.valueUnit (0 : Fin 3)) ^ 2 := by
    classical
    change (-1 : Kˣ) * a.toBONG.prefixProduct 3 *
        b.toBONG.prefixProduct 1 = _
    unfold BONG.prefixProduct
    rw [show Finset.univ.filter (fun j : Fin 3 => j.1 < 3) =
        Finset.univ by ext j; simp,
      show Finset.univ.filter (fun j : Fin 1 => j.1 < 1) =
        Finset.univ by ext j; simp]
    simp only [Fin.prod_univ_three]
    have hbProduct : (∏ j : Fin 1, b.toBONG.valueUnit j) =
        b.toBONG.valueUnit (0 : Fin 1) := by
      simp
    rw [hbProduct]
    unfold lemma814Epsilon GoodBONG.adjacentProduct
      GoodBONG.valueUnit
    have hcast : (1 : Fin 2).castSucc = (1 : Fin 3) := rfl
    have hsucc : (1 : Fin 2).succ = (2 : Fin 3) := rfl
    rw [hcast, hsucc]
    apply Units.ext
    simp only [Units.val_mul, Units.val_neg, Units.val_one,
      Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
    field_simp [Units.ne_zero (a.toBONG.valueUnit (0 : Fin 3))]
  unfold truncatedPrefixDefect
  rw [a.prefixAlphaCap_last, b.prefixAlphaCap_last, min_top_right,
    hproduct, defectOrder_mul_square]
  simp

/-- The numerical calculation at the start of the `R₁ < R₃` branch:
Lemma 8.13(a), the second adjacent-defect bound, and the displayed outer
inequality imply `α₁ + α₂ ≤ 2e`. -/
theorem alphaSum_le_twoE_of_lemma814UnequalOuterBound
    [QuadraticDefectLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L 3) (b : GoodBONG r M 1)
    (conditions : a.Lemma813Conditions b)
    (houter : a.Lemma814UnequalOuterBound b) :
    a.alphaValue (0 : Fin 2) + a.alphaValue (1 : Fin 2) ≤
      2 * (ramificationIndex K : ℚ) := by
  let lower : WithTop ℚ :=
    (((a.order (1 : Fin 3) - a.order (2 : Fin 3) : Int) : ℚ) :
        WithTop ℚ) + (a.alphaValue (1 : Fin 2) : WithTop ℚ)
  have hlowerAlpha : lower ≤
      (a.alphaValue (0 : Fin 2) : WithTop ℚ) := by
    have hp1 := (a.alpha_p1 (0 : Fin 2) (by omega)).2
    have hrat :
        ((a.order (1 : Fin 3) - a.order (2 : Fin 3) : Int) : ℚ) +
            a.alphaValue (1 : Fin 2) ≤
          a.alphaValue (0 : Fin 2) := by
      unfold alphaRightEndpoint at hp1
      change
        -(a.order (2 : Fin 3) : ℚ) + a.alphaValue (1 : Fin 2) ≤
          -(a.order (1 : Fin 3) : ℚ) + a.alphaValue (0 : Fin 2) at hp1
      push_cast at hp1 ⊢
      linarith
    dsimp only [lower]
    exact_mod_cast hrat
  have hlowerAdjacent : lower ≤
      a.adjacentDefect (1 : Fin 2) := by
    have hcandidate := a.alpha_le_leftDefectCandidate
      (i := (1 : Fin 2)) (j := (1 : Fin 2)) le_rfl
    rw [← a.coe_alphaValue] at hcandidate
    change
      (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
        (((a.order (2 : Fin 3) - a.order (1 : Fin 3) : Int) : ℚ) :
          WithTop ℚ) + a.adjacentDefect (1 : Fin 2) at hcandidate
    by_cases htop : a.adjacentDefect (1 : Fin 2) = ⊤
    · rw [htop]
      exact le_top
    · obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp htop
      rw [← hd] at hcandidate ⊢
      dsimp only [lower]
      change
        (((a.order (1 : Fin 3) - a.order (2 : Fin 3) : Int) : ℚ) :
            WithTop ℚ) + (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
          (d : WithTop ℚ)
      norm_cast at hcandidate ⊢
      push_cast at hcandidate ⊢
      linarith
  have hεDefect := a.alpha_le_lemma814EpsilonDefect b conditions
  have hlowerEpsilon : lower ≤
      defectOrder (K := K) (a.lemma814Epsilon b) :=
    hlowerAlpha.trans hεDefect
  have hlowerProduct : lower ≤
      defectOrder (K := K)
        (a.lemma814Epsilon b * a.adjacentProduct (1 : Fin 2)) := by
    exact (le_min hlowerEpsilon hlowerAdjacent).trans
      (defectOrder_mul_ge_min
        (a.lemma814Epsilon b) (a.adjacentProduct (1 : Fin 2)))
  have hlowerTruncated : lower ≤
      a.truncatedPrefixDefect b (-1) 3 1 := by
    rw [a.lemma814TernaryFullDefect_eq_epsilon_mul_secondAdjacent b]
    exact hlowerProduct
  have hshift :
      ((a.order (2 : Fin 3) : ℚ) : WithTop ℚ) + lower =
        ((a.order (1 : Fin 3) : ℚ) : WithTop ℚ) +
          (a.alphaValue (1 : Fin 2) : WithTop ℚ) := by
    dsimp only [lower]
    norm_cast
    push_cast
    ring
  have hwithTop :
      (a.alphaValue (0 : Fin 2) : WithTop ℚ) +
          (((a.order (1 : Fin 3) : ℚ) : WithTop ℚ) +
            (a.alphaValue (1 : Fin 2) : WithTop ℚ)) ≤
        (((2 * (ramificationIndex K : ℚ)) : WithTop ℚ) +
          ((a.order (1 : Fin 3) : ℚ) : WithTop ℚ)) := by
    calc
      (a.alphaValue (0 : Fin 2) : WithTop ℚ) +
          (((a.order (1 : Fin 3) : ℚ) : WithTop ℚ) +
            (a.alphaValue (1 : Fin 2) : WithTop ℚ)) =
          (a.alphaValue (0 : Fin 2) : WithTop ℚ) +
            (((a.order (2 : Fin 3) : ℚ) : WithTop ℚ) + lower) := by
        rw [hshift]
      _ ≤ (a.alphaValue (0 : Fin 2) : WithTop ℚ) +
          (((a.order (2 : Fin 3) : ℚ) : WithTop ℚ) +
            a.truncatedPrefixDefect b (-1) 3 1) := by
        gcongr
      _ ≤ (((2 * (ramificationIndex K : ℚ)) : WithTop ℚ) +
          ((a.order (1 : Fin 3) : ℚ) : WithTop ℚ)) := houter.2
  have htwoE :
      (2 : WithTop ℚ) *
          ((ramificationIndex K : ℚ) : WithTop ℚ) =
        (((2 : ℚ) * (ramificationIndex K : ℚ)) : WithTop ℚ) := by
    norm_num
  have hcancelForm :
      ((a.order (1 : Fin 3) : ℚ) : WithTop ℚ) +
          ((a.alphaValue (0 : Fin 2) : WithTop ℚ) +
            (a.alphaValue (1 : Fin 2) : WithTop ℚ)) ≤
        ((a.order (1 : Fin 3) : ℚ) : WithTop ℚ) +
          ((2 : WithTop ℚ) *
            ((ramificationIndex K : ℚ) : WithTop ℚ)) := by
    simpa only [add_assoc, add_comm, add_left_comm] using hwithTop
  have hsumTop :
      (a.alphaValue (0 : Fin 2) : WithTop ℚ) +
          (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
        (2 : WithTop ℚ) *
          ((ramificationIndex K : ℚ) : WithTop ℚ) :=
    (WithTop.add_le_add_iff_left WithTop.coe_ne_top).1 hcancelForm
  rw [htwoE] at hsumTop
  norm_cast at hsumTop
  push_cast at hsumTop
  exact hsumTop

/-- In the Hilbert-negative unequal-outer branch, the second alpha cannot
vanish.  Otherwise P2 and `R₁ < R₃` force the first order gap, hence by P5
the first alpha and the defect of `ε`, strictly beyond `2e`; `ε` would then
be a square and its Hilbert symbol would be positive. -/
theorem secondAlpha_pos_of_lemma814UnequalOuterBound
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L 3) (b : GoodBONG r M 1)
    (conditions : a.Lemma813Conditions b)
    (houter : a.Lemma814UnequalOuterBound b)
    (hhilbert : hilbertSymbol K (a.lemma814Epsilon b)
      (a.adjacentProduct (0 : Fin 2)) = -1) :
    0 < a.alphaValue (1 : Fin 2) := by
  have hnonnegative := (a.alpha_p2 (1 : Fin 2)).1
  apply lt_of_le_of_ne hnonnegative
  intro hzero
  have hgapOne : a.orderGap (1 : Fin 2) =
      -(2 * (ramificationIndex K : Int)) :=
    (a.alpha_p2 (1 : Fin 2)).2.mp hzero.symm
  have hgapZero : 2 * (ramificationIndex K : Int) <
      a.orderGap (0 : Fin 2) := by
    have houterlt := houter.1
    unfold orderGap at hgapOne ⊢
    change a.order (2 : Fin 3) - a.order (1 : Fin 3) =
      -(2 * (ramificationIndex K : Int)) at hgapOne
    change 2 * (ramificationIndex K : Int) <
      a.order (1 : Fin 3) - a.order (0 : Fin 3)
    omega
  have hfirstAlpha : 2 * (ramificationIndex K : ℚ) <
      a.alphaValue (0 : Fin 2) :=
    (a.alpha_p5 (0 : Fin 2)).2.2.mpr hgapZero
  have hεDefect := a.alpha_le_lemma814EpsilonDefect b conditions
  have htwoELtDefect :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        defectOrder (K := K) (a.lemma814Epsilon b) := by
    have htwoELtAlpha :
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
          (a.alphaValue (0 : Fin 2) : WithTop ℚ) := by
      exact_mod_cast hfirstAlpha
    exact htwoELtAlpha.trans_le hεDefect
  have hsquare : IsSquare (a.lemma814Epsilon b) :=
    isSquare_of_two_mul_e_lt_defectOrder
      (a.lemma814Epsilon b) htwoELtDefect
  have hone : hilbertSymbol K (a.lemma814Epsilon b)
      (a.adjacentProduct (0 : Fin 2)) = 1 :=
    hilbertSymbol_eq_one_of_isSquare_left K hsquare
  rw [hhilbert] at hone
  norm_num at hone

/-- The sharper defect inequality used to choose `η` in ternary rank:
`α₂ + d(-a₁a₂a₃b₁) ≤ 2e`. -/
theorem secondAlpha_add_fullDefect_le_twoE_of_unequalOuter
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L 3) (b : GoodBONG r M 1)
    (houter : a.Lemma814UnequalOuterBound b) :
    (a.alphaValue (1 : Fin 2) : WithTop ℚ) +
        a.truncatedPrefixDefect b (-1) 3 1 ≤
      (2 : WithTop ℚ) *
        ((ramificationIndex K : ℚ) : WithTop ℚ) := by
  have hp1 := (a.alpha_p1 (0 : Fin 2) (by omega)).2
  have hp1Rat :
      (a.order (1 : Fin 3) : ℚ) + a.alphaValue (1 : Fin 2) ≤
        (a.order (2 : Fin 3) : ℚ) + a.alphaValue (0 : Fin 2) := by
    unfold alphaRightEndpoint at hp1
    change
      -(a.order (2 : Fin 3) : ℚ) + a.alphaValue (1 : Fin 2) ≤
        -(a.order (1 : Fin 3) : ℚ) + a.alphaValue (0 : Fin 2) at hp1
    linarith
  have hp1Top :
      ((a.order (1 : Fin 3) : ℚ) : WithTop ℚ) +
          (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
        ((a.order (2 : Fin 3) : ℚ) : WithTop ℚ) +
          (a.alphaValue (0 : Fin 2) : WithTop ℚ) := by
    exact_mod_cast hp1Rat
  have hcancelForm :
      ((a.order (1 : Fin 3) : ℚ) : WithTop ℚ) +
          ((a.alphaValue (1 : Fin 2) : WithTop ℚ) +
            a.truncatedPrefixDefect b (-1) 3 1) ≤
        ((a.order (1 : Fin 3) : ℚ) : WithTop ℚ) +
          ((2 : WithTop ℚ) *
            ((ramificationIndex K : ℚ) : WithTop ℚ)) := by
    calc
      ((a.order (1 : Fin 3) : ℚ) : WithTop ℚ) +
            ((a.alphaValue (1 : Fin 2) : WithTop ℚ) +
              a.truncatedPrefixDefect b (-1) 3 1) =
          (((a.order (1 : Fin 3) : ℚ) : WithTop ℚ) +
            (a.alphaValue (1 : Fin 2) : WithTop ℚ)) +
              a.truncatedPrefixDefect b (-1) 3 1 := by
        ac_rfl
      _ ≤ (((a.order (2 : Fin 3) : ℚ) : WithTop ℚ) +
            (a.alphaValue (0 : Fin 2) : WithTop ℚ)) +
              a.truncatedPrefixDefect b (-1) 3 1 := by
        gcongr
      _ = (a.alphaValue (0 : Fin 2) : WithTop ℚ) +
          (((a.order (2 : Fin 3) : ℚ) : WithTop ℚ) +
            a.truncatedPrefixDefect b (-1) 3 1) := by
        ac_rfl
      _ ≤ (2 : WithTop ℚ) *
            ((ramificationIndex K : ℚ) : WithTop ℚ) +
          ((a.order (1 : Fin 3) : ℚ) : WithTop ℚ) := houter.2
      _ = ((a.order (1 : Fin 3) : ℚ) : WithTop ℚ) +
          ((2 : WithTop ℚ) *
            ((ramificationIndex K : ℚ) : WithTop ℚ)) := by
        ac_rfl
  exact (WithTop.add_le_add_iff_left WithTop.coe_ne_top).1 hcancelForm

/-- Under `R₁ = R₃`, Remark 8.7 makes both adjacent square classes have
even valuation. -/
theorem ternaryAdjacentOrders_even_of_equalOuter
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L 3)
    (houter : a.order (0 : Fin 3) = a.order (2 : Fin 3)) :
    Even (ordUnit K (a.adjacentProduct (0 : Fin 2))) ∧
      Even (ordUnit K (a.adjacentProduct (1 : Fin 2))) := by
  have hremark := a.beli2019Remark87 (0 : Fin 1) (by
    simpa [remark87PreviousValue, remark87NextValue] using houter)
  have adjacentOrder (i : Fin 2) :
      ordUnit K (a.adjacentProduct i) =
        a.order i.castSucc + a.order i.succ := by
    have horderUnit (j : Fin 3) :
        ordUnit K (a.valueUnit j) = a.order j :=
      (a.toBONG.order_eq_ordUnit j).symm
    unfold adjacentProduct
    rw [ordUnit_neg, ordUnit_mul, horderUnit, horderUnit]
  have evenSum {x y : Int} (hxy : Int.ModEq 2 x y) : Even (x + y) := by
    rcases Int.modEq_iff_add_fac.mp hxy with ⟨t, ht⟩
    refine ⟨x + t, ?_⟩
    omega
  constructor
  · rw [adjacentOrder]
    simpa [remark87PreviousValue, remark87MiddleValue] using
      evenSum hremark.previous_middle_modEq
  · rw [adjacentOrder]
    simpa [remark87MiddleValue, remark87NextValue] using
      evenSum hremark.middle_next_modEq

/-- Outside exception (a), anisotropy and `R₁ = R₃` force the non-strict
boundary inequality used in the equal-outer-order construction. -/
theorem secondAlpha_add_fullDefect_le_twoE_of_notExceptional_anisotropic
    (a : GoodBONG q L 3) (b : GoodBONG r M 1)
    (houter : a.order (0 : Fin 3) = a.order (2 : Fin 3))
    (hanisotropic : a.Lemma814FirstThreeAnisotropic)
    (hnotExceptional : ¬a.Beli2019Lemma814Exceptional b) :
    (a.alphaValue (1 : Fin 2) : WithTop ℚ) +
        a.truncatedPrefixDefect b (-1) 3 1 ≤
      (((2 * (ramificationIndex K : ℚ)) : ℚ) : WithTop ℚ) := by
  by_contra hnotLe
  have hstrict :
      (((2 * (ramificationIndex K : ℚ)) : ℚ) : WithTop ℚ) <
        (a.alphaValue (1 : Fin 2) : WithTop ℚ) +
          a.truncatedPrefixDefect b (-1) 3 1 :=
    lt_of_not_ge hnotLe
  apply hnotExceptional
  left
  exact {
    firstThirdOrders_eq := houter
    defectSum_strict := by
      simpa [lemma814FirstThirdCappedDefect] using hstrict
    firstThree_anisotropic := hanisotropic
  }

/-- An anisotropic first ternary prefix has negative adjacent Hilbert
symbol. -/
theorem adjacentHilbert_neg_of_firstThreeAnisotropic
    [HilbertSymbolLaws K]
    (a : GoodBONG q L 3)
    (hanisotropic : a.Lemma814FirstThreeAnisotropic) :
    hilbertSymbol K
        (a.adjacentProduct (0 : Fin 2))
        (a.adjacentProduct (1 : Fin 2)) = -1 := by
  have hnotOne :
      hilbertSymbol K
          (a.adjacentProduct (0 : Fin 2))
          (a.adjacentProduct (1 : Fin 2)) ≠ 1 := by
    intro hone
    exact a.not_firstThreeIsotropic_of_anisotropic hanisotropic
      ((a.lemma814FirstThreeIsotropic_iff_adjacentHilbertOne).mpr hone)
  exact (Int.units_eq_one_or
    (hilbertSymbol K
      (a.adjacentProduct (0 : Fin 2))
      (a.adjacentProduct (1 : Fin 2)))).resolve_left hnotOne

/-- In the anisotropic `R₁ = R₃` case, the second alpha is an odd rational
integer.  This is the parity contradiction in the corresponding paragraph
of Beli's proof. -/
theorem secondAlpha_isOddRationalInteger_of_equalOuter_anisotropic
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L 3)
    (houter : a.order (0 : Fin 3) = a.order (2 : Fin 3))
    (hanisotropic : a.Lemma814FirstThreeAnisotropic) :
    IsOddRationalInteger (a.alphaValue (1 : Fin 2)) := by
  have hremark := a.beli2019Remark87 (0 : Fin 1) (by
    simpa [remark87PreviousValue, remark87NextValue] using houter)
  have hfirstNonnegative : 0 ≤ a.alphaValue (0 : Fin 2) :=
    (a.beli2009Lemma27_i (0 : Fin 2)).1
  have hsecondNonnegative : 0 ≤ a.alphaValue (1 : Fin 2) :=
    (a.beli2009Lemma27_i (1 : Fin 2)).1
  have hsecondLe : a.alphaValue (1 : Fin 2) ≤
      2 * (ramificationIndex K : ℚ) := by
    have hsum := hremark.alphaSum_le_twoE
    change a.alphaValue (0 : Fin 2) + a.alphaValue (1 : Fin 2) ≤
      2 * (ramificationIndex K : ℚ) at hsum
    linarith
  have hsecondIntegral : IsRationalInteger
      (a.alphaValue (1 : Fin 2)) := by
    rcases a.beli2009Corollary28_iii (1 : Fin 2) with hfinite | hlarge
    · exact hfinite.2.2
    · exact ((not_lt_of_ge hsecondLe) hlarge.1).elim
  rcases hsecondIntegral with ⟨z, hz⟩
  rcases Int.even_or_odd z with hzEven | hzOdd
  · have hsecondHalf :
        a.alphaValue (1 : Fin 2) = a.halfGapValue (1 : Fin 2) := by
      by_contra hnotHalf
      rcases a.beli2009Lemma27_iv (1 : Fin 2) hnotHalf with
        ⟨w, hwOdd, hw⟩
      have hzw : z = w := by
        exact_mod_cast hz.symm.trans hw
      rw [← hzw] at hwOdd
      exact ((Int.not_odd_iff_even.mpr hzEven) hwOdd).elim
    have hfirstAttains : a.AttainsHalfGap (0 : Fin 2) := by
      apply hremark.attainsHalfGap_iff.mpr
      simpa [AttainsHalfGap, remark87CurrentAlpha] using hsecondHalf
    have halphaSum :
        a.alphaValue (0 : Fin 2) + a.alphaValue (1 : Fin 2) =
          2 * (ramificationIndex K : ℚ) := by
      have hsum := hremark.alphaSum_eq_twoE_iff.mpr hfirstAttains
      simpa [remark87PreviousAlpha, remark87CurrentAlpha] using hsum
    have hhilbert :=
      a.adjacentHilbert_neg_of_firstThreeAnisotropic hanisotropic
    have hquadraticSum :
        quadraticDefect K (a.adjacentProduct (0 : Fin 2)) +
            quadraticDefect K (a.adjacentProduct (1 : Fin 2)) ≤
          ((2 * ramificationIndex K : Nat) : WithTop Nat) :=
      (beli2019Lemma82_i
        (a.adjacentProduct (0 : Fin 2))
        (a.adjacentProduct (1 : Fin 2))).mp
          ⟨a.adjacentProduct (1 : Fin 2), rfl, hhilbert⟩
    have hdefectSum :=
      defectOrder_add_le_twoE_of_quadraticDefect_add_le_twoE
        (a.adjacentProduct (0 : Fin 2))
        (a.adjacentProduct (1 : Fin 2)) hquadraticSum
    have hfirstLower :
        (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
          defectOrder (K := K) (a.adjacentProduct (0 : Fin 2)) := by
      simpa [adjacentDefect, remark87PreviousAlpha,
        remark87CurrentAlpha] using
          hremark.currentAlpha_le_previousRawDefect
    have hsecondLower :
        (a.alphaValue (0 : Fin 2) : WithTop ℚ) ≤
          defectOrder (K := K) (a.adjacentProduct (1 : Fin 2)) := by
      simpa [adjacentDefect, remark87PreviousAlpha,
        remark87CurrentAlpha] using
          hremark.previousAlpha_le_currentRawDefect
    have halphaSumTop :
        (a.alphaValue (1 : Fin 2) : WithTop ℚ) +
            (a.alphaValue (0 : Fin 2) : WithTop ℚ) =
          (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
      exact_mod_cast (show
        a.alphaValue (1 : Fin 2) + a.alphaValue (0 : Fin 2) =
          2 * (ramificationIndex K : ℚ) by
            simpa [add_comm] using halphaSum)
    have hfirstUpperForm :
        defectOrder (K := K) (a.adjacentProduct (0 : Fin 2)) +
            (a.alphaValue (0 : Fin 2) : WithTop ℚ) ≤
          (a.alphaValue (1 : Fin 2) : WithTop ℚ) +
            (a.alphaValue (0 : Fin 2) : WithTop ℚ) := by
      calc
        defectOrder (K := K) (a.adjacentProduct (0 : Fin 2)) +
              (a.alphaValue (0 : Fin 2) : WithTop ℚ) ≤
            defectOrder (K := K) (a.adjacentProduct (0 : Fin 2)) +
              defectOrder (K := K) (a.adjacentProduct (1 : Fin 2)) := by
                gcongr
        _ ≤ (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) :=
          hdefectSum
        _ = (a.alphaValue (1 : Fin 2) : WithTop ℚ) +
            (a.alphaValue (0 : Fin 2) : WithTop ℚ) := halphaSumTop.symm
    have hfirstUpper :
        defectOrder (K := K) (a.adjacentProduct (0 : Fin 2)) ≤
          (a.alphaValue (1 : Fin 2) : WithTop ℚ) :=
      (WithTop.add_le_add_iff_right WithTop.coe_ne_top).mp hfirstUpperForm
    have hfirstDefect :
        defectOrder (K := K) (a.adjacentProduct (0 : Fin 2)) =
          (a.alphaValue (1 : Fin 2) : WithTop ℚ) :=
      le_antisymm hfirstUpper hfirstLower
    have hsecondUpperForm :
        (a.alphaValue (1 : Fin 2) : WithTop ℚ) +
            defectOrder (K := K) (a.adjacentProduct (1 : Fin 2)) ≤
          (a.alphaValue (1 : Fin 2) : WithTop ℚ) +
            (a.alphaValue (0 : Fin 2) : WithTop ℚ) := by
      calc
        (a.alphaValue (1 : Fin 2) : WithTop ℚ) +
              defectOrder (K := K) (a.adjacentProduct (1 : Fin 2)) ≤
            defectOrder (K := K) (a.adjacentProduct (0 : Fin 2)) +
              defectOrder (K := K) (a.adjacentProduct (1 : Fin 2)) := by
                gcongr
        _ ≤ (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) :=
          hdefectSum
        _ = (a.alphaValue (1 : Fin 2) : WithTop ℚ) +
            (a.alphaValue (0 : Fin 2) : WithTop ℚ) := halphaSumTop.symm
    have hsecondUpper :
        defectOrder (K := K) (a.adjacentProduct (1 : Fin 2)) ≤
          (a.alphaValue (0 : Fin 2) : WithTop ℚ) :=
      (WithTop.add_le_add_iff_left WithTop.coe_ne_top).mp hsecondUpperForm
    have hsecondDefect :
        defectOrder (K := K) (a.adjacentProduct (1 : Fin 2)) =
          (a.alphaValue (0 : Fin 2) : WithTop ℚ) :=
      le_antisymm hsecondUpper hsecondLower
    have hadjacentEven := a.ternaryAdjacentOrders_even_of_equalOuter houter
    rcases lt_or_eq_of_le hsecondLe with hsecondLt | hsecondEndpoint
    · have hsecondOdd :=
        isOddRationalInteger_of_even_ordUnit_of_defectOrder_eq
          (a.adjacentProduct (0 : Fin 2))
          (a.alphaValue (1 : Fin 2)) hadjacentEven.1
          hfirstDefect hsecondLt
      rcases hsecondOdd with ⟨w, hwOdd, hw⟩
      have hzw : z = w := by
        exact_mod_cast hz.symm.trans hw
      rw [← hzw] at hwOdd
      exact ((Int.not_odd_iff_even.mpr hzEven) hwOdd).elim
    · have hfirstZero : a.alphaValue (0 : Fin 2) = 0 := by
        linarith
      have hrawZero :
          defectOrder (K := K) (a.adjacentProduct (1 : Fin 2)) = 0 := by
        rw [hsecondDefect, hfirstZero]
        rfl
      have hquadraticZero :
          quadraticDefect K (a.adjacentProduct (1 : Fin 2)) = 0 :=
        quadraticDefect_eq_zero_of_defectOrder_eq_zero
          (a.adjacentProduct (1 : Fin 2)) hrawZero
      exact ((quadraticDefect_ne_zero_of_even_ordUnit
        (a.adjacentProduct (1 : Fin 2)) hadjacentEven.2) hquadraticZero).elim
  · exact ⟨z, hzOdd, hz⟩

/-- Two negative Hilbert pairings are exactly what is needed to preserve the
adjacent Hilbert invariant under the ternary coefficient scaling. -/
theorem lemma814Ternary_adjacentHilbert_eq_of_neg
    [HilbertSymbolLaws K]
    (a : GoodBONG q L 3) (b : GoodBONG r M 1) (η : Kˣ)
    (hεHilbert : hilbertSymbol K (a.lemma814Epsilon b)
      (a.adjacentProduct (0 : Fin 2)) = -1)
    (hηHilbert : hilbertSymbol K η
      (a.lemma814Epsilon b * a.adjacentProduct (1 : Fin 2)) = -1) :
    hilbertSymbol K
        (-(η * a.valueUnit (0 : Fin 3) * a.valueUnit (1 : Fin 3)))
        (-(a.lemma814Epsilon b * a.valueUnit (1 : Fin 3) *
          a.valueUnit (2 : Fin 3))) =
      hilbertSymbol K
        (-(a.valueUnit (0 : Fin 3) * a.valueUnit (1 : Fin 3)))
        (-(a.valueUnit (1 : Fin 3) * a.valueUnit (2 : Fin 3))) := by
  have hfirst :
      -(η * a.valueUnit (0 : Fin 3) * a.valueUnit (1 : Fin 3)) =
        η * a.adjacentProduct (0 : Fin 2) := by
    unfold adjacentProduct
    have hcast : (0 : Fin 2).castSucc = (0 : Fin 3) := rfl
    have hsucc : (0 : Fin 2).succ = (1 : Fin 3) := rfl
    rw [hcast, hsucc]
    apply Units.ext
    simp only [Units.val_neg, Units.val_mul]
    ring
  have hsecond :
      -(a.lemma814Epsilon b * a.valueUnit (1 : Fin 3) *
          a.valueUnit (2 : Fin 3)) =
        a.lemma814Epsilon b * a.adjacentProduct (1 : Fin 2) := by
    unfold adjacentProduct
    have hcast : (1 : Fin 2).castSucc = (1 : Fin 3) := rfl
    have hsucc : (1 : Fin 2).succ = (2 : Fin 3) := rfl
    rw [hcast, hsucc]
    apply Units.ext
    simp only [Units.val_neg, Units.val_mul]
    ring
  rw [hfirst, hsecond]
  change
    hilbertSymbol K (η * a.adjacentProduct (0 : Fin 2))
        (a.lemma814Epsilon b * a.adjacentProduct (1 : Fin 2)) =
      hilbertSymbol K (a.adjacentProduct (0 : Fin 2))
        (a.adjacentProduct (1 : Fin 2))
  rw [hilbertSymbol_mul_left, hηHilbert, hilbertSymbol_mul_right,
    hilbertSymbol_comm K (a.adjacentProduct (0 : Fin 2))
      (a.lemma814Epsilon b), hεHilbert]
  simp

/-- In target rank at least three, the explicit clauses of Lemma 8.13 are
invariant under a change of the target good BONG.  This is the noncircular
normalization lemma needed in the converse proof of Lemma 8.14: the ordinary
rank-three endpoint is transported by the complete BONG coordinate change,
while the proper-prefix clauses are transported by Lemma 3.10. -/
theorem lemma813Conditions_changeTargetBONG
    [Beli2006AlphaLaws.{u, v} K]
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    [Beli2019Lemma310RepresentationLaws.{u, v, w} K]
    (a a' : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (hfirst : a.order (0 : Fin (N + 3)) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b) :
    a'.Lemma813Conditions b := by
  have horders : a.SameOrders a' := by
    letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
    exact a.order_invariant a'
  have hfirst' : a'.order (0 : Fin (N + 3)) = b.order (0 : Fin 1) := by
    rw [← horders (0 : Fin (N + 3))]
    exact hfirst
  have original : RepresentationConditions a b (Nat.zero_le (N + 2)) := by
    refine {
      orderCondition := a.lemma813_orderCondition b hfirst
      defectCondition :=
        (a.lemma813_defectCondition_iff b hfirst).mpr
          conditions.defectEquality
      centralRepresentations := ?_
      longRepresentations := ?_
    }
    · exact (a.lemma813_centralCondition_iff b hfirst).mpr
        (conditions.binaryHigher (by omega))
    · cases N with
      | zero =>
          intro i
          have := i.one_lt
          have := i.succ_lt_large
          omega
      | succ N =>
          exact (a.lemma813_longCondition_iff b hfirst).mpr
            (conditions.ternaryHigher (by omega))
  have changed : RepresentationConditions a' b (Nat.zero_le (N + 2)) :=
    (a.representationConditions_changeBONG_iff
      (classificationV := classificationV)
      (classificationW := classificationW) a' b b
      (Nat.zero_le (N + 2))).mp original
  refine {
    defectEquality :=
      (a'.lemma813_defectCondition_iff b hfirst').mp
        changed.defectCondition
    binaryRankTwo := ?_
    binaryHigher := ?_
    ternaryRankThree := ?_
    ternaryHigher := ?_
  }
  · intro hm
    omega
  · intro hm
    exact (a'.lemma813_centralCondition_iff b hfirst').mp
      changed.centralRepresentations
  · intro hm houter'
    have hN : N = 0 := by omega
    subst N
    have houter : a.order (0 : Fin 3) = a.order (2 : Fin 3) := by
      rw [horders (0 : Fin 3), horders (2 : Fin 3)]
      exact houter'
    have hrepresentation := conditions.ternaryRankThree rfl houter
    exact hrepresentation.trans (a.fullPrefix_represents a')
  · intro hm
    cases N with
    | zero => omega
    | succ N =>
        exact (a'.lemma813_longCondition_iff b hfirst').mp
          changed.longRepresentations

/-- The data retained after reduction (I) in the converse proof of Lemma
8.14.  In addition to Corollary 8.10's binary normal form, it records the
transported Lemma 8.13 hypotheses and the transported exclusion of (a)--(c).
-/
structure Beli2019Lemma814FirstNormalForm
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1) where
  transformed : GoodBONG q L (N + 3)
  headValue_eq :
    transformed.valueUnit (0 : Fin (N + 3)) =
      a.valueUnit (0 : Fin (N + 3))
  firstOrder_eq :
    transformed.order (0 : Fin (N + 3)) = b.order (0 : Fin 1)
  firstBinaryAlpha_eq :
    transformed.firstBinaryAlpha =
      (transformed.alphaValue (0 : Fin (N + 2)) : WithTop ℚ)
  conditions : transformed.Lemma813Conditions b
  notExceptional : ¬transformed.Beli2019Lemma814Exceptional b

/-- Reduction (I) is legitimate in the noncircular formulation of Lemma
8.14: Corollary 8.10 supplies the normal form, Lemma 3.10 transports the
proper-prefix representation clauses, and the full rank-three endpoint is
transported by an actual BONG coordinate change. -/
theorem exists_lemma814FirstNormalForm
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
    [Beli2019Lemma310RepresentationLaws.{u, v, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (hfirst : a.order (0 : Fin (N + 3)) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hnotExceptional : ¬a.Beli2019Lemma814Exceptional b) :
    Nonempty (a.Beli2019Lemma814FirstNormalForm b) := by
  letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
  rcases a.beli2019Corollary810 with ⟨D⟩
  have horders : a.SameOrders D.transformed := a.order_invariant D.transformed
  have hfirst' : D.transformed.order (0 : Fin (N + 3)) =
      b.order (0 : Fin 1) := by
    rw [← horders (0 : Fin (N + 3))]
    exact hfirst
  have hconditions := a.lemma813Conditions_changeTargetBONG
    (classificationV := classificationV)
    (classificationW := classificationW) D.transformed b hfirst conditions
  have hinvariant := a.lemma814Exceptional_changeBONG_iff_full
    (classificationV := classificationV)
    (classificationW := classificationW)
    (prefixChangeV := prefixChangeV)
    (prefixChangeW := prefixChangeW) D.transformed b
  exact ⟨{
    transformed := D.transformed
    headValue_eq := D.headValue_eq
    firstOrder_eq := hfirst'
    firstBinaryAlpha_eq := D.firstBinaryAlpha_eq
    conditions := hconditions
    notExceptional := fun E ↦ hnotExceptional (hinvariant.mpr E)
  }⟩

/-- Direct binary branch of Lemma 8.14.  If `ε` lies in the norm group of
the first adjacent binary form, generalized binary scaling changes the first
BONG value to `b₁` while preserving the target lattice. -/
theorem beli2019Lemma814_binaryBranch
    [QuadraticDefectLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (horder : a.order (0 : Fin (N + 3)) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hbinary : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin (N + 2)) : WithTop ℚ))
    (hhilbert : hilbertSymbol K (a.lemma814Epsilon b)
      (a.adjacentProduct (0 : Fin (N + 2))) = 1) :
    Nonempty (a.Beli2019PrescribedFirstValueTransform b) := by
  have hunit := a.lemma814Epsilon_isValuationUnit b horder
  have hdefect := a.alpha_le_lemma814EpsilonDefect b conditions
  rcases a.exists_firstValueScaling_of_firstBinaryAlpha
      (a.lemma814Epsilon b) hunit hdefect hbinary hhilbert with
    ⟨transformed, hfirst⟩
  refine ⟨{
    transformed := transformed
    firstValue_eq := ?_
  }⟩
  exact hfirst.trans (a.lemma814Epsilon_mul_firstValue b)

/-- The concrete rank-three, unequal-outer-order construction after the
choice of the auxiliary unit `η`.  The hypotheses on `η` are exactly the
defect and Hasse conditions verified in the corresponding paragraph of the
paper; all subsequent ambient-space, Lemma 8.6, and lattice-classification
steps are proved here. -/
theorem beli2019Lemma814_ternaryUnequal_of_eta
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicDiagonalClassificationLaws K]
    (a : GoodBONG q L 3) (b : GoodBONG r M 1)
    (horder : a.order (0 : Fin 3) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (houter : a.Lemma814UnequalOuterBound b)
    (η : Kˣ)
    (hηUnit : IsValuationUnit K (η : K))
    (hηDefect : (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
      defectOrder (K := K) η)
    (hadjacent :
      hilbertSymbol K
          (-(η * a.valueUnit (0 : Fin 3) * a.valueUnit (1 : Fin 3)))
          (-(a.lemma814Epsilon b * a.valueUnit (1 : Fin 3) *
            a.valueUnit (2 : Fin 3))) =
        hilbertSymbol K
          (-(a.valueUnit (0 : Fin 3) * a.valueUnit (1 : Fin 3)))
          (-(a.valueUnit (1 : Fin 3) * a.valueUnit (2 : Fin 3)))) :
    Nonempty (a.Beli2019PrescribedFirstValueTransform b) := by
  have hproperty : a.toBONG.HasPropertyA := by
    intro i hi
    fin_cases i
    · change a.order (0 : Fin 3) < a.order (2 : Fin 3)
      exact houter.1
    · norm_num at hi
    · norm_num at hi
  have hεUnit := a.lemma814Epsilon_isValuationUnit b horder
  have hεDefect := a.alpha_le_lemma814EpsilonDefect b conditions
  have hAlphaSum :=
    a.alphaSum_le_twoE_of_lemma814UnequalOuterBound b conditions houter
  rcases a.exists_goodBONG_ternaryScaled_of_propertyA
      (a.lemma814Epsilon b) η hεUnit hηUnit hεDefect hηDefect
      hadjacent hproperty hAlphaSum with
    ⟨transformed, hfirst⟩
  exact ⟨{
    transformed := transformed
    firstValue_eq := hfirst.trans (a.lemma814Epsilon_mul_firstValue b)
  }⟩

/-- The concrete rank-three, equal-outer-order construction after the
choice of the auxiliary unit `η`.  These are exactly conditions (1)--(3)
isolated in the corresponding paragraph of the paper. -/
theorem beli2019Lemma814_ternaryEqual_of_eta
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicDiagonalClassificationLaws K]
    (a : GoodBONG q L 3) (b : GoodBONG r M 1)
    (horder : a.order (0 : Fin 3) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (houter : a.order (0 : Fin 3) = a.order (2 : Fin 3))
    (η : Kˣ)
    (hηUnit : IsValuationUnit K (η : K))
    (hηDefect : (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
      defectOrder (K := K) η)
    (halpha : a.TernaryEqualOuterAlphaCriterion
      (a.lemma814Epsilon b) η)
    (hadjacent :
      hilbertSymbol K
          (-(η * a.valueUnit (0 : Fin 3) * a.valueUnit (1 : Fin 3)))
          (-(a.lemma814Epsilon b * a.valueUnit (1 : Fin 3) *
            a.valueUnit (2 : Fin 3))) =
        hilbertSymbol K
          (-(a.valueUnit (0 : Fin 3) * a.valueUnit (1 : Fin 3)))
          (-(a.valueUnit (1 : Fin 3) * a.valueUnit (2 : Fin 3)))) :
    Nonempty (a.Beli2019PrescribedFirstValueTransform b) := by
  have hεUnit := a.lemma814Epsilon_isValuationUnit b horder
  have hεDefect := a.alpha_le_lemma814EpsilonDefect b conditions
  rcases a.exists_goodBONG_ternaryScaled_of_equalOuter
      (a.lemma814Epsilon b) η hεUnit hηUnit hεDefect hηDefect
      hadjacent houter halpha with
    ⟨transformed, hfirst⟩
  exact ⟨{
    transformed := transformed
    firstValue_eq := hfirst.trans (a.lemma814Epsilon_mul_firstValue b)
  }⟩

/-- Complete anisotropic subcase of the rank-three `R₁ = R₃` branch.
The oddness of `α₂`, exclusion of exception (a), and Lemma 8.2(i) choose
the auxiliary valuation unit; its product with the first adjacent class has
defect exactly `α₂` and the required negative Hilbert sign. -/
theorem beli2019Lemma814_ternaryEqual_anisotropic
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicDiagonalClassificationLaws K]
    (a : GoodBONG q L 3) (b : GoodBONG r M 1)
    (horder : a.order (0 : Fin 3) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (houter : a.order (0 : Fin 3) = a.order (2 : Fin 3))
    (hanisotropic : a.Lemma814FirstThreeAnisotropic)
    (hnotExceptional : ¬a.Beli2019Lemma814Exceptional b) :
    Nonempty (a.Beli2019PrescribedFirstValueTransform b) := by
  have hremark := a.beli2019Remark87 (0 : Fin 1) (by
    simpa [remark87PreviousValue, remark87NextValue] using houter)
  have hsecondOdd :=
    a.secondAlpha_isOddRationalInteger_of_equalOuter_anisotropic
      houter hanisotropic
  have hfirstNonnegative : 0 ≤ a.alphaValue (0 : Fin 2) :=
    (a.beli2009Lemma27_i (0 : Fin 2)).1
  have hsecondNonnegative : 0 ≤ a.alphaValue (1 : Fin 2) :=
    (a.beli2009Lemma27_i (1 : Fin 2)).1
  have hsecondLe : a.alphaValue (1 : Fin 2) ≤
      2 * (ramificationIndex K : ℚ) := by
    have hsum := hremark.alphaSum_le_twoE
    change a.alphaValue (0 : Fin 2) + a.alphaValue (1 : Fin 2) ≤
      2 * (ramificationIndex K : ℚ) at hsum
    linarith
  have hsecondNe : a.alphaValue (1 : Fin 2) ≠
      2 * (ramificationIndex K : ℚ) := by
    intro hendpoint
    have hcopy := hsecondOdd
    rcases hcopy with ⟨z, hzOdd, hz⟩
    have hzEndpoint : z = 2 * (ramificationIndex K : Int) := by
      exact_mod_cast hz.symm.trans hendpoint
    rcases hzOdd with ⟨k, hk⟩
    omega
  have hsecondLt : a.alphaValue (1 : Fin 2) <
      2 * (ramificationIndex K : ℚ) :=
    lt_of_le_of_ne hsecondLe hsecondNe
  rcases DyadicUnitDefectSpectrumLaws.exists_unit_of_odd_rational_defect
      (a.alphaValue (1 : Fin 2)) hsecondOdd hsecondNonnegative
      hsecondLt with
    ⟨reference, hrefUnit, hrefDefect⟩
  have hsumTop :=
    a.secondAlpha_add_fullDefect_le_twoE_of_notExceptional_anisotropic
      b houter hanisotropic hnotExceptional
  have hsumDefectOrder :
      defectOrder (K := K)
          (a.lemma814Epsilon b * a.adjacentProduct (1 : Fin 2)) +
          defectOrder (K := K) reference ≤
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
    rw [hrefDefect,
      ← a.lemma814TernaryFullDefect_eq_epsilon_mul_secondAdjacent b]
    simpa only [add_comm, Nat.cast_mul, Nat.cast_ofNat] using hsumTop
  have hsumQuadratic :=
    quadraticDefect_add_le_twoE_of_defectOrder_add_le_twoE
      (a.lemma814Epsilon b * a.adjacentProduct (1 : Fin 2))
      reference hsumDefectOrder
  have hadjacentEven := a.ternaryAdjacentOrders_even_of_equalOuter houter
  rcases exists_valuationUnit_multiplier_hilbert_neg_of_defect_sum
      (a.lemma814Epsilon b * a.adjacentProduct (1 : Fin 2))
      (a.adjacentProduct (0 : Fin 2)) reference
      hadjacentEven.1 hrefUnit hsumQuadratic with
    ⟨η, hηUnit, hηQuadraticDefect, hηHilbert⟩
  have hηProductDefect :
      defectOrder (K := K)
          (η * a.adjacentProduct (0 : Fin 2)) =
        (a.alphaValue (1 : Fin 2) : WithTop ℚ) := by
    have h := defectOrder_eq_of_quadraticDefect_eq
      (η * a.adjacentProduct (0 : Fin 2)) reference
      hηQuadraticDefect
    rw [hrefDefect] at h
    exact h
  have hfirstAdjacentLower :
      (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
        defectOrder (K := K) (a.adjacentProduct (0 : Fin 2)) := by
    simpa [adjacentDefect, remark87PreviousAlpha,
      remark87CurrentAlpha] using
        hremark.currentAlpha_le_previousRawDefect
  have hηDefect :
      (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
        defectOrder (K := K) η := by
    by_contra hnot
    have hηLt : defectOrder (K := K) η <
        (a.alphaValue (1 : Fin 2) : WithTop ℚ) := lt_of_not_ge hnot
    have hηLtAdjacent : defectOrder (K := K) η <
        defectOrder (K := K) (a.adjacentProduct (0 : Fin 2)) :=
      hηLt.trans_le hfirstAdjacentLower
    have hdomination :=
      defectOrder_mul_eq_left_of_lt_right hηLtAdjacent
    have hηEq : defectOrder (K := K) η =
        (a.alphaValue (1 : Fin 2) : WithTop ℚ) :=
      hdomination.symm.trans hηProductDefect
    exact (ne_of_lt hηLt) hηEq
  have hfirstCoefficient :
      -(η * a.valueUnit (0 : Fin 3) * a.valueUnit (1 : Fin 3)) =
        η * a.adjacentProduct (0 : Fin 2) := by
    unfold adjacentProduct
    have hcast : (0 : Fin 2).castSucc = (0 : Fin 3) := rfl
    have hsucc : (0 : Fin 2).succ = (1 : Fin 3) := rfl
    rw [hcast, hsucc]
    apply Units.ext
    simp only [Units.val_neg, Units.val_mul]
    ring
  have hsecondCoefficient :
      -(a.lemma814Epsilon b * a.valueUnit (1 : Fin 3) *
          a.valueUnit (2 : Fin 3)) =
        a.lemma814Epsilon b * a.adjacentProduct (1 : Fin 2) := by
    unfold adjacentProduct
    have hcast : (1 : Fin 2).castSucc = (1 : Fin 3) := rfl
    have hsucc : (1 : Fin 2).succ = (2 : Fin 3) := rfl
    rw [hcast, hsucc]
    apply Units.ext
    simp only [Units.val_neg, Units.val_mul]
    ring
  have halpha : a.TernaryEqualOuterAlphaCriterion
      (a.lemma814Epsilon b) η := by
    right
    right
    rw [hfirstCoefficient]
    exact hηProductDefect
  have horiginalHilbert :=
    a.adjacentHilbert_neg_of_firstThreeAnisotropic hanisotropic
  have hadjacent :
      hilbertSymbol K
          (-(η * a.valueUnit (0 : Fin 3) * a.valueUnit (1 : Fin 3)))
          (-(a.lemma814Epsilon b * a.valueUnit (1 : Fin 3) *
            a.valueUnit (2 : Fin 3))) =
        hilbertSymbol K
          (-(a.valueUnit (0 : Fin 3) * a.valueUnit (1 : Fin 3)))
          (-(a.valueUnit (1 : Fin 3) * a.valueUnit (2 : Fin 3))) := by
    rw [hfirstCoefficient, hsecondCoefficient]
    change hilbertSymbol K
        (η * a.adjacentProduct (0 : Fin 2))
        (a.lemma814Epsilon b * a.adjacentProduct (1 : Fin 2)) =
      hilbertSymbol K
        (a.adjacentProduct (0 : Fin 2))
        (a.adjacentProduct (1 : Fin 2))
    exact hηHilbert.trans horiginalHilbert.symm
  exact a.beli2019Lemma814_ternaryEqual_of_eta
    b horder conditions houter η hηUnit hηDefect halpha hadjacent

/-- The easy isotropic subcase of `R₁ = R₃`: if the first alpha already
attains its half-gap, or the full comparison defect is the first alpha, a
valuation-unit multiplier can make the first scaled adjacent class square.
-/
theorem beli2019Lemma814_ternaryEqual_isotropic_easy
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicDiagonalClassificationLaws K]
    (a : GoodBONG q L 3) (b : GoodBONG r M 1)
    (horder : a.order (0 : Fin 3) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (houter : a.order (0 : Fin 3) = a.order (2 : Fin 3))
    (hisotropic : a.Lemma814FirstThreeIsotropic)
    (heasy :
      a.AttainsHalfGap (0 : Fin 2) ∨
        a.truncatedPrefixDefect b (-1) 3 1 =
          (a.alphaValue (0 : Fin 2) : WithTop ℚ)) :
    Nonempty (a.Beli2019PrescribedFirstValueTransform b) := by
  have hremark := a.beli2019Remark87 (0 : Fin 1) (by
    simpa [remark87PreviousValue, remark87NextValue] using houter)
  have hadjacentEven := a.ternaryAdjacentOrders_even_of_equalOuter houter
  rcases exists_valuationUnit_multiplier_isSquare
      (a.adjacentProduct (0 : Fin 2)) hadjacentEven.1 with
    ⟨η, hηUnit, hηSquare, hηQuadraticDefect⟩
  have hηDefectEq : defectOrder (K := K) η =
      defectOrder (K := K) (a.adjacentProduct (0 : Fin 2)) :=
    defectOrder_eq_of_quadraticDefect_eq η
      (a.adjacentProduct (0 : Fin 2)) hηQuadraticDefect
  have hfirstAdjacentLower :
      (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
        defectOrder (K := K) (a.adjacentProduct (0 : Fin 2)) := by
    simpa [adjacentDefect, remark87PreviousAlpha,
      remark87CurrentAlpha] using
        hremark.currentAlpha_le_previousRawDefect
  have hηDefect :
      (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
        defectOrder (K := K) η := by
    rw [hηDefectEq]
    exact hfirstAdjacentLower
  have hfirstCoefficient :
      -(η * a.valueUnit (0 : Fin 3) * a.valueUnit (1 : Fin 3)) =
        η * a.adjacentProduct (0 : Fin 2) := by
    unfold adjacentProduct
    have hcast : (0 : Fin 2).castSucc = (0 : Fin 3) := rfl
    have hsucc : (0 : Fin 2).succ = (1 : Fin 3) := rfl
    rw [hcast, hsucc]
    apply Units.ext
    simp only [Units.val_neg, Units.val_mul]
    ring
  have hsecondCoefficient :
      -(a.lemma814Epsilon b * a.valueUnit (1 : Fin 3) *
          a.valueUnit (2 : Fin 3)) =
        a.lemma814Epsilon b * a.adjacentProduct (1 : Fin 2) := by
    unfold adjacentProduct
    have hcast : (1 : Fin 2).castSucc = (1 : Fin 3) := rfl
    have hsucc : (1 : Fin 2).succ = (2 : Fin 3) := rfl
    rw [hcast, hsucc]
    apply Units.ext
    simp only [Units.val_neg, Units.val_mul]
    ring
  have halpha : a.TernaryEqualOuterAlphaCriterion
      (a.lemma814Epsilon b) η := by
    rcases heasy with hhalf | hfull
    · exact Or.inl hhalf
    · right
      left
      rw [hsecondCoefficient]
      calc
        defectOrder (K := K)
            (a.lemma814Epsilon b * a.adjacentProduct (1 : Fin 2)) =
            a.truncatedPrefixDefect b (-1) 3 1 :=
          (a.lemma814TernaryFullDefect_eq_epsilon_mul_secondAdjacent b).symm
        _ = (a.alphaValue (0 : Fin 2) : WithTop ℚ) := hfull
  have hcandidateOne :
      hilbertSymbol K
          (η * a.adjacentProduct (0 : Fin 2))
          (a.lemma814Epsilon b * a.adjacentProduct (1 : Fin 2)) = 1 :=
    hilbertSymbol_eq_one_of_isSquare_left K hηSquare
  have horiginalOne :
      hilbertSymbol K
          (a.adjacentProduct (0 : Fin 2))
          (a.adjacentProduct (1 : Fin 2)) = 1 :=
    (a.lemma814FirstThreeIsotropic_iff_adjacentHilbertOne).mp hisotropic
  have hadjacent :
      hilbertSymbol K
          (-(η * a.valueUnit (0 : Fin 3) * a.valueUnit (1 : Fin 3)))
          (-(a.lemma814Epsilon b * a.valueUnit (1 : Fin 3) *
            a.valueUnit (2 : Fin 3))) =
        hilbertSymbol K
          (-(a.valueUnit (0 : Fin 3) * a.valueUnit (1 : Fin 3)))
          (-(a.valueUnit (1 : Fin 3) * a.valueUnit (2 : Fin 3))) := by
    rw [hfirstCoefficient, hsecondCoefficient]
    change hilbertSymbol K
        (η * a.adjacentProduct (0 : Fin 2))
        (a.lemma814Epsilon b * a.adjacentProduct (1 : Fin 2)) =
      hilbertSymbol K
        (a.adjacentProduct (0 : Fin 2))
        (a.adjacentProduct (1 : Fin 2))
    exact hcandidateOne.trans horiginalOne.symm
  exact a.beli2019Lemma814_ternaryEqual_of_eta
    b horder conditions houter η hηUnit hηDefect halpha hadjacent

/-- The remaining isotropic `R₁ = R₃` subcase.  Strictness of the first
half-gap makes `α₂` an odd unit defect.  Lemma 8.2(ii)--(iii) supplies the
positive Hilbert partner; in residue cardinality two, exception (b) is
exactly the forbidden endpoint equality. -/
theorem beli2019Lemma814_ternaryEqual_isotropic_strict
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicDiagonalClassificationLaws K]
    (a : GoodBONG q L 3) (b : GoodBONG r M 1)
    (horder : a.order (0 : Fin 3) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (houter : a.order (0 : Fin 3) = a.order (2 : Fin 3))
    (hisotropic : a.Lemma814FirstThreeIsotropic)
    (hfirstStrict : ¬a.AttainsHalfGap (0 : Fin 2))
    (hnotExceptional : ¬a.Beli2019Lemma814Exceptional b) :
    Nonempty (a.Beli2019PrescribedFirstValueTransform b) := by
  have hremark := a.beli2019Remark87 (0 : Fin 1) (by
    simpa [remark87PreviousValue, remark87NextValue] using houter)
  have hsecondNotHalf :
      a.alphaValue (1 : Fin 2) ≠ a.halfGapValue (1 : Fin 2) := by
    intro hsecondHalf
    apply hfirstStrict
    apply hremark.attainsHalfGap_iff.mpr
    exact hsecondHalf
  have hsecondOdd := a.beli2009Lemma27_iv (1 : Fin 2) hsecondNotHalf
  have hfirstNonnegative : 0 ≤ a.alphaValue (0 : Fin 2) :=
    (a.beli2009Lemma27_i (0 : Fin 2)).1
  have hsecondNonnegative : 0 ≤ a.alphaValue (1 : Fin 2) :=
    (a.beli2009Lemma27_i (1 : Fin 2)).1
  have hsecondLe : a.alphaValue (1 : Fin 2) ≤
      2 * (ramificationIndex K : ℚ) := by
    have hsum := hremark.alphaSum_le_twoE
    change a.alphaValue (0 : Fin 2) + a.alphaValue (1 : Fin 2) ≤
      2 * (ramificationIndex K : ℚ) at hsum
    linarith
  have hsecondNe : a.alphaValue (1 : Fin 2) ≠
      2 * (ramificationIndex K : ℚ) := by
    intro hendpoint
    have hcopy := hsecondOdd
    rcases hcopy with ⟨z, hzOdd, hz⟩
    have hzEndpoint : z = 2 * (ramificationIndex K : Int) := by
      exact_mod_cast hz.symm.trans hendpoint
    rcases hzOdd with ⟨k, hk⟩
    omega
  have hsecondLt : a.alphaValue (1 : Fin 2) <
      2 * (ramificationIndex K : ℚ) :=
    lt_of_le_of_ne hsecondLe hsecondNe
  rcases DyadicUnitDefectSpectrumLaws.exists_unit_of_odd_rational_defect
      (a.alphaValue (1 : Fin 2)) hsecondOdd hsecondNonnegative
      hsecondLt with
    ⟨reference, hrefUnit, hrefDefect⟩
  have hrefNonzero : quadraticDefect K reference ≠ 0 :=
    quadraticDefect_ne_zero_of_isValuationUnit reference hrefUnit
  have hrefNotTwoE : quadraticDefect K reference ≠
      ((2 * ramificationIndex K : Nat) : WithTop Nat) := by
    intro hrefTwoE
    have horderEndpoint : defectOrder (K := K) reference =
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
      unfold defectOrder
      rw [hrefTwoE]
      rfl
    rw [hrefDefect] at horderEndpoint
    have hendpoint : a.alphaValue (1 : Fin 2) =
        2 * (ramificationIndex K : ℚ) := by
      have h := WithTop.coe_eq_coe.mp horderEndpoint
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using h
    exact (ne_of_lt hsecondLt) hendpoint
  have hnotZeroTwoE :
      ¬IsZeroTwoEDefectPair (K := K)
        (a.lemma814Epsilon b * a.adjacentProduct (1 : Fin 2))
        reference := by
    rintro (hleft | hright)
    · exact hrefNotTwoE hleft.2
    · exact hrefNonzero hright.2
  obtain ⟨u, huUnit, huDefect, huHilbert⟩ :
      ∃ u : Kˣ,
        IsValuationUnit K (u : K) ∧
          quadraticDefect K u = quadraticDefect K reference ∧
          hilbertSymbol K
            (a.lemma814Epsilon b * a.adjacentProduct (1 : Fin 2)) u = 1 := by
    by_cases hres : HasResidueFieldMoreThanTwoElements (K := K)
    · exact beli2019Lemma82_ii_unit hres
        (a.lemma814Epsilon b * a.adjacentProduct (1 : Fin 2))
        reference hrefUnit hnotZeroTwoE
    · have hsumNe :
          quadraticDefect K
                (a.lemma814Epsilon b * a.adjacentProduct (1 : Fin 2)) +
              quadraticDefect K reference ≠
            ((2 * ramificationIndex K : Nat) : WithTop Nat) := by
        intro hsumEq
        have horderSum :=
          defectOrder_add_eq_twoE_of_quadraticDefect_add_eq_twoE
            (a.lemma814Epsilon b * a.adjacentProduct (1 : Fin 2))
            reference hsumEq
        rw [hrefDefect,
          ← a.lemma814TernaryFullDefect_eq_epsilon_mul_secondAdjacent b]
          at horderSum
        have hdefectSum :
            (a.alphaValue (1 : Fin 2) : WithTop ℚ) +
                a.truncatedPrefixDefect b (-1) 3 1 =
              (((2 * (ramificationIndex K : ℚ)) : ℚ) : WithTop ℚ) := by
          simpa only [add_comm, Nat.cast_mul, Nat.cast_ofNat] using horderSum
        apply hnotExceptional
        right
        left
        exact {
          firstThirdOrders_eq := houter
          residueTwo := hres
          firstAlpha_strict := lt_of_le_of_ne
            (a.alphaValue_le_halfGapValue (0 : Fin 2))
            (by exact hfirstStrict)
          defectSum_eq := by
            simpa [lemma814FirstThirdCappedDefect] using hdefectSum
          firstThree_isotropic := hisotropic
          laterAlphaSum_strict := by
            intro hfour
            omega
        }
      exact beli2019Lemma82_iii_unit hres
        (a.lemma814Epsilon b * a.adjacentProduct (1 : Fin 2))
        reference hrefUnit hsumNe
  have huNonzero : quadraticDefect K u ≠ 0 := by
    rw [huDefect]
    exact hrefNonzero
  have hadjacentEven := a.ternaryAdjacentOrders_even_of_equalOuter houter
  rcases exists_valuationUnit_multiplier_same_defect_same_hilbert
      (a.lemma814Epsilon b * a.adjacentProduct (1 : Fin 2))
      (a.adjacentProduct (0 : Fin 2)) u hadjacentEven.1 huNonzero with
    ⟨η, hηUnit, hηDefectU, hηHilbertU⟩
  have hηQuadraticDefect :
      quadraticDefect K (η * a.adjacentProduct (0 : Fin 2)) =
        quadraticDefect K reference :=
    hηDefectU.trans huDefect
  have hηProductDefect :
      defectOrder (K := K)
          (η * a.adjacentProduct (0 : Fin 2)) =
        (a.alphaValue (1 : Fin 2) : WithTop ℚ) := by
    have h := defectOrder_eq_of_quadraticDefect_eq
      (η * a.adjacentProduct (0 : Fin 2)) reference
      hηQuadraticDefect
    rw [hrefDefect] at h
    exact h
  have hfirstAdjacentLower :
      (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
        defectOrder (K := K) (a.adjacentProduct (0 : Fin 2)) := by
    simpa [adjacentDefect, remark87PreviousAlpha,
      remark87CurrentAlpha] using
        hremark.currentAlpha_le_previousRawDefect
  have hηDefect :
      (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
        defectOrder (K := K) η := by
    by_contra hnot
    have hηLt : defectOrder (K := K) η <
        (a.alphaValue (1 : Fin 2) : WithTop ℚ) := lt_of_not_ge hnot
    have hηLtAdjacent : defectOrder (K := K) η <
        defectOrder (K := K) (a.adjacentProduct (0 : Fin 2)) :=
      hηLt.trans_le hfirstAdjacentLower
    have hdomination :=
      defectOrder_mul_eq_left_of_lt_right hηLtAdjacent
    have hηEq : defectOrder (K := K) η =
        (a.alphaValue (1 : Fin 2) : WithTop ℚ) :=
      hdomination.symm.trans hηProductDefect
    exact (ne_of_lt hηLt) hηEq
  have hfirstCoefficient :
      -(η * a.valueUnit (0 : Fin 3) * a.valueUnit (1 : Fin 3)) =
        η * a.adjacentProduct (0 : Fin 2) := by
    unfold adjacentProduct
    have hcast : (0 : Fin 2).castSucc = (0 : Fin 3) := rfl
    have hsucc : (0 : Fin 2).succ = (1 : Fin 3) := rfl
    rw [hcast, hsucc]
    apply Units.ext
    simp only [Units.val_neg, Units.val_mul]
    ring
  have hsecondCoefficient :
      -(a.lemma814Epsilon b * a.valueUnit (1 : Fin 3) *
          a.valueUnit (2 : Fin 3)) =
        a.lemma814Epsilon b * a.adjacentProduct (1 : Fin 2) := by
    unfold adjacentProduct
    have hcast : (1 : Fin 2).castSucc = (1 : Fin 3) := rfl
    have hsucc : (1 : Fin 2).succ = (2 : Fin 3) := rfl
    rw [hcast, hsucc]
    apply Units.ext
    simp only [Units.val_neg, Units.val_mul]
    ring
  have halpha : a.TernaryEqualOuterAlphaCriterion
      (a.lemma814Epsilon b) η := by
    right
    right
    rw [hfirstCoefficient]
    exact hηProductDefect
  have hcandidateOne :
      hilbertSymbol K
          (η * a.adjacentProduct (0 : Fin 2))
          (a.lemma814Epsilon b * a.adjacentProduct (1 : Fin 2)) = 1 := by
    calc
      hilbertSymbol K
          (η * a.adjacentProduct (0 : Fin 2))
          (a.lemma814Epsilon b * a.adjacentProduct (1 : Fin 2)) =
          hilbertSymbol K
            (a.lemma814Epsilon b * a.adjacentProduct (1 : Fin 2))
            (η * a.adjacentProduct (0 : Fin 2)) :=
        hilbertSymbol_comm K _ _
      _ = hilbertSymbol K
          (a.lemma814Epsilon b * a.adjacentProduct (1 : Fin 2)) u :=
        hηHilbertU
      _ = 1 := huHilbert
  have horiginalOne :
      hilbertSymbol K
          (a.adjacentProduct (0 : Fin 2))
          (a.adjacentProduct (1 : Fin 2)) = 1 :=
    (a.lemma814FirstThreeIsotropic_iff_adjacentHilbertOne).mp hisotropic
  have hadjacent :
      hilbertSymbol K
          (-(η * a.valueUnit (0 : Fin 3) * a.valueUnit (1 : Fin 3)))
          (-(a.lemma814Epsilon b * a.valueUnit (1 : Fin 3) *
            a.valueUnit (2 : Fin 3))) =
        hilbertSymbol K
          (-(a.valueUnit (0 : Fin 3) * a.valueUnit (1 : Fin 3)))
          (-(a.valueUnit (1 : Fin 3) * a.valueUnit (2 : Fin 3))) := by
    rw [hfirstCoefficient, hsecondCoefficient]
    change hilbertSymbol K
        (η * a.adjacentProduct (0 : Fin 2))
        (a.lemma814Epsilon b * a.adjacentProduct (1 : Fin 2)) =
      hilbertSymbol K
        (a.adjacentProduct (0 : Fin 2))
        (a.adjacentProduct (1 : Fin 2))
    exact hcandidateOne.trans horiginalOne.symm
  exact a.beli2019Lemma814_ternaryEqual_of_eta
    b horder conditions houter η hηUnit hηDefect halpha hadjacent

/-- Complete isotropic subcase in ternary rank. -/
theorem beli2019Lemma814_ternaryEqual_isotropic
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicDiagonalClassificationLaws K]
    (a : GoodBONG q L 3) (b : GoodBONG r M 1)
    (horder : a.order (0 : Fin 3) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (houter : a.order (0 : Fin 3) = a.order (2 : Fin 3))
    (hisotropic : a.Lemma814FirstThreeIsotropic)
    (hnotExceptional : ¬a.Beli2019Lemma814Exceptional b) :
    Nonempty (a.Beli2019PrescribedFirstValueTransform b) := by
  by_cases hhalf : a.AttainsHalfGap (0 : Fin 2)
  · exact a.beli2019Lemma814_ternaryEqual_isotropic_easy
      b horder conditions houter hisotropic (Or.inl hhalf)
  · by_cases hfull : a.truncatedPrefixDefect b (-1) 3 1 =
        (a.alphaValue (0 : Fin 2) : WithTop ℚ)
    · exact a.beli2019Lemma814_ternaryEqual_isotropic_easy
        b horder conditions houter hisotropic (Or.inr hfull)
    · exact a.beli2019Lemma814_ternaryEqual_isotropic_strict
        b horder conditions houter hisotropic hhalf hnotExceptional

/-- Complete rank-three `R₁ = R₃` branch, split according to isotropy of
the first ternary prefix exactly as in the paper. -/
theorem beli2019Lemma814_ternaryEqual
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicDiagonalClassificationLaws K]
    (a : GoodBONG q L 3) (b : GoodBONG r M 1)
    (horder : a.order (0 : Fin 3) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (houter : a.order (0 : Fin 3) = a.order (2 : Fin 3))
    (hnotExceptional : ¬a.Beli2019Lemma814Exceptional b) :
    Nonempty (a.Beli2019PrescribedFirstValueTransform b) := by
  by_cases hisotropic : a.Lemma814FirstThreeIsotropic
  · exact a.beli2019Lemma814_ternaryEqual_isotropic
      b horder conditions houter hisotropic hnotExceptional
  · exact a.beli2019Lemma814_ternaryEqual_anisotropic
      b horder conditions houter
        ((a.not_firstThreeIsotropic_iff_anisotropic).mp hisotropic)
        hnotExceptional

/-- The complete rank-three branch with unequal outer orders.  The numerical
inequality makes the full comparison defect finite and strictly below `2e`;
the complementary Hilbert choice supplies `η`, and the preceding concrete
ternary construction finishes the prescribed first-value change. -/
theorem beli2019Lemma814_ternaryUnequal
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicDiagonalClassificationLaws K]
    (a : GoodBONG q L 3) (b : GoodBONG r M 1)
    (horder : a.order (0 : Fin 3) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (houter : a.Lemma814UnequalOuterBound b)
    (hεHilbert : hilbertSymbol K (a.lemma814Epsilon b)
      (a.adjacentProduct (0 : Fin 2)) = -1) :
    Nonempty (a.Beli2019PrescribedFirstValueTransform b) := by
  have hsecondPos :=
    a.secondAlpha_pos_of_lemma814UnequalOuterBound
      b conditions houter hεHilbert
  have hsumTop :=
    a.secondAlpha_add_fullDefect_le_twoE_of_unequalOuter b houter
  have hfullNotTop :
      a.truncatedPrefixDefect b (-1) 3 1 ≠ ⊤ := by
    intro htop
    rw [htop] at hsumTop
    have hfinite :
        (2 : WithTop ℚ) *
            ((ramificationIndex K : ℚ) : WithTop ℚ) ≠ ⊤ := by
      rw [show
        (2 : WithTop ℚ) *
            ((ramificationIndex K : ℚ) : WithTop ℚ) =
          ((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) by
        norm_num]
      exact WithTop.coe_ne_top
    have hrightTop :
        (2 : WithTop ℚ) *
            ((ramificationIndex K : ℚ) : WithTop ℚ) = ⊤ :=
      top_unique (by simpa only [add_top] using hsumTop)
    exact hfinite hrightTop
  obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp hfullNotTop
  have hzDefect :
      defectOrder (K := K)
          (a.lemma814Epsilon b * a.adjacentProduct (1 : Fin 2)) =
        (d : WithTop ℚ) := by
    calc
      defectOrder (K := K)
          (a.lemma814Epsilon b * a.adjacentProduct (1 : Fin 2)) =
          a.truncatedPrefixDefect b (-1) 3 1 :=
        (a.lemma814TernaryFullDefect_eq_epsilon_mul_secondAdjacent b).symm
      _ = (d : WithTop ℚ) := hd.symm
  have hdNonnegative : 0 ≤ d := by
    have hnonnegative := defectOrder_nonneg
      (K := K)
      (a.lemma814Epsilon b * a.adjacentProduct (1 : Fin 2))
    rw [hzDefect] at hnonnegative
    exact_mod_cast hnonnegative
  rw [← hd] at hsumTop
  have htwoE :
      (2 : WithTop ℚ) *
          ((ramificationIndex K : ℚ) : WithTop ℚ) =
        ((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) := by
    norm_num
  rw [htwoE] at hsumTop
  have hsumRat :
      a.alphaValue (1 : Fin 2) + d ≤
        2 * (ramificationIndex K : ℚ) := by
    exact_mod_cast hsumTop
  have hdLt : d < 2 * (ramificationIndex K : ℚ) := by
    linarith
  rcases exists_complementaryDefect_hilbert_neg_of_nonnegative
      (K := K)
      (a.lemma814Epsilon b * a.adjacentProduct (1 : Fin 2))
      d hzDefect hdNonnegative hdLt with
    ⟨η, hηUnit, hηDefect, hηHilbert⟩
  have hηDefectBound :
      (a.alphaValue (1 : Fin 2) : WithTop ℚ) ≤
        defectOrder (K := K) η := by
    rw [hηDefect]
    exact_mod_cast (show a.alphaValue (1 : Fin 2) ≤
        2 * (ramificationIndex K : ℚ) - d by linarith)
  have hadjacent :=
    a.lemma814Ternary_adjacentHilbert_eq_of_neg
      b η hεHilbert hηHilbert
  exact a.beli2019Lemma814_ternaryUnequal_of_eta
    b horder conditions houter η hηUnit hηDefectBound hadjacent

/-- Complete rank-three sufficiency after reduction (I).  The Hilbert sign
selects the binary branch or one of the two outer-order ternary branches. -/
theorem beli2019Lemma814_rankThree_reduced
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [classification : GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [DyadicDiagonalClassificationLaws K]
    (a : GoodBONG q L 3) (b : GoodBONG r M 1)
    (horder : a.order (0 : Fin 3) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hbinary : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin 2) : WithTop ℚ))
    (hnotExceptional : ¬a.Beli2019Lemma814Exceptional b) :
    Nonempty (a.Beli2019PrescribedFirstValueTransform b) := by
  rcases Int.units_eq_one_or
      (hilbertSymbol K (a.lemma814Epsilon b)
        (a.adjacentProduct (0 : Fin 2))) with hhilbert | hhilbert
  · exact a.beli2019Lemma814_binaryBranch
      b horder conditions hbinary hhilbert
  · rcases a.lemma814_outerCases_of_hilbert_neg_one
        b conditions hhilbert with houter | hbound
    · exact a.beli2019Lemma814_ternaryEqual
        b horder conditions houter hnotExceptional
    · exact a.beli2019Lemma814_ternaryUnequal
        b horder conditions hbound hhilbert

/-- Complete noncircular rank-three sufficiency for Lemma 8.14.  Corollary
8.10 first supplies reduction (I); the reduced theorem then constructs the
prescribed first value in the original lattice. -/
theorem beli2019Lemma814_rankThree
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
    [Beli2019Lemma310RepresentationLaws.{u, v, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicDiagonalClassificationLaws K]
    (a : GoodBONG q L 3) (b : GoodBONG r M 1)
    (horder : a.order (0 : Fin 3) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hnotExceptional : ¬a.Beli2019Lemma814Exceptional b) :
    Nonempty (a.Beli2019PrescribedFirstValueTransform b) := by
  rcases a.exists_lemma814FirstNormalForm
      (N := 0)
      (classificationV := classificationV)
      (classificationW := classificationW)
      (prefixChangeV := prefixChangeV)
      (prefixChangeW := prefixChangeW)
      b horder conditions hnotExceptional with ⟨D⟩
  rcases D.transformed.beli2019Lemma814_rankThree_reduced
      (classification := classificationV)
      b D.firstOrder_eq D.conditions D.firstBinaryAlpha_eq
      D.notExceptional with ⟨T⟩
  exact ⟨{
    transformed := T.transformed
    firstValue_eq := T.firstValue_eq
  }⟩

/-- Lemma 8.14 in ternary rank, in its noncircular explicit form. -/
theorem beli2019Lemma814Explicit_rankThree
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
    [Beli2019Lemma310RepresentationLaws.{u, v, w} K]
    [prefixChangeV : Beli2006PrefixChangeLaws.{u, v} K]
    [prefixChangeW : Beli2006PrefixChangeLaws.{u, w} K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    [DyadicQuaternaryComplementLaws K]
    [DyadicDiagonalClassificationLaws K]
    (a : GoodBONG q L 3) (b : GoodBONG r M 1) :
    a.Beli2019Lemma814ExplicitStatement b := by
  intro horder conditions
  constructor
  · exact a.beli2019Lemma814_necessity
      (classificationV := classificationV)
      (classificationW := classificationW)
      (prefixChangeV := prefixChangeV)
      (prefixChangeW := prefixChangeW) b
  · intro hnotExceptional
    exact a.beli2019Lemma814_rankThree
      (classificationV := classificationV)
      (classificationW := classificationW)
      (prefixChangeV := prefixChangeV)
      (prefixChangeW := prefixChangeW)
      b horder conditions hnotExceptional

/-- After reduction (I), the converse proof is reduced to the two
rank-stratified outer-order branches.  The Hilbert-positive case is already
the generalized binary scaling theorem; Hilbert negativity and Lemma 8.13
produce precisely `R₁ < R₃` or `R₁ = R₃`. -/
theorem beli2019Lemma814_of_outerBranches
    [QuadraticDefectLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    (a : GoodBONG q L (N + 3)) (b : GoodBONG r M 1)
    (horder : a.order (0 : Fin (N + 3)) = b.order (0 : Fin 1))
    (conditions : a.Lemma813Conditions b)
    (hbinary : a.firstBinaryAlpha =
      (a.alphaValue (0 : Fin (N + 2)) : WithTop ℚ))
    (hnotExceptional : ¬a.Beli2019Lemma814Exceptional b)
    (unequalBranch : ¬a.Beli2019Lemma814Exceptional b →
      a.Lemma814UnequalOuterBound b →
        Nonempty (a.Beli2019PrescribedFirstValueTransform b))
    (equalBranch : ¬a.Beli2019Lemma814Exceptional b →
      a.order (0 : Fin (N + 3)) = a.order (2 : Fin (N + 3)) →
        Nonempty (a.Beli2019PrescribedFirstValueTransform b)) :
    Nonempty (a.Beli2019PrescribedFirstValueTransform b) := by
  rcases Int.units_eq_one_or
      (hilbertSymbol K (a.lemma814Epsilon b)
        (a.adjacentProduct (0 : Fin (N + 2)))) with hhilbert | hhilbert
  · exact a.beli2019Lemma814_binaryBranch b horder conditions hbinary hhilbert
  · rcases a.lemma814_outerCases_of_hilbert_neg_one b conditions hhilbert with
      houter | hbound
    · exact equalBranch hnotExceptional houter
    · exact unequalBranch hnotExceptional hbound

end BONG.GoodBONG

end Bong
