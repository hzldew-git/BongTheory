/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma91OrderBranches

/-!
# Beli (2019), Lemma 9.1: the equal-second-order branch

The remaining long branch of Lemma 9.1 starts from `R₂ = S₂`.  Before the
three exceptional cases of Lemma 8.14 are excluded, the paper derives two
rigidity facts shared by all of them: `α₁ ≤ β₁`, and, when the full
first-three defect is capped by `β₁`, the equal-outer-order identities force
`A₂ = α₂` and `β₁ = α₁`.

This file proves those common facts directly from `RepresentationConditions`,
Lemma 8.12, and Remark 8.7.  No Lemma 9.1-specific local-law interface is
introduced.
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
  {L : Lattice K V} {M : Lattice K W} {N S : Nat}

/-- At the first boundary, condition 2.1(ii) and Lemma 8.12(i) put the
target alpha below the source alpha.  The last step is just the source cap
in the cross-lattice bracketed defect. -/
theorem firstAlpha_le_sourceFirstAlpha_of_representationConditions
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hRank : S + 1 ≤ N + 2)
    (hfirst : a.order (0 : Fin (N + 3)) =
      c.order (0 : Fin (S + 2)))
    (conditions : RepresentationConditions a c hRank) :
    a.alphaValue (0 : Fin (N + 2)) ≤
      c.alphaValue (0 : Fin (S + 1)) := by
  let first := firstRepresentationIndex (N + 1) (S + 1)
  have hcondition := conditions.defectCondition first
  rw [a.coe_representationAlphaValue c first,
    a.beli2019Lemma812_i c hfirst] at hcondition
  have hcap := a.truncatedPrefixDefect_le_rightCap c 1 1 1
  rw [c.prefixAlphaCap_of_internal (by omega) (by omega)] at hcap
  have hsourceIndex : (⟨1 - 1, by omega⟩ : Fin (S + 1)) =
      (0 : Fin (S + 1)) := by
    apply Fin.ext
    simp
  rw [hsourceIndex] at hcap
  exact WithTop.coe_le_coe.mp (hcondition.trans hcap)

/-- The full-source first-three defect is the unary defect capped by the
source first alpha.  This is the precise minimum identity used throughout
the last two cases of Lemma 9.1. -/
theorem fullFirstThirdDefect_eq_min_unary_sourceFirstAlpha
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2)) :
    a.truncatedPrefixDefect c (-1) 3 1 =
      min (a.lemma814FirstThirdCappedDefect c.firstUnarySegment)
        (c.alphaValue (0 : Fin (S + 1)) : WithTop ℚ) := by
  unfold lemma814FirstThirdCappedDefect truncatedPrefixDefect
  rw [c.firstUnarySegment_prefixProduct_one,
    c.firstUnarySegment.prefixAlphaCap_last,
    c.prefixAlphaCap_of_internal (by omega) (by omega), min_top_right]
  have hsourceIndex : (⟨1 - 1, by omega⟩ : Fin (S + 1)) =
      (0 : Fin (S + 1)) := by
    apply Fin.ext
    simp
  rw [hsourceIndex]
  simp only [min_assoc]

/-- Condition 2.1(ii) at the second boundary is capped by the target second
alpha. -/
theorem secondRepresentationAlpha_le_targetSecond_of_conditions
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hRank : S + 1 ≤ N + 2)
    (conditions : RepresentationConditions a c hRank) :
    a.representationAlpha c (secondRepresentationIndex N S) ≤
      (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) := by
  let second := secondRepresentationIndex N S
  have hcondition := conditions.defectCondition second
  rw [a.coe_representationAlphaValue c second] at hcondition
  have hcap := a.truncatedPrefixDefect_le_leftCap c 1 2 2
  rw [a.prefixAlphaCap_of_internal (by omega) (by omega)] at hcap
  have htargetIndex : (⟨2 - 1, by omega⟩ : Fin (N + 2)) =
      (1 : Fin (N + 2)) := by
    apply Fin.ext
    simp
  rw [htargetIndex] at hcap
  exact hcondition.trans hcap

/-- The common rigidity calculation at the start of the `R₂ = S₂` branch.

If `R₁ = R₃`, `R₂ = S₂`, and the full first-three defect is the source
first alpha, then condition 2.1(ii) squeezes the second representation alpha
between the target second alpha and its explicit Lemma 8.12 formula.  Remark
8.7 identifies the two endpoints, forcing both displayed equalities. -/
theorem secondRepresentationAlpha_eq_targetSecond_and_sourceFirst_eq_targetFirst
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hRank : S + 1 ≤ N + 2)
    (hfirst : a.order (0 : Fin (N + 3)) =
      c.order (0 : Fin (S + 2)))
    (houter : a.order (0 : Fin (N + 3)) =
      a.order (2 : Fin (N + 3)))
    (hsecond : a.order (1 : Fin (N + 3)) =
      c.order (1 : Fin (S + 2)))
    (conditions : RepresentationConditions a c hRank)
    (hfull : a.truncatedPrefixDefect c (-1) 3 1 =
      (c.alphaValue (0 : Fin (S + 1)) : WithTop ℚ)) :
    a.representationAlpha c (secondRepresentationIndex N S) =
        (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) ∧
      c.alphaValue (0 : Fin (S + 1)) =
        a.alphaValue (0 : Fin (N + 2)) := by
  let second := secondRepresentationIndex N S
  have hfirstAlpha :=
    a.firstAlpha_le_sourceFirstAlpha_of_representationConditions
      c hRank hfirst conditions
  have hsourceHalfGap :=
    c.alphaValue_le_halfGapValue (0 : Fin (S + 1))
  change c.alphaValue (0 : Fin (S + 1)) ≤
      (((c.order (1 : Fin (S + 2)) -
        c.order (0 : Fin (S + 2)) : Int) : ℚ) / 2 +
          (ramificationIndex K : ℚ)) at hsourceHalfGap
  have hprimaryLe : a.secondRepresentationPrimaryFormula c ≤
      a.secondRepresentationHalfGapFormula c := by
    unfold secondRepresentationPrimaryFormula
      secondRepresentationHalfGapFormula
    rw [hfull]
    apply WithTop.coe_le_coe.mpr
    rw [← houter, hfirst]
    push_cast at hsourceHalfGap ⊢
    linarith
  have hsecondDefect := conditions.defectCondition second
  rw [a.coe_representationAlphaValue c second] at hsecondDefect
  have htargetCap := a.truncatedPrefixDefect_le_leftCap c 1 2 2
  rw [a.prefixAlphaCap_of_internal (by omega) (by omega)] at htargetCap
  have htargetIndex : (⟨2 - 1, by omega⟩ : Fin (N + 2)) =
      (1 : Fin (N + 2)) := by
    apply Fin.ext
    simp
  rw [htargetIndex] at htargetCap
  have hrepresentationLe : a.representationAlpha c second ≤
      (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) :=
    hsecondDefect.trans htargetCap
  have hformula := a.beli2019Lemma812_ii c hfirst
  have hprimaryBound :
      (((a.order (2 : Fin (N + 3)) -
          c.order (1 : Fin (S + 2)) : Int) : ℚ) +
        c.alphaValue (0 : Fin (S + 1))) ≤
          a.alphaValue (1 : Fin (N + 2)) := by
    rw [show second = secondRepresentationIndex N S by rfl,
      hformula, min_eq_right hprimaryLe] at hrepresentationLe
    unfold secondRepresentationPrimaryFormula at hrepresentationLe
    rw [hfull] at hrepresentationLe
    exact WithTop.coe_le_coe.mp (by simpa only [WithTop.coe_add] using
      hrepresentationLe)
  have hremark :=
    (a.beli2019Remark87 (0 : Fin (N + 1)) houter).currentAlpha_eq
  change a.alphaValue (1 : Fin (N + 2)) =
      (((a.order (0 : Fin (N + 3)) -
        a.order (1 : Fin (N + 3)) : Int) : ℚ) +
          a.alphaValue (0 : Fin (N + 2))) at hremark
  have hsourceLeTarget : c.alphaValue (0 : Fin (S + 1)) ≤
      a.alphaValue (0 : Fin (N + 2)) := by
    rw [← houter, ← hsecond] at hprimaryBound
    linarith
  have hfirstAlphaEq : c.alphaValue (0 : Fin (S + 1)) =
      a.alphaValue (0 : Fin (N + 2)) :=
    le_antisymm hsourceLeTarget hfirstAlpha
  refine ⟨?_, hfirstAlphaEq⟩
  rw [show secondRepresentationIndex N S = second by rfl,
    hformula, min_eq_right hprimaryLe]
  unfold secondRepresentationPrimaryFormula
  rw [hfull, hfirstAlphaEq, ← houter, ← hsecond]
  exact WithTop.coe_eq_coe.mpr hremark.symm

/-- In exceptions (b) and (c), the `R₂ = S₂` branch cannot select the
uncapped unary first-three defect.  Lemma 8.12(ii) would then make both
candidates defining `A₂` strictly larger than `α₂`, contradicting condition
2.1(ii).  Hence the full defect is exactly the source first alpha. -/
theorem fullFirstThirdDefect_eq_sourceFirstAlpha_of_exceptionBC
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hRank : S + 1 ≤ N + 2)
    (hfirst : a.order (0 : Fin (N + 3)) =
      c.order (0 : Fin (S + 2)))
    (hsecond : a.order (1 : Fin (N + 3)) =
      c.order (1 : Fin (S + 2)))
    (conditions : RepresentationConditions a c hRank)
    (E : a.Beli2019Lemma814ExceptionB c.firstUnarySegment ∨
      a.Beli2019Lemma814ExceptionC c.firstUnarySegment) :
    a.truncatedPrefixDefect c (-1) 3 1 =
      (c.alphaValue (0 : Fin (S + 1)) : WithTop ℚ) := by
  obtain ⟨houter, hsecondAlphaStrict, hdefectSum⟩ :
      a.order (0 : Fin (N + 3)) = a.order (2 : Fin (N + 3)) ∧
        a.alphaValue (1 : Fin (N + 2)) <
          a.halfGapValue (1 : Fin (N + 2)) ∧
        (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) +
            a.lemma814FirstThirdCappedDefect c.firstUnarySegment =
          ((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) := by
    rcases E with B | C
    · have R := a.beli2019Remark87 (0 : Fin (N + 1))
          B.firstThirdOrders_eq
      have hnotFirst : ¬a.AttainsHalfGap (0 : Fin (N + 2)) := by
        intro h
        exact (ne_of_lt B.firstAlpha_strict) h
      have hnotSecond : ¬a.AttainsHalfGap (1 : Fin (N + 2)) := by
        intro h
        exact hnotFirst (R.attainsHalfGap_iff.mpr h)
      have hstrict : a.alphaValue (1 : Fin (N + 2)) <
          a.halfGapValue (1 : Fin (N + 2)) := by
        apply lt_of_le_of_ne (a.alphaValue_le_halfGapValue 1)
        simpa only [AttainsHalfGap] using hnotSecond
      exact ⟨B.firstThirdOrders_eq, hstrict, B.defectSum_eq⟩
    · have hthree : 3 ≤ N + 2 := by
        have := C.rank_four
        omega
      have hsumQ :
          a.alphaValue (1 : Fin (N + 2)) +
              a.alphaValue (⟨2, hthree⟩ : Fin (N + 2)) =
            2 * (ramificationIndex K : ℚ) :=
        a.secondAlpha_add_thirdAlpha_eq_twoE_of_lemma814ExceptionC
          c.firstUnarySegment C hthree
      have hsumTop :
          (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) +
              a.lemma814FirstThirdCappedDefect c.firstUnarySegment =
            ((2 * (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ) := by
        rw [C.firstThirdDefect_eq_alpha]
        exact_mod_cast hsumQ
      exact ⟨C.firstThirdOrders_eq,
        a.secondAlpha_lt_halfGap_of_lemma814ExceptionC
          c.firstUnarySegment C,
        hsumTop⟩
  have hunaryFinite :
      a.lemma814FirstThirdCappedDefect c.firstUnarySegment ≠ ⊤ := by
    intro htop
    rw [htop, add_top] at hdefectSum
    exact WithTop.top_ne_coe hdefectSum
  let unaryDefect : ℚ :=
    (a.lemma814FirstThirdCappedDefect c.firstUnarySegment).untop
      hunaryFinite
  have hunaryCoe : (unaryDefect : WithTop ℚ) =
      a.lemma814FirstThirdCappedDefect c.firstUnarySegment := by
    exact WithTop.coe_untop _ _
  have hdefectSumQ : a.alphaValue (1 : Fin (N + 2)) + unaryDefect =
      2 * (ramificationIndex K : ℚ) := by
    apply WithTop.coe_eq_coe.mp
    rw [WithTop.coe_add, hunaryCoe]
    exact hdefectSum
  have hnotUnary : a.truncatedPrefixDefect c (-1) 3 1 ≠
      a.lemma814FirstThirdCappedDefect c.firstUnarySegment := by
    intro hfullUnary
    have hhalfStrict :
        (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) <
          a.secondRepresentationHalfGapFormula c := by
      unfold secondRepresentationHalfGapFormula
      rw [← hsecond]
      apply WithTop.coe_lt_coe.mpr
      unfold halfGapValue orderGap at hsecondAlphaStrict
      convert hsecondAlphaStrict using 1 <;> congr 1
    have hprimaryStrict :
        (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) <
          a.secondRepresentationPrimaryFormula c := by
      have hsecondAlphaStrict' := hsecondAlphaStrict
      unfold halfGapValue orderGap at hsecondAlphaStrict'
      change a.alphaValue (1 : Fin (N + 2)) <
        (((a.order (2 : Fin (N + 3)) -
          a.order (1 : Fin (N + 3)) : Int) : ℚ) / 2 +
            (ramificationIndex K : ℚ)) at hsecondAlphaStrict'
      have hprimaryQ : a.alphaValue (1 : Fin (N + 2)) <
          (((a.order (2 : Fin (N + 3)) -
            c.order (1 : Fin (S + 2)) : Int) : ℚ) + unaryDefect) := by
        rw [← hsecond]
        push_cast at hsecondAlphaStrict' ⊢
        linarith
      unfold secondRepresentationPrimaryFormula
      rw [hfullUnary, ← hunaryCoe]
      exact WithTop.coe_lt_coe.mpr hprimaryQ
    have hformula := a.beli2019Lemma812_ii c hfirst
    have hrepresentationStrict :
        (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) <
          a.representationAlpha c (secondRepresentationIndex N S) := by
      rw [hformula]
      exact lt_min hhalfStrict hprimaryStrict
    have hrepresentationLe :=
      a.secondRepresentationAlpha_le_targetSecond_of_conditions
        c hRank conditions
    exact (not_lt_of_ge hrepresentationLe) hrepresentationStrict
  have hminimum := a.fullFirstThirdDefect_eq_min_unary_sourceFirstAlpha c
  by_cases hle : a.lemma814FirstThirdCappedDefect c.firstUnarySegment ≤
      (c.alphaValue (0 : Fin (S + 1)) : WithTop ℚ)
  · have hfullUnary : a.truncatedPrefixDefect c (-1) 3 1 =
        a.lemma814FirstThirdCappedDefect c.firstUnarySegment := by
      rw [hminimum, min_eq_left hle]
    exact (hnotUnary hfullUnary).elim
  · rw [hminimum, min_eq_right (le_of_not_ge hle)]

/-- Exceptions (b) and (c) therefore enter the rigid source-cap subcase of
the equal-second-order proof. -/
theorem secondOrderRigidity_of_exceptionBC
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hRank : S + 1 ≤ N + 2)
    (hfirst : a.order (0 : Fin (N + 3)) =
      c.order (0 : Fin (S + 2)))
    (hsecond : a.order (1 : Fin (N + 3)) =
      c.order (1 : Fin (S + 2)))
    (conditions : RepresentationConditions a c hRank)
    (E : a.Beli2019Lemma814ExceptionB c.firstUnarySegment ∨
      a.Beli2019Lemma814ExceptionC c.firstUnarySegment) :
    a.representationAlpha c (secondRepresentationIndex N S) =
        (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) ∧
      c.alphaValue (0 : Fin (S + 1)) =
        a.alphaValue (0 : Fin (N + 2)) := by
  have hfull :=
    a.fullFirstThirdDefect_eq_sourceFirstAlpha_of_exceptionBC
      c hRank hfirst hsecond conditions E
  have houter : a.order (0 : Fin (N + 3)) =
      a.order (2 : Fin (N + 3)) := by
    rcases E with B | C
    · exact B.firstThirdOrders_eq
    · exact C.firstThirdOrders_eq
  exact
    a.secondRepresentationAlpha_eq_targetSecond_and_sourceFirst_eq_targetFirst
      c hRank hfirst houter hsecond conditions hfull

/-- The Hilbert-symbol calculation used in the exception-(a) contradiction.
The first source adjacent defect is bounded below by `α₂`, while the second
factor is bounded below by the unary first-three defect.  Exception (a)
makes their sum strictly larger than `2e`. -/
theorem sourceFirstAdjacent_firstThirdProduct_hilbert_one_of_exceptionA
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hRank : S + 1 ≤ N + 2)
    (hfirst : a.order (0 : Fin (N + 3)) =
      c.order (0 : Fin (S + 2)))
    (hsecond : a.order (1 : Fin (N + 3)) =
      c.order (1 : Fin (S + 2)))
    (conditions : RepresentationConditions a c hRank)
    (A : a.Beli2019Lemma814ExceptionA c.firstUnarySegment) :
    hilbertSymbol K (c.adjacentProduct (0 : Fin (S + 1)))
        ((-1 : Kˣ) * a.prefixProduct 3 * c.prefixProduct 1) = 1 := by
  have hfirstAlpha :=
    by
      letI : Beli2006AlphaLaws.{u, v} K := targetLaws
      exact a.firstAlpha_le_sourceFirstAlpha_of_representationConditions
        c hRank hfirst conditions
  have hremark :=
    by
      letI : Beli2006AlphaLaws.{u, v} K := targetLaws
      exact (a.beli2019Remark87 (0 : Fin (N + 1))
        A.firstThirdOrders_eq).currentAlpha_eq
  change a.alphaValue (1 : Fin (N + 2)) =
      (((a.order (0 : Fin (N + 3)) -
        a.order (1 : Fin (N + 3)) : Int) : ℚ) +
          a.alphaValue (0 : Fin (N + 2))) at hremark
  have htargetSecondQ : a.alphaValue (1 : Fin (N + 2)) ≤
      (((c.order (0 : Fin (S + 2)) -
        c.order (1 : Fin (S + 2)) : Int) : ℚ) +
          c.alphaValue (0 : Fin (S + 1))) := by
    rw [hfirst, hsecond] at hremark
    linarith
  have htargetSecondTop :
      (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) ≤
        (((((c.order (0 : Fin (S + 2)) -
          c.order (1 : Fin (S + 2)) : Int) : ℚ) +
            c.alphaValue (0 : Fin (S + 1)) : ℚ)) : WithTop ℚ) := by
    exact_mod_cast htargetSecondQ
  have hsourceCapped :=
    by
      letI : Beli2006AlphaLaws.{u, w} K := sourceLaws
      exact c.order_sub_add_alpha_le_cappedAdjacent (0 : Fin (S + 1))
  have hsourceRaw :=
    c.truncatedPrefixDefect_le_defect c (-1) 0 2
  have hsourceRawEq :
      defectOrder (K := K)
          ((-1 : Kˣ) * c.prefixProduct 0 * c.prefixProduct 2) =
        c.adjacentDefect (0 : Fin (S + 1)) := by
    simpa using c.defectOrder_prefixPair_eq_adjacentDefect
      (0 : Fin (S + 1))
  rw [hsourceRawEq] at hsourceRaw
  have hfirstDefect :
      (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) ≤
        defectOrder (K := K) (c.adjacentProduct (0 : Fin (S + 1))) := by
    unfold adjacentDefect at hsourceRaw
    exact htargetSecondTop.trans (hsourceCapped.trans hsourceRaw)
  have hsecondDefect :=
    a.truncatedPrefixDefect_le_defect c.firstUnarySegment (-1) 3 1
  change a.lemma814FirstThirdCappedDefect c.firstUnarySegment ≤
    defectOrder (K := K)
      ((-1 : Kˣ) * a.prefixProduct 3 *
        c.firstUnarySegment.prefixProduct 1) at hsecondDefect
  rw [c.firstUnarySegment_prefixProduct_one] at hsecondDefect
  have hstrict :
      ((((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ)) <
        defectOrder (K := K) (c.adjacentProduct (0 : Fin (S + 1))) +
          defectOrder (K := K)
            ((-1 : Kˣ) * a.prefixProduct 3 * c.prefixProduct 1) := by
    have hpaper :
        ((((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ)) <
          (a.alphaValue (1 : Fin (N + 2)) : WithTop ℚ) +
            a.lemma814FirstThirdCappedDefect c.firstUnarySegment := by
      exact_mod_cast A.defectSum_strict
    exact hpaper.trans_le (add_le_add hfirstDefect hsecondDefect)
  exact hilbertSymbol_eq_one_of_defectOrder_add_gt_two_mul_e hstrict

set_option maxHeartbeats 800000 in
-- Determinant completion introduces a dependent ternary coefficient and the
-- proof then normalizes its two adjacent Hilbert-symbol arguments.
/-- Once the initial source binary prefix is represented by the target
ternary prefix, exception (a) is impossible in the `R₂ = S₂` branch. -/
theorem not_lemma814ExceptionA_of_binaryPrefixRepresentation
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    [DiagonalCodimensionOneCancellationLaws K]
    (a : GoodBONG q L (N + 3)) (c : GoodBONG r M (S + 2))
    (hRank : S + 1 ≤ N + 2)
    (hfirst : a.order (0 : Fin (N + 3)) =
      c.order (0 : Fin (S + 2)))
    (hsecond : a.order (1 : Fin (N + 3)) =
      c.order (1 : Fin (S + 2)))
    (conditions : RepresentationConditions a c hRank)
    (hbinary : DiagonalRepresents
      (c.prefixValues 2 (by omega))
      (a.prefixValues 3 (by omega))) :
    ¬a.Beli2019Lemma814ExceptionA c.firstUnarySegment := by
  intro A
  let base := a.prefixValueUnits 3 (by omega)
  let head := c.prefixValueUnits 2 (by omega)
  let d := diagonalUnitDeterminant base * diagonalUnitDeterminant head
  let candidate : Fin 3 → Kˣ := Fin.snoc head d
  have hheadRep : DiagonalRepresents
      (diagonalUnitCoefficients head)
      (diagonalUnitCoefficients base) := by
    simpa only [head, base,
      c.diagonalUnitCoefficients_prefixValueUnits,
      a.diagonalUnitCoefficients_prefixValueUnits] using hbinary
  have hcandidateRep : DiagonalRepresents
      (diagonalUnitCoefficients candidate)
      (diagonalUnitCoefficients base) := by
    simpa only [candidate, d] using
      determinantCompletion_represents_base base head hheadRep
  have hcandidateZero : candidate (0 : Fin 3) = head (0 : Fin 2) := by
    simp [candidate]
  have hcandidateOne : candidate (1 : Fin 3) = head (1 : Fin 2) := by
    change (Fin.snoc head d : Fin 3 → Kˣ) 1 = head 1
    rw [show (1 : Fin 3) = (1 : Fin 2).castSucc by rfl,
      Fin.snoc_castSucc]
  have hcandidateTwo : candidate (2 : Fin 3) = d := by
    change (Fin.snoc head d : Fin 3 → Kˣ) 2 = d
    rw [show (2 : Fin 3) = Fin.last 2 by rfl, Fin.snoc_last]
  have hheadOne : head (1 : Fin 2) =
      c.valueUnit (1 : Fin (S + 2)) := by
    rfl
  have hfirstArgument : -(candidate 0 * candidate 1) =
      c.adjacentProduct (0 : Fin (S + 1)) := by
    rw [hcandidateZero, hcandidateOne]
    simp [head, prefixValueUnits, adjacentProduct]
  have hsecondArgument : -(candidate 1 * candidate 2) =
      ((-1 : Kˣ) * a.prefixProduct 3 * c.prefixProduct 1) *
        (c.valueUnit (1 : Fin (S + 2))) ^ 2 := by
    rw [hcandidateOne, hcandidateTwo, hheadOne]
    dsimp only [d]
    rw [a.diagonalUnitDeterminant_prefixValueUnits 3 (by omega),
      c.diagonalUnitDeterminant_prefixValueUnits 2 (by omega)]
    have hprefix := c.toBONG.prefixProduct_succ 1 (by omega)
    change c.prefixProduct 2 = c.prefixProduct 1 *
      c.valueUnit (1 : Fin (S + 2)) at hprefix
    rw [hprefix]
    apply Units.ext
    simp only [Units.val_neg, Units.val_mul, Units.val_one, pow_two]
    ring
  have hhilbert :=
    a.sourceFirstAdjacent_firstThirdProduct_hilbert_one_of_exceptionA
      (targetLaws := targetLaws) (sourceLaws := sourceLaws)
      c hRank hfirst hsecond conditions A
  have hcandidateHilbert :
      hilbertSymbol K (-(candidate 0 * candidate 1))
          (-(candidate 1 * candidate 2)) = 1 := by
    rw [hfirstArgument, hsecondArgument, hilbertSymbol_mul_square_right]
    exact hhilbert
  have hcandidateIsotropic :
      DiagonalIsotropic (diagonalUnitCoefficients candidate) :=
    (diagonalUnitTernary_isotropic_iff_adjacentHilbertOne candidate).mpr
      hcandidateHilbert
  have hbaseIsotropic : a.Lemma814FirstThreeIsotropic := by
    change DiagonalIsotropic (diagonalUnitCoefficients base)
    exact hcandidateRep.isotropic_of hcandidateIsotropic
  exact a.not_firstThreeIsotropic_of_anisotropic
    A.firstThree_anisotropic hbaseIsotropic

end BONG.GoodBONG

end Bong
