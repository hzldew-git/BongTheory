/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliUniversalCentral
import Bong.Bong.DiagonalTernaryRepresentationObstructionProof

/-!
# The long unary condition in Beli's universal-lattice theorem

This file formalizes Beli's Lemma 2.14.  For a unary target, condition
`(iv)` has one possible index, and only when the source has rank at least
four.  Its exceptional branch is the square class
`-a₁a₂a₃ F^{×2}`; on that branch representation is equivalent to isotropy
of the first ternary prefix.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG.GoodBONG

/-- A nonzero value represented by a diagonal polynomial gives the
corresponding unary diagonal representation. -/
theorem diagonalUnaryRepresents_of_exists_value_general {n : Nat}
    (c : Fin n → K) (b : Kˣ)
    (hvalue : ∃ x : Fin n → K, diagonalQuadratic c x = (b : K)) :
    DiagonalRepresents (fun _ : Fin 1 ↦ (b : K)) c := by
  classical
  rcases hvalue with ⟨x, hxvalue⟩
  have hx : x ≠ 0 := by
    intro hzero
    rw [hzero] at hxvalue
    have hbzero : (b : K) = 0 := by
      simpa [diagonalQuadratic] using hxvalue.symm
    exact Units.ne_zero b hbzero
  obtain ⟨j, hxj⟩ : ∃ j : Fin n, x j ≠ 0 := by
    by_contra hnot
    push Not at hnot
    apply hx
    funext j
    exact hnot j
  let f : (Fin 1 → K) →ₗ[K] (Fin n → K) :=
    { toFun := fun y i ↦ y 0 * x i
      map_add' := by
        intro y z
        funext i
        simp only [Pi.add_apply]
        ring
      map_smul' := by
        intro s y
        funext i
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ac_rfl }
  refine ⟨f, ?_, ?_⟩
  · intro y z hyz
    apply funext
    intro i
    fin_cases i
    have hj := congrFun hyz j
    change y 0 * x j = z 0 * x j at hj
    exact mul_right_cancel₀ hxj hj
  · intro y
    change diagonalQuadratic c (fun i ↦ y 0 * x i) =
      diagonalQuadratic (fun _ : Fin 1 ↦ (b : K)) y
    calc
      diagonalQuadratic c (fun i ↦ y 0 * x i) =
          y 0 ^ 2 * diagonalQuadratic c x := by
            unfold diagonalQuadratic
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _hi
            ring
      _ = y 0 ^ 2 * (b : K) := by rw [hxvalue]
      _ = diagonalQuadratic (fun _ : Fin 1 ↦ (b : K)) y := by
        simp [diagonalQuadratic]
        ring

/-- Condition `(iv)` for every unary target of order zero or one. -/
def UniversalAllUnaryLongConditions {tail : Nat}
    (a : GoodBONG q L (tail + 2)) : Prop :=
  ∀ b : Kˣ, ordUnit K b = 0 ∨ ordUnit K b = 1 →
    a.LongRepresentationConditions (BONG.unaryModelGoodBONG b)

/-- The exact Case I(c) clause, separated from I(a) and I(b). -/
def UniversalLongCaseIConditions {tail : Nat}
    (a : GoodBONG q L (tail + 2)) : Prop :=
  ∀ hthree : 0 < tail,
    a.order ⟨2, by omega⟩ = 1 →
      (tail = 1 ∨ ∃ hfour : 1 < tail,
        2 * (ramificationIndex K : Int) + 1 < a.order ⟨3, by omega⟩) →
      a.UniversalFirstTwoIsotropic

/-- The exact Case II(c) clause, separated from II(a) and II(b). -/
def UniversalLongCaseIIConditions {tail : Nat}
    (a : GoodBONG q L (tail + 2)) : Prop :=
  ∀ hthree : 0 < tail,
    a.order ⟨1, by omega⟩ ≤ 0 →
    a.order ⟨2, by omega⟩ ≤ 1 →
    (tail = 1 ∨ ∃ hfour : 1 < tail,
      2 * (ramificationIndex K : Int) <
        a.order ⟨3, by omega⟩ - a.order ⟨2, by omega⟩) →
    a.UniversalFirstThreeIsotropic hthree

/-- At source rank at least four, the abstract long condition is the
literal implication displayed in Lemma 2.3. -/
theorem unary_longRepresentationConditions_iff_literal
    {m : Nat} (a : GoodBONG q L (m + 4)) (b : Kˣ) :
    a.LongRepresentationConditions (BONG.unaryModelGoodBONG b) ↔
      ((a.order 2 ≤ ordUnit K b ∧
          ordUnit K b + 2 * (ramificationIndex K : Int) < a.order 3) →
        DiagonalRepresents (fun _ : Fin 1 ↦ (b : K))
          (a.prefixValues 3 (by omega))) := by
  rw [a.unary_longRepresentationConditions_iff b]
  have htwo : a.order ⟨2, by omega⟩ = a.order 2 := by congr 1
  have hthree : a.order ⟨3, by omega⟩ = a.order 3 := by congr 1
  simp only [dif_neg (by omega : ¬ 2 ≤ 1), true_and,
    BONG.unaryModelGoodBONG_order, unary_prefixValues_one_eq,
    htwo, hthree]
  constructor
  · intro h htrigger
    apply h
    constructor
    · exact htrigger.2
    · omega
  · intro h htrigger
    apply h
    constructor
    · omega
    · exact htrigger.1

/-- A ternary prefix represents `b` precisely off its exceptional signed
determinant square class, or when the prefix is isotropic. -/
theorem firstThree_represents_iff_not_signedProductSquare_or_isotropic
    {tail : Nat} (a : GoodBONG q L (tail + 2)) (hthree : 0 < tail)
    (b : Kˣ) :
    DiagonalRepresents (fun _ : Fin 1 ↦ (b : K))
        (a.prefixValues 3 (by omega)) ↔
      ¬ IsSquare ((-1 : Kˣ) * a.prefixProduct 3 * b) ∨
        a.UniversalFirstThreeIsotropic hthree := by
  let head : Fin 3 → Kˣ := a.prefixValueUnits 3 (by omega)
  have hvalues : diagonalUnitCoefficients head =
      a.prefixValues 3 (by omega) :=
    a.diagonalUnitCoefficients_prefixValueUnits 3 (by omega)
  have hdet : diagonalUnitDeterminant head = a.prefixProduct 3 :=
    a.diagonalUnitDeterminant_prefixValueUnits 3 (by omega)
  constructor
  · intro hrep
    by_cases hsquare : IsSquare ((-1 : Kˣ) * a.prefixProduct 3 * b)
    · right
      change DiagonalIsotropic (a.prefixValues 3 (by omega))
      rw [← hvalues]
      apply
        DyadicTernaryRepresentationObstructionLaws.isotropic_of_represents_and_signedDeterminantSquare
          (K := K) head b
      · simpa only [hvalues] using hrep
      · simpa only [hdet] using hsquare
    · exact Or.inl hsquare
  · rintro (hnonsquare | hisotropic)
    · by_contra hnot
      have hobstruction :=
        DyadicTernaryRepresentationObstructionLaws.obstruction
          (K := K) head b (by simpa only [hvalues] using hnot)
      exact hnonsquare (by simpa only [hdet] using hobstruction.2)
    · have hisotropic' : DiagonalIsotropic
          (diagonalUnitCoefficients head) := by
        change DiagonalIsotropic (a.prefixValues 3 (by omega)) at hisotropic
        rwa [hvalues]
      have hvalue := diagonal_exists_value_of_isotropic
        (diagonalUnitCoefficients head) (fun i ↦ Units.ne_zero (head i))
          hisotropic' b
      simpa only [hvalues] using
        (diagonalUnaryRepresents_of_exists_value head b hvalue)

/-- A line-universal ternary ambient space is isotropic.  This is the
rank-three clause used to include the vacuous condition `(iv)` in the
uniform statement of Lemma 2.14. -/
theorem firstThreeIsotropic_of_isLineUniversal_rankThree
    (a : GoodBONG q L 3) (hline : q.IsLineUniversal) :
    a.UniversalFirstThreeIsotropic (by omega) := by
  let b : Kˣ := -(a.prefixProduct 3)
  have hambient : q.Represents
      (QuadraticSpace.rescaleUnit b (QuadraticSpace.line K)) := hline b
  have hdiagonal : DiagonalRepresents
      (BONG.unaryModelBONG b).value a.toBONG.value :=
    a.toBONG.diagonalRepresents_of_ambient (BONG.unaryModelBONG b) hambient
  have hrep : DiagonalRepresents (fun _ : Fin 1 ↦ (b : K))
      (a.prefixValues 3 (by omega)) := by
    convert hdiagonal using 1 <;> funext i
    · fin_cases i
      exact (BONG.unaryModelBONG_value b 0).symm
    · fin_cases i <;> rfl
  have hsquare : IsSquare
      ((-1 : Kˣ) * a.prefixProduct 3 * b) := by
    refine ⟨a.prefixProduct 3, ?_⟩
    simp [b]
  rcases (a.firstThree_represents_iff_not_signedProductSquare_or_isotropic
      (by omega) b).mp hrep with hnonsquare | hisotropic
  · exact False.elim (hnonsquare hsquare)
  · exact hisotropic

/-- Isotropy of the binary prefix propagates to the ternary prefix. -/
theorem firstThreeIsotropic_of_firstTwoIsotropic {tail : Nat}
    (a : GoodBONG q L (tail + 3))
    (hbinary : a.UniversalFirstTwoIsotropic) :
    a.UniversalFirstThreeIsotropic (by omega) := by
  have hrep : DiagonalRepresents
      (a.prefixValues 2 (by omega)) (a.prefixValues 3 (by omega)) := by
    unfold prefixValues
    exact DiagonalRepresents.prefixOfLE _ (by omega)
  exact hrep.isotropic_of hbinary

/-- At the endpoint `R₂=-2e`, if `R₃=1`, ternary isotropy forces
binary isotropy.  In the nonsplit endpoint class the binary form represents
exactly the even-order coefficients, whereas `-a₃` has odd order. -/
theorem firstTwoIsotropic_of_firstThreeIsotropic_at_endpoint_order_two_one
    {tail : Nat} (a : GoodBONG q L (tail + 3))
    (hzero : a.order 0 = 0)
    (hsecond : a.order 1 = -(2 * (ramificationIndex K : Int)))
    (hthird : a.order 2 = 1)
    (hternary : a.UniversalFirstThreeIsotropic (by omega)) :
    a.UniversalFirstTwoIsotropic := by
  rcases a.firstBinary_endpoint_signedProduct_cases (tail := tail + 1)
      hzero hsecond with hsquare | hdiscriminant
  · have hisotropic := diagonalBinary_isotropic_of_isSquare_neg_product
      (a.valueUnit 0) (a.valueUnit 1) hsquare
    change DiagonalIsotropic (a.prefixValues 2 (by omega))
    convert hisotropic using 1
    funext i
    fin_cases i <;> rfl
  · change DiagonalIsotropic (a.prefixValues 3 (by omega)) at hternary
    rcases hternary with ⟨x, hx, hxzero⟩
    by_cases hxlast : x 2 = 0
    · let y : Fin 2 → K := fun i ↦ x ⟨i.val, i.isLt.trans (by omega)⟩
      have hy : y ≠ 0 := by
        intro hyzero
        apply hx
        funext i
        fin_cases i
        · exact congrFun hyzero 0
        · exact congrFun hyzero 1
        · exact hxlast
      refine ⟨y, hy, ?_⟩
      have hxzero' := hxzero
      simp only [diagonalQuadratic, Fin.sum_univ_three,
        Fin.sum_univ_two] at hxzero' ⊢
      dsimp only [prefixValues, y] at hxzero' ⊢
      rw [hxlast] at hxzero'
      simpa using hxzero'
    · let y : Fin 2 → K := fun i ↦
          (x 2)⁻¹ * x ⟨i.val, i.isLt.trans (by omega)⟩
      have hyvalue : diagonalQuadratic (a.prefixValues 2 (by omega)) y =
          -(a.valueUnit 2 : K) := by
        have hindexTwo : (⟨2, by omega⟩ : Fin (tail + 3)) =
            (2 : Fin (tail + 3)) := by
          apply Fin.ext
          change 2 = 2 % (tail + 3)
          exact (Nat.mod_eq_of_lt (by omega)).symm
        have hcoeTwo : (a.valueUnit 2 : K) =
            a.toBONG.value (2 : Fin (tail + 3)) := by
          exact a.toBONG.coe_valueUnit (2 : Fin (tail + 3))
        rw [hcoeTwo]
        have hxzero' :
            a.toBONG.value 0 * x 0 ^ 2 +
              a.toBONG.value 1 * x 1 ^ 2 +
                a.toBONG.value 2 * x 2 ^ 2 = 0 := by
          simpa [diagonalQuadratic, Fin.sum_univ_three, prefixValues,
            GoodBONG.value, hindexTwo] using hxzero
        simp [diagonalQuadratic, Fin.sum_univ_two, prefixValues, y,
          GoodBONG.value, hindexTwo]
        field_simp
        linear_combination hxzero'
      have hrep : DiagonalRepresents
          (fun _ : Fin 1 ↦ (-(a.valueUnit 2 : K)))
          (a.prefixValues 2 (by omega)) :=
        diagonalUnaryRepresents_of_exists_value_general
          (a.prefixValues 2 (by omega)) (-a.valueUnit 2) ⟨y, hyvalue⟩
      have heven :=
        (a.firstTwo_represents_iff_even_of_discriminant_endpoint
          (tail := tail + 1) hzero hdiscriminant (-a.valueUnit 2)).mp hrep
      have hodd : Odd (ordUnit K (-a.valueUnit 2)) := by
        rw [ordUnit_neg]
        have horder : ordUnit K (a.valueUnit 2) = 1 := by
          calc
            ordUnit K (a.valueUnit 2) = a.order 2 := by
              simpa only [GoodBONG.order, GoodBONG.valueUnit] using
                (a.toBONG.order_eq_ordUnit (2 : Fin (tail + 3))).symm
            _ = 1 := hthird
        rw [horder]
        exact odd_one
      exact False.elim (Int.not_even_iff_odd.mpr hodd heven)

/-- The paper's condition `(*)` in rank at least four, stated for either
allowed unary order `S=0,1`. -/
def UniversalLongStarConditions {m : Nat}
    (a : GoodBONG q L (m + 4)) : Prop :=
  ∀ S : Int, S = 0 ∨ S = 1 →
    Even (S - (a.order 1 + a.order 2)) →
    a.order 2 ≤ S →
    S + 2 * (ramificationIndex K : Int) < a.order 3 →
    a.UniversalFirstThreeIsotropic (by omega)

/-- Membership in the exceptional signed ternary square class gives the
parity congruence `ord(b) ≡ R₂+R₃ (mod 2)`. -/
theorem signedTernarySquare_orderParity {tail : Nat}
    (a : GoodBONG q L (tail + 2)) (hthree : 0 < tail)
    (hzero : a.order 0 = 0) (b : Kˣ)
    (hsquare : IsSquare ((-1 : Kˣ) * a.prefixProduct 3 * b)) :
    Even (ordUnit K b - (a.order 1 + a.order 2)) := by
  rcases hsquare with ⟨s, hs⟩
  have hord := congrArg (ordUnit K) hs
  have hnegOne : ordUnit K (-1 : Kˣ) = 0 := by
    rw [ordUnit_neg]
    have hone := ordUnit_mul K (1 : Kˣ) 1
    simp only [mul_one] at hone
    omega
  rw [ordUnit_mul, ordUnit_mul, hnegOne,
    a.prefixProduct_three_order hthree, hzero, zero_add,
    ordUnit_mul] at hord
  refine ⟨ordUnit K s - (a.order 1 + a.order 2), ?_⟩
  omega

/-- In rank at least four, condition `(iv)` for all unary targets is
equivalent to the paper's condition `(*)`. -/
theorem universalAllUnaryLongConditions_iff_star
    {m : Nat} (a : GoodBONG q L (m + 4)) (hzero : a.order 0 = 0) :
    a.UniversalAllUnaryLongConditions ↔
      a.UniversalLongStarConditions := by
  constructor
  · intro hall S hSAllowed hSParity hthirdLe hfourth
    obtain ⟨b, hbOrder, hbSquare⟩ :=
      a.exists_order_in_negative_ternary_prefix_squareClass
        (by omega) hzero S hSParity
    have hlong := hall b (by simpa only [hbOrder] using hSAllowed)
    rw [a.unary_longRepresentationConditions_iff_literal b] at hlong
    have hrep := hlong ⟨by simpa only [hbOrder] using hthirdLe, by
      simpa only [hbOrder] using hfourth⟩
    rcases (a.firstThree_represents_iff_not_signedProductSquare_or_isotropic
        (by omega) b).mp hrep with hnonsquare | hisotropic
    · exact False.elim (hnonsquare hbSquare)
    · exact hisotropic
  · intro hstar b hb
    rw [a.unary_longRepresentationConditions_iff_literal b]
    intro htrigger
    apply (a.firstThree_represents_iff_not_signedProductSquare_or_isotropic
      (by omega) b).2
    by_cases hsquare : IsSquare ((-1 : Kˣ) * a.prefixProduct 3 * b)
    · right
      apply hstar (ordUnit K b) hb
      · exact a.signedTernarySquare_orderParity (by omega) hzero b hsquare
      · exact htrigger.1
      · exact htrigger.2
    · exact Or.inl hsquare

/-- Below rank four there is no long representation index. -/
theorem universalAllUnaryLongConditions_of_tail_le_one {tail : Nat}
    (a : GoodBONG q L (tail + 2)) (htail : tail ≤ 1) :
    a.UniversalAllUnaryLongConditions := by
  intro b _hb
  unfold LongRepresentationConditions
  intro i
  have hone := i.one_lt
  have hlarge := i.succ_lt_large
  omega

/-- Beli, Lemma 2.14 in Case I: under ambient universality and I(a), the
unary long conditions are equivalent to I(c). -/
theorem universalAllUnaryLongConditions_iff_caseI
    {tail : Nat} (a : GoodBONG q L (tail + 2))
    (hline : q.IsLineUniversal) (hzero : a.order 0 = 0)
    (halpha : a.alphaValue (0 : Fin (tail + 1)) = 0) :
    a.UniversalAllUnaryLongConditions ↔
      a.UniversalLongCaseIConditions := by
  by_cases hlow : tail ≤ 1
  · constructor
    · intro _hall hthree hthird _hbranch
      have htail : tail = 1 := by omega
      subst tail
      have hternary :=
        a.firstThreeIsotropic_of_isLineUniversal_rankThree hline
      have hsecond :=
        a.order_one_eq_neg_two_e_of_alphaValue_zero hzero halpha
      exact
        a.firstTwoIsotropic_of_firstThreeIsotropic_at_endpoint_order_two_one
          hzero hsecond hthird hternary
    · intro _hcase
      exact a.universalAllUnaryLongConditions_of_tail_le_one hlow
  · have htwo : 2 ≤ tail := by omega
    obtain ⟨m, rfl⟩ : ∃ m : Nat, tail = m + 2 :=
      ⟨tail - 2, by omega⟩
    rw [a.universalAllUnaryLongConditions_iff_star hzero]
    have hsecond :=
      a.order_one_eq_neg_two_e_of_alphaValue_zero hzero halpha
    constructor
    · intro hstar hthree hthird hbranch
      rcases hbranch with hrankThree | ⟨hfour, hfourth⟩
      · omega
      · have horderThree : a.order ⟨2, by omega⟩ = a.order 2 := by
          congr 1
        have hthird' : a.order 2 = 1 := by
          rw [horderThree] at hthird
          exact hthird
        have hparity : Even
            ((1 : Int) - (a.order 1 + a.order 2)) := by
          refine ⟨(ramificationIndex K : Int), ?_⟩
          rw [hsecond, hthird']
          omega
        have hternary := hstar 1 (Or.inr rfl) hparity (by omega) (by
          have horderFour : a.order ⟨3, by omega⟩ = a.order 3 := by
            congr 1
          rw [horderFour] at hfourth
          omega)
        exact
          a.firstTwoIsotropic_of_firstThreeIsotropic_at_endpoint_order_two_one
            hzero hsecond hthird' hternary
    · intro hcase S hSAllowed hSParity hthirdLe hfourth
      have hthirdNonnegative : 0 ≤ a.order 2 :=
        a.order_two_nonnegative_of_order_zero_eq_zero hzero
      have hthirdCases : a.order 2 = 0 ∨ a.order 2 = 1 := by
        rcases hSAllowed with hSZero | hSOne <;> omega
      rcases hthirdCases with hthirdZero | hthirdOne
      · exact a.firstThree_isotropic_of_endpoint_order_two_zero
          hzero hsecond hthirdZero
      · have hSOne : S = 1 := by
          rcases hSAllowed with hSZero | hSOne <;> omega
        have horderFour : a.order ⟨3, by omega⟩ = a.order 3 := by
          congr 1
        have hbinary := hcase (by omega) hthirdOne (Or.inr ⟨by omega, by
          rw [horderFour]
          rw [hSOne] at hfourth
          omega⟩)
        exact a.firstThreeIsotropic_of_firstTwoIsotropic hbinary

/-- Beli, Lemma 2.14 in Case II': under ambient universality and II(a'),
the unary long conditions are equivalent to II(c). -/
theorem universalAllUnaryLongConditions_iff_caseII
    {tail : Nat} (a : GoodBONG q L (tail + 2))
    (hline : q.IsLineUniversal) (hzero : a.order 0 = 0)
    (hcase : a.UniversalCaseIIPrime) :
    a.UniversalAllUnaryLongConditions ↔
      a.UniversalLongCaseIIConditions := by
  have hpositive : 0 < tail := hcase.1
  by_cases hrankThree : tail = 1
  · subst tail
    constructor
    · intro _hall _hthree _hsecond _hthird _hbranch
      exact a.firstThreeIsotropic_of_isLineUniversal_rankThree hline
    · intro _hcase
      exact a.universalAllUnaryLongConditions_of_tail_le_one (by omega)
  · have htwo : 2 ≤ tail := by omega
    obtain ⟨m, rfl⟩ : ∃ m : Nat, tail = m + 2 :=
      ⟨tail - 2, by omega⟩
    rw [a.universalAllUnaryLongConditions_iff_star hzero]
    have hgapZero : a.orderGap (0 : Fin (m + 3)) = a.order 1 := by
      unfold orderGap
      simpa [hzero]
    have hsecondCases : a.order 1 = 1 ∨
        (Even (a.order 1) ∧
          2 - 2 * (ramificationIndex K : Int) ≤ a.order 1 ∧
          a.order 1 ≤ 0) := by
      have hcases :=
        (a.alphaValue_eq_one_consequences (0 : Fin (m + 3))
          hcase.2.1).2.1
      rwa [hgapZero] at hcases
    constructor
    · intro hstar hthree hsecond hthird hbranch
      rcases hbranch with htailOne | ⟨hfour, hfourth⟩
      · omega
      · have horderSecond : a.order ⟨1, by omega⟩ = a.order 1 := by
          congr 1
        have horderThird : a.order ⟨2, by omega⟩ = a.order 2 := by
          congr 1
        rw [horderSecond] at hsecond
        rw [horderThird] at hthird
        have hsecondEven : Even (a.order 1) := by
          rcases hsecondCases with hsecondOne | hsecondEven
          · omega
          · exact hsecondEven.1
        have hthirdNonnegative : 0 ≤ a.order 2 :=
          a.order_two_nonnegative_of_order_zero_eq_zero hzero
        have hthirdCases : a.order 2 = 0 ∨ a.order 2 = 1 := by
          omega
        have hthirdAllowed : a.order 2 = 0 ∨ a.order 2 = 1 :=
          hthirdCases
        have hparity : Even
            (a.order 2 - (a.order 1 + a.order 2)) := by
          rcases hsecondEven with ⟨k, hk⟩
          refine ⟨-k, ?_⟩
          omega
        apply hstar (a.order 2) hthirdAllowed hparity le_rfl
        have horderThree : a.order ⟨2, by omega⟩ = a.order 2 := by
          congr 1
        have horderFour : a.order ⟨3, by omega⟩ = a.order 3 := by
          congr 1
        rw [horderThree, horderFour] at hfourth
        omega
    · intro hboundary S hSAllowed hSParity hthirdLe hfourth
      have hthirdNonnegative : 0 ≤ a.order 2 :=
        a.order_two_nonnegative_of_order_zero_eq_zero hzero
      have hthirdUpper : a.order 2 ≤ 1 := by
        rcases hSAllowed with hSZero | hSOne <;> omega
      have hsecondNonpositive : a.order 1 ≤ 0 := by
        rcases hsecondCases with hsecondOne | hsecondEven
        · have hthirdLower :=
            a.one_le_order_two_of_order_zero_eq_zero_order_one_eq_one
              hzero hsecondOne
          have hthirdOne : a.order 2 = 1 := by omega
          have hSOne : S = 1 := by
            rcases hSAllowed with hSZero | hSOne <;> omega
          rcases hSParity with ⟨k, hk⟩
          rw [hsecondOne, hthirdOne, hSOne] at hk
          omega
        · exact hsecondEven.2.2
      have hsecondEven : Even (a.order 1) := by
        rcases hsecondCases with hsecondOne | hsecondEven
        · omega
        · exact hsecondEven.1
      have hS_eq_third : S = a.order 2 := by
        rcases hsecondEven with ⟨k, hk⟩
        rcases hSParity with ⟨l, hl⟩
        rcases hSAllowed with hSZero | hSOne <;> omega
      apply hboundary (by omega) hsecondNonpositive hthirdUpper
      right
      refine ⟨by omega, ?_⟩
      have horderThree : a.order ⟨2, by omega⟩ = a.order 2 := by
        congr 1
      have horderFour : a.order ⟨3, by omega⟩ = a.order 3 := by
        congr 1
      rw [horderThree, horderFour]
      rw [hS_eq_third] at hfourth
      omega

end BONG.GoodBONG

end Bong
