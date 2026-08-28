/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019CanonicalApproximation
import Bong.Bong.Beli2019Lemma812

/-!
# Beli (2019), Lemma 8.13

This file rewrites the four conditions of Theorem 2.1 for a unary source.
The target has rank `m + 2`; consequently the paper's exceptional target
ranks two and three are the cases `m = 0` and `m = 1`.

The main normalization theorem does not invoke Theorem 2.1.  It proves an
equivalence with `RepresentationConditions`, so it can be used inside the
later proof of the main theorem without circularity.  A final wrapper accepts
the main-theorem equivalence as an explicit argument and recovers the literal
lattice-representation statement of Lemma 8.13.
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {targetRank sourceRank : Nat}

/-- An ambient quadratic-space representation, written in the coordinates
of arbitrary BONG bases, is a representation of the associated diagonal
forms. -/
theorem diagonalRepresents_of_ambient
    (a : BONG V q L targetRank) (b : BONG W r M sourceRank)
    (ambient : q.Represents r) :
    DiagonalRepresents b.value a.value := by
  rcases ambient with ⟨f⟩
  let coordinateMap : (Fin sourceRank → K) →ₗ[K] (Fin targetRank → K) :=
    a.basis.equivFun.toLinearMap.comp
      (f.toLinearMap.comp b.basis.equivFun.symm.toLinearMap)
  refine ⟨coordinateMap, ?_, ?_⟩
  · exact a.basis.equivFun.injective.comp
      (f.injective.comp b.basis.equivFun.symm.injective)
  · intro x
    change diagonalQuadratic a.value
        (a.basis.equivFun (f.toLinearMap (b.basis.equivFun.symm x))) =
      diagonalQuadratic b.value x
    rw [a.diagonalQuadratic_value_eq, b.diagonalQuadratic_value_eq]
    simpa using f.map_quadratic (b.basis.equivFun.symm x)

end BONG

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {m : Nat}

/-- The ambient representation expressed by the complete good-BONG
coordinate systems. -/
theorem fullPrefix_represents_of_ambient
    (a : GoodBONG q L (m + 2)) (b : GoodBONG r M 1)
    (ambient : q.Represents r) :
    DiagonalRepresents
      (b.prefixValues 1 (Nat.le_refl _))
      (a.prefixValues (m + 2) (Nat.le_refl _)) := by
  convert a.toBONG.diagonalRepresents_of_ambient b.toBONG ambient using 1 <;>
    funext i <;> rfl

/-- The normalized trigger from condition (iii) when the unary source is
compared with a target of rank at least three.  Its second inequality is the
paper's
`alpha_1 + d[-a_(1,3)b_1] > 2e + R_2 - R_3`, with `R_3` moved to the
right-hand sum. -/
noncomputable def lemma813CentralTrigger
    (a : GoodBONG q L (m + 2)) (b : GoodBONG r M 1) (hm : 0 < m) : Prop :=
  a.order (0 : Fin (m + 2)) < a.order ⟨2, by omega⟩ ∧
    (((2 * (ramificationIndex K : ℚ) +
        (a.order (1 : Fin (m + 2)) : ℚ) : ℚ) : WithTop ℚ) <
      (a.alphaValue (0 : Fin (m + 1)) : WithTop ℚ) +
        ((((a.order ⟨2, by omega⟩ : Int) : ℚ) : WithTop ℚ) +
          a.truncatedPrefixDefect b (-1) 3 1))

/-- The normalized trigger from condition (iv) for a target of rank at least
four.  Under `R_1 = S_1`, the original three inequalities are equivalent to
`R_1 = R_3` and `R_4 - R_3 > 2e`. -/
def lemma813LongTrigger
    (a : GoodBONG q L (m + 2)) (_b : GoodBONG r M 1) (hm : 1 < m) : Prop :=
  a.order (0 : Fin (m + 2)) = a.order ⟨2, by omega⟩ ∧
    a.order ⟨2, by omega⟩ + 2 * (ramificationIndex K : Int) <
      a.order ⟨3, by omega⟩

/-- The explicit conditions (a)--(c) following Lemma 8.12 in the paper.

The two low-rank clauses are separated from the higher-rank clauses so every
finite index is accompanied by its exact range proof:

* `m = 0` is target rank two, where binary representation is unconditional;
* `m = 1` is target rank three, where the ternary representation is required
  only when `R_1 = R_3`;
* positive `m` and `1 < m` carry the displayed conditions (iii) and (iv)
  triggers respectively.
-/
structure Lemma813Conditions
    (a : GoodBONG q L (m + 2)) (b : GoodBONG r M 1) : Prop where
  defectEquality :
    a.truncatedPrefixDefect b 1 1 1 =
      (a.alphaValue (0 : Fin (m + 1)) : WithTop ℚ)
  binaryRankTwo : m = 0 →
    DiagonalRepresents
      (b.prefixValues 1 (Nat.le_refl _))
      (a.prefixValues 2 (by omega))
  binaryHigher : ∀ hm : 0 < m, a.lemma813CentralTrigger b hm →
    DiagonalRepresents
      (b.prefixValues 1 (Nat.le_refl _))
      (a.prefixValues 2 (by omega))
  ternaryRankThree : ∀ hm : m = 1,
    a.order (0 : Fin (m + 2)) = a.order ⟨2, by omega⟩ →
      DiagonalRepresents
        (b.prefixValues 1 (Nat.le_refl _))
        (a.prefixValues 3 (by omega))
  ternaryHigher : ∀ hm : 1 < m, a.lemma813LongTrigger b hm →
    DiagonalRepresents
      (b.prefixValues 1 (Nat.le_refl _))
      (a.prefixValues 3 (by omega))

/-- Condition (i) of Theorem 2.1 is automatic for a unary source whose first
order agrees with the target's first order. -/
theorem lemma813_orderCondition
    (a : GoodBONG q L (m + 2)) (b : GoodBONG r M 1)
    (hfirst : a.order (0 : Fin (m + 2)) = b.order (0 : Fin 1)) :
    a.RepresentationOrderCondition b (Nat.zero_le (m + 1)) := by
  intro i
  left
  have hi : i = (0 : Fin 1) := by
    apply Fin.ext
    omega
  subst i
  have htarget :
      (⟨(0 : Fin 1).val, by omega⟩ : Fin (m + 2)) =
        (0 : Fin (m + 2)) := by
    apply Fin.ext
    rfl
  rw [htarget, hfirst]

/-- Condition (ii) at the unique unary boundary is equivalent to condition
(a), namely `d[a_1 b_1] = alpha_1`. -/
theorem lemma813_defectCondition_iff
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (m + 2)) (b : GoodBONG r M 1)
    (hfirst : a.order (0 : Fin (m + 2)) = b.order (0 : Fin 1)) :
    a.RepresentationDefectCondition b ↔
      a.truncatedPrefixDefect b 1 1 1 =
        (a.alphaValue (0 : Fin (m + 1)) : WithTop ℚ) := by
  let first := firstRepresentationIndex m 0
  have halpha : a.representationAlpha b first =
      (a.alphaValue (0 : Fin (m + 1)) : WithTop ℚ) :=
    a.beli2019Lemma812_i b hfirst
  have hupper : a.truncatedPrefixDefect b 1 1 1 ≤
      (a.alphaValue (0 : Fin (m + 1)) : WithTop ℚ) := by
    have hcap := a.truncatedPrefixDefect_le_leftCap b 1 1 1
    rw [a.prefixAlphaCap_of_internal (by omega) (by omega)] at hcap
    have hindex : (⟨1 - 1, by omega⟩ : Fin (m + 1)) =
        (0 : Fin (m + 1)) := by
      apply Fin.ext
      simp
    rw [hindex] at hcap
    exact hcap
  constructor
  · intro h
    have hlower := h first
    rw [a.coe_representationAlphaValue b first, halpha] at hlower
    exact le_antisymm hupper hlower
  · intro heq i
    have hi : i = first := by
      cases i with
      | mk val pos lt_large le_small =>
          have hval : val = 1 := by omega
          subst val
          rfl
    subst i
    rw [a.coe_representationAlphaValue b first, halpha]
    change (a.alphaValue (0 : Fin (m + 1)) : WithTop ℚ) ≤
      a.truncatedPrefixDefect b 1 1 1
    rw [heq]

/-- The uncapped defect `d(a_1 b_1)` appearing in the equivalent version of
condition (a). -/
noncomputable def lemma813RawDefect
    (a : GoodBONG q L (m + 2)) (b : GoodBONG r M 1) : WithTop ℚ :=
  defectOrder (K := K)
    (a.valueUnit (0 : Fin (m + 2)) * b.valueUnit (0 : Fin 1))

/-- At the first unary boundary the bracketed defect is precisely the raw
defect capped by `alpha_1`. -/
theorem lemma813_firstDefect_eq_min_raw
    (a : GoodBONG q L (m + 2)) (b : GoodBONG r M 1) :
    a.truncatedPrefixDefect b 1 1 1 =
      min (a.lemma813RawDefect b)
        (a.alphaValue (0 : Fin (m + 1)) : WithTop ℚ) := by
  have haProduct : a.prefixProduct 1 = a.valueUnit (0 : Fin (m + 2)) := by
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
  have hindex : (⟨1 - 1, by omega⟩ : Fin (m + 1)) =
      (0 : Fin (m + 1)) := by
    apply Fin.ext
    simp
  unfold truncatedPrefixDefect lemma813RawDefect
  rw [a.prefixAlphaCap_of_internal (by omega) (by omega),
    b.prefixAlphaCap_last, hindex, haProduct, hbProduct]
  simp only [one_mul, min_top_right]

/-- The equality `d[a_1 b_1] = alpha_1` is equivalent to the paper's
uncapped inequality `d(a_1 b_1) ≥ alpha_1`. -/
theorem lemma813_defectEquality_iff_raw
    (a : GoodBONG q L (m + 2)) (b : GoodBONG r M 1) :
    a.truncatedPrefixDefect b 1 1 1 =
        (a.alphaValue (0 : Fin (m + 1)) : WithTop ℚ) ↔
      (a.alphaValue (0 : Fin (m + 1)) : WithTop ℚ) ≤
        a.lemma813RawDefect b := by
  rw [a.lemma813_firstDefect_eq_min_raw b]
  exact (min_eq_right_iff :
    min (a.lemma813RawDefect b)
        (a.alphaValue (0 : Fin (m + 1)) : WithTop ℚ) =
          (a.alphaValue (0 : Fin (m + 1)) : WithTop ℚ) ↔
      (a.alphaValue (0 : Fin (m + 1)) : WithTop ℚ) ≤
        a.lemma813RawDefect b)

/-- The unique condition-(iii) index for a unary source and a target of rank
at least three. -/
def lemma813CentralIndex (targetTail : Nat) :
    CentralRepresentationIndex (targetTail + 3) 1 where
  val := 2
  one_lt := by omega
  lt_large := by omega
  le_small_succ := by omega

@[simp]
theorem lemma813CentralIndex_previous (targetTail : Nat) :
    (lemma813CentralIndex targetTail).previous =
      firstRepresentationIndex (targetTail + 1) 0 := by
  rfl

/-- At the unique unary central index, Definition 4's adjusted quantity is
the rank-one terminal formula from Lemma 8.12(ii). -/
theorem centralAdjustedAlpha_lemma813CentralIndex
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (m + 3)) (b : GoodBONG r M 1)
    (hfirst : a.order (0 : Fin (m + 3)) = b.order (0 : Fin 1)) :
    a.centralAdjustedAlpha b (lemma813CentralIndex m) =
      a.terminalSecondPrimaryFormula b := by
  unfold centralAdjustedAlpha
  rw [dif_neg (by simp [lemma813CentralIndex])]
  exact a.beli2019Lemma812_ii_rankOne b hfirst

/-- For a target of rank at least three, condition (iii) at its unique unary
index is exactly the higher-rank clause (b) in Lemma 8.13. -/
theorem lemma813_centralCondition_iff
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (m + 3)) (b : GoodBONG r M 1)
    (hfirst : a.order (0 : Fin (m + 3)) = b.order (0 : Fin 1)) :
    a.CentralRepresentationConditions b ↔
      a.lemma813CentralTrigger b (by omega) →
        DiagonalRepresents
          (b.prefixValues 1 (Nat.le_refl _))
          (a.prefixValues 2 (by omega)) := by
  let central := lemma813CentralIndex m
  have hprevious : central.previous = firstRepresentationIndex (m + 1) 0 := by
    simp only [central, lemma813CentralIndex_previous]
  have halpha :
      (a.representationAlphaValue b central.previous : WithTop ℚ) =
        (a.alphaValue (0 : Fin (m + 2)) : WithTop ℚ) := by
    rw [a.coe_representationAlphaValue b central.previous, hprevious,
      a.beli2019Lemma812_i b hfirst]
  have hadjusted : a.centralAdjustedAlpha b central =
      a.terminalSecondPrimaryFormula b := by
    simpa only [central] using
      a.centralAdjustedAlpha_lemma813CentralIndex b hfirst
  have hsourceZero :
      (⟨central.val - 2, by
        have := central.one_lt
        have := central.le_small_succ
        omega⟩ : Fin 1) =
        (0 : Fin 1) := by
    apply Fin.ext
    simp [central, lemma813CentralIndex]
  have htargetSecond :
      (⟨central.val - 1, by
        have := central.one_lt
        have := central.lt_large
        omega⟩ : Fin (m + 3)) = (1 : Fin (m + 3)) := by
    apply Fin.ext
    simp [central, lemma813CentralIndex]
  have htargetThird :
      (⟨central.val, central.lt_large⟩ : Fin (m + 3)) =
        (⟨2, by omega⟩ : Fin (m + 3)) := by
    apply Fin.ext
    simp [central, lemma813CentralIndex]
  constructor
  · intro h htrigger
    have hcentral := h central
    rcases htrigger with ⟨horder, hdefect⟩
    have hrepresentation := hcentral (by
      constructor
      · rw [hsourceZero, htargetThird, ← hfirst]
        exact horder
      · rw [htargetSecond, halpha, hadjusted]
        simpa only [terminalSecondPrimaryFormula] using hdefect)
    simpa only [central, lemma813CentralIndex] using hrepresentation
  · intro h i htrigger
    have hi : i = central := by
      cases i with
      | mk val one_lt lt_large le_small_succ =>
          have hval : val = 2 := by omega
          subst val
          rfl
    subst i
    rcases htrigger with ⟨horder, hdefect⟩
    have hnormalized : a.lemma813CentralTrigger b (by omega) := by
      constructor
      · rw [hfirst]
        simpa only [hsourceZero, htargetThird] using horder
      · rw [htargetSecond, halpha, hadjusted] at hdefect
        simpa only [terminalSecondPrimaryFormula] using hdefect
    have hrepresentation := h hnormalized
    simpa only [central, lemma813CentralIndex] using hrepresentation

/-- The unique condition-(iv) index for a unary source and a target of rank
at least four. -/
def lemma813LongIndex (targetTail : Nat) :
    LongRepresentationIndex (targetTail + 4) 1 where
  val := 2
  one_lt := by omega
  succ_lt_large := by omega
  le_small_succ := by omega

/-- For a target of rank at least four, condition (iv) at its unique unary
index is exactly the higher-rank clause (c) in Lemma 8.13. -/
theorem lemma813_longCondition_iff
    (a : GoodBONG q L (m + 4)) (b : GoodBONG r M 1)
    (hfirst : a.order (0 : Fin (m + 4)) = b.order (0 : Fin 1)) :
    a.LongRepresentationConditions b ↔
      a.lemma813LongTrigger b (by omega) →
        DiagonalRepresents
          (b.prefixValues 1 (Nat.le_refl _))
          (a.prefixValues 3 (by omega)) := by
  let long := lemma813LongIndex m
  have hsourceZero :
      (⟨long.val - 2, by
        have := long.one_lt
        have := long.le_small_succ
        omega⟩ : Fin 1) = (0 : Fin 1) := by
    apply Fin.ext
    simp [long, lemma813LongIndex]
  have htargetThird :
      (⟨long.val, by have := long.succ_lt_large; omega⟩ : Fin (m + 4)) =
        (⟨2, by omega⟩ : Fin (m + 4)) := by
    apply Fin.ext
    simp [long, lemma813LongIndex]
  have htargetFourth :
      (⟨long.val + 1, long.succ_lt_large⟩ : Fin (m + 4)) =
        (⟨3, by omega⟩ : Fin (m + 4)) := by
    apply Fin.ext
    simp [long, lemma813LongIndex]
  constructor
  · intro h htrigger
    rcases htrigger with ⟨hequal, hgap⟩
    have hlong := h long
    have hrepresentation := hlong (by
      constructor
      · simp [long, lemma813LongIndex]
      · constructor
        · rw [hsourceZero, htargetFourth, ← hfirst, hequal]
          exact hgap
        · rw [htargetThird, hsourceZero, ← hfirst, hequal])
    simpa only [long, lemma813LongIndex] using hrepresentation
  · intro h i htrigger
    have hi : i = long := by
      cases i with
      | mk val one_lt succ_lt_large le_small_succ =>
          have hval : val = 2 := by omega
          subst val
          rfl
    subst i
    rcases htrigger with ⟨_, hgap, hreverse⟩
    have hgap' :
        b.order (0 : Fin 1) + 2 * (ramificationIndex K : Int) <
          a.order (⟨3, by omega⟩ : Fin (m + 4)) := by
      simpa only [hsourceZero, htargetFourth] using hgap
    have hreverse' :
        a.order (⟨2, by omega⟩ : Fin (m + 4)) +
            2 * (ramificationIndex K : Int) ≤
          b.order (0 : Fin 1) + 2 * (ramificationIndex K : Int) := by
      simpa only [htargetThird, hsourceZero] using hreverse
    have hleSource : a.order (⟨2, by omega⟩ : Fin (m + 4)) ≤
        b.order (0 : Fin 1) := by
      omega
    have hleTarget : a.order (⟨2, by omega⟩ : Fin (m + 4)) ≤
        a.order (0 : Fin (m + 4)) := by
      rw [hfirst]
      exact hleSource
    have htargetZero : (⟨0, by omega⟩ : Fin (m + 4)) =
        (0 : Fin (m + 4)) := by
      apply Fin.ext
      rfl
    have hgood : a.order (0 : Fin (m + 4)) ≤
        a.order (⟨2, by omega⟩ : Fin (m + 4)) := by
      have h := a.order_zero_le_two
      rw [htargetZero] at h
      exact h
    have hequal : a.order (0 : Fin (m + 4)) =
        a.order (⟨2, by omega⟩ : Fin (m + 4)) := by
      exact le_antisymm hgood hleTarget
    have hnormalized : a.lemma813LongTrigger b (by omega) := by
      refine ⟨hequal, ?_⟩
      rw [← hequal, hfirst]
      exact hgap'
    have hrepresentation := h hnormalized
    simpa only [long, lemma813LongIndex] using hrepresentation

/-- Noncircular form of Lemma 8.13: for a unary source with `R_1 = S_1`,
the four conditions of Theorem 2.1 are equivalent to the explicit clauses
(a)--(c).  The ambient-space hypothesis is used only for the full-prefix
target-rank-two and target-rank-three boundary cases. -/
theorem representationConditions_iff_lemma813
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (m + 2)) (b : GoodBONG r M 1)
    (hfirst : a.order (0 : Fin (m + 2)) = b.order (0 : Fin 1))
    (ambient : q.Represents r) :
    RepresentationConditions a b (Nat.zero_le (m + 1)) ↔
      Lemma813Conditions a b := by
  constructor
  · intro conditions
    refine
      { defectEquality :=
          (a.lemma813_defectCondition_iff b hfirst).mp
            conditions.defectCondition
        binaryRankTwo := ?_
        binaryHigher := ?_
        ternaryRankThree := ?_
        ternaryHigher := ?_ }
    · intro hm
      subst m
      simpa only using a.fullPrefix_represents_of_ambient b ambient
    · intro hm htrigger
      cases m with
      | zero => omega
      | succ k =>
          exact (a.lemma813_centralCondition_iff b hfirst).mp
            conditions.centralRepresentations htrigger
    · intro hm _
      subst m
      simpa only using a.fullPrefix_represents_of_ambient b ambient
    · intro hm htrigger
      cases m with
      | zero => omega
      | succ k =>
          cases k with
          | zero => omega
          | succ l =>
              exact (a.lemma813_longCondition_iff b hfirst).mp
                conditions.longRepresentations htrigger
  · intro explicit
    refine
      { orderCondition := a.lemma813_orderCondition b hfirst
        defectCondition :=
          (a.lemma813_defectCondition_iff b hfirst).mpr
            explicit.defectEquality
        centralRepresentations := ?_
        longRepresentations := ?_ }
    · cases m with
      | zero =>
          intro i
          have := i.one_lt
          have := i.lt_large
          omega
      | succ k =>
          exact (a.lemma813_centralCondition_iff b hfirst).mpr
            (explicit.binaryHigher (by omega))
    · cases m with
      | zero =>
          intro i
          have := i.one_lt
          have := i.succ_lt_large
          omega
      | succ k =>
          cases k with
          | zero =>
              intro i
              have := i.one_lt
              have := i.succ_lt_large
              omega
          | succ l =>
              exact (a.lemma813_longCondition_iff b hfirst).mpr
                (explicit.ternaryHigher (by omega))

/-- Literal statement of Beli (2019), Lemma 8.13, parameterized by the
already-established main-theorem equivalence.  Keeping that equivalence as an
argument prevents any circular dependency in Sections 8--9. -/
theorem beli2019Lemma813
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (m + 2)) (b : GoodBONG r M 1)
    (hfirst : a.order (0 : Fin (m + 2)) = b.order (0 : Fin 1))
    (ambient : q.Represents r)
    (mainTheorem : Lattice.Represents q r L M ↔
      RepresentationConditions a b (Nat.zero_le (m + 1))) :
    Lattice.Represents q r L M ↔ Lemma813Conditions a b :=
  mainTheorem.trans (a.representationConditions_iff_lemma813 b hfirst ambient)

end BONG.GoodBONG

end Bong
