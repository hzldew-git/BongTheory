/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma95

/-!
# Beli (2019), Lemma 9.6

This file starts the exceptional-head reduction of Lemma 9.6.  The first
displayed argument in the paper expands
`d[-a_(1,3)b_1] >= 2e` and obtains lower bounds for the source first alpha,
the target third alpha, and the two adjacent order gaps.  These consequences
are proved here directly from the definition of the capped defect and P5.

The paper uses one-based indices.  Thus its `beta_1` is `b.alphaValue 0`,
its `alpha_3` is `a.alphaValue 2`, and its orders `R_4` and `S_2` are Lean
indices `3` and `1`.
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
  {L : Lattice K V} {M : Lattice K W} {n : Nat}

/-- The exact lower-bound hypothesis `d[-a_(1,3)b_1] >= 2e` occurring in
Lemma 9.6. -/
def Beli2019Lemma96DefectBound
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1)) : Prop :=
  (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) ≤
    a.truncatedPrefixDefect b (-1) 3 1

/-- A lower bound on the rationally embedded defect order reflects to the
underlying extended-natural quadratic defect. -/
theorem quadraticDefect_ge_twoE_of_defectOrder_ge_twoE
    (x : Kˣ)
    (hdefect : (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) ≤
      defectOrder (K := K) x) :
    ((2 * ramificationIndex K : Nat) : ℕ∞) ≤ quadraticDefect K x := by
  let f : Nat → ℚ := Nat.castAddMonoidHom ℚ
  have hf : ∀ {m n : Nat}, f m ≤ f n ↔ m ≤ n := by
    intro m n
    change (m : ℚ) ≤ (n : ℚ) ↔ m ≤ n
    exact_mod_cast Iff.rfl
  let d : WithTop Nat := quadraticDefect K x
  change ((2 * ramificationIndex K : Nat) : WithTop Nat) ≤ d
  apply (WithTop.map_le_iff f hf).mp
  change (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) ≤
    defectOrder (K := K) x
  exact hdefect

/-- The capped Lemma 9.6 hypothesis bounds the uncapped scalar defect used
in the paper. -/
theorem lemma96_rawDefect_ge_twoE
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (hdefect : a.Beli2019Lemma96DefectBound b) :
    (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) ≤
      defectOrder (K := K)
        ((-1) * a.prefixProduct 3 * b.prefixProduct 1) :=
  hdefect.trans
    (a.truncatedPrefixDefect_le_defect b (-1) 3 1)

/-- The field-level endpoint theorem turns the preceding defect bound into
the paper's dichotomy
`-a_(1,3)b_1 ∈ Kˣ²` or `-a_(1,3)b_1 ∈ Δ Kˣ²`. -/
theorem lemma96_rawSquareClassCases
    [laws : DyadicDiscriminantClassLaws K]
    [DyadicMaximalDefectClassLaws K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (hdefect : a.Beli2019Lemma96DefectBound b) :
    IsSquare ((-1) * a.prefixProduct 3 * b.prefixProduct 1) ∨
      IsSquare (((-1) * a.prefixProduct 3 * b.prefixProduct 1) /
        laws.discriminantUnit) := by
  apply isSquare_or_isSquare_div_discriminant_of_defect_ge_twoE
  exact quadraticDefect_ge_twoE_of_defectOrder_ge_twoE
    ((-1) * a.prefixProduct 3 * b.prefixProduct 1)
    (a.lemma96_rawDefect_ge_twoE b hdefect)

/-- Expanding the right alpha cap in the Lemma 9.6 defect gives
`beta_1 >= 2e`. -/
theorem lemma96_sourceFirstAlpha_ge_twoE
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (hthree : 3 ≤ n + 1) (hdefect : a.Beli2019Lemma96DefectBound b) :
    2 * (ramificationIndex K : ℚ) ≤
      b.alphaValue (⟨0, by omega⟩ : Fin n) := by
  have hcap := a.truncatedPrefixDefect_le_rightCap b (-1) 3 1
  rw [b.prefixAlphaCap_of_internal (i := 1) (by omega) (by omega)] at hcap
  have hbound :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) ≤
        (b.alphaValue (⟨0, by omega⟩ : Fin n) : WithTop ℚ) :=
    hdefect.trans hcap
  exact_mod_cast hbound

/-- Expanding the left alpha cap in the Lemma 9.6 defect gives
`alpha_3 >= 2e`. -/
theorem lemma96_targetThirdAlpha_ge_twoE
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (hfour : 4 ≤ n + 1) (hdefect : a.Beli2019Lemma96DefectBound b) :
    2 * (ramificationIndex K : ℚ) ≤
      a.alphaValue (⟨2, by omega⟩ : Fin n) := by
  have hcap := a.truncatedPrefixDefect_le_leftCap b (-1) 3 1
  rw [a.prefixAlphaCap_of_internal (i := 3) (by omega) (by omega)] at hcap
  have hbound :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) ≤
        (a.alphaValue (⟨2, by omega⟩ : Fin n) : WithTop ℚ) :=
    hdefect.trans hcap
  exact_mod_cast hbound

/-- P5 converts an alpha lower bound at the dyadic endpoint into the same
lower bound for the adjacent order gap. -/
theorem orderGap_ge_twoE_of_alphaValue_ge_twoE
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (i : Fin n)
    (halpha : 2 * (ramificationIndex K : ℚ) ≤ a.alphaValue i) :
    2 * (ramificationIndex K : Int) ≤ a.orderGap i := by
  by_contra hnot
  have hgap : a.orderGap i < 2 * (ramificationIndex K : Int) :=
    lt_of_not_ge hnot
  have halpha' : a.alphaValue i < 2 * (ramificationIndex K : ℚ) :=
    (a.alpha_p5 i).1.mpr hgap
  exact (not_lt_of_ge halpha) halpha'

/-- The source consequence displayed in Lemma 9.6:
`S_2 - S_1 >= 2e`. -/
theorem lemma96_sourceFirstGap_ge_twoE
    [Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (hthree : 3 ≤ n + 1) (hdefect : a.Beli2019Lemma96DefectBound b) :
    2 * (ramificationIndex K : Int) ≤
      b.order (⟨1, by omega⟩ : Fin (n + 1)) -
        b.order (⟨0, by omega⟩ : Fin (n + 1)) := by
  have halpha := a.lemma96_sourceFirstAlpha_ge_twoE b hthree hdefect
  have hgap := b.orderGap_ge_twoE_of_alphaValue_ge_twoE
    (⟨0, by omega⟩ : Fin n) halpha
  change 2 * (ramificationIndex K : Int) ≤
    b.order (⟨1, by omega⟩ : Fin (n + 1)) -
      b.order (⟨0, by omega⟩ : Fin (n + 1)) at hgap
  exact hgap

/-- The target consequence displayed in Lemma 9.6:
`R_4 - R_3 >= 2e`. -/
theorem lemma96_targetThirdGap_ge_twoE
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (hfour : 4 ≤ n + 1) (hdefect : a.Beli2019Lemma96DefectBound b) :
    2 * (ramificationIndex K : Int) ≤
      a.order (⟨3, by omega⟩ : Fin (n + 1)) -
        a.order (⟨2, by omega⟩ : Fin (n + 1)) := by
  have halpha := a.lemma96_targetThirdAlpha_ge_twoE b hfour hdefect
  have hgap := a.orderGap_ge_twoE_of_alphaValue_ge_twoE
    (⟨2, by omega⟩ : Fin n) halpha
  change 2 * (ramificationIndex K : Int) ≤
    a.order (⟨3, by omega⟩ : Fin (n + 1)) -
      a.order (⟨2, by omega⟩ : Fin (n + 1)) at hgap
  exact hgap

/-- With the paper's equality `R_1 = R_3 = S_1`, the two gap bounds become
the absolute order estimates `R_4,S_2 >= R_1 + 2e`. -/
structure Beli2019Lemma96InitialOrderConsequences
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (hfour : 4 ≤ n + 1) where
  sourceFirstAlpha_ge :
    2 * (ramificationIndex K : ℚ) ≤
      b.alphaValue (⟨0, by omega⟩ : Fin n)
  targetThirdAlpha_ge :
    2 * (ramificationIndex K : ℚ) ≤
      a.alphaValue (⟨2, by omega⟩ : Fin n)
  sourceSecondOrder_ge :
    a.order (0 : Fin (n + 1)) + 2 * (ramificationIndex K : Int) ≤
      b.order (⟨1, by omega⟩ : Fin (n + 1))
  targetFourthOrder_ge :
    a.order (0 : Fin (n + 1)) + 2 * (ramificationIndex K : Int) ≤
      a.order (⟨3, by omega⟩ : Fin (n + 1))

/-- The complete first displayed calculation in the proof of Lemma 9.6. -/
theorem beli2019Lemma96_initialOrderConsequences
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [sourceLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (hfour : 4 ≤ n + 1)
    (hfirstThirdSource :
      a.order (0 : Fin (n + 1)) =
        a.order (⟨2, by omega⟩ : Fin (n + 1)) ∧
      a.order (0 : Fin (n + 1)) = b.order (0 : Fin (n + 1)))
    (hdefect : a.Beli2019Lemma96DefectBound b) :
    Beli2019Lemma96InitialOrderConsequences a b hfour := by
  have hsourceGap := by
    letI : Beli2006AlphaLaws.{u, w} K := sourceLaws
    exact a.lemma96_sourceFirstGap_ge_twoE b (by omega) hdefect
  have htargetGap := by
    letI : Beli2006AlphaLaws.{u, v} K := targetLaws
    exact a.lemma96_targetThirdGap_ge_twoE b hfour hdefect
  have hzero : (⟨0, by omega⟩ : Fin (n + 1)) = 0 := by
    apply Fin.ext
    rfl
  rw [hzero] at hsourceGap
  refine
    { sourceFirstAlpha_ge :=
        a.lemma96_sourceFirstAlpha_ge_twoE b (by omega) hdefect
      targetThirdAlpha_ge :=
        a.lemma96_targetThirdAlpha_ge_twoE b hfour hdefect
      sourceSecondOrder_ge := ?_
      targetFourthOrder_ge := ?_ }
  · rw [hfirstThirdSource.2]
    omega
  · rw [hfirstThirdSource.1]
    omega

/-! ## The first ternary block -/

/-- From `R_2-R_1=2e-2` and `R_3=R_1`, the first two alpha values of
the ternary block are exactly `2e-1` and `1`, as asserted immediately
before Lemma 9.5 is applied in the paper. -/
theorem lemma96_firstTwoAlphaValues
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (n + 1))
    (hthree : 3 ≤ n + 1)
    (houter : a.order (0 : Fin (n + 1)) =
      a.order (⟨2, by omega⟩ : Fin (n + 1)))
    (hfirstGap :
      a.order (⟨1, by omega⟩ : Fin (n + 1)) -
          a.order (0 : Fin (n + 1)) =
        2 * (ramificationIndex K : Int) - 2) :
    a.alphaValue (⟨0, by omega⟩ : Fin n) =
        ((2 * (ramificationIndex K : Int) - 1 : Int) : ℚ) ∧
      a.alphaValue (⟨1, by omega⟩ : Fin n) = 1 := by
  let first : Fin n := ⟨0, by omega⟩
  let second : Fin n := ⟨1, by omega⟩
  have hfirstOrderGap :
      a.orderGap first = 2 * (ramificationIndex K : Int) - 2 := by
    change a.order (⟨1, by omega⟩ : Fin (n + 1)) -
        a.order (⟨0, by omega⟩ : Fin (n + 1)) =
      2 * (ramificationIndex K : Int) - 2
    have hzero : (⟨0, by omega⟩ : Fin (n + 1)) = 0 := by
      apply Fin.ext
      rfl
    rw [hzero]
    exact hfirstGap
  have hsecondOrderGap :
      a.orderGap second = 2 - 2 * (ramificationIndex K : Int) := by
    change a.order (⟨2, by omega⟩ : Fin (n + 1)) -
        a.order (⟨1, by omega⟩ : Fin (n + 1)) =
      2 - 2 * (ramificationIndex K : Int)
    rw [← houter]
    omega
  have hfirstFormula : a.alphaValue first = a.halfGapValue first :=
    a.beli2009Corollary29_i first
      (Or.inr (Or.inr (Or.inr hfirstOrderGap)))
  have hsecondFormula : a.alphaValue second = a.halfGapValue second :=
    a.beli2009Corollary29_i second
      (Or.inr (Or.inr (Or.inl hsecondOrderGap)))
  constructor
  · change a.alphaValue first = _
    rw [hfirstFormula]
    unfold halfGapValue
    rw [hfirstOrderGap]
    push_cast
    ring
  · change a.alphaValue second = _
    rw [hsecondFormula]
    unfold halfGapValue
    rw [hsecondOrderGap]
    push_cast
    ring

end BONG.GoodBONG

end Bong
