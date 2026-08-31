/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliUniversalTheorem21

/-!
# Beli's universal-lattice main theorem

The reductions in Section 2 split naturally into two parts.  Lemma 2.3,
already proved from the revised Beli 2019 representation theorem, reduces
universality to ambient line representation plus four unary representation
conditions.  Theorem 2.1 then identifies those unary conditions with its
explicit Cases I and II.

The componentwise case analysis is now proved by Lemmas 2.10, 2.13, and
2.14, including the replacement of the temporary II(a') by the published
II(a).  The final theorem below closes the former proof boundary.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG.GoodBONG

/-- The complete unary condition produced by Lemma 2.3, including ambient
line representation and all four revised Beli 2019 conditions. -/
def UniversalAllUnaryRepresentationConditions {tail : Nat}
    (a : GoodBONG q L (tail + 2)) : Prop :=
  ∀ b : Kˣ, ordUnit K b = 0 ∨ ordUnit K b = 1 →
    q.Represents
        (QuadraticSpace.rescaleUnit b (QuadraticSpace.line K)) ∧
          RepresentationConditionsPrime a (BONG.unaryModelGoodBONG b)
        (by omega)

/-- The result of applying Lemmas 2.5, 2.10, 2.13, and 2.14 to the four
unary representation conditions, before II(a') is replaced by II(a). -/
def UniversalUnaryCaseAnalysisConditions {tail : Nat}
    (a : GoodBONG q L (tail + 2)) : Prop :=
  q.IsLineUniversal ∧ a.order 0 = 0 ∧
    ((a.alphaValue (0 : Fin (tail + 1)) = 0 ∧
        a.UniversalCentralCaseIConditions ∧
        a.UniversalLongCaseIConditions) ∨
      (a.UniversalCaseIIPrime ∧
        a.UniversalCentralCaseIIConditions ∧
        a.UniversalLongCaseIIConditions))

/-- The four universal unary conditions are exactly the componentwise
conditions isolated by Lemmas 2.5, 2.10, 2.13, and 2.14. -/
theorem universalAllUnaryRepresentationConditions_iff_components
    {tail : Nat} (a : GoodBONG q L (tail + 2))
    (hintegral : Lattice.IsIntegral q L) :
    a.UniversalAllUnaryRepresentationConditions ↔
      a.UniversalUnaryCaseAnalysisConditions := by
  constructor
  · intro hall
    have hline : q.IsLineUniversal :=
      (beliUniversalLemma24 q).1 (fun b hb ↦ (hall b hb).1)
    have horder : ∀ b : Kˣ, ordUnit K b = 0 ∨ ordUnit K b = 1 →
        a.RepresentationOrderCondition (BONG.unaryModelGoodBONG b)
          (by omega) := fun b hb ↦ (hall b hb).2.orderCondition
    have hzero :=
      (a.universalUnaryOrderConditions_iff_order_zero hintegral).1 horder
    have hdefect : a.UniversalUnaryDefectConditions :=
      fun b hb ↦ (hall b hb).2.defectCondition
    have hcentral : a.UniversalAllUnaryCentralConditions :=
      fun b hb ↦ (hall b hb).2.centralRepresentations
    have hlong : a.UniversalAllUnaryLongConditions :=
      fun b hb ↦ (hall b hb).2.longRepresentations
    refine ⟨hline, hzero, ?_⟩
    rcases
        (a.universalUnaryDefectConditions_iff_alphaZero_or_caseIIPrime
          hzero hline).1 hdefect with halpha | hII
    · left
      exact ⟨halpha,
        (a.universalAllUnaryCentralConditions_iff_caseI
          hline hzero halpha).1 hcentral,
        (a.universalAllUnaryLongConditions_iff_caseI
          hline hzero halpha).1 hlong⟩
    · right
      exact ⟨hII,
        (a.universalAllUnaryCentralConditions_iff_caseII hzero hII).1 hcentral,
        (a.universalAllUnaryLongConditions_iff_caseII
          hline hzero hII).1 hlong⟩
  · rintro ⟨hline, hzero, hcases⟩ b hb
    refine ⟨hline b, ?_⟩
    have horder :=
      (a.universalUnaryOrderConditions_iff_order_zero hintegral).2 hzero b hb
    rcases hcases with ⟨halpha, hcentral, hlong⟩ |
        ⟨hII, hcentral, hlong⟩
    · refine {
        orderCondition := horder
        defectCondition :=
          (a.universalUnaryDefectConditions_iff_alphaZero_or_caseIIPrime
            hzero hline).2 (Or.inl halpha) b hb
        centralRepresentations :=
          (a.universalAllUnaryCentralConditions_iff_caseI
            hline hzero halpha).2 hcentral b hb
        longRepresentations :=
          (a.universalAllUnaryLongConditions_iff_caseI
            hline hzero halpha).2 hlong b hb }
    · refine {
        orderCondition := horder
        defectCondition :=
          (a.universalUnaryDefectConditions_iff_alphaZero_or_caseIIPrime
            hzero hline).2 (Or.inr hII) b hb
        centralRepresentations :=
          (a.universalAllUnaryCentralConditions_iff_caseII
            hzero hII).2 hcentral b hb
        longRepresentations :=
          (a.universalAllUnaryLongConditions_iff_caseII
            hline hzero hII).2 hlong b hb }

/-- The componentwise result is exactly the two published alternatives in
Theorem 2.1. -/
theorem universalUnaryCaseAnalysisConditions_iff_theorem21Conditions
    {tail : Nat} (a : GoodBONG q L (tail + 2)) :
    a.UniversalUnaryCaseAnalysisConditions ↔
      a.UniversalTheorem21Conditions := by
  constructor
  · rintro ⟨_hline, hzero, hcases⟩
    rcases hcases with ⟨halpha, hcentral, hlong⟩ |
        ⟨hII, hcentral, hlong⟩
    · exact ⟨hzero, Or.inl {
        alphaOne := halpha
        binaryRankTwo := hcentral.1
        binaryAboveOne := hcentral.2
        binaryAtOne := hlong }⟩
    · refine ⟨hzero, Or.inr ?_⟩
      exact {
        rankAtLeastThree := hII.1
        alphaOne := hII.2.1
        alphaThreeBound := by
          intro hbranch
          apply hcentral
          rcases hbranch with hsecond | hthird
          · exact Or.inl hsecond
          · exact Or.inr ⟨hII.1, hthird⟩
        ternaryBoundary := by
          intro hsecond hthird hbranch
          exact hlong hII.1 hsecond hthird hbranch }
  · rintro ⟨hzero, hI | hII⟩
    · refine ⟨hI.isLineUniversal hzero, hzero, Or.inl ?_⟩
      exact ⟨hI.alphaOne, ⟨hI.binaryRankTwo, hI.binaryAboveOne⟩,
        hI.binaryAtOne⟩
    · have hIIPrime := hII.toCaseIIPrime hzero
      refine ⟨hII.isLineUniversal hzero, hzero, Or.inr ?_⟩
      refine ⟨hIIPrime, ?_, ?_⟩
      · intro hbranch
        apply hII.alphaThreeBound
        rcases hbranch with hsecond | ⟨_hthree, hthird⟩
        · exact Or.inl hsecond
        · exact Or.inr hthird
      · intro hthree hsecond hthird hbranch
        exact hII.ternaryBoundary hsecond hthird hbranch

/-- Lemma 2.3 in a named, theorem-level reduction form for the rank
parameterization used by Theorem 2.1. -/
theorem isUniversal_iff_allUnaryRepresentationConditions {tail : Nat}
    (a : GoodBONG q L (tail + 2))
    (hintegral : Lattice.IsIntegral q L) :
    Lattice.IsUniversal q L ↔
      a.UniversalAllUnaryRepresentationConditions := by
  simpa only [UniversalAllUnaryRepresentationConditions] using
    beliUniversalLemma23 a hintegral

/-- The exact remaining Section 2 proof obligation after Lemma 2.3. -/
def UniversalTheorem21CaseAnalysisObligation {tail : Nat}
    (a : GoodBONG q L (tail + 2)) : Prop :=
  Lattice.IsIntegral q L →
    (a.UniversalAllUnaryRepresentationConditions ↔
      a.UniversalTheorem21Conditions)

/-- The literal main theorem statement, with `m >= 2` enforced by the type
`tail + 2` and integrality kept as the paper's hypothesis.  This is a
statement object and carries no proof. -/
def UniversalTheorem21Statement {tail : Nat}
    (a : GoodBONG q L (tail + 2)) : Prop :=
  Lattice.IsIntegral q L →
    (Lattice.IsUniversal q L ↔ a.UniversalTheorem21Conditions)

/-- Once the explicit unary case analysis is supplied, Theorem 2.1 follows
formally from the proved Lemma 2.3 reduction. -/
theorem universalTheorem21_of_caseAnalysis {tail : Nat}
    (a : GoodBONG q L (tail + 2))
    (hcases : a.UniversalTheorem21CaseAnalysisObligation) :
    a.UniversalTheorem21Statement := by
  intro hintegral
  exact (a.isUniversal_iff_allUnaryRepresentationConditions hintegral).trans
    (hcases hintegral)

/-- Conversely, the paper's main theorem implies exactly the isolated unary
case-analysis obligation.  Thus the named obligation loses no content under
the integrality consequence of `R_1 = 0`. -/
theorem caseAnalysis_of_universalTheorem21 {tail : Nat}
    (a : GoodBONG q L (tail + 2))
    (hmain : a.UniversalTheorem21Statement) :
    a.UniversalTheorem21CaseAnalysisObligation := by
  intro hintegral
  exact (a.isUniversal_iff_allUnaryRepresentationConditions hintegral).symm.trans
    (hmain hintegral)

/-- The two main-theorem formulations are equivalent: completing the
case-analysis obligation is neither weaker nor stronger than Theorem 2.1. -/
theorem universalTheorem21Statement_iff_caseAnalysis {tail : Nat}
    (a : GoodBONG q L (tail + 2)) :
    a.UniversalTheorem21Statement ↔
      a.UniversalTheorem21CaseAnalysisObligation := by
  constructor
  · exact a.caseAnalysis_of_universalTheorem21
  · exact a.universalTheorem21_of_caseAnalysis

/-- The Section 2 case-analysis obligation is discharged. -/
theorem universalTheorem21CaseAnalysis_proved {tail : Nat}
    (a : GoodBONG q L (tail + 2)) :
    a.UniversalTheorem21CaseAnalysisObligation := by
  intro hintegral
  exact
    (a.universalAllUnaryRepresentationConditions_iff_components
      hintegral).trans
      a.universalUnaryCaseAnalysisConditions_iff_theorem21Conditions

/-- Beli, Theorem 2.1: the complete universal integral quadratic-form
criterion over a dyadic local field. -/
theorem beliUniversalTheorem21 {tail : Nat}
    (a : GoodBONG q L (tail + 2)) :
    a.UniversalTheorem21Statement :=
  a.universalTheorem21_of_caseAnalysis
    a.universalTheorem21CaseAnalysis_proved

/-- Direct theorem form with the paper's integrality hypothesis supplied. -/
theorem isUniversal_iff_universalTheorem21Conditions {tail : Nat}
    (a : GoodBONG q L (tail + 2))
    (hintegral : Lattice.IsIntegral q L) :
    Lattice.IsUniversal q L ↔ a.UniversalTheorem21Conditions :=
  a.beliUniversalTheorem21 hintegral

/-- The explicit right-hand side already implies the paper's integrality
hypothesis. -/
theorem UniversalTheorem21Conditions.isIntegral {tail : Nat}
    {a : GoodBONG q L (tail + 2)}
    (h : a.UniversalTheorem21Conditions) : Lattice.IsIntegral q L := by
  apply (BONG.beliUniversalLemma22 a.toBONG).2
  change 0 ≤ a.order 0
  rw [h.1]

end BONG.GoodBONG

/-- A universal lattice has a line-universal ambient quadratic space. -/
theorem Lattice.IsUniversal.isLineUniversal
    (h : Lattice.IsUniversal q L) : q.IsLineUniversal := by
  rw [← beliUniversalLemma24 q]
  intro b hb
  have hbIntegral : Dyadic.IsIntegral K (b : K) := by
    rw [Dyadic.IsIntegral, ← coe_ordUnit]
    rcases hb with hb | hb <;> rw [hb] <;> norm_num
  have hscalar := h.representsScalar hbIntegral
  have hlattice :=
    (Lattice.represents_unaryModel_iff_representsScalar b).2 hscalar
  rcases hlattice with ⟨f⟩
  exact ⟨f.toQuadraticSpaceRepresentation⟩

end Bong
