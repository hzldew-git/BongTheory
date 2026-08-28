/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma517
import Bong.Bong.Beli2019Lemma216Complete
import Bong.Bong.Beli2019RepresentationTransitivity
import Bong.Bong.Beli2019IndexPOrderCertificate

/-!
# Beli (2019), Section 5: the index-uniformizer case

Section 5 proves necessity for a same-rank inclusion of lattice index
`\mathfrak p`.  The scalar part is factored through Lemmas 5.13 and 5.17;
the representation-valued parts are recorded as vacuity-or-representation
certificates matching the Jordan cases in the paper.

The resulting theorem assembles all four clauses of Theorem 2.1, and also
the revised v2 clause (iii').  No implication for arbitrary representations
and no final representation equivalence is assumed here.
-/

namespace Bong

open Dyadic

universe u v

/-- A literal same-space inclusion of index `\mathfrak p`.  With normalized
valuation, its Gram-volume order increases by two. -/
structure Beli2019IndexPInclusion
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    {V : Type v} [AddCommGroup V] [Module K V]
    (q : QuadraticSpace K V) (M N : Lattice K V) : Prop where
  lattice_le : N ≤ M
  volumeOrder_eq : Lattice.volumeOrder q N =
    Lattice.volumeOrder q M + 2

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V} {n : Nat}

/-! ## Condition (ii) -/

/-- A pointwise certificate for the three kinds of boundary occurring in
the proof of condition 2.1(ii).  The first two constructors are precisely
the two conclusions issued from Lemma 5.13.  The third is essential in the
rank-one adjacent-transposition interval `n_{k₁} < i ≤ n_{k₂}`:
the paper's cases 3--4 prove the defect inequality there directly, and the
proper case does not satisfy the global common-or-odd dichotomy. -/
inductive Beli2019SectionFiveDefectCertificate
    (a : GoodBONG q M (n + 1)) (b : GoodBONG q N (n + 1))
    (i : RepresentationIndex (n + 1) (n + 1)) : Prop
  | common (X : Kˣ)
      (sourceApproximation : a.IsPrefixApproximation i.val X)
      (targetApproximation : b.IsPrefixApproximation i.val X)
      (bound : a.representationAlpha b i ≤
        min (a.prefixAlphaCap i.val) (b.prefixAlphaCap i.val))
  | odd
      (prefixSum_succ : b.orderSequence.prefixSum i.val =
        a.orderSequence.prefixSum i.val + 1)
      (bound : a.representationAlpha b i ≤ 0)
  | direct
      (bound : (a.representationAlphaValue b i : WithTop ℚ) ≤
        a.truncatedPrefixDefect b 1 i.val i.val)

namespace Beli2019SectionFiveDefectCertificate

/-- Each checked Section 5 boundary certificate discharges the pointwise
defect inequality. -/
theorem discharge
    [alpha : Beli2006AlphaLaws.{u, v} K]
    {a : GoodBONG q M (n + 1)} {b : GoodBONG q N (n + 1)}
    {i : RepresentationIndex (n + 1) (n + 1)}
    (C : Beli2019SectionFiveDefectCertificate a b i) :
    (a.representationAlphaValue b i : WithTop ℚ) ≤
      a.truncatedPrefixDefect b 1 i.val i.val := by
  cases C with
  | common X hX hY hbound =>
      exact a.representationDefect_at_of_common_approximation
        b i X hX hY hbound
  | odd hsum hbound =>
      exact representationDefect_at_of_prefixSum_succ
        (alphaV := alpha) (alphaW := alpha) a b i hsum hbound
  | direct hbound => exact hbound

end Beli2019SectionFiveDefectCertificate

/-- The complete pointwise output of the Section 5 Jordan calculation.
Unlike the former global `Beli2019Lemma513Data` field, this interface keeps
the exceptional unary interval separate, exactly as in the paper. -/
structure Beli2019SectionFiveDefectData
    (a : GoodBONG q M (n + 1)) (b : GoodBONG q N (n + 1)) : Prop where
  certificate
    (i : RepresentationIndex (n + 1) (n + 1)) :
    Beli2019SectionFiveDefectCertificate a b i

namespace Beli2019SectionFiveDefectData

/-- Section 5, proof of condition 2.1(ii). -/
theorem defectCondition
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    {a : GoodBONG q M (n + 1)} {b : GoodBONG q N (n + 1)}
    (D : Beli2019SectionFiveDefectData a b) :
    a.RepresentationDefectCondition b := by
  intro i
  exact (D.certificate i).discharge

end Beli2019SectionFiveDefectData

/-! ## Conditions (iii) and (iv) -/

/-- A checked Section 5 case for condition (iii): either its numerical
antecedent is false, or the required prefix representation is supplied. -/
inductive Beli2019SectionFiveCentralCertificate
    (a : GoodBONG q M (n + 1)) (b : GoodBONG q N (n + 1))
    (i : CentralRepresentationIndex (n + 1) (n + 1)) : Prop
  | vacuous (htrigger : ¬a.centralAlphaTrigger b i)
  | represented (representation : DiagonalRepresents
      (b.prefixValues (i.val - 1) i.previous_le_sameRank)
      (a.prefixValues i.val i.current_le_sameRank))

namespace Beli2019SectionFiveCentralCertificate

/-- Every Section 5 central certificate discharges its implication. -/
theorem discharge
    {a : GoodBONG q M (n + 1)} {b : GoodBONG q N (n + 1)}
    {i : CentralRepresentationIndex (n + 1) (n + 1)}
    (C : Beli2019SectionFiveCentralCertificate a b i) :
    a.centralAlphaTrigger b i →
      DiagonalRepresents
        (b.prefixValues (i.val - 1) i.previous_le_sameRank)
        (a.prefixValues i.val i.current_le_sameRank) := by
  intro htrigger
  cases C with
  | vacuous h => exact False.elim (h htrigger)
  | represented h => exact h

end Beli2019SectionFiveCentralCertificate

/-- The numerical antecedent of condition 2.1(iv), named for use by the
Section 5 certificate type. -/
noncomputable def sectionFiveLongTrigger
    (a : GoodBONG q M (n + 1)) (b : GoodBONG q N (n + 1))
    (i : LongRepresentationIndex (n + 1) (n + 1)) : Prop :=
  ((if hi : i.val ≤ n + 1 then
      a.order ⟨i.val + 1, i.succ_lt_large⟩ ≤
        b.order ⟨i.val - 1, by have := i.one_lt; have := hi; omega⟩
    else True) ∧
    b.order ⟨i.val - 2, by
      have := i.one_lt
      have := i.le_small_succ
      omega⟩ + 2 * (ramificationIndex K : Int) <
      a.order ⟨i.val + 1, i.succ_lt_large⟩ ∧
    a.order ⟨i.val, by have := i.succ_lt_large; omega⟩ +
        2 * (ramificationIndex K : Int) ≤
      b.order ⟨i.val - 2, by
        have := i.one_lt
        have := i.le_small_succ
        omega⟩ + 2 * (ramificationIndex K : Int))

/-- A checked Section 5 case for condition (iv). -/
inductive Beli2019SectionFiveLongCertificate
    (a : GoodBONG q M (n + 1)) (b : GoodBONG q N (n + 1))
    (i : LongRepresentationIndex (n + 1) (n + 1)) : Prop
  | vacuous (htrigger : ¬sectionFiveLongTrigger a b i)
  | represented (representation : DiagonalRepresents
      (b.prefixValues (i.val - 1) i.previous_le_sameRank)
      (a.prefixValues (i.val + 1) i.next_le_sameRank))

namespace Beli2019SectionFiveLongCertificate

/-- Every Section 5 long certificate discharges its implication. -/
theorem discharge
    {a : GoodBONG q M (n + 1)} {b : GoodBONG q N (n + 1)}
    {i : LongRepresentationIndex (n + 1) (n + 1)}
    (C : Beli2019SectionFiveLongCertificate a b i) :
    sectionFiveLongTrigger a b i →
      DiagonalRepresents
        (b.prefixValues (i.val - 1) i.previous_le_sameRank)
        (a.prefixValues (i.val + 1) i.next_le_sameRank) := by
  intro htrigger
  cases C with
  | vacuous h => exact False.elim (h htrigger)
  | represented h => exact h

end Beli2019SectionFiveLongCertificate

theorem longRepresentationConditions_iff_sectionFiveTrigger
    (a : GoodBONG q M (n + 1)) (b : GoodBONG q N (n + 1)) :
    a.LongRepresentationConditions b ↔
      ∀ i : LongRepresentationIndex (n + 1) (n + 1),
        sectionFiveLongTrigger a b i →
          DiagonalRepresents
            (b.prefixValues (i.val - 1) i.previous_le_sameRank)
            (a.prefixValues (i.val + 1) i.next_le_sameRank) := by
  rfl

/-! ## Complete index-`\mathfrak p` assembly -/

/-- All local outputs of Sections 5 and 6 needed for an index-uniformizer
inclusion.  The revised trigger equivalence is Lemma 2.16. -/
structure Beli2019SectionFiveData
    (a : GoodBONG q M (n + 1)) (b : GoodBONG q N (n + 1)) : Prop
    extends Beli2019SectionFiveDefectData a b where
  orderData : Beli2019SectionFiveOrderData a b
  centralCertificate
    (i : CentralRepresentationIndex (n + 1) (n + 1)) :
    Beli2019SectionFiveCentralCertificate a b i
  longCertificate
    (i : LongRepresentationIndex (n + 1) (n + 1)) :
    Beli2019SectionFiveLongCertificate a b i

namespace Beli2019SectionFiveData

/-- Section 5 proves the original four conditions for an index-`\mathfrak p`
inclusion. -/
theorem representationConditions
    [alpha : Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q M (n + 1)) (b : GoodBONG q N (n + 1))
    (_inclusion : Beli2019IndexPInclusion q M N)
    (D : Beli2019SectionFiveData a b) :
    RepresentationConditions a b (Nat.le_refl n) where
  orderCondition := D.orderData.orderCondition
  defectCondition := D.toBeli2019SectionFiveDefectData.defectCondition
  centralRepresentations := by
    rw [a.centralRepresentationConditions_iff_forall_alphaTrigger b]
    intro i
    exact (D.centralCertificate i).discharge
  longRepresentations := by
    rw [a.longRepresentationConditions_iff_sectionFiveTrigger b]
    intro i
    exact (D.longCertificate i).discharge

/-- The same Section 5 result with the revised v2 condition (iii'). -/
theorem representationConditionsPrime
    [alpha : Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q M (n + 1)) (b : GoodBONG q N (n + 1))
    (inclusion : Beli2019IndexPInclusion q M N)
    (D : Beli2019SectionFiveData a b) :
    RepresentationConditionsPrime a b (Nat.le_refl n) := by
  have hconditions := D.representationConditions a b inclusion
  have htrigger := a.beli2019Lemma216 b (Nat.le_refl n)
    hconditions.orderCondition hconditions.defectCondition
  exact (representationConditions_iff_prime a b (Nat.le_refl n) htrigger).mp
    hconditions

end Beli2019SectionFiveData

end BONG.GoodBONG

end Bong
