/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019KeyLemma
import Bong.Bong.Beli2019RepresentationParity
import Bong.Bong.DiagonalTernaryCore

/-!
# Beli (2019), Section 4: composition of all four representation conditions

The scalar part of transitivity was completed in the preceding modules.
Here we formalize the representation-valued output of the Section 4 case
analysis.  Certificates record either a genuine factorization through a
prefix of the middle BONG or one of Lemma 1.5's four-space parity diagrams.
They therefore expose the geometric content instead of assuming the target
representation itself through a global law.
-/

namespace Bong

open Dyadic

universe u v w z

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {U : Type z} [AddCommGroup U] [Module K U]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {s : QuadraticSpace K U}
  {L : Lattice K V} {M : Lattice K W} {N : Lattice K U}
  {n : Nat}

theorem _root_.Bong.CentralRepresentationIndex.previous_le_sameRank
    (i : CentralRepresentationIndex (n + 1) (n + 1)) :
    i.val - 1 ≤ n + 1 := by
  have := i.lt_large
  omega

theorem _root_.Bong.CentralRepresentationIndex.current_le_sameRank
    (i : CentralRepresentationIndex (n + 1) (n + 1)) :
    i.val ≤ n + 1 := by
  have := i.lt_large
  omega

theorem _root_.Bong.LongRepresentationIndex.previous_le_sameRank
    (i : LongRepresentationIndex (n + 1) (n + 1)) :
    i.val - 1 ≤ n + 1 := by
  have := i.succ_lt_large
  omega

theorem _root_.Bong.LongRepresentationIndex.current_le_sameRank
    (i : LongRepresentationIndex (n + 1) (n + 1)) :
    i.val ≤ n + 1 := by
  have := i.succ_lt_large
  omega

theorem _root_.Bong.LongRepresentationIndex.next_le_sameRank
    (i : LongRepresentationIndex (n + 1) (n + 1)) :
    i.val + 1 ≤ n + 1 := by
  have := i.succ_lt_large
  omega

/-! ## Certificates for condition (iii) -/

/-- A checkable construction of the target one-step prefix representation.
The first two constructors are literal compositions through a prefix of the
middle BONG.  The third is the parity mechanism used in the non-composable
cases of the paper. -/
inductive CentralRepresentationCertificate
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (i : CentralRepresentationIndex (n + 1) (n + 1)) : Prop
  | throughPrevious
      (sourceToMiddle : DiagonalRepresents
        (c.prefixValues (i.val - 1) i.previous_le_sameRank)
        (b.prefixValues (i.val - 1) i.previous_le_sameRank))
      (middleToTarget : DiagonalRepresents
        (b.prefixValues (i.val - 1) i.previous_le_sameRank)
        (a.prefixValues i.val i.current_le_sameRank))
  | throughCurrent
      (sourceToMiddle : DiagonalRepresents
        (c.prefixValues (i.val - 1) i.previous_le_sameRank)
        (b.prefixValues i.val i.current_le_sameRank))
      (middleToTarget : DiagonalRepresents
        (b.prefixValues i.val i.current_le_sameRank)
        (a.prefixValues i.val i.current_le_sameRank))
  | parity
      (diagram : Beli2019RepresentationParityDiagram.{max u (max v (max w z))})
      (first : diagram.first)
      (second : diagram.second)
      (third : diagram.third)
      (target_iff : diagram.fourth ↔ DiagonalRepresents
        (c.prefixValues (i.val - 1) i.previous_le_sameRank)
        (a.prefixValues i.val i.current_le_sameRank))
  | direct
      (representation : DiagonalRepresents
        (c.prefixValues (i.val - 1) i.previous_le_sameRank)
        (a.prefixValues i.val i.current_le_sameRank))

namespace CentralRepresentationCertificate

/-- Every central certificate produces the representation required by
condition (iii). -/
theorem represents
    {a : GoodBONG q L (n + 1)} {b : GoodBONG r M (n + 1)}
    {c : GoodBONG s N (n + 1)}
    {i : CentralRepresentationIndex (n + 1) (n + 1)}
    (certificate : CentralRepresentationCertificate a b c i) :
    DiagonalRepresents
      (c.prefixValues (i.val - 1) i.previous_le_sameRank)
      (a.prefixValues i.val i.current_le_sameRank) := by
  cases certificate with
  | throughPrevious sourceToMiddle middleToTarget =>
      exact sourceToMiddle.trans middleToTarget
  | throughCurrent sourceToMiddle middleToTarget =>
      exact sourceToMiddle.trans middleToTarget
  | parity diagram first second third target_iff =>
      exact target_iff.mp (diagram.fourth_of_first_three first second third)
  | direct representation => exact representation

end CentralRepresentationCertificate

/-- The Section 4 case analysis for condition (iii), with one certificate
for every target boundary whose trigger is active. -/
structure SectionFourCentralCertificates
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1)) : Prop where
  certificate (i : CentralRepresentationIndex (n + 1) (n + 1)) :
    a.centralAlphaTrigger c i → CentralRepresentationCertificate a b c i

theorem centralRepresentationConditions_trans_of_certificates
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hcert : SectionFourCentralCertificates a b c) :
    a.CentralRepresentationConditions c := by
  rw [a.centralRepresentationConditions_iff_forall_alphaTrigger c]
  intro i htrigger
  exact (hcert.certificate i htrigger).represents

/-! ## Certificates for condition (iv) -/

/-- The same-rank form of the trigger in condition (iv). -/
def LongRepresentationTrigger
    (a : GoodBONG q L (n + 1)) (c : GoodBONG s N (n + 1))
    (i : LongRepresentationIndex (n + 1) (n + 1)) : Prop :=
  a.order ⟨i.val + 1, i.succ_lt_large⟩ ≤
      c.order ⟨i.val - 1, by
        have := i.succ_lt_large
        omega⟩ ∧
    c.order ⟨i.val - 2, by
        have := i.succ_lt_large
        omega⟩ + 2 * (ramificationIndex K : Int) <
      a.order ⟨i.val + 1, i.succ_lt_large⟩ ∧
    a.order ⟨i.val, by
        have := i.succ_lt_large
        omega⟩ + 2 * (ramificationIndex K : Int) ≤
      c.order ⟨i.val - 2, by
        have := i.succ_lt_large
        omega⟩ + 2 * (ramificationIndex K : Int)

theorem longRepresentationConditions_iff_forall_trigger
    (a : GoodBONG q L (n + 1)) (c : GoodBONG s N (n + 1)) :
    a.LongRepresentationConditions c ↔
      ∀ i : LongRepresentationIndex (n + 1) (n + 1),
        a.LongRepresentationTrigger c i →
          DiagonalRepresents
            (c.prefixValues (i.val - 1) i.previous_le_sameRank)
            (a.prefixValues (i.val + 1) i.next_le_sameRank) := by
  unfold LongRepresentationConditions LongRepresentationTrigger
  constructor <;> intro h i htrigger
  · apply h i
    simpa only [dif_pos (show i.val ≤ n + 1 by
      have := i.succ_lt_large
      omega)] using htrigger
  · apply h i
    simpa only [dif_pos (show i.val ≤ n + 1 by
      have := i.succ_lt_large
      omega)] using htrigger

/-- A factorization of the target two-step representation through one of
the three neighboring prefixes of the middle BONG. -/
inductive LongRepresentationCertificate
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (i : LongRepresentationIndex (n + 1) (n + 1)) : Prop
  | throughPrevious
      (sourceToMiddle : DiagonalRepresents
        (c.prefixValues (i.val - 1) i.previous_le_sameRank)
        (b.prefixValues (i.val - 1) i.previous_le_sameRank))
      (middleToTarget : DiagonalRepresents
        (b.prefixValues (i.val - 1) i.previous_le_sameRank)
        (a.prefixValues (i.val + 1) i.next_le_sameRank))
  | throughCurrent
      (sourceToMiddle : DiagonalRepresents
        (c.prefixValues (i.val - 1) i.previous_le_sameRank)
        (b.prefixValues i.val i.current_le_sameRank))
      (middleToTarget : DiagonalRepresents
        (b.prefixValues i.val i.current_le_sameRank)
        (a.prefixValues (i.val + 1) i.next_le_sameRank))
  | throughNext
      (sourceToMiddle : DiagonalRepresents
        (c.prefixValues (i.val - 1) i.previous_le_sameRank)
        (b.prefixValues (i.val + 1) i.next_le_sameRank))
      (middleToTarget : DiagonalRepresents
        (b.prefixValues (i.val + 1) i.next_le_sameRank)
        (a.prefixValues (i.val + 1) i.next_le_sameRank))
  | direct
      (representation : DiagonalRepresents
        (c.prefixValues (i.val - 1) i.previous_le_sameRank)
        (a.prefixValues (i.val + 1) i.next_le_sameRank))

namespace LongRepresentationCertificate

/-- Every long certificate produces the representation required by
condition (iv). -/
theorem represents
    {a : GoodBONG q L (n + 1)} {b : GoodBONG r M (n + 1)}
    {c : GoodBONG s N (n + 1)}
    {i : LongRepresentationIndex (n + 1) (n + 1)}
    (certificate : LongRepresentationCertificate a b c i) :
    DiagonalRepresents
      (c.prefixValues (i.val - 1) i.previous_le_sameRank)
      (a.prefixValues (i.val + 1) i.next_le_sameRank) := by
  cases certificate with
  | throughPrevious sourceToMiddle middleToTarget =>
      exact sourceToMiddle.trans middleToTarget
  | throughCurrent sourceToMiddle middleToTarget =>
      exact sourceToMiddle.trans middleToTarget
  | throughNext sourceToMiddle middleToTarget =>
      exact sourceToMiddle.trans middleToTarget
  | direct representation => exact representation

end LongRepresentationCertificate

/-- The Section 4 case analysis for condition (iv), as explicit prefix
factorizations through the middle BONG. -/
structure SectionFourLongCertificates
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1)) : Prop where
  certificate (i : LongRepresentationIndex (n + 1) (n + 1)) :
    a.LongRepresentationTrigger c i → LongRepresentationCertificate a b c i

theorem longRepresentationConditions_trans_of_certificates
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hcert : SectionFourLongCertificates a b c) :
    a.LongRepresentationConditions c := by
  rw [a.longRepresentationConditions_iff_forall_trigger c]
  intro i htrigger
  exact (hcert.certificate i htrigger).represents

/-! ## Assembly of the four-condition package -/

/-- All local outputs of the Section 4 case analysis that are not already
contained in the two source four-condition packages. -/
structure SectionFourTransitivityData
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1)) : Prop where
  keyLemma : SectionFourKeyLemmaBounds a b c
  defectReduction : SectionFourDefectReduction a b c
  central : SectionFourCentralCertificates a b c
  long : SectionFourLongCertificates a b c

/-- Section 4's transitivity theorem at equal rank, once its explicit local
key-lemma, reduction, parity, and factorization certificates are supplied. -/
theorem representationConditions_trans_sameRank
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (c : GoodBONG s N (n + 1))
    (hab : RepresentationConditions a b le_rfl)
    (hbc : RepresentationConditions b c le_rfl)
    (data : SectionFourTransitivityData a b c) :
    RepresentationConditions a c le_rfl where
  orderCondition :=
    a.representationOrderCondition_trans b c le_rfl le_rfl
      hab.orderCondition hbc.orderCondition
  defectCondition :=
    a.representationDefectCondition_trans_of_keyLemma b c
      hab.defectCondition hbc.defectCondition data.keyLemma
      data.defectReduction
  centralRepresentations :=
    a.centralRepresentationConditions_trans_of_certificates b c data.central
  longRepresentations :=
    a.longRepresentationConditions_trans_of_certificates b c data.long

end BONG.GoodBONG

end Bong
