/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79CentralCommonSuffix

/-!
# Beli (2019), Lemma 7.9(iii): reduction to the difference prefix

The profile-specific work in condition (iii) is needed only before the first
common boundary.  The boundary itself and every later index were proved in
`Beli2019Lemma79CentralCommonSuffix`.  This file packages that exhaustion, so
the remaining ten-case analysis has an exact domain: central indices at or
before the final unequal order coordinate.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Every normalized profile carries its final unequal order coordinate. -/
theorem Lemma79NormalizedClassification.exists_lastDifference
    {a : GoodBONG q L (n + 2)} {b : GoodBONG q M (n + 2)}
    (D : Lemma79NormalizedClassification a b) :
    ∃ last, BeliOrderSequence.IsLastDifferenceAt
      a.orderSequence b.orderSequence last := by
  cases D with
  | typeI E _ => exact ⟨E.profile.last, E.profile.lastDifference⟩
  | typeII E _ => exact ⟨E.outer.last, E.outer.lastDifference⟩
  | typeIII E _ _ => exact ⟨E.outer.last, E.outer.lastDifference⟩

/-- The unresolved part of Lemma 7.9(iii): the paper index lies no later
than the final unequal order coordinate. -/
def Lemma79NormalizedClassification.IsDifferencePrefixAt
    {a : GoodBONG q L (n + 2)} {b : GoodBONG q M (n + 2)}
    (_D : Lemma79NormalizedClassification a b)
    (i : CentralRepresentationIndex (n + 2) (n + 2)) : Prop :=
  ∃ last, BeliOrderSequence.IsLastDifferenceAt
      a.orderSequence b.orderSequence last ∧ i.val ≤ last

/-- Outside the difference prefix, an index is either the first common
boundary or belongs to the strict common suffix. -/
theorem Lemma79NormalizedClassification.firstBoundary_or_strictCommonSuffix
    {a : GoodBONG q L (n + 2)} {b : GoodBONG q M (n + 2)}
    (D : Lemma79NormalizedClassification a b)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hprefix : ¬ D.IsDifferencePrefixAt i) :
    D.IsFirstCommonBoundaryAt i ∨ D.IsStrictCommonSuffixAt i := by
  rcases D.exists_lastDifference with ⟨last, hlast⟩
  have hlastLt : last < i.val := by
    by_contra hnot
    exact hprefix ⟨last, hlast, Nat.le_of_not_gt hnot⟩
  by_cases hboundary : i.val = last + 1
  · exact Or.inl ⟨last, hlast, hboundary⟩
  · exact Or.inr ⟨last, hlast, by omega⟩

/-- All central certificates outside the finite difference prefix.  The
proof also handles the full-rank endpoint, where there is no following
central index. -/
theorem Lemma79NormalizedClassification.centralCertificate_of_not_differencePrefix
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    {a : GoodBONG q L (n + 2)} {b : GoodBONG q M (n + 2)}
    {c : GoodBONG q N (n + 2)}
    (D : Lemma79NormalizedClassification a b)
    (hab : RepresentationConditions a b le_rfl)
    (hac : RepresentationConditions a c le_rfl)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hdefectBC : b.RepresentationDefectCondition c)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hprefix : ¬ D.IsDifferencePrefixAt i)
    (htrigger : b.centralAlphaTrigger c i) :
    Lemma79CentralCertificate a b c i := by
  rcases D.firstBoundary_or_strictCommonSuffix i hprefix with
    hboundary | htail
  · by_cases hfull : i.val + 1 = n + 2
    · exact D.centralCertificate_of_firstCommonBoundary_endpoint
        hab hac horderBC hdefectBC htotal i hfull hboundary htrigger
    · have hiNext : i.val + 1 < n + 2 := by
        have := i.lt_large
        omega
      exact D.centralCertificate_of_firstCommonBoundary
        hab hac horderBC hdefectBC htotal i hiNext hboundary htrigger
  · by_cases hfull : i.val + 1 = n + 2
    · exact D.centralCertificate_of_strictCommonSuffix_endpoint
        hab hac horderBC hdefectBC i hfull htail htrigger
    · have hiNext : i.val + 1 < n + 2 := by
        have := i.lt_large
        omega
      exact D.centralCertificate_of_strictCommonSuffix
        hab hac horderBC hdefectBC i hiNext htail htrigger

/-- The still-local part of the ten-case proof, isolated without introducing
a typeclass or an opaque local-field law. -/
structure Lemma79DifferencePrefixCentralCertificates
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma79NormalizedClassification a b) : Prop where
  certificate (i : CentralRepresentationIndex (n + 2) (n + 2)) :
    D.IsDifferencePrefixAt i →
      b.centralAlphaTrigger c i → Lemma79CentralCertificate a b c i

/-- The exact local obligation left by the paper: on the finite difference
prefix one may supply either a Lemma 1.5 certificate or one of the direct
endpoint-tower representations used in cases 1 and 5. -/
structure Lemma79DifferencePrefixCentralWitnesses
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma79NormalizedClassification a b) : Prop where
  witness (i : CentralRepresentationIndex (n + 2) (n + 2)) :
    D.IsDifferencePrefixAt i →
      b.centralAlphaTrigger c i → Lemma79CentralWitness a b c i

/-- Completing the difference-prefix cases is sufficient for the complete
certificate family; the common boundary and suffix are inserted
automatically. -/
theorem Lemma79NormalizedClassification.centralCertificates_of_differencePrefix
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    {a : GoodBONG q L (n + 2)} {b : GoodBONG q M (n + 2)}
    {c : GoodBONG q N (n + 2)}
    (D : Lemma79NormalizedClassification a b)
    (hab : RepresentationConditions a b le_rfl)
    (hac : RepresentationConditions a c le_rfl)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hdefectBC : b.RepresentationDefectCondition c)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (hprefix : Lemma79DifferencePrefixCentralCertificates a b c D) :
    Lemma79CentralCertificates a b c := by
  refine ⟨?_⟩
  intro i htrigger
  by_cases hi : D.IsDifferencePrefixAt i
  · exact hprefix.certificate i hi htrigger
  · exact D.centralCertificate_of_not_differencePrefix
      hab hac horderBC hdefectBC htotal i hi htrigger

/-- Completing the finite prefix with either of the two proof routes is
sufficient for condition (iii); the common boundary and suffix are inserted
as Lemma 1.5 witnesses automatically. -/
theorem Lemma79NormalizedClassification.centralWitnesses_of_differencePrefix
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    {a : GoodBONG q L (n + 2)} {b : GoodBONG q M (n + 2)}
    {c : GoodBONG q N (n + 2)}
    (D : Lemma79NormalizedClassification a b)
    (hab : RepresentationConditions a b le_rfl)
    (hac : RepresentationConditions a c le_rfl)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hdefectBC : b.RepresentationDefectCondition c)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2))
    (hprefix : Lemma79DifferencePrefixCentralWitnesses a b c D) :
    Lemma79CentralWitnesses a b c := by
  refine ⟨?_⟩
  intro i htrigger
  by_cases hi : D.IsDifferencePrefixAt i
  · exact hprefix.witness i hi htrigger
  · exact .viaCertificate (D.centralCertificate_of_not_differencePrefix
      hab hac horderBC hdefectBC htotal i hi htrigger)

end BONG.GoodBONG

end Bong
