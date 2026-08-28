/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma79PointwiseComplete
import Bong.Bong.Beli2019MainConditions

/-!
# Beli (2019), Lemma 7.9: connection with Theorem 2.1

The three-profile proof of Lemma 7.9(ii) supplies the defect field of the
four-condition packages in Theorem 2.1.  These assembly theorems make the
remaining obligations explicit: Condition (i), Condition (iii) (or v2's
Condition (iii')), and Condition (iv).
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Lemma 7.9(ii), together with the other three verified obligations,
constructs the original four-condition package of Theorem 2.1. -/
theorem beli2019Lemma79_representationConditions
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [PerfectResidueFieldLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    [DyadicUnramifiedNormLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma79NormalizedClassification a b)
    (hab : RepresentationConditions a b le_rfl)
    (hac : RepresentationConditions a c le_rfl)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hcentralBC : b.CentralRepresentationConditions c)
    (hlongBC : b.LongRepresentationConditions c)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2)) :
    RepresentationConditions b c le_rfl := by
  refine {
    orderCondition := horderBC
    defectCondition := ?_
    centralRepresentations := hcentralBC
    longRepresentations := hlongBC }
  exact beli2019Lemma79_ii_of_normalizedClassification
    a b c D hab.orderCondition hab.defectCondition
      hab.centralRepresentations hac.orderCondition hac.defectCondition
      hac.centralRepresentations horderBC hnorm htotal

/-- The revised-v2 form of the preceding assembly.  Lemma 2.16 converts
Condition (iii') to the original trigger exactly where the type-I part of
Lemma 7.9(ii) uses it, and converts the completed package back to v2 form. -/
theorem beli2019Lemma79_representationConditionsPrime
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [PerfectResidueFieldLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    [DyadicUnramifiedNormLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma79NormalizedClassification a b)
    (hab : RepresentationConditions a b le_rfl)
    (hac : RepresentationConditions a c le_rfl)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (hcentralBC : b.CentralRepresentationConditionsPrime c)
    (hlongBC : b.LongRepresentationConditions c)
    (htriggerBC : b.CentralTriggerEquivalence c)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2)) :
    RepresentationConditionsPrime b c le_rfl := by
  have hcentralBCOriginal : b.CentralRepresentationConditions c :=
    (b.centralRepresentationConditions_iff_prime c htriggerBC).mpr
      hcentralBC
  have hconditions := beli2019Lemma79_representationConditions
    a b c D hab hac horderBC hcentralBCOriginal hlongBC hnorm htotal
  exact (representationConditions_iff_prime b c le_rfl htriggerBC).mp
    hconditions

end BONG.GoodBONG

end Bong
