/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019IntermediateReduction
import Bong.Bong.Beli2019Lemma71Index
import Bong.Bong.Beli2019Lemma79CentralCommonSuffix
import Bong.Bong.Beli2019Lemma79CentralAssembly
import Bong.Bong.Beli2019Lemma79CentralDifferencePrefix
import Bong.Bong.Beli2019Lemma79Conditions
import Bong.Bong.Beli2019Lemma79LongExceptional
import Bong.Bong.Beli2019Lemma79OrderAssembled
import Bong.Bong.Beli2019Necessity
import Bong.Bong.GoodExistence

/-!
# Section 7: the strict first-gap reduction core

When the first gap is strictly larger than `-2e`, Lemma 7.1 constructs the
index-`p` lattice of non-norm-generators.  This file chooses an actual good
BONG of that lattice and assembles every part of Lemma 7.9 already proved:
the literal inclusion, its four conditions relative to the old target,
the volume jump, strict norm-ideal decrease, the normalized three-profile
classification, and condition (i) relative to the source.

The profile-specific difference prefix, the first common boundary, the common
suffix, and the long-prefix clause are all assembled internally.  Thus the
strict Section 7 reduction no longer takes a temporary Lemma 7.9(iii)
certificate family as an input.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L N : Lattice K V} {n : Nat}

variable [BeliCorollary44Laws.{u, v} K]

/-- A chosen good BONG of the literal lattice constructed in Lemma 7.1. -/
noncomputable def Beli2019Lemma71Data.goodBONG
    [BONGStructuralLaws.{u, v} K]
    {a : GoodBONG q L (n + 2)} (D : Beli2019Lemma71Data a) :
    GoodBONG q D.lattice (n + 2) :=
  (GoodBONG.ofLattice q D.lattice).castLength
    a.toBONG.length_eq_finrank.symm

/-- Every nonempty BONG of the non-norm-generator lattice has strictly
smaller norm ideal than the original lattice. -/
theorem Beli2019Lemma71Data.normIdeal_lt
    {a : GoodBONG q L (n + 2)} (D : Beli2019Lemma71Data a)
    (b : GoodBONG q D.lattice (n + 2)) :
    Lattice.normIdeal q D.lattice < Lattice.normIdeal q L := by
  have hle : Lattice.normIdeal q D.lattice ≤
      Lattice.normIdeal q L :=
    Lattice.normIdeal_mono q D.indexP.lattice_le
  have hne : Lattice.normIdeal q D.lattice ≠
      Lattice.normIdeal q L := by
    intro heq
    let x : V := b.toBONG.head
    have hxGeneratorL : Lattice.IsNormGenerator q L x := by
      refine ⟨D.indexP.lattice_le b.toBONG.head_isNormGenerator.mem, ?_⟩
      exact heq.symm.trans b.toBONG.head_isNormGenerator.normIdeal_eq
    have hxMem : x ∈ D.lattice := b.toBONG.head_isNormGenerator.mem
    rw [D.lattice_eq, Lattice.mem_nonNormGeneratorLattice_iff] at hxMem
    exact hxMem.2 hxGeneratorL
  exact lt_of_le_of_ne hle hne

/-- The index-`p` certificate is exactly the full-prefix order-sum jump used
in Lemma 7.9. -/
theorem Beli2019Lemma71Data.fullPrefixSum_eq
    {a : GoodBONG q L (n + 2)} (D : Beli2019Lemma71Data a)
    (b : GoodBONG q D.lattice (n + 2)) :
    a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2) := by
  have hvolume := D.indexPInclusion.volumeOrder_eq
  rw [← a.orderPrefixSum_full_eq_volumeOrder,
    ← b.orderPrefixSum_full_eq_volumeOrder] at hvolume
  simpa only [orderPrefixSum] using hvolume.symm

/-- All strict-gap reduction data except the two prefix-representation
clauses of Lemma 7.9(iii),(iv). -/
structure Beli2019SectionSevenStrictCore
    (a : GoodBONG q L (n + 2)) (c : GoodBONG q N (n + 2)) where
  lemma71 : Beli2019Lemma71Data a
  targetBONG : GoodBONG q lemma71.lattice (n + 2)
  inclusion : Beli2019IndexPInclusion q L lemma71.lattice
  targetConditions : RepresentationConditions a targetBONG le_rfl
  fullPrefixSum : a.orderSequence.prefixSum (n + 2) + 2 =
    targetBONG.orderSequence.prefixSum (n + 2)
  targetNorm_lt : Lattice.normIdeal q lemma71.lattice <
    Lattice.normIdeal q L
  sourceNorm_lt : Lattice.normIdeal q N < Lattice.normIdeal q L
  initialGap : -(2 * (ramificationIndex K : Int)) <
    a.orderGap ⟨0, by omega⟩
  normalized : Lemma79NormalizedClassification a targetBONG
  targetSourceOrder :
    targetBONG.RepresentationOrderCondition c le_rfl

/-- Lemmas 7.1 and 7.9(i),(ii-arithmetic setup) construct the strict
reduction core from the printed first-gap hypothesis. -/
noncomputable def beli2019SectionSevenStrictCore
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [PerfectResidueFieldLaws K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [Beli2019SectionFiveLaws.{u, v} K]
    [Beli2019SectionFourLaws.{u, v} K]
    (a : GoodBONG q L (n + 2)) (c : GoodBONG q N (n + 2))
    (hac : RepresentationConditions a c le_rfl)
    (hgap : a.order 1 - a.order 0 ≠
      -(2 * (ramificationIndex K : Int)))
    (hnormAC : Lattice.normIdeal q N < Lattice.normIdeal q L) :
    Beli2019SectionSevenStrictCore a c := by
  let D := beli2019Lemma71 a hgap
  let b := D.goodBONG
  have hab : RepresentationConditions a b le_rfl :=
    a.representationConditions_of_lattice_le b D.indexP.lattice_le
  have htotal : a.orderSequence.prefixSum (n + 2) + 2 =
      b.orderSequence.prefixSum (n + 2) :=
    D.fullPrefixSum_eq b
  have hnormAB : Lattice.normIdeal q D.lattice <
      Lattice.normIdeal q L := D.normIdeal_lt b
  have hinitial : -(2 * (ramificationIndex K : Int)) <
      a.orderGap ⟨0, by omega⟩ := by
    have hstrict := (a.strictScaleBound_iff_firstGap_gt_negTwoE).1
      (a.strictScaleBound_of_firstGap_ne_negTwoE hgap)
    let i0 : Fin (n + 1) := ⟨0, by omega⟩
    have hsucc : i0.succ = (1 : Fin (n + 2)) := by
      apply Fin.ext
      simp [i0]
    have hcastSucc : i0.castSucc = (0 : Fin (n + 2)) := by
      apply Fin.ext
      simp [i0]
    change -(2 * (ramificationIndex K : Int)) <
      a.order i0.succ - a.order i0.castSucc
    rw [hsucc, hcastSucc]
    exact hstrict
  have hnormalized : Lemma79NormalizedClassification a b :=
    beli2019Lemma79_normalizedClassification a b
      hab.orderCondition hab.defectCondition htotal hnormAB hinitial
  have horderBC : b.RepresentationOrderCondition c le_rfl :=
    beli2019Lemma79_i_of_normalizedClassification a b c hnormalized
      hab.orderCondition hac.orderCondition hab.defectCondition
      hac.defectCondition hinitial hnormAC
  exact {
    lemma71 := D
    targetBONG := b
    inclusion := D.indexPInclusion
    targetConditions := hab
    fullPrefixSum := htotal
    targetNorm_lt := hnormAB
    sourceNorm_lt := hnormAC
    initialGap := hinitial
    normalized := hnormalized
    targetSourceOrder := horderBC }

namespace Beli2019SectionSevenStrictCore

variable {a : GoodBONG q L (n + 2)} {c : GoodBONG q N (n + 2)}

/-- Lemma 7.9(ii) is independent of the still-missing output clauses
(iii),(iv), so expose it for constructing their pointwise certificates. -/
theorem defectCondition
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [PerfectResidueFieldLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    [DyadicUnramifiedNormLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    (E : Beli2019SectionSevenStrictCore a c)
    (hac : RepresentationConditions a c le_rfl) :
    E.targetBONG.RepresentationDefectCondition c :=
  beli2019Lemma79_ii_of_normalizedClassification
    a E.targetBONG c E.normalized E.targetConditions.orderCondition
      E.targetConditions.defectCondition E.targetConditions.centralRepresentations
      hac.orderCondition hac.defectCondition hac.centralRepresentations
      E.targetSourceOrder E.sourceNorm_lt E.fullPrefixSum

/-- Lemma 7.9(iv) follows from the normalized type-I/II/III classification;
there is no additional long-prefix hypothesis in the strict reduction. -/
theorem longRepresentationConditions
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [QuadraticDefectLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DyadicDiagonalCodimensionTwoLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    (E : Beli2019SectionSevenStrictCore a c)
    (hac : RepresentationConditions a c le_rfl) :
    E.targetBONG.LongRepresentationConditions c :=
  E.normalized.longRepresentationConditions E.targetConditions hac
    E.sourceNorm_lt E.fullPrefixSum

/-- Lemma 7.9(iii) on every nonterminal boundary strictly beyond the last
unequal order.  Cases 4 and 10 are selected internally by Lemma 2.18. -/
theorem centralCertificate_of_strictCommonSuffix
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [PerfectResidueFieldLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    [DyadicUnramifiedNormLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    (E : Beli2019SectionSevenStrictCore a c)
    (hac : RepresentationConditions a c le_rfl)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hiNext : i.val + 1 < n + 2)
    (htail : E.normalized.IsStrictCommonSuffixAt i)
    (htrigger : E.targetBONG.centralAlphaTrigger c i) :
    Lemma79CentralCertificate a E.targetBONG c i :=
  E.normalized.centralCertificate_of_strictCommonSuffix
    E.targetConditions hac E.targetSourceOrder (E.defectCondition hac)
      i hiNext htail htrigger

/-- Lemma 7.9(iii) at the terminal boundary strictly beyond the last
unequal order.  The complete target prefix replaces the unavailable next
central index in the second Lemma 2.18 alternative. -/
theorem centralCertificate_of_strictCommonSuffix_endpoint
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [PerfectResidueFieldLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    [DyadicUnramifiedNormLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    (E : Beli2019SectionSevenStrictCore a c)
    (hac : RepresentationConditions a c le_rfl)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hfull : i.val + 1 = n + 2)
    (htail : E.normalized.IsStrictCommonSuffixAt i)
    (htrigger : E.targetBONG.centralAlphaTrigger c i) :
    Lemma79CentralCertificate a E.targetBONG c i :=
  E.normalized.centralCertificate_of_strictCommonSuffix_endpoint
    E.targetConditions hac E.targetSourceOrder (E.defectCondition hac)
      i hfull htail htrigger

/-- Lemma 7.9(iii) at the first common boundary, nonterminal form.  The
type-I/II/III boundary-alpha estimate is selected internally. -/
theorem centralCertificate_of_firstCommonBoundary
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [PerfectResidueFieldLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    [DyadicUnramifiedNormLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    (E : Beli2019SectionSevenStrictCore a c)
    (hac : RepresentationConditions a c le_rfl)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hiNext : i.val + 1 < n + 2)
    (hboundary : E.normalized.IsFirstCommonBoundaryAt i)
    (htrigger : E.targetBONG.centralAlphaTrigger c i) :
    Lemma79CentralCertificate a E.targetBONG c i :=
  E.normalized.centralCertificate_of_firstCommonBoundary
    E.targetConditions hac E.targetSourceOrder (E.defectCondition hac)
      E.fullPrefixSum i hiNext hboundary htrigger

/-- Lemma 7.9(iii) at a terminal first common boundary. -/
theorem centralCertificate_of_firstCommonBoundary_endpoint
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [PerfectResidueFieldLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    [DyadicUnramifiedNormLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    (E : Beli2019SectionSevenStrictCore a c)
    (hac : RepresentationConditions a c le_rfl)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hfull : i.val + 1 = n + 2)
    (hboundary : E.normalized.IsFirstCommonBoundaryAt i)
    (htrigger : E.targetBONG.centralAlphaTrigger c i) :
    Lemma79CentralCertificate a E.targetBONG c i :=
  E.normalized.centralCertificate_of_firstCommonBoundary_endpoint
    E.targetConditions hac E.targetSourceOrder (E.defectCondition hac)
      E.fullPrefixSum i hfull hboundary htrigger

/-- The central condition now needs certificates only on the finite
difference prefix; the first common boundary and the entire suffix are
filled by the proved profile-independent assembly. -/
theorem centralRepresentationConditions_of_differencePrefix
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [PerfectResidueFieldLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    [DyadicUnramifiedNormLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    (E : Beli2019SectionSevenStrictCore a c)
    (hac : RepresentationConditions a c le_rfl)
    (hprefix : Lemma79DifferencePrefixCentralCertificates
      a E.targetBONG c E.normalized) :
    E.targetBONG.CentralRepresentationConditions c :=
  centralRepresentationConditions_of_lemma79Certificates
    a E.targetBONG c
      (E.normalized.centralCertificates_of_differencePrefix
        E.targetConditions hac E.targetSourceOrder (E.defectCondition hac)
          E.fullPrefixSum hprefix)

/-- Fidelity-preserving form of the preceding reduction: the finite prefix
may use either Lemma 1.5 or the direct endpoint-tower argument printed in the
paper. -/
theorem centralRepresentationConditions_of_differencePrefixWitnesses
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [PerfectResidueFieldLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    [DyadicUnramifiedNormLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    (E : Beli2019SectionSevenStrictCore a c)
    (hac : RepresentationConditions a c le_rfl) :
    E.targetBONG.CentralRepresentationConditions c :=
  centralRepresentationConditions_of_lemma79Witnesses
    a E.targetBONG c
      (E.normalized.centralWitnesses_of_differencePrefix
        E.targetConditions hac E.targetSourceOrder (E.defectCondition hac)
          E.fullPrefixSum
          (E.normalized.differencePrefixCentralWitnesses
            E.targetConditions hac E.targetSourceOrder (E.defectCondition hac)
              E.sourceNorm_lt E.fullPrefixSum))

/-- Once Lemma 7.9(iii),(iv) are supplied, the existing pointwise proof of
Lemma 7.9(ii) completes all four original conditions. -/
theorem representationConditions
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [QuadraticDefectLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DyadicDiagonalCodimensionTwoLaws K]
    [PerfectResidueFieldLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    [DyadicUnramifiedNormLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    (E : Beli2019SectionSevenStrictCore a c)
    (hac : RepresentationConditions a c le_rfl)
    (hcentral : E.targetBONG.CentralRepresentationConditions c) :
    RepresentationConditions E.targetBONG c le_rfl :=
  beli2019Lemma79_representationConditions a E.targetBONG c E.normalized
    E.targetConditions hac E.targetSourceOrder hcentral
      (E.longRepresentationConditions hac)
      E.sourceNorm_lt E.fullPrefixSum

/-- The strict branch in the exact proof architecture of Lemma 7.9:
condition (iii) is supplied by one of the two explicit Lemma 1.5 diagrams at
every active boundary, while condition (iv) remains the independent long
prefix obligation. -/
theorem representationConditions_of_centralCertificates
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [QuadraticDefectLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DyadicDiagonalCodimensionTwoLaws K]
    [PerfectResidueFieldLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    [DyadicUnramifiedNormLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    (E : Beli2019SectionSevenStrictCore a c)
    (hac : RepresentationConditions a c le_rfl)
    (hcentral : Lemma79CentralCertificates a E.targetBONG c) :
    RepresentationConditions E.targetBONG c le_rfl :=
  E.representationConditions hac
    (centralRepresentationConditions_of_lemma79Certificates
      a E.targetBONG c hcentral)

/-- Strict Section 7 reduction with only the unresolved difference-prefix
part of Lemma 7.9(iii) supplied. -/
theorem representationConditions_of_differencePrefix
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [QuadraticDefectLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DyadicDiagonalCodimensionTwoLaws K]
    [PerfectResidueFieldLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    [DyadicUnramifiedNormLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    (E : Beli2019SectionSevenStrictCore a c)
    (hac : RepresentationConditions a c le_rfl)
    (hprefix : Lemma79DifferencePrefixCentralCertificates
      a E.targetBONG c E.normalized) :
    RepresentationConditions E.targetBONG c le_rfl :=
  E.representationConditions hac
    (E.centralRepresentationConditions_of_differencePrefix hac hprefix)

/-- Strict Section 7 reduction with all ten printed central cases selected
internally from the normalized profile. -/
theorem representationConditions_of_differencePrefixWitnesses
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [QuadraticDefectLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DyadicDiagonalCodimensionTwoLaws K]
    [PerfectResidueFieldLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    [DyadicUnramifiedNormLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    (E : Beli2019SectionSevenStrictCore a c)
    (hac : RepresentationConditions a c le_rfl) :
    RepresentationConditions E.targetBONG c le_rfl :=
  E.representationConditions hac
    (E.centralRepresentationConditions_of_differencePrefixWitnesses
      hac)

/-- The completed strict core is the concrete index-`p` reduction expected
by the common-space recursive problem. -/
noncomputable def indexPReduction
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [QuadraticDefectLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DyadicDiagonalCodimensionTwoLaws K]
    [PerfectResidueFieldLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    [DyadicUnramifiedNormLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    (E : Beli2019SectionSevenStrictCore a c)
    (hac : RepresentationConditions a c le_rfl) :
    Beli2019RepresentationProblem.IndexPReduction
      (Beli2019RepresentationProblem.ofData a c le_rfl
        (QuadraticSpace.represents_refl q) hac) where
  index_eq := rfl
  lattice := E.lemma71.lattice
  inclusion := E.inclusion
  targetBONG := E.targetBONG
  conditions := E.representationConditions_of_differencePrefixWitnesses hac

end Beli2019SectionSevenStrictCore

end BONG.GoodBONG

end Bong
