/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019MainTheorem
import Bong.Bong.Beli2019FinalStep
import Bong.Bong.Beli2019Lemma912SectionNine
import Bong.Bong.Beli2019Lemma81
import Bong.Bong.Beli2019Lemma82
import Bong.Bong.Beli2019Lemma82Unit
import Bong.Bong.Beli2019Lemma84
import Bong.Bong.Beli2019Lemma85
import Bong.Bong.Beli2019Lemma86
import Bong.Bong.Beli2019Remark87
import Bong.Bong.Beli2019Lemma88Statement
import Bong.Bong.Beli2019Lemma88Necessity
import Bong.Bong.Beli2019Lemma83
import Bong.Bong.Beli2019Lemma88Binary
import Bong.Bong.Beli2019Lemma88Tail
import Bong.Bong.Beli2019Lemma88Choice
import Bong.Bong.Beli2019Lemma88Induction
import Bong.Bong.Beli2019Lemma88Critical
import Bong.Bong.Beli2019Lemma88Quaternary
import Bong.Bong.Beli2019Lemma88ExceptionA
import Bong.Bong.Beli2019Lemma88Sufficiency
import Bong.Bong.Beli2019Corollary810
import Bong.Bong.Beli2019Corollary811
import Bong.Bong.Beli2019Lemma812
import Bong.Bong.Beli2019Lemma813
import Bong.Bong.Beli2019Lemma814Statement
import Bong.Bong.Beli2019Lemma814Invariants
import Bong.Bong.Beli2019Lemma814GeometricInvariants
import Bong.Bong.Beli2019Lemma814ComplementInvariants
import Bong.Bong.Beli2019Lemma814Necessity
import Bong.Bong.Beli2019Lemma814Complete
import Bong.Bong.Beli2019Lemma91OrderBranches
import Bong.Bong.Beli2019Lemma91SecondOrder
import Bong.Bong.Beli2019Lemma91ExceptionA
import Bong.Bong.Beli2019Lemma91ExceptionB
import Bong.Bong.Beli2019Lemma91ExceptionC
import Bong.Bong.Beli2019Lemma91
import Bong.Bong.Beli2019Lemma710SegmentDual
import Bong.Bong.Beli2019Lemma79Conditions
import Bong.Bong.Beli2019Lemma79OrderTypeIAssembled
import Bong.Bong.Beli2019Lemma79TypeIIIOverlapOrderComplete
import Bong.Bong.Beli2019Lemma79OrderTypeIIINonterminal
import Bong.Bong.Beli2019Lemma79RightTailGapOneTypeIIIComplete
import Bong.Bong.Beli2019Lemma69CappedPropagationRight
import Bong.Bong.Beli2019FullRankDefect
import Bong.Bong.Beli2019Lemma69TypeIRightComplete
import Bong.Bong.Beli2019Lemma77TypeINonterminal
import Bong.Bong.Beli2019Lemma78Arithmetic
import Bong.Bong.Beli2019DefectDual
import Bong.Bong.Beli2019RepresentationAlphaDual
import Bong.Bong.Beli2019DefectConditionDual
import Bong.Bong.Beli2019OrderConditionDual
import Bong.Bong.Beli2019Lemma78Dual
import Bong.Bong.Beli2019Lemma78Defect
import Bong.Bong.Beli2019Lemma69TypeIIISecondary
import Bong.Bong.Beli2019Lemma69TypeIIIPrimary
import Bong.Bong.Beli2019Lemma78AlphaZero
import Bong.Bong.Beli2019CappedDefectSharp
import Bong.Bong.Beli2019Lemma78PrefixDefect
import Bong.Bong.Beli2019Lemma78TailBound
import Bong.Bong.Beli2019Lemma78SourcePropagation
import Bong.Bong.Beli2019Lemma78TargetAlpha
import Bong.Bong.Beli2019Remark616
import Bong.Bong.Beli2019Lemma78PreviousAlpha
import Bong.Bong.Beli2019Lemma69TypeIIILeftValue
import Bong.Bong.Beli2019Lemma69TypeIIIRightValue
import Bong.Bong.Beli2019Lemma78TargetPropagation
import Bong.Bong.Beli2019Lemma71Index
import Bong.Bong.Beli2019Lemma73
import Bong.Bong.Beli2019Lemma75Splitting
import Bong.Bong.Beli2019Lemma75EndpointClass
import Bong.Bong.Beli2019Lemma75Models
import Bong.Bong.Beli2019Lemma75StandardModels
import Bong.Bong.Beli2019Lemma75
import Bong.Bong.Beli2019Lemma76Early
import Bong.Bong.Beli2019Lemma710Extension
import Bong.Bong.Beli2019Lemma710Orders
import Bong.Bong.Beli2019Lemma710OrthogonalSum
import Bong.Bong.Beli2019Lemma710ProjectionProduct
import Bong.Bong.Beli2019Lemma710BONGProduct
import Bong.Bong.Beli2019Lemma710PrefixProduct
import Bong.Bong.Beli2019Lemma710RightEnd
import Bong.Lattice.DualIsometry
import Bong.Lattice.OrthogonalDecompositionDual
import Bong.Bong.MaximalNormSplittingDual
import Bong.Bong.Beli2019Lemma710DualProduct
import Bong.Bong.Beli2019Lemma710Swap
import Bong.Bong.Beli2019Lemma710General
import Bong.Bong.Beli2019Lemma710TargetPrefix
import Bong.Bong.Beli2019Lemma711
import Bong.Bong.Beli2019Lemma76Boundary
import Bong.Bong.Beli2019Lemma76CanonicalBoundary
import Bong.Bong.Beli2019Lemma69TypeIWeight
import Bong.Bong.Beli2019IntervalRigidity
import Bong.Bong.Beli2019Lemma69TypeIInterval
import Bong.Bong.Beli2019WeightSegmentSum
import Bong.Bong.Beli2019Lemma69TypeISum
import Bong.Bong.Beli2019BoundaryRounding
import Bong.Bong.Beli2019Lemma69TypeIBoundary
import Bong.Bong.Beli2019Lemma69TypeINeighbor
import Bong.Bong.Beli2019Lemma69TypeIRightNeighbor
import Bong.Bong.Beli2019Lemma69TypeIPivot
import Bong.Bong.Beli2019Lemma69TypeIAlphaTail
import Bong.Bong.Beli2019Lemma714Plateau
import Bong.Bong.Beli2019Lemma714Types
import Bong.Bong.Beli2019Lemma714BoundaryOrders
import Bong.Bong.Beli2019Lemma66
import Bong.Bong.Beli2019Lemma65
import Bong.Bong.Beli2019Lemma67Classification
import Bong.Bong.Beli2019Lemma72TypeI
import Bong.Bong.Beli2019Lemma72TypeII
import Bong.Bong.Beli2019Lemma72TypeIII

/-!
# Beli 2019 paper entry point

This module is the review and distribution entry point for Constantin N. Beli,
*Representations of quadratic lattices over dyadic local fields* (2019), using
the frozen arXiv v2 revision dated 30 May 2022.
-/
