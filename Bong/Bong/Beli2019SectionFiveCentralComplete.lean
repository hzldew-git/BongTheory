/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFiveCentralUnaryShift

/-!
# Complete central certificates in Beli (2019), Section 5

This file assembles the aligned and adjacent-unary direct calculations and
then applies the swapped reverse-dual reduction to cover every central
boundary.
-/

namespace Bong

open Dyadic Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V}

namespace Lattice.Beli2019Lemma51Data

set_option maxHeartbeats 0 in
/-- Complete condition 2.1(iii) on Section 5's direct reduced range. -/
theorem centralCertificate_direct
    [DyadicDiscriminantClassLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hrange : D.CentralReducedRange i) :
    BONG.GoodBONG.Beli2019SectionFiveCentralCertificate a b i := by
  classical
  by_cases htrigger : a.centralAlphaTrigger b i
  · rcases D.rank_one_or_two with hOne | hTwo
    · rcases D.selectedPositions_unary_alternative hOne with
        hselected | ⟨i₀, ⟨hi₀, _hadjacent⟩, _hunique⟩
      · exact D.weakAligned_centralCertificate
          hselected a b hdefect i hrange htrigger
      · exact D.weakUnaryShift_centralCertificate
          hOne i₀ hi₀ a b hdefect i hrange htrigger
    · exact D.weakAligned_centralCertificate
        (D.selectedPositions_eq_of_rank_two hTwo)
          a b hdefect i hrange htrigger
  · exact .vacuous htrigger

set_option maxHeartbeats 0 in
/-- The complete pointwise Section 5 certificate for condition 2.1(iii).
Every boundary lies in the direct reduced range on the original side or at
the complementary boundary of the swapped reverse-dual inclusion. -/
theorem centralCertificate_complete
    [DyadicDiscriminantClassLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    {n : Nat} {a : BONG.GoodBONG q M (n + 2)}
    {b : BONG.GoodBONG q N (n + 2)}
    {inclusion : Beli2019IndexPInclusion q M N}
    (R : BONG.GoodBONG.Beli2019SectionFiveReverseDualData a b inclusion)
    (hdefect : a.RepresentationDefectCondition b)
    (hdualDefect :
      R.sourceDual.RepresentationDefectCondition R.targetDual)
    (i : CentralRepresentationIndex (n + 2) (n + 2)) :
    BONG.GoodBONG.Beli2019SectionFiveCentralCertificate a b i := by
  rcases D.centralReducedRange_or_reverseDualReducedRange R.lemma51 i
      a.toBONG.length_eq_finrank with hrange | hreverse
  · exact D.centralCertificate_direct a b hdefect i hrange
  · have Cdual := R.lemma51.centralCertificate_direct
      R.sourceDual R.targetDual hdualDefect
        i.reversePrevious hreverse
    exact R.originalCentralCertificate_of_reverse i Cdual

end Lattice.Beli2019Lemma51Data

end Bong
