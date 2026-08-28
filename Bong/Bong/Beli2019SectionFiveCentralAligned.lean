/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFiveCentralCollisionLeft

/-!
# Aligned direct central representations in Beli (2019), Section 5

This file assembles the complete direct central certificate when the selected
weak component has the same position on the source and target sides.  Targets
before the selected block are split into the ordinary and collision-left
resolutions; targets in the selected block are split by its unary/binary rank.
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
/-- Complete Section 5's direct central-representation certificate in the
weak-aligned case. -/
theorem weakAligned_centralCertificate
    [DyadicDiscriminantClassLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hrange : D.CentralReducedRange i)
    (htrigger : a.centralAlphaTrigger b i) :
    BONG.GoodBONG.Beli2019SectionFiveCentralCertificate a b i := by
  classical
  have hpositions := D.weakAligned_central_strict_source_and_target_position
    hselected a b i hrange
  rcases hpositions.2 with htargetBefore | ⟨htargetSelected, htargetLocal⟩
  · by_cases hcollisionLeft : ∃ c : Fin D.complementComponentCount,
        ordUnit K (D.complementStrictWeak.scaleGenerator c) =
            ordUnit K D.input.block.enlargedScaleGenerator ∧
          ((D.largeWeakProfileWitness a).indexEquiv
            (⟨i.val - 1, by have := i.lt_large; omega⟩ :
              Fin (n + 2))).1 = D.largeCommonPosition c
    · obtain ⟨c, hscale, hposition⟩ := hcollisionLeft
      exact D.weakAligned_centralCertificate_of_collisionLeft
        hselected c hscale a b hdefect i htrigger htargetBefore hposition
    · exact D.weakAligned_centralCertificate_before_of_notCollisionLeft
        hselected a b hdefect i hrange htrigger htargetBefore hcollisionLeft
  · rcases D.rank_one_or_two with hOne | hTwo
    · exact D.weakAligned_centralCertificate_of_targetSelected_rank_one
        hselected a b hdefect i htrigger hOne htargetSelected htargetLocal
    · exact D.weakAligned_centralCertificate_of_targetSelected_rank_two
        hselected a b hdefect i htrigger hTwo htargetSelected htargetLocal

end Lattice.Beli2019Lemma51Data

end Bong
