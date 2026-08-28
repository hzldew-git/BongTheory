/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFiveCentralTernary

/-!
# Ordinary aligned central representation cases in Beli (2019), Section 5

This file assembles all direct aligned cases for which the target coordinate
does not lie in the left member of the unique large-side scale collision.
The endpoint alternatives are exactly the three cases isolated in Section
5.14: source penultimate/target last, source last/target first, and the
proper ternary exception.
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
/-- Complete the ordinary target-before-selected part of the aligned direct
range.  The only excluded coordinate is the left member of the unique
large-side collision; that amalgamation boundary is treated separately. -/
theorem weakAligned_centralCertificate_before_of_notCollisionLeft
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
    (htrigger : a.centralAlphaTrigger b i)
    (htargetBefore :
      ((D.largeWeakProfileWitness a).indexEquiv
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 <
          D.largeSelectedPosition)
    (hnotCollisionLeft : ¬ ∃ c : Fin D.complementComponentCount,
      ordUnit K (D.complementStrictWeak.scaleGenerator c) =
          ordUnit K D.input.block.enlargedScaleGenerator ∧
        ((D.largeWeakProfileWitness a).indexEquiv
          (⟨i.val - 1, by have := i.lt_large; omega⟩ :
            Fin (n + 2))).1 = D.largeCommonPosition c) :
    BONG.GoodBONG.Beli2019SectionFiveCentralCertificate a b i := by
  classical
  let gTarget : Fin (n + 1) := ⟨i.val - 1, by
    have := i.lt_large
    omega⟩
  let gSource : Fin (n + 1) := ⟨i.val - 2, by
    have := i.lt_large
    omega⟩
  let ITarget : Fin (n + 2) := gTarget.castSucc
  let ISource : Fin (n + 2) := gSource.castSucc
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  have hpositions := D.weakAligned_central_strict_source_and_target_position
    hselected a b i hrange
  have hsourceBefore : (y.indexEquiv ISource).1 <
      D.smallSelectedPosition := by
    simpa only [y, ISource, gSource] using hpositions.1
  have htri := D.weakAligned_central_endpoint_pair_trichotomy
    hselected a b hdefect i hrange htrigger htargetBefore hnotCollisionLeft
  rcases htri with hsourcePenultimate | htargetFirst | hternary
  · by_cases hindex : i.val = 2
    · have hsourceBefore' :
          ((D.smallWeakProfileWitness b).indexEquiv
            (⟨i.val - 2, by have := i.lt_large; omega⟩ :
              Fin (n + 2))).1 < D.smallSelectedPosition := by
        simpa only [y, ISource, gSource, Fin.castSucc_mk] using hsourceBefore
      have hcoordinatesInput :
          let ITarget' : Fin (n + 2) := ⟨i.val - 1, by
            have := i.lt_large
            omega⟩
          ((D.largeWeakProfileWitness a).indexEquiv ITarget').1 =
              ((D.smallWeakProfileWitness b).indexEquiv ITarget').1 ∧
            ((D.largeWeakProfileWitness a).indexEquiv ITarget').2.val =
              ((D.smallWeakProfileWitness b).indexEquiv ITarget').2.val := by
        simpa only [ITarget, gTarget, Fin.castSucc_mk] using
          D.weakProfile_coordinates_eq hselected a b ITarget
      have htargetRankEq :
          let ITarget' : Fin (n + 2) := ⟨i.val - 1, by
            have := i.lt_large
            omega⟩
          finrank K (D.largeAlmostJordan.component
              ((D.largeWeakProfileWitness a).indexEquiv ITarget').1).carrier =
            finrank K (D.smallAlmostJordan.component
              ((D.largeWeakProfileWitness a).indexEquiv ITarget').1).carrier := by
        dsimp only
        exact congrFun (D.almostJordan_componentRank_eq hselected)
          ((D.largeWeakProfileWitness a).indexEquiv
            (⟨i.val - 1, by have := i.lt_large; omega⟩ :
              Fin (n + 2))).1
      have hrightOuter :=
        D.weakAligned_source_rightTwoStep_lt_of_penultimate
          hselected a b i htrigger hsourceBefore' hsourcePenultimate.1
      have hprefixCarrier :
          let ISource' : Fin (n + 2) := ⟨i.val - 2, by
            have := i.lt_large
            omega⟩
          D.largeAlmostJordan.toOrthogonalDecomposition.prefixCarrier
              (((D.smallWeakProfileWitness b).indexEquiv ISource').1.val + 1) =
            D.smallAlmostJordan.toOrthogonalDecomposition.prefixCarrier
              (((D.smallWeakProfileWitness b).indexEquiv ISource').1.val + 1) := by
        dsimp only
        exact D.aligned_prefixCarrier_eq hselected _
      exact D.centralCertificate_of_sourcePenultimate_of_notCollision_at_two_of_prefixAlignment
        a b hdefect i htrigger hindex hsourceBefore' htargetBefore
          hcoordinatesInput htargetRankEq hrightOuter hprefixCarrier
            hsourcePenultimate.1 hnotCollisionLeft
    · have hthree : 3 ≤ i.val := by
        have := i.one_lt
        omega
      have hsourceBefore' :
          ((D.smallWeakProfileWitness b).indexEquiv
            (⟨i.val - 2, by have := i.lt_large; omega⟩ :
              Fin (n + 2))).1 < D.smallSelectedPosition := by
        simpa only [y, ISource, gSource, Fin.castSucc_mk] using hsourceBefore
      have hcoordinatesInput :
          let ITarget' : Fin (n + 2) := ⟨i.val - 1, by
            have := i.lt_large
            omega⟩
          ((D.largeWeakProfileWitness a).indexEquiv ITarget').1 =
              ((D.smallWeakProfileWitness b).indexEquiv ITarget').1 ∧
            ((D.largeWeakProfileWitness a).indexEquiv ITarget').2.val =
              ((D.smallWeakProfileWitness b).indexEquiv ITarget').2.val := by
        simpa only [ITarget, gTarget, Fin.castSucc_mk] using
          D.weakProfile_coordinates_eq hselected a b ITarget
      have htargetRankEq :
          let ITarget' : Fin (n + 2) := ⟨i.val - 1, by
            have := i.lt_large
            omega⟩
          finrank K (D.largeAlmostJordan.component
              ((D.largeWeakProfileWitness a).indexEquiv ITarget').1).carrier =
            finrank K (D.smallAlmostJordan.component
              ((D.largeWeakProfileWitness a).indexEquiv ITarget').1).carrier := by
        dsimp only
        exact congrFun (D.almostJordan_componentRank_eq hselected)
          ((D.largeWeakProfileWitness a).indexEquiv
            (⟨i.val - 1, by have := i.lt_large; omega⟩ :
              Fin (n + 2))).1
      have hrightOuter :=
        D.weakAligned_source_rightTwoStep_lt_of_penultimate
          hselected a b i htrigger hsourceBefore' hsourcePenultimate.1
      have hprefixCarrier :
          let ISource' : Fin (n + 2) := ⟨i.val - 2, by
            have := i.lt_large
            omega⟩
          D.largeAlmostJordan.toOrthogonalDecomposition.prefixCarrier
              (((D.smallWeakProfileWitness b).indexEquiv ISource').1.val + 1) =
            D.smallAlmostJordan.toOrthogonalDecomposition.prefixCarrier
              (((D.smallWeakProfileWitness b).indexEquiv ISource').1.val + 1) := by
        dsimp only
        exact D.aligned_prefixCarrier_eq hselected _
      exact D.centralCertificate_of_sourcePenultimate_of_notCollision_of_prefixAlignment
        a b hdefect i htrigger hsourceBefore' htargetBefore hcoordinatesInput
          htargetRankEq hrightOuter hprefixCarrier hsourcePenultimate.1 hthree
            hnotCollisionLeft
  · let hbounds := D.weakAligned_central_component_bounds
      hselected a b i hrange
    let Rtarget := D.largeStrictCoordinateResolution a ITarget hbounds.1
    have hrankPos : 0 < Rtarget.jordan.componentRank Rtarget.component :=
      Rtarget.jordan.component_finrank_pos Rtarget.component
    by_cases hrankOne : Rtarget.jordan.componentRank Rtarget.component = 1
    · exact D.weakAligned_centralCertificate_of_sourceLast_targetFirst_rank_one
        hselected a b hdefect i htrigger
          (by simpa only [y, ISource, gSource, Fin.castSucc_mk] using
            hsourceBefore)
          htargetBefore htargetFirst.1 htargetFirst.2 hrankOne
            hnotCollisionLeft
    · by_cases hrankTwo : Rtarget.jordan.componentRank Rtarget.component = 2
      · exact D.weakAligned_centralCertificate_of_targetFirst_rank_two
          hselected a b hdefect i htrigger htargetBefore htargetFirst.2
            hrankTwo hnotCollisionLeft
      · have hrankHigh : 2 < Rtarget.jordan.componentRank Rtarget.component := by
          omega
        exact D.weakAligned_centralCertificate_of_targetFirst
          hselected a b hdefect i htrigger htargetBefore htargetFirst.2
            hrankHigh
  · by_cases hindex : i.val = 2
    · exact D.weakAligned_centralCertificate_of_sourceFirst_at_two
        hselected a b i htrigger
          (by simpa only [y, ISource, gSource, Fin.castSucc_mk] using
            hsourceBefore)
          hindex hternary.1 hternary.2.2.2.1
    · have hsourcePositive : 0 < i.val - 2 := by
        have := i.one_lt
        omega
      exact D.weakAligned_centralCertificate_of_sourceFirst_targetPenultimate_ternary
        hselected a b hdefect i htrigger
          (by simpa only [y, ISource, gSource, Fin.castSucc_mk] using
            hsourceBefore)
          htargetBefore hnotCollisionLeft hsourcePositive hternary.1
            hternary.2.1 hternary.2.2.1 hternary.2.2.2.1
              hternary.2.2.2.2

end Lattice.Beli2019Lemma51Data

end Bong
