/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaClassificationFoundations

/-!
# O'Meara 93:14a for arbitrary unimodular summands

The hyperbolic-summand form of 93:14a is enough after adjoining the negative
of the summand.  Indeed, `J ⊥ (-J)` is hyperbolic, its norm group is the
norm group of `J`, and an isometry `J ≃ J'` also identifies their negative
copies.  This file performs that stabilization and then applies the already
proved hyperbolic cancellation theorem.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u u' u'' v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- Negating a quadratic form preserves an arbitrary modular parameter.
This is the scaled form of the observation used in the stabilization proof
of O'Meara 93:14a. -/
theorem IsModular.rescaleUnit_neg_one_general
    {U : Type u'} [AddCommGroup U] [Module K U]
    {p : QuadraticSpace K U} {J : Lattice K U} {a : Kˣ}
    (hJ : IsModular p J a) :
    IsModular (p.rescaleUnit (-1 : Kˣ)) J a := by
  rw [IsModular, dualLattice_rescaleUnit_neg_one]
  exact hJ

/-- O'Meara 93:14a for arbitrary modular summands and arbitrary
complements.

Unlike `omeara9314a_unimodular`, the complements need not be modular.  The
two norm-group hypotheses are exactly the hypotheses in the printed
corollary, expressed using O'Meara's scale truncation at the modular
parameter.  The proof adjoins the negative summand, turns the resulting
quadratic space into an explicit hyperbolic model, and invokes the already
proved universe-polymorphic hyperbolic cancellation theorem. -/
noncomputable def omeara9314a_general
    {U : Type u'} {U' : Type u''} {V : Type v} {W : Type w}
    [AddCommGroup U] [Module K U]
    [AddCommGroup U'] [Module K U']
    [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    {p : QuadraticSpace K U} {p' : QuadraticSpace K U'}
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {J : Lattice K U} {J' : Lattice K U'}
    {L : Lattice K V} {M : Lattice K W}
    (a : Kˣ)
    (hJ : IsModular p J a) (hJ' : IsModular p' J' a)
    (summand : Isometry p p' J J')
    (hgroup : normGroupSet p J ⊆
      normGroupSet q (omearaScaleTruncation q L a))
    (hgroup' : normGroupSet p' J' ⊆
      normGroupSet r (omearaScaleTruncation r M a))
    (total : Isometry (p.orthogonalSum q) (p'.orthogonalSum r)
      (product J L) (product J' M)) :
    Isometry q r L M := by
  letI : FiniteDimensional K U :=
    J.ambientBasis.finiteDimensional_of_finite
  letI : FiniteDimensional K U' :=
    J'.ambientBasis.finiteDimensional_of_finite
  let negative := p.rescaleUnit (-1 : Kˣ)
  let negative' := p'.rescaleUnit (-1 : Kˣ)
  let commonAmbient := p.orthogonalSum negative
  let commonAmbient' := p'.orthogonalSum negative'
  let commonLattice := product J J
  let commonLattice' := product J' J'
  let hyperbolic := hyperbolicExtensionForm
    (zeroCoordinateQuadraticSpace (K := K)) (finrank K U)
  let commonToHyperbolic : QuadraticSpace.Isometry
      commonAmbient hyperbolic :=
    quadraticNegativeHyperbolicIsometry p
  let commonModel := map commonToHyperbolic.toLinearEquiv commonLattice
  let commonIsometry :=
    Isometry.toMap commonAmbient commonToHyperbolic commonLattice
  have hnegative : IsModular negative J a :=
    hJ.rescaleUnit_neg_one_general
  have hnegative' : IsModular negative' J' a :=
    hJ'.rescaleUnit_neg_one_general
  have hcommon : IsModular commonAmbient commonLattice a :=
    hJ.orthogonalProduct hnegative
  have hcommon' : IsModular commonAmbient' commonLattice' a :=
    hJ'.orthogonalProduct hnegative'
  have hcommonModel : IsModular hyperbolic commonModel a :=
    hcommon.mapLatticeIsometry commonIsometry
  have hcommonGroup : normGroupSet commonAmbient commonLattice =
      normGroupSet p J :=
    normGroupSet_quadraticNegativeProduct p J
  have hcommonGroup' : normGroupSet commonAmbient' commonLattice' =
      normGroupSet p' J' :=
    normGroupSet_quadraticNegativeProduct p' J'
  have hcancel : normGroupSet commonAmbient commonLattice ⊆
      normGroupSet q (omearaScaleTruncation q L a) := by
    rw [hcommonGroup]
    exact hgroup
  have hcancel' : normGroupSet commonAmbient' commonLattice' ⊆
      normGroupSet r (omearaScaleTruncation r M a) := by
    rw [hcommonGroup']
    exact hgroup'
  let negativeSummand : Isometry negative negative' J J' :=
    summand.rescaleUnitBoth (-1 : Kˣ)
  let commonSummand : Isometry commonAmbient commonAmbient'
      commonLattice commonLattice' :=
    summand.orthogonalProductBasic negativeSummand
  let commonModelToTarget : Isometry hyperbolic commonAmbient'
      commonModel commonLattice' :=
    commonIsometry.symm.trans commonSummand
  let extended : Isometry
      (negative.orthogonalSum (p.orthogonalSum q))
      (negative'.orthogonalSum (p'.orthogonalSum r))
      (product J (product J L))
      (product J' (product J' M)) :=
    negativeSummand.orthogonalProductBasic total
  let sourceRotate : Isometry
      (negative.orthogonalSum (p.orthogonalSum q))
      (commonAmbient.orthogonalSum q)
      (product J (product J L))
      (product commonLattice L) :=
    orthogonalProductRotateLeft
  let targetRotate : Isometry
      (negative'.orthogonalSum (p'.orthogonalSum r))
      (commonAmbient'.orthogonalSum r)
      (product J' (product J' M))
      (product commonLattice' M) :=
    orthogonalProductRotateLeft
  let stabilized : Isometry
      (commonAmbient.orthogonalSum q)
      (commonAmbient'.orthogonalSum r)
      (product commonLattice L) (product commonLattice' M) :=
    sourceRotate.symm.trans (extended.trans targetRotate)
  exact omeara9314a_abstract_universe a
    commonModel commonModel hcommonModel hcommonModel
    commonIsometry.symm commonModelToTarget
    hcancel hcancel' stabilized

/-- O'Meara 93:14a at unit scale, without assuming that the cancellable
summand itself is hyperbolic. -/
noncomputable def omeara9314a_unimodular
    {U : Type u'} {U' : Type u''} {V : Type v} {W : Type w}
    [AddCommGroup U] [Module K U]
    [AddCommGroup U'] [Module K U']
    [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    {p : QuadraticSpace K U} {p' : QuadraticSpace K U'}
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {J : Lattice K U} {J' : Lattice K U'}
    {L : Lattice K V} {M : Lattice K W}
    (hJ : IsUnimodular p J) (hJ' : IsUnimodular p' J')
    (hL : IsUnimodular q L) (hM : IsUnimodular r M)
    (summand : Isometry p p' J J')
    (hgroup : normGroupSet p J ⊆ normGroupSet q L)
    (hgroup' : normGroupSet p' J' ⊆ normGroupSet r M)
    (total : Isometry (p.orthogonalSum q) (p'.orthogonalSum r)
      (product J L) (product J' M)) :
    Isometry q r L M := by
  letI : FiniteDimensional K U :=
    J.ambientBasis.finiteDimensional_of_finite
  letI : FiniteDimensional K U' :=
    J'.ambientBasis.finiteDimensional_of_finite
  let negative := p.rescaleUnit (-1 : Kˣ)
  let negative' := p'.rescaleUnit (-1 : Kˣ)
  let commonAmbient := p.orthogonalSum negative
  let commonAmbient' := p'.orthogonalSum negative'
  let commonLattice := product J J
  let commonLattice' := product J' J'
  let hyperbolic := hyperbolicExtensionForm
    (zeroCoordinateQuadraticSpace (K := K)) (finrank K U)
  let commonToHyperbolic : QuadraticSpace.Isometry
      commonAmbient hyperbolic :=
    quadraticNegativeHyperbolicIsometry p
  let commonModel := map commonToHyperbolic.toLinearEquiv commonLattice
  let commonIsometry :=
    Isometry.toMap commonAmbient commonToHyperbolic commonLattice
  have hnegative : IsUnimodular negative J :=
    (isUnimodular_rescaleUnit_neg_one_iff p J).mpr hJ
  have hnegative' : IsUnimodular negative' J' :=
    (isUnimodular_rescaleUnit_neg_one_iff p' J').mpr hJ'
  have hcommon : IsUnimodular commonAmbient commonLattice :=
    hJ.orthogonalProduct hnegative
  have hcommon' : IsUnimodular commonAmbient' commonLattice' :=
    hJ'.orthogonalProduct hnegative'
  have hcommonModel : IsModular hyperbolic commonModel (1 : Kˣ) :=
    hcommon.mapLatticeIsometry commonIsometry
  have htrunc : omearaScaleTruncation q L (1 : Kˣ) = L :=
    omearaScaleTruncation_one_eq_of_unimodular hL
  have htrunc' : omearaScaleTruncation r M (1 : Kˣ) = M :=
    omearaScaleTruncation_one_eq_of_unimodular hM
  have hcommonGroup : normGroupSet commonAmbient commonLattice =
      normGroupSet p J :=
    normGroupSet_quadraticNegativeProduct p J
  have hcommonGroup' : normGroupSet commonAmbient' commonLattice' =
      normGroupSet p' J' :=
    normGroupSet_quadraticNegativeProduct p' J'
  have hcancel : normGroupSet commonAmbient commonLattice ⊆
      normGroupSet q (omearaScaleTruncation q L (1 : Kˣ)) := by
    rw [hcommonGroup, htrunc]
    exact hgroup
  have hcancel' : normGroupSet commonAmbient' commonLattice' ⊆
      normGroupSet r (omearaScaleTruncation r M (1 : Kˣ)) := by
    rw [hcommonGroup', htrunc']
    exact hgroup'
  let negativeSummand : Isometry negative negative' J J' :=
    summand.rescaleUnitBoth (-1 : Kˣ)
  let commonSummand : Isometry commonAmbient commonAmbient'
      commonLattice commonLattice' :=
    summand.orthogonalProductBasic negativeSummand
  let commonModelToTarget : Isometry hyperbolic commonAmbient'
      commonModel commonLattice' :=
    commonIsometry.symm.trans commonSummand
  let extended : Isometry
      (negative.orthogonalSum (p.orthogonalSum q))
      (negative'.orthogonalSum (p'.orthogonalSum r))
      (product J (product J L))
      (product J' (product J' M)) :=
    negativeSummand.orthogonalProductBasic total
  let sourceRotate : Isometry
      (negative.orthogonalSum (p.orthogonalSum q))
      (commonAmbient.orthogonalSum q)
      (product J (product J L))
      (product commonLattice L) :=
    orthogonalProductRotateLeft
  let targetRotate : Isometry
      (negative'.orthogonalSum (p'.orthogonalSum r))
      (commonAmbient'.orthogonalSum r)
      (product J' (product J' M))
      (product commonLattice' M) :=
    orthogonalProductRotateLeft
  let stabilized : Isometry
      (commonAmbient.orthogonalSum q)
      (commonAmbient'.orthogonalSum r)
      (product commonLattice L) (product commonLattice' M) :=
    sourceRotate.symm.trans (extended.trans targetRotate)
  exact omeara9314a_abstract_universe (1 : Kˣ)
    commonModel commonModel hcommonModel hcommonModel
    commonIsometry.symm commonModelToTarget
    hcancel hcancel' stabilized

end Lattice

end Bong
