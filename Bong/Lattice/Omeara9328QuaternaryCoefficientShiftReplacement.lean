/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328CoefficientShiftReplacement

/-!
# Installing O'Meara 93:19 inside a quaternary head component

In the computational part of 93:28 the first Jordan component has rank
four and is displayed as two binary O'Meara planes.  Proposition 93:19 is
applied only to the second plane and the next Jordan component.  This file
performs the reassociation, applies the already constructed coefficient
shift, recombines the untouched first plane with the new second plane, and
installs the resulting two components in the ambient Jordan splitting.
-/

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u v x y

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [DyadicDiscriminantClassLaws K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {X : Type x} [AddCommGroup X] [Module K X]
  {Y : Type y} [AddCommGroup Y] [Module K Y]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
  {p : QuadraticSpace K X} {A : Lattice K X}
  {r : QuadraticSpace K Y} {N : Lattice K Y} {s : Kˣ}

/-- Apply 93:19 to the right binary factor of a displayed quaternary first
component.  The scale, norm and saturation hypotheses are exactly the local
facts needed to certify that the two recombined outputs are again the first
two components of a saturated Jordan decomposition. -/
noncomputable def quaternaryCoefficientShiftJordanReplacement
    (J : JordanDecomposition q L (n + 2))
    (hJ : J.IsSaturated)
    (E : Omeara9319ExchangeSetup r N s)
    (hN : IsModular r N s) (hrank : 3 ≤ finrank K Y)
    (headIso : Isometry (p.orthogonalSum E.oldPlane)
      (J.component 0).space
      (product A (hyperbolicPlaneLattice (K := K)))
      (J.component 0).lattice)
    (tailIso : Isometry r (J.component 1).space
      N (J.component 1).lattice)
    (hnewHeadModular : IsModular
      (p.orthogonalSum E.newPlane)
      (product A (hyperbolicPlaneLattice (K := K)))
      (J.scaleGenerator 0))
    (hcomplementModular : IsModular
      ((E.coefficientShift hN hrank).splitting.decomposition.component 1).space
      ((E.coefficientShift hN hrank).splitting.decomposition.component 1).lattice
      (J.scaleGenerator 1))
    (hnewHeadScale : scaleIdeal (p.orthogonalSum E.newPlane)
      (product A (hyperbolicPlaneLattice (K := K))) =
        principalIdeal (K := K) (J.scaleGenerator 0 : K))
    (hcomplementScale : scaleIdeal
      ((E.coefficientShift hN hrank).splitting.decomposition.component 1).space
      ((E.coefficientShift hN hrank).splitting.decomposition.component 1).lattice =
        principalIdeal (K := K) (J.scaleGenerator 1 : K))
    (hnewHeadNorm : normIdeal (p.orthogonalSum E.newPlane)
      (product A (hyperbolicPlaneLattice (K := K))) =
        principalIdeal (K := K) (J.normGenerator 0 : K))
    (hcomplementNorm : normIdeal
      ((E.coefficientShift hN hrank).splitting.decomposition.component 1).space
      ((E.coefficientShift hN hrank).splitting.decomposition.component 1).lattice =
        principalIdeal (K := K) (J.normGenerator 1 : K))
    (hheadContains : normGroupSet (J.component 0).space
        (J.component 0).lattice ⊆
      normGroupSet (p.orthogonalSum E.newPlane)
        (product A (hyperbolicPlaneLattice (K := K)))) :
    Omeara9319JordanReplacement J := by
  let D := E.coefficientShift hN hrank
  let expose : Isometry
      ((p.orthogonalSum E.oldPlane).orthogonalSum r)
      J.firstPairSublattice.space
      (product (product A (hyperbolicPlaneLattice (K := K))) N)
      J.firstPairSublattice.lattice :=
    (headIso.orthogonalProductBasic tailIso).trans
      (J.toOrthogonalDecomposition.orthogonalSupLatticeIsometry
        firstIndex_ne_secondIndex)
  let leftIdentity := Isometry.refl p A
  let reassociateNew : Isometry
      ((p.orthogonalSum E.newPlane).orthogonalSum
        (D.splitting.decomposition.component 1).space)
      (p.orthogonalSum
        (E.newPlane.orthogonalSum
          (D.splitting.decomposition.component 1).space))
      (product (product A (hyperbolicPlaneLattice (K := K)))
        (D.splitting.decomposition.component 1).lattice)
      (product A
        (product (hyperbolicPlaneLattice (K := K))
          (D.splitting.decomposition.component 1).lattice)) :=
    orthogonalProductAssoc
  let undoShift : Isometry
      (p.orthogonalSum
        (E.newPlane.orthogonalSum
          (D.splitting.decomposition.component 1).space))
      (p.orthogonalSum (E.oldPlane.orthogonalSum r))
      (product A
        (product (hyperbolicPlaneLattice (K := K))
          (D.splitting.decomposition.component 1).lattice))
      (product A (product (hyperbolicPlaneLattice (K := K)) N)) :=
    leftIdentity.orthogonalProductBasic D.shifted.symm
  let reassociateOld : Isometry
      (p.orthogonalSum (E.oldPlane.orthogonalSum r))
      ((p.orthogonalSum E.oldPlane).orthogonalSum r)
      (product A (product (hyperbolicPlaneLattice (K := K)) N))
      (product (product A (hyperbolicPlaneLattice (K := K))) N) :=
    orthogonalProductAssoc.symm
  let shifted : Isometry
      ((p.orthogonalSum E.newPlane).orthogonalSum
        (D.splitting.decomposition.component 1).space)
      J.firstPairSublattice.space
      (product (product A (hyperbolicPlaneLattice (K := K)))
        (D.splitting.decomposition.component 1).lattice)
      J.firstPairSublattice.lattice :=
    reassociateNew.trans
      (undoShift.trans (reassociateOld.trans expose))
  let T := J.replaceFirstPairOfIsometry shifted hnewHeadModular
    hcomplementModular hnewHeadScale hcomplementScale hnewHeadNorm
    hcomplementNorm
  have htailContains : normGroupSet (J.component 1).space
      (J.component 1).lattice ⊆
      normGroupSet (D.splitting.decomposition.component 1).space
        (D.splitting.decomposition.component 1).lattice := by
    intro z hz
    apply D.normGroup_subset
    rw [← normGroupSet_eq_of_latticeIsometry tailIso]
    exact hz
  exact
    { target := T
      fundamentalType :=
        J.replaceFirstPairOfIsometry_sameFundamentalType shifted
          hnewHeadModular hcomplementModular hnewHeadScale hcomplementScale
          hnewHeadNorm hcomplementNorm
      saturated :=
        J.replaceFirstPairOfIsometry_isSaturated shifted
          hnewHeadModular hcomplementModular hnewHeadScale hcomplementScale
          hnewHeadNorm hcomplementNorm hJ hheadContains htailContains
      laterPrefixIsometry := by
        intro k hk
        exact J.toOrthogonalDecomposition
          |>.replacePair_first_prefixLatticeIsometry
            (J.firstPairDecompositionOfIsometry shifted) k hk }

end Lattice.JordanDecomposition

end Bong
