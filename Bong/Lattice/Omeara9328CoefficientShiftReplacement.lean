/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaCoefficientShift
import Bong.Lattice.JordanReplaceFirstPairIsometry
import Bong.Lattice.OrthogonalDecompositionReplacePairPrefix

/-!
# Installing O'Meara 93:19 in a Jordan splitting

The coefficient shift of 93:19 is constructed on an explicit binary plane
and a modular lattice.  This file transports that calculation into the first
two components of a Jordan decomposition and records the two invariants used
by 93:28: equality of fundamental type and saturation.
-/

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u v x

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [DyadicDiscriminantClassLaws K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {X : Type x} [AddCommGroup X] [Module K X]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
  {p : QuadraticSpace K X} {N : Lattice K X} {s : Kˣ}

/-- Output of one coefficient shift installed in the first two Jordan
components.  Later 93:28 case calculations only have to prove that the new
head has the desired determinant/space and that the three conditions are
retained. -/
structure Omeara9319JordanReplacement
    (J : JordanDecomposition q L (n + 2)) where
  target : JordanDecomposition q L (n + 2)
  fundamentalType : SameFundamentalType J target
  saturated : target.IsSaturated
  /-- Every prefix containing both changed components is integrally
  unchanged.  Thus only the first 93:28 boundary has to be recomputed. -/
  laterPrefixIsometry : ∀ (k : Nat), 2 ≤ k →
    Isometry
      (J.toOrthogonalDecomposition.prefixQuadraticSublattice k).space
      (target.toOrthogonalDecomposition.prefixQuadraticSublattice k).space
      (J.toOrthogonalDecomposition.prefixQuadraticSublattice k).lattice
      (target.toOrthogonalDecomposition.prefixQuadraticSublattice k).lattice

/-- Apply the concrete 93:19 calculation to displayed models of the first
two components.  The six modular/ideal hypotheses are the local checks that
the new displayed factors still carry the old Jordan scale and norm data.
The old-head containment is the remaining norm-group calculation for the
particular coefficient chosen in cases 4--7; the tail containment is supplied
by 93:19 itself. -/
noncomputable def coefficientShiftJordanReplacement
    (J : JordanDecomposition q L (n + 2))
    (hJ : J.IsSaturated)
    (E : Omeara9319ExchangeSetup p N s)
    (hN : IsModular p N s) (hrank : 3 ≤ finrank K X)
    (headIso : Isometry E.oldPlane (J.component 0).space
      (hyperbolicPlaneLattice (K := K)) (J.component 0).lattice)
    (tailIso : Isometry p (J.component 1).space
      N (J.component 1).lattice)
    (hnewModular : IsModular E.newPlane
      (hyperbolicPlaneLattice (K := K)) (J.scaleGenerator 0))
    (hcomplementModular : IsModular
      ((E.coefficientShift hN hrank).splitting.decomposition.component 1).space
      ((E.coefficientShift hN hrank).splitting.decomposition.component 1).lattice
      (J.scaleGenerator 1))
    (hnewScale : scaleIdeal E.newPlane
      (hyperbolicPlaneLattice (K := K)) =
        principalIdeal (K := K) (J.scaleGenerator 0 : K))
    (hcomplementScale : scaleIdeal
      ((E.coefficientShift hN hrank).splitting.decomposition.component 1).space
      ((E.coefficientShift hN hrank).splitting.decomposition.component 1).lattice =
        principalIdeal (K := K) (J.scaleGenerator 1 : K))
    (hnewNorm : normIdeal E.newPlane
      (hyperbolicPlaneLattice (K := K)) =
        principalIdeal (K := K) (J.normGenerator 0 : K))
    (hcomplementNorm : normIdeal
      ((E.coefficientShift hN hrank).splitting.decomposition.component 1).space
      ((E.coefficientShift hN hrank).splitting.decomposition.component 1).lattice =
        principalIdeal (K := K) (J.normGenerator 1 : K))
    (hheadContains : normGroupSet (J.component 0).space
        (J.component 0).lattice ⊆
      normGroupSet E.newPlane (hyperbolicPlaneLattice (K := K))) :
    Omeara9319JordanReplacement J := by
  let D := E.coefficientShift hN hrank
  let expose : Isometry (E.oldPlane.orthogonalSum p)
      (J.firstPairSublattice).space
      (product (hyperbolicPlaneLattice (K := K)) N)
      (J.firstPairSublattice).lattice :=
    (headIso.orthogonalProductBasic tailIso).trans
      (J.toOrthogonalDecomposition.orthogonalSupLatticeIsometry
        firstIndex_ne_secondIndex)
  let shifted : Isometry
      (E.newPlane.orthogonalSum (D.splitting.decomposition.component 1).space)
      (J.firstPairSublattice).space
      (product (hyperbolicPlaneLattice (K := K))
        (D.splitting.decomposition.component 1).lattice)
      (J.firstPairSublattice).lattice :=
    D.shifted.symm.trans expose
  let T := J.replaceFirstPairOfIsometry shifted hnewModular
    hcomplementModular hnewScale hcomplementScale hnewNorm hcomplementNorm
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
          hnewModular hcomplementModular hnewScale hcomplementScale
          hnewNorm hcomplementNorm
      saturated :=
        J.replaceFirstPairOfIsometry_isSaturated shifted
          hnewModular hcomplementModular hnewScale hcomplementScale
          hnewNorm hcomplementNorm hJ hheadContains htailContains
      laterPrefixIsometry := by
        intro k hk
        exact J.toOrthogonalDecomposition
          |>.replacePair_first_prefixLatticeIsometry
            (J.firstPairDecompositionOfIsometry shifted) k hk }

end Lattice.JordanDecomposition

end Bong
