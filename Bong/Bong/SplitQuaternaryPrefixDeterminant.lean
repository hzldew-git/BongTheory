/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.HeHu2022AmbientRank
import Bong.Bong.BeliUniversalHalfTower
import Bong.Bong.Beli2009AmbientDeterminantProof

/-!
# Full BONG determinant of the split quaternary space

This paper-independent bridge records the determinant fact used by both
He--Hu's exceptional binary case and He's classic-universality criterion:
the full product of any length-four BONG on `H ⊥ H` is a square.
-/

namespace Bong

open Dyadic Module

universe u v

namespace QuadraticSpace

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- Identify the canonical half-hyperbolic tower of length two with
two ordinary hyperbolic planes. -/
noncomputable def halfHyperbolicTowerTwoToHyperbolicPairIsometry : by
    let T := Lattice.QuadraticLatticeModel.halfHyperbolicTower (K := K) 2
    letI : AddCommGroup T.Carrier := T.addCommGroup
    letI : Module K T.Carrier := T.module
    exact Isometry T.form
      ((hyperbolicPlane (K := K) (1 : Kˣ)).orthogonalSum
        (hyperbolicPlane (K := K) (1 : Kˣ))) := by
  let ordinaryToHalf :=
    hyperbolicExtensionToHalfExtensionSpaceIsometry
      (Lattice.zeroCoordinateQuadraticSpace (K := K)) 2
  exact ordinaryToHalf.symm.trans
    (hyperbolicExtensionTwoToHyperbolicPairSpaceIsometry (K := K))

end QuadraticSpace

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- The full BONG value product of a split quaternary quadratic space is a
square. -/
theorem splitQuaternary_fullPrefix_isSquare
    (a : GoodBONG q L 4)
    (hsplit :
      q.IsIsometric
        ((QuadraticSpace.hyperbolicPlane (K := K) (1 : Kˣ)).orthogonalSum
          (QuadraticSpace.hyperbolicPlane (K := K) (1 : Kˣ)))) :
    IsSquare (a.prefixProduct 4) := by
  let T := Lattice.QuadraticLatticeModel.halfHyperbolicTower (K := K) 2
  letI : AddCommGroup T.Carrier := T.addCommGroup
  letI : Module K T.Carrier := T.module
  let b := standardHalfHyperbolicTowerBONG (K := K) 2
  let qToTower : QuadraticSpace.Isometry q T.form :=
    (Classical.choice hsplit).trans
      (QuadraticSpace.halfHyperbolicTowerTwoToHyperbolicPairIsometry
        (K := K)).symm
  have hboth : IsSquare (a.prefixProduct 4 * b.prefixProduct 4) := by
    simpa only [comparisonPrefixUnit] using
      (fullComparison_isSquare_proof ⟨qToTower⟩ a b)
  have hbSigned :=
    standardHalfHyperbolicTowerBONG_signedProduct_isSquare (K := K) 2
  have hb : IsSquare (b.prefixProduct 4) := by
    simpa [BONG.signedEvenPrefixProduct, GoodBONG.prefixProduct] using hbSigned
  have hquotient := hboth.div hb
  simpa using hquotient

end BONG.GoodBONG

end Bong
