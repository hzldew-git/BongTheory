/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma46Proof
import Bong.Bong.BeliLemma43MaximalNormProof
import Bong.Bong.MaximalNormSplittingDual

/-!
# Unconditional structural laws for good BONGs

Beli (2003), Section 4 has already supplied the three independent pieces of
the compatibility package `BONGStructuralLaws`: existence of good BONGs,
reverse duality, and the Jordan-coordinate characterization of property A.
This file only assembles those proved results into the legacy aggregate
interface used by later papers.
-/

namespace Bong

universe u v

open Dyadic

/-- The aggregate structural interface has no remaining mathematical input. -/
noncomputable instance bongStructuralLawsProved
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] :
    BONGStructuralLaws.{u, v} K where
  exists_good_bong := BONGGoodExistenceLaws.exists_good_bong
  reverse_dual_good := fun b => b.exists_reverseDual_of_beli
  propertyA_coordinates := BONGJordanCoordinateLaws.propertyA_coordinates

end Bong
