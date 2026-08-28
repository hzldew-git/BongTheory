/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019MainTheorem

/-!
# Beli 2019 quaternary first-scaling audit

This test checks that the former rank-four scaling interface from Lemma 8.3
is inferred from the concrete dyadic defect, Hilbert, alpha-parity, and local
diagonal-classification results.  It also records the axioms used by the
concrete instance and the two forms of Theorem 2.1.
-/

namespace BongTest

open Bong Bong.Dyadic

universe u v

variable (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [QuadraticDefectLaws K] [Beli2006AlphaLaws.{u, v} K]

example : DyadicQuaternaryFirstScalingLaws.{u, v} K := inferInstance

#print axioms Bong.BONG.GoodBONG.dyadicQuaternaryFirstScalingLawsProved
#print axioms Bong.BONG.GoodBONG.quaternaryNegativeScale_alphaData
#print axioms Bong.beli2019Theorem21
#print axioms Bong.beli2019Theorem21_prime

end BongTest
