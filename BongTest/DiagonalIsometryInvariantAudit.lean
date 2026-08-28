/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.DiagonalIsometryInvariantProof

/-!
# Diagonal-isometry invariant audit

This test verifies that determinant square-class invariance and Beli's
diagonal Hasse-symbol invariance are now synthesized from the concrete
finite-dimensional proof, without a project-specific law assumption.
-/

namespace BongTest

open Bong Bong.Dyadic

variable (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

example : DiagonalIsometryInvariantLaws K := inferInstance

#print axioms Bong.diagonalIsometryInvariantLaws

end BongTest
