/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019MainTheorem

/-!
# Codimension-one diagonal cancellation audit

This test verifies that the former local-law boundary is inferred from
finite-dimensional linear algebra and that closing it adds no nonstandard
axioms to the Beli 2019 endpoints.
-/

namespace BongTest

open Bong

variable (K : Type*) [Field K] [CharZero K]

example : DiagonalCodimensionOneCancellationLaws K := inferInstance

#print axioms Bong.diagonalCodimensionOneCancellationLawsProved
#print axioms Bong.beli2019Theorem21
#print axioms Bong.beli2019Theorem21_prime

end BongTest
