/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong

/-!
# M16 Wall-form smoke tests
-/

namespace BongTest.M16

open Bong

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V}

example (f : QuadraticSpace.Isometry q q) :
    Function.Surjective (QuadraticSpace.residualMap f) :=
  QuadraticSpace.residualMap_surjective f

example (f : QuadraticSpace.Isometry q q)
    (y : QuadraticSpace.residualSpace f) :
    QuadraticSpace.residualMap f (QuadraticSpace.residualSection f y) = y :=
  QuadraticSpace.residualMap_residualSection f y

example (f : QuadraticSpace.Isometry q q) (w : V)
    (z : QuadraticSpace.residualSpace f) :
    QuadraticSpace.wallForm f (QuadraticSpace.residualMap f w) z =
      2 * q.bilin w (z : V) :=
  QuadraticSpace.wallForm_residualMap_left f w z

#print axioms Bong.QuadraticSpace.residualSection
#print axioms Bong.QuadraticSpace.bilin_section_independent
#print axioms Bong.QuadraticSpace.wallForm
#print axioms Bong.QuadraticSpace.wallForm_residualMap_left

end

end BongTest.M16
