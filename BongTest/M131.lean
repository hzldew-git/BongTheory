/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019EssentialIndex

/-!
# M131 Beli 2019, Definition 7 essential-index smoke tests
-/

namespace BongTest.M131

open Bong

example {N : Nat} (x y : BeliOrderSequence (N + 1) Int) :
    x.IsEssentialFor y 0 :=
  x.isEssentialFor_zero y

example {N : Nat} (x y : BeliOrderSequence (N + 1) Int) :
    x.IsEssentialFor y (Fin.last N) :=
  x.isEssentialFor_last y

example {N : Nat} (x y : BeliOrderSequence N Int) (i : Fin N) :
    y.reverseNegate.IsEssentialFor x.reverseNegate (Fin.rev i) ↔
      x.IsEssentialFor y i :=
  x.reverseNegate_isEssentialFor_iff y i

#print axioms Bong.BeliOrderSequence.isEssentialFor_zero
#print axioms Bong.BeliOrderSequence.isEssentialFor_last
#print axioms Bong.BeliOrderSequence.reverseNegate_isEssentialFor_iff
#print axioms Bong.BONG.GoodBONG.reverseDualOrder_isEssentialFor_iff

end BongTest.M131
