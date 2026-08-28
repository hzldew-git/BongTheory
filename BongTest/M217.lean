/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019MainTheorem

/-!
# M217 proved Beli (2019), Lemma 3.10(iv)
-/

namespace BongTest.M217

open Bong
open Bong.Dyadic

#check DiagonalRepresents.symm_of_sameRank
#check DiagonalCodimensionOneCancellationLaws
#check isSquare_of_two_mul_e_lt_defectOrder
#check BONG.GoodBONG.longTarget_iff_of_cancellation
#check BONG.GoodBONG.longSource_iff_of_cancellation
#check BONG.GoodBONG.longPrefix_change_of_approximation
#check BONG.GoodBONG.centralPrefix_change_of_approximation
#check beli2019Theorem21
#check beli2019Theorem21_prime

#print axioms DiagonalRepresents.symm_of_sameRank
#print axioms isSquare_of_two_mul_e_lt_defectOrder
#print axioms BONG.GoodBONG.longTarget_iff_of_cancellation
#print axioms BONG.GoodBONG.longSource_iff_of_cancellation
#print axioms BONG.GoodBONG.longPrefix_change_of_approximation

end BongTest.M217
