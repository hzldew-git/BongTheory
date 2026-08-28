/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019MainTheorem

/-!
# M215 proved the central replacements in Lemma 3.10
-/

namespace BongTest.M215

open Bong
open Bong.Dyadic

#check BONG.GoodBONG.beli2019Lemma218_target
#check BONG.GoodBONG.beli2019Lemma218_source
#check DiagonalCodimensionOneCancellationLaws
#check BONG.GoodBONG.longTarget_iff_of_cancellation
#check BONG.GoodBONG.longSource_iff_of_cancellation
#check BONG.GoodBONG.leftApproximationTrigger_of_prefixCaps
#check BONG.GoodBONG.rightApproximationTrigger_of_prefixCaps
#check hilbertSymbol_eq_one_of_defectOrder_add_gt_two_mul_e
#check BONG.GoodBONG.centralTarget_iff_of_lemma218
#check BONG.GoodBONG.centralSource_iff_of_lemma218
#check BONG.GoodBONG.centralPrefix_change_of_approximation
#check beli2019Theorem21
#check beli2019Theorem21_prime

#print axioms BONG.GoodBONG.leftApproximationTrigger_of_prefixCaps
#print axioms BONG.GoodBONG.rightApproximationTrigger_of_prefixCaps
#print axioms hilbertSymbol_eq_one_of_defectOrder_add_gt_two_mul_e
#print axioms BONG.GoodBONG.centralTarget_iff_of_lemma218
#print axioms BONG.GoodBONG.centralSource_iff_of_lemma218

end BongTest.M215
