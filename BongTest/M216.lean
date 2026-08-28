/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019MainTheorem

/-!
# M216 proved Beli (2019), Lemma 2.18
-/

namespace BongTest.M216

open Bong
open Bong.Dyadic

#check BONG.GoodBONG.alpha_eq_min_halfGap_add_cappedAdjacent
#check BONG.GoodBONG.truncatedPrefixDefect_triangle_alternative
#check withTop_alpha_sum_alternative
#check BONG.GoodBONG.centralAdjustedAlpha_le_currentOrder_add_defect
#check BONG.GoodBONG.beli2019Lemma218_target
#check BONG.GoodBONG.beli2019Lemma218_source
#check BONG.GoodBONG.centralTarget_iff_of_lemma218
#check BONG.GoodBONG.centralSource_iff_of_lemma218
#check beli2019Theorem21
#check beli2019Theorem21_prime

#print axioms BONG.GoodBONG.alpha_eq_min_halfGap_add_cappedAdjacent
#print axioms BONG.GoodBONG.truncatedPrefixDefect_triangle_alternative
#print axioms withTop_alpha_sum_alternative
#print axioms BONG.GoodBONG.beli2019Lemma218_target
#print axioms BONG.GoodBONG.beli2019Lemma218_source

end BongTest.M216
