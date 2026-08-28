/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019MainTheorem

/-!
# M176 Beli 2019 Theorem 2.1 smoke tests
-/

namespace BongTest.M176

open Bong
open Bong.Dyadic

#check GoodBONGDeepIntegralExtensionData
#check GoodBONGDeepIntegralExtensionLaws
#check GoodBONGSameRankIntegralImageData
#check beli2019_necessity
#check beli2019Theorem21
#check beli2019Theorem21_prime

#print axioms beli2019_necessity
#print axioms beli2019Theorem21
#print axioms beli2019Theorem21_prime

end BongTest.M176
