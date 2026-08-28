/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019MainTheorem

/-!
# M213 removed the canonical-prefix Lemma 3.8 interface
-/

namespace BongTest.M213

open Bong
open Bong.Dyadic

#check DiagonalRepresents.of_source_length_eq_zero
#check BONG.GoodBONG.prefixRepresents_cast
#check BONG.GoodBONG.internalRepresentationConditions_sameLattice
#check BONG.GoodBONG.spaceApproximationRepresentationBridge_prefixValueUnits
#check BONG.GoodBONG.centralPrefix_change_of_approximation
#check lemma310PrefixLawsOfApproximationLaws
#check beli2019Theorem21
#check beli2019Theorem21_prime

#print axioms DiagonalRepresents.of_source_length_eq_zero
#print axioms BONG.GoodBONG.prefixRepresents_cast
#print axioms BONG.GoodBONG.internalRepresentationConditions_sameLattice
#print axioms BONG.GoodBONG.spaceApproximationRepresentationBridge_prefixValueUnits
#print axioms BONG.GoodBONG.centralPrefix_change_of_approximation
#print axioms lemma310PrefixLawsOfApproximationLaws

end BongTest.M213
