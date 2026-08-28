/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019MainTheorem

/-!
# M207 proved prime-index chain and local decorations
-/

namespace BongTest.M207

open Bong
open Bong.Dyadic

#check Lattice.IndexPChain
#check Lattice.indexPChain_of_le
#check Beli2019Corollary311Laws
#check Beli2019SectionFiveLaws
#check Beli2019SectionFourLaws
#check BONG.GoodBONG.onLattice
#check Lattice.IndexPChain.representationConditions
#check BONG.GoodBONG.representationConditions_of_lattice_le
#check beli2019_necessity
#check beli2019Theorem21_prime

#print axioms Lattice.indexPChain_of_le
#print axioms Lattice.IndexPChain.representationConditions
#print axioms BONG.GoodBONG.representationConditions_of_lattice_le
#print axioms beli2019Theorem21_prime

end BongTest.M207
