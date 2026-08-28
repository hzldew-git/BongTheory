/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma71Index

/-!
# M220 Beli 2019 Lemma 7.1 smoke tests
-/

namespace BongTest.M220

open Bong
open Bong.Dyadic

#check Lattice.nonNormGeneratorSubmodule
#check Lattice.mem_nonNormGeneratorSubmodule_iff
#check Lattice.nonNormGeneratorLattice
#check Lattice.mem_nonNormGeneratorLattice_iff
#check Lattice.exists_sub_smul_mem_nonNormGeneratorLattice
#check Lattice.IndexPGeneratorCertificate
#check Lattice.exists_volumeOrder_eq_add_two_mul_nat
#check Lattice.IndexPGeneratorCertificate.toBeli2019IndexPInclusion
#check BONG.GoodBONG.strictScaleBound_of_firstGap_ne_negTwoE
#check BONG.GoodBONG.beli2019Lemma71
#check BONG.GoodBONG.Beli2019Lemma71Data.indexPInclusion

#print axioms Lattice.mem_nonNormGeneratorLattice_iff
#print axioms Lattice.exists_sub_smul_mem_nonNormGeneratorLattice
#print axioms Lattice.IndexPGeneratorCertificate.toBeli2019IndexPInclusion
#print axioms BONG.GoodBONG.Beli2019Lemma71Data.indexPInclusion

end BongTest.M220
