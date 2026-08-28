import Bong.Lattice.SmithPowerBasis

/-! Smoke checks for milestone M203. -/

open Bong
open Bong.Dyadic

#check Lattice.relativeSubmodule
#check Lattice.relativeSubmoduleEquiv
#check Lattice.relativeSubmodule_finrank_eq
#check Lattice.SmithPowerBasisData
#check Lattice.exists_smithPowerBasisData

#print axioms Lattice.exists_smithPowerBasisData
