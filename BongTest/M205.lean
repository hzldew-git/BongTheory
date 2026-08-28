import Bong.Bong.Beli2019PrimeIndexChain

/-! Smoke checks for milestone M205. -/

open Bong

#check Lattice.IndexPChain
#check Lattice.indexPChain_powerBasis
#check Lattice.SmithPowerBasisData.indexPChain
#check Lattice.indexPChain_of_le

#print axioms Lattice.indexPChain_of_le
