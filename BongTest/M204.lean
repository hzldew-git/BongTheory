import Bong.Bong.Beli2019PrimeIndexBasis

/-! Smoke checks for milestone M204. -/

open Bong

#check Lattice.coordinateScaleBasis
#check Lattice.basisLattice_coordinateScaleBasis_le
#check Lattice.basisGramDeterminant_coordinateScaleBasis
#check Lattice.volumeOrder_basisLattice_coordinateScaleBasis
#check Lattice.indexPInclusion_coordinateScaleBasis

#print axioms Lattice.indexPInclusion_coordinateScaleBasis
