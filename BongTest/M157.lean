/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.ProjectionScaling

/-!
# M157 Orthogonal-projection scaling smoke tests
-/

namespace BongTest.M157

#check Bong.QuadraticSpace.vectorOrthogonal_smul
#check Bong.QuadraticSpace.isAnisotropic_smul
#check Bong.QuadraticSpace.orthogonalProjection_smul
#check Bong.QuadraticSpace.vectorOrthogonalSMulEquiv
#check Bong.QuadraticSpace.orthogonalSpaceSMulIsometry
#check Bong.Lattice.map_projectedLattice_smul
#check Bong.Lattice.Isometry.toMap

#print axioms Bong.QuadraticSpace.orthogonalProjection_smul
#print axioms Bong.Lattice.map_projectedLattice_smul

end BongTest.M157
