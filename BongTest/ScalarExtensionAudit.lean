/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.QuadraticSpace.ScalarExtension

/-!
# Audit for scalar extension of quadratic spaces

This test exposes the algebraic scalar-extension endpoints and their
transitive trust boundary.  They are infrastructure for He (2025), Lemma 2.2.
-/

#check Bong.QuadraticSpace.toMatrix_baseChange
#check LinearMap.BilinForm.Nondegenerate.baseChangeField
#check Bong.QuadraticSpace.scalarExtension
#check Bong.QuadraticSpace.scalarExtension_bilin_tmul
#check Bong.QuadraticSpace.scalarExtension_quadratic_tmul
#check Bong.QuadraticSpace.Isometry.scalarExtension
#check Bong.QuadraticSpace.Representation.scalarExtension
#check Bong.QuadraticSpace.scalarExtensionFiniteDiagonalIsometry
#check Bong.QuadraticSpace.scalarExtensionOrthogonalSumIsometry
#check Bong.QuadraticSpace.scalarExtensionScaledLineIsometry

#print axioms Bong.QuadraticSpace.toMatrix_baseChange
#print axioms LinearMap.BilinForm.Nondegenerate.baseChangeField
#print axioms Bong.QuadraticSpace.scalarExtension
#print axioms Bong.QuadraticSpace.scalarExtension_bilin_tmul
#print axioms Bong.QuadraticSpace.scalarExtension_quadratic_tmul
#print axioms Bong.QuadraticSpace.Isometry.scalarExtension
#print axioms Bong.QuadraticSpace.Representation.scalarExtension
#print axioms Bong.QuadraticSpace.scalarExtensionFiniteDiagonalIsometry
#print axioms Bong.QuadraticSpace.scalarExtensionOrthogonalSumIsometry
#print axioms Bong.QuadraticSpace.scalarExtensionScaledLineIsometry
