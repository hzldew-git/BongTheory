/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.QuadraticSpace.FieldDiagonalization

/-!
# Audit for field-generic diagonalization and Witt cancellation

This test keeps the reusable characteristic-zero-field endpoints in the
ordinary build and exposes their transitive trust boundary.
-/

#check Bong.QuadraticSpace.fieldDiagonalizationIsometry
#check Bong.QuadraticSpace.fieldScaledLineDiagonalizationIsometry
#check Bong.QuadraticSpace.fieldScaledLineIsometryOfEqMulSquare
#check Bong.QuadraticSpace.fieldFiniteDiagonalScaledLineSnocIsometry
#check Bong.QuadraticSpace.fieldFiniteDiagonalRepresentsScaledLineOfValue
#check Bong.QuadraticSpace.fieldOrthogonalSumSwap
#check Bong.QuadraticSpace.fieldOrthogonalSumLeftCancelRepresents
#check Bong.QuadraticSpace.fieldOrthogonalSumCancelRepresents
#check Bong.QuadraticSpace.fieldOrthogonalSumLeftCancel
#check Bong.QuadraticSpace.fieldOrthogonalSumCancel

#print axioms Bong.QuadraticSpace.fieldDiagonalizationIsometry
#print axioms Bong.QuadraticSpace.fieldScaledLineDiagonalizationIsometry
#print axioms Bong.QuadraticSpace.fieldScaledLineIsometryOfEqMulSquare
#print axioms Bong.QuadraticSpace.fieldFiniteDiagonalScaledLineSnocIsometry
#print axioms Bong.QuadraticSpace.fieldFiniteDiagonalRepresentsScaledLineOfValue
#print axioms Bong.QuadraticSpace.fieldOrthogonalSumSwap
#print axioms Bong.QuadraticSpace.fieldOrthogonalSumLeftCancelRepresents
#print axioms Bong.QuadraticSpace.fieldOrthogonalSumCancelRepresents
#print axioms Bong.QuadraticSpace.fieldOrthogonalSumLeftCancel
#print axioms Bong.QuadraticSpace.fieldOrthogonalSumCancel
