/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.He2022ClassicSectionEight

/-!
# Focused audit for Theorem 1.9 finite-place universality

The all-places conclusion is derived from separate non-dyadic, dyadic unary,
and dyadic higher-rank arithmetic branches.
-/

open Bong.HeClassic2024GlobalData

#check SumOfSquaresLocalUniversalityLaws
#check SumOfSquaresLocalUniversalityLaws.sumOfSquares_localUniversal_of_oddDiscriminant
#check SectionEightLaws.sumOfSquares_localUniversal_of_oddDiscriminant
#check SectionEightLaws.he2022ClassicTheorem19

#print axioms SumOfSquaresLocalUniversalityLaws.sumOfSquares_localUniversal_of_oddDiscriminant
#print axioms SectionEightLaws.sumOfSquares_localUniversal_of_oddDiscriminant
#print axioms SectionEightLaws.he2022ClassicTheorem19
