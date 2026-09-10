/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.He2022ClassicSectionEight

/-!
# Focused audit for discriminant parity and dyadic ramification

Only the direction used by the paper's global applications is an arithmetic
input.  Existence of a ramified dyadic place when the discriminant is even is
derived in Lean.
-/

open Bong.HeClassic2024GlobalData

#check DiscriminantRamificationLaws
#check DiscriminantRamificationLaws.exists_ramifiedDyadic_of_not_discriminantOdd
#check SectionEightLaws.he2022ClassicTheorem15_discriminantOdd
#check SectionEightLaws.he2022ClassicTheorem17
#check SectionEightLaws.he2022ClassicTheorem19

#print axioms DiscriminantRamificationLaws.exists_ramifiedDyadic_of_not_discriminantOdd
#print axioms SectionEightLaws.he2022ClassicTheorem15_discriminantOdd
#print axioms SectionEightLaws.he2022ClassicTheorem17
#print axioms SectionEightLaws.he2022ClassicTheorem19
