/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Papers.Beli2003

/-!
# Beli 2003 public-theorem audit

This file prints the signatures and transitive axiom sets of the five public
endpoints for the paper's three main theorem families.
-/

#check @Bong.BONG.beliTheoremOne_proved
#check @Bong.BONG.beliTheoremOne_set_proved
#check @Bong.Lattice.beliTheoremTwo_proved
#check @Bong.Lattice.beliTheoremTwo_eq_unit_proved
#check @Bong.BONG.beliTheoremThree_proved

#print axioms Bong.BONG.beliTheoremOne_proved
#print axioms Bong.BONG.beliTheoremOne_set_proved
#print axioms Bong.Lattice.beliTheoremTwo_proved
#print axioms Bong.Lattice.beliTheoremTwo_eq_unit_proved
#print axioms Bong.BONG.beliTheoremThree_proved
