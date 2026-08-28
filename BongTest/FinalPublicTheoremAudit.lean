/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2006MainTheorems
import Bong.Bong.Beli2009BinaryConnectivityComplete
import Bong.Bong.BeliTheoremOneProof
import Bong.Bong.BeliTheoremTwoProof
import Bong.Bong.BeliTheoremThreeUnconditional

/-!
# Public theorem and trust-boundary audit

These are the unconditional endpoints for Beli 2003, 2006, 2009/2010, and
2019 v2.  Their printed signatures expose the ambient dyadic-local-field data
but no project-specific law or data interfaces.
-/

-- Beli 2003, Theorems 1--3.
#check @Bong.BONG.beliTheoremOne_proved
#check @Bong.BONG.beliTheoremOne_set_proved
#check @Bong.Lattice.beliTheoremTwo_proved
#check @Bong.Lattice.beliTheoremTwo_eq_unit_proved
#check @Bong.BONG.beliTheoremThree_proved

-- Beli 2006, Theorems 3.2 and 4.5.
#check @Bong.beli2006Theorem32_proved
#check @Bong.beli2006Theorem45_proved

-- Beli 2009/2010, Theorem 3.1 and the final Section 5 conclusions.
#check @Bong.BONG.GoodBONG.beli2009Theorem31_concrete
#check @Bong.beli2009Section5_largeResidueConnectivity_proved
#check @Bong.Beli2009FinalRemarksProof.beli2009Section5_residueTwoParametricCounterexample_proved
#check @Bong.Beli2009FinalRemarksProof.beli2009Section5_residueTwoCounterexample_proved
#check @Bong.Beli2009FinalRemarksProof.beli2009Section5_q2Counterexample_proved
#check @Bong.beli2009Section5_binaryTransformationDichotomy_proved

-- Beli 2019 v2, Theorem 2.1 in its two equivalent presentations.
#check @Bong.beli2019Theorem21
#check @Bong.beli2019Theorem21_prime

#print axioms Bong.BONG.beliTheoremOne_proved
#print axioms Bong.BONG.beliTheoremOne_set_proved
#print axioms Bong.Lattice.beliTheoremTwo_proved
#print axioms Bong.Lattice.beliTheoremTwo_eq_unit_proved
#print axioms Bong.BONG.beliTheoremThree_proved
#print axioms Bong.beli2006Theorem32_proved
#print axioms Bong.beli2006Theorem45_proved
#print axioms Bong.BONG.GoodBONG.beli2009Theorem31_concrete
#print axioms Bong.beli2009Section5_largeResidueConnectivity_proved
#print axioms Bong.Beli2009FinalRemarksProof.beli2009Section5_residueTwoParametricCounterexample_proved
#print axioms Bong.Beli2009FinalRemarksProof.beli2009Section5_residueTwoCounterexample_proved
#print axioms Bong.Beli2009FinalRemarksProof.beli2009Section5_q2Counterexample_proved
#print axioms Bong.beli2009Section5_binaryTransformationDichotomy_proved
#print axioms Bong.beli2019Theorem21
#print axioms Bong.beli2019Theorem21_prime

-- The only three project `opaque` declarations are definitions with
-- kernel-checked bodies, not assumptions.  Audit them explicitly because
-- opacity alone should not be confused with an axiom.
#print axioms Bong.Lattice.JordanDecomposition.saturationStepResult
#print axioms Bong.Lattice.omearaTwoPlaneAddLatticeIsometry
#print axioms Bong.Lattice.omearaTwoPlaneSquareAddLatticeIsometry
