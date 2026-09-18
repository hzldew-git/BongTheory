/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.He2022ClassicSectionEight
import Bong.Lattice.He2022ClassicLemma83Carrier
import Bong.Lattice.He2022ClassicCompletionLatticeScalarExtension
import Bong.Lattice.He2022ClassicScalarExtensionBONGIsometry

/-!
# Focused audit for the proved even scope of Lemma 8.3 and Theorem 1.8

The author-corrected v6 statements explicitly assume even `n >= 2`. The
carrier lemma proves the orthogonal-basis equality deduction.  The new
finite-completion theorems identify the specified scalar-extension lattice
with the pure-tensor span and transport every integral basis to its base
change.  A mapped diagonal realization is isometric to the literal scalar
extension under explicit BONG basis-lattice hypotheses.  Establishing those
hypotheses for the actual independently constructed upper good-BONG lattice
remains open.  The local obstruction
and global extension results remain conditional on their arithmetic data.
-/

#check Bong.HeClassic2024ExtensionData.Lemma83Laws
#check Bong.HeClassic2024ExtensionData.Lemma83Laws.he2022ClassicLemma83_even
#check Bong.HeClassic2024ExtensionData.Lemma83Laws.he2022ClassicTheorem18_even
#check Bong.HeClassic2024Carrier.he2022ClassicLemma83_carrier_eq_of_basisTransport
#check Bong.Lattice.scalarExtension_toSubmodule_eq_span
#check Bong.Lattice.scalarExtension_basisLattice
#check Bong.HeClassic2024NumberFieldScalarExtension.completionMap_preserves_integerRing
#check Bong.HeClassic2024NumberFieldScalarExtension.completionScalarExtension_toSubmodule_eq_span
#check Bong.HeClassic2024NumberFieldScalarExtension.completionScalarExtension_basisLattice
#check Bong.Lattice.scalarExtension_basisLattice_isIsometric_of_mappedValues
#check Bong.Lattice.scalarExtension_isIsometric_of_mappedValues
#check Bong.Lattice.scalarExtension_isIsometric_diagonalRealization

#print axioms Bong.HeClassic2024ExtensionData.Lemma83Laws.he2022ClassicLemma83_even
#print axioms Bong.HeClassic2024ExtensionData.Lemma83Laws.he2022ClassicTheorem18_even
#print axioms Bong.HeClassic2024Carrier.he2022ClassicLemma83_carrier_eq_of_basisTransport
#print axioms Bong.Lattice.scalarExtension_toSubmodule_eq_span
#print axioms Bong.Lattice.scalarExtension_basisLattice
#print axioms Bong.HeClassic2024NumberFieldScalarExtension.completionMap_preserves_integerRing
#print axioms Bong.HeClassic2024NumberFieldScalarExtension.completionScalarExtension_toSubmodule_eq_span
#print axioms Bong.HeClassic2024NumberFieldScalarExtension.completionScalarExtension_basisLattice
#print axioms Bong.Lattice.scalarExtension_basisLattice_isIsometric_of_mappedValues
#print axioms Bong.Lattice.scalarExtension_isIsometric_of_mappedValues
#print axioms Bong.Lattice.scalarExtension_isIsometric_diagonalRealization
