/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.He2022ClassicSectionEight
import Bong.Lattice.He2022ClassicLemma83Carrier

/-!
# Focused audit for the proved even scope of Lemma 8.3 and Theorem 1.8

The author-corrected v6 statements explicitly assume even `n >= 2`. The
carrier lemma proves the orthogonal-basis equality deduction but retains
the concrete scalar-extension basis transport as an explicit hypothesis.
The local obstruction and global extension results remain conditional on
their declared arithmetic packages.
-/

#check Bong.HeClassic2024ExtensionData.Lemma83Laws
#check Bong.HeClassic2024ExtensionData.Lemma83Laws.he2022ClassicLemma83_even
#check Bong.HeClassic2024ExtensionData.Lemma83Laws.he2022ClassicTheorem18_even
#check Bong.HeClassic2024Carrier.he2022ClassicLemma83_carrier_eq_of_basisTransport

#print axioms Bong.HeClassic2024ExtensionData.Lemma83Laws.he2022ClassicLemma83_even
#print axioms Bong.HeClassic2024ExtensionData.Lemma83Laws.he2022ClassicTheorem18_even
#print axioms Bong.HeClassic2024Carrier.he2022ClassicLemma83_carrier_eq_of_basisTransport
