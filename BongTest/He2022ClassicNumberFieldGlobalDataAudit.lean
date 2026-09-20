/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.He2022ClassicNumberFieldGlobalData

/-!
# Focused audit for the canonical number-field Section 8 adapter
-/

open Bong
open Bong.HeClassic2024NumberFieldGlobalData

#check HeClassic2024NumberFieldGlobalData
#check HeClassic2024NumberFieldGlobalData.toGlobalData
#check HeClassic2024NumberFieldGlobalData.heightOneSpectrumIdentification
#check HeClassic2024NumberFieldGlobalData.numberFieldDiscriminantBridge
#check HeClassic2024NumberFieldGlobalData.SectionEightInputs
#check HeClassic2024NumberFieldGlobalData.sectionEightLaws

#print axioms HeClassic2024NumberFieldGlobalData.toGlobalData
#print axioms HeClassic2024NumberFieldGlobalData.heightOneSpectrumIdentification
#print axioms HeClassic2024NumberFieldGlobalData.numberFieldDiscriminantBridge
#print axioms HeClassic2024NumberFieldGlobalData.sectionEightLaws
