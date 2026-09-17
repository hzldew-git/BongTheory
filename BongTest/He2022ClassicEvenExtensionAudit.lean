/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.He2022ClassicSectionEight

/-!
# Focused audit for the proved even scope of Lemma 8.3 and Theorem 1.8

The author-corrected v5 statements are unrestricted, while their written
argument begins with the even case and gives no valid odd reduction.  These
endpoints expose exactly the proved `n >= 2`, even-rank scope.
-/

#check Bong.HeClassic2024ExtensionData.Lemma83Laws
#check Bong.HeClassic2024ExtensionData.Lemma83Laws.he2022ClassicLemma83_even
#check Bong.HeClassic2024ExtensionData.Lemma83Laws.he2022ClassicTheorem18_even

#print axioms Bong.HeClassic2024ExtensionData.Lemma83Laws.he2022ClassicLemma83_even
#print axioms Bong.HeClassic2024ExtensionData.Lemma83Laws.he2022ClassicTheorem18_even
