/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019MainTheorem
import Bong.Bong.Beli2019ComplementaryHilbertChoice
import Bong.Bong.MaximalDefectClassProof

/-!
# He--Hu (2024), Definition 3.1 and Proposition 3.2

The published definition chooses an element `c#` from an auxiliary unit
expansion.  Its later use depends only on the three properties isolated in
Proposition 3.2.  Here `heHuSharpData` makes a canonical noncomputable choice
from the proved complementary-defect theorem.  Proposition 3.3 below will
show that the resulting binary isometry class is independent of this choice,
which is exactly the independence asserted in the paper.
-/

namespace Bong

open Dyadic
open BONG.GoodBONG

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The source domain
`F^x \ (F^{x2} union Delta F^{x2})` in Definition 3.1. -/
structure HeHuSharpDomain (c : Kˣ) : Prop where
  notSquare : ¬ IsSquare c
  notDiscriminantSquare :
    ¬ IsSquare (c /
      (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit)

/-- A choice of `c#` together with the exact data in Proposition 3.2.
The subtraction formula is kept over `ℚ`; the source defect is proved to be
an integer in `heHuSharpData_sourceDefect_integer` below. -/
structure HeHuSharpData (c : Kˣ) where
  sourceDefect : ℚ
  sourceDefect_integer : ∃ d : Nat, sourceDefect = d
  sourceDefect_nonneg : 0 ≤ sourceDefect
  sourceDefect_lt_twoE :
    sourceDefect < 2 * (ramificationIndex K : ℚ)
  source_defectOrder :
    defectOrder (K := K) c = (sourceDefect : WithTop ℚ)
  sharp : Kˣ
  sharp_isValuationUnit : IsValuationUnit K (sharp : K)
  sharp_defectOrder :
    defectOrder (K := K) sharp =
      ((2 * (ramificationIndex K : ℚ) - sourceDefect : ℚ) :
        WithTop ℚ)
  sharp_hilbert : hilbertSymbol K sharp c = -1

/-- Existence of the `c#` data for every square class in the published
domain.  All local-field inputs invoked here have proved instances in the
repository. -/
noncomputable def heHuSharpData (c : Kˣ) (hc : HeHuSharpDomain c) :
    HeHuSharpData c := by
  let d : Nat := (quadraticDefect K c).toNat
  have hfinite : quadraticDefect K c ≠ ⊤ := by
    intro htop
    exact hc.notSquare
      ((quadraticDefect_eq_top_iff_isSquare (K := K) c).mp htop)
  have hdefectCoe : quadraticDefect K c = (d : ℕ∞) := by
    simpa only [d] using (ENat.coe_toNat hfinite).symm
  have hdLe : d ≤ 2 * ramificationIndex K := by
    have hle := quadraticDefect_le_two_mul_e_of_not_isSquare
      (K := K) hc.notSquare
    rw [hdefectCoe] at hle
    exact_mod_cast hle
  have hdNe : d ≠ 2 * ramificationIndex K := by
    intro hd
    have hlarge : ((2 * ramificationIndex K : Nat) : ℕ∞) ≤
        quadraticDefect K c := by
      rw [hdefectCoe, hd]
    rcases isSquare_or_isSquare_div_discriminant_of_defect_ge_twoE
        c hlarge with hsquare | hdiscriminant
    · exact hc.notSquare hsquare
    · exact hc.notDiscriminantSquare hdiscriminant
  have hdLt : d < 2 * ramificationIndex K := lt_of_le_of_ne hdLe hdNe
  have hdefectOrder : defectOrder (K := K) c =
      ((d : ℚ) : WithTop ℚ) := by
    unfold defectOrder
    rw [hdefectCoe]
    rfl
  have hdNonnegative : (0 : ℚ) ≤ d := by positivity
  have hdLtQ : (d : ℚ) < 2 * (ramificationIndex K : ℚ) := by
    exact_mod_cast hdLt
  let hchoice := BONG.exists_complementaryDefect_hilbert_neg_of_nonnegative
    (K := K) c (d : ℚ) hdefectOrder hdNonnegative hdLtQ
  let sharp : Kˣ := Classical.choose hchoice
  have hsharp := Classical.choose_spec hchoice
  exact
    { sourceDefect := d
      sourceDefect_integer := ⟨d, rfl⟩
      sourceDefect_nonneg := hdNonnegative
      sourceDefect_lt_twoE := hdLtQ
      source_defectOrder := hdefectOrder
      sharp := sharp
      sharp_isValuationUnit := hsharp.1
      sharp_defectOrder := hsharp.2.1
      sharp_hilbert := hsharp.2.2 }

/-- The selected element `c#` of Definition 3.1. -/
noncomputable def heHuSharp (c : Kˣ) (hc : HeHuSharpDomain c) : Kˣ :=
  (heHuSharpData c hc).sharp

/-- The paper's defect `d(c)` is integral for the chosen data. -/
theorem heHuSharpData_sourceDefect_integer (c : Kˣ)
    (hc : HeHuSharpDomain c) :
    ∃ d : Nat, (heHuSharpData c hc).sourceDefect = d := by
  exact (heHuSharpData c hc).sourceDefect_integer

/-- He--Hu, Proposition 3.2: `c#` is a unit, its defect is complementary
to that of `c`, and `(c#,c)_p=-1`. -/
theorem heHu2022Proposition32 (c : Kˣ) (hc : HeHuSharpDomain c) :
    IsValuationUnit K (heHuSharp c hc : K) ∧
      defectOrder (K := K) (heHuSharp c hc) =
        ((2 * (ramificationIndex K : ℚ) -
          (heHuSharpData c hc).sourceDefect : ℚ) : WithTop ℚ) ∧
      hilbertSymbol K (heHuSharp c hc) c = -1 := by
  exact ⟨(heHuSharpData c hc).sharp_isValuationUnit,
    (heHuSharpData c hc).sharp_defectOrder,
    (heHuSharpData c hc).sharp_hilbert⟩

end Bong
