/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Lattice.He2023ADCSectionEight
import Bong.Lattice.NADC

/-!
# A concrete dyadic local model for He (2025), Section 8

This file instantiates the local objects and relations in
`GlobalLocalLatticeSystem` with the repository's actual bundled quadratic
lattices over one dyadic local field.  It proves that four of the five fields
in `LocalMaximalityLaws` follow from the concrete lattice API.  In the final
field, the equal-rank case is also proved; only the rank-`n+1` classification
direction remains an explicit hypothesis.

This is a one-place local model.  It is not a construction of quadratic
lattices over a number field and does not discharge the global arithmetic
interfaces in Section 8.
-/

namespace Bong

open Dyadic

namespace He2023ADCDyadicLocalModel

universe u

variable (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The concrete bundled lattice type used at the unique local place. -/
abbrev Model := Lattice.QuadraticLatticeModel (K := K)

/-- A one-place global/local system whose local component is the repository's
actual dyadic quadratic-lattice model.  The global fields are copied from the
same bundled object only so that the Section 8 local interface can be
instantiated without claiming a number-field construction. -/
noncomputable def system : GlobalLocalLatticeSystem where
  GlobalLattice := Model K
  Place := Unit
  LocalLattice := fun _ ↦ Model K
  globalRank := fun X ↦ X.rank
  localRank := fun X ↦ X.rank
  globalIntegral := fun X ↦ X.IsIntegral
  localIntegral := fun X ↦ X.IsIntegral
  globalAmbientRepresents := fun X Y ↦ X.AmbientlyRepresents Y
  globalAdmissible := fun X Y ↦ X.AmbientlyRepresents Y
  localAmbientRepresents := fun X Y ↦ X.AmbientlyRepresents Y
  globalRepresents := fun X Y ↦ X.Represents Y
  localRepresents := fun X Y ↦ X.Represents Y
  localize := fun _ X ↦ X
  localMaximal := fun X ↦ X.IsOMaximal
  localEquivalent := fun X Y ↦ Nonempty (X.Isometry Y)

/-- The abstract pointwise definition agrees with the concrete bundled
definition of local `n`-ADC-ness. -/
theorem isNADCAt_iff_isNADC (X : Model K) (n : Nat) :
    (system K).IsNADCAt X () n ↔ X.IsNADC n := by
  constructor
  · rintro ⟨hIntegral, hRepresents⟩
    refine ⟨hIntegral, ?_⟩
    intro W _ _ r N hRank hNIntegral hAmbient
    let Y : Model K :=
      { Carrier := W
        form := r
        lattice := N }
    exact hRepresents Y hRank hNIntegral hAmbient
  · intro h
    refine ⟨h.1, ?_⟩
    intro Y hRank hIntegral hAmbient
    exact h.represents hRank hIntegral hAmbient

/-- The concrete maximal-extension construction, including the ambient-space
compatibility needed by the abstract Section 8 argument. -/
theorem exists_oMaximal_extension (N : Model K) (hN : N.IsIntegral) :
    ∃ N' : Model K,
      N'.IsOMaximal ∧ N'.Represents N ∧
        ∀ M : Model K,
          M.AmbientlyRepresents N → M.AmbientlyRepresents N' := by
  letI : AddCommGroup N.Carrier := N.addCommGroup
  letI : Module K N.Carrier := N.module
  obtain ⟨P, hNP, hPMaximal⟩ :=
    Lattice.exists_oMaximal_superlattice (q := N.form) (L := N.lattice) hN
  let N' : Model K := { N with lattice := P }
  refine ⟨N', ?_, ?_, ?_⟩
  · exact hPMaximal
  · exact Lattice.represents_of_le N.form hNP
  · intro M hAmbient
    letI : AddCommGroup M.Carrier := M.addCommGroup
    letI : Module K M.Carrier := M.module
    change M.form.Represents N.form at hAmbient
    change M.form.Represents N.form
    exact hAmbient

/-- Concrete maximal lattices represent concrete maximal lattices whenever
their ambient quadratic spaces are in the representation relation. -/
theorem oMaximal_represents_of_ambient
    {X Y : Model K} (hX : X.IsOMaximal) (hY : Y.IsOMaximal)
    (hAmbient : X.AmbientlyRepresents Y) : X.Represents Y := by
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  letI : AddCommGroup Y.Carrier := Y.addCommGroup
  letI : Module K Y.Carrier := Y.module
  exact Lattice.IsOMaximal.represents_of_ambient hX hY hAmbient

/-- Concrete bundled lattice representations compose. -/
theorem represents_trans {X Y Z : Model K} :
    X.Represents Y → Y.Represents Z → X.Represents Z := by
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  letI : AddCommGroup Y.Carrier := Y.addCommGroup
  letI : Module K Y.Carrier := Y.module
  letI : AddCommGroup Z.Carrier := Z.addCommGroup
  letI : Module K Z.Carrier := Z.module
  exact Lattice.Represents.trans

/-- In the concrete one-place model, all generic local maximality laws reduce
to a single classification input in ambient rank `n+1`.  The equal-rank
necessity direction is supplied by the proved concrete Proposition 4.15. -/
theorem localMaximalityLaws_of_rank_succ_necessity
    (hSucc : ∀ (X : Model K) (n : Nat),
      2 ≤ n → X.rank = n + 1 → X.IsNADC n → X.IsOMaximal) :
    HeADC2025GlobalData.LocalMaximalityLaws (S := system K) := by
  constructor
  · intro p M hM
    letI : AddCommGroup M.Carrier := M.addCommGroup
    letI : Module K M.Carrier := M.module
    exact hM.isIntegral
  · intro p N hN
    exact exists_oMaximal_extension K N hN
  · intro p M N hM hN hAmbient
    exact oMaximal_represents_of_ambient K hM hN hAmbient
  · intro p M N P hMN hNP
    exact represents_trans K hMN hNP
  · intro M p n hTwo hRank hNADC
    cases p
    change M.IsOMaximal
    have hConcrete : M.IsNADC n :=
      (isNADCAt_iff_isNADC K M n).mp hNADC
    rcases hRank with hRank | hRank
    · letI : AddCommGroup M.Carrier := M.addCommGroup
      letI : Module K M.Carrier := M.module
      exact Lattice.IsNADC.isOMaximal_of_finrank_eq hConcrete hRank
    · exact hSucc M n hTwo hRank hConcrete

/-- Theorem 1.5(i) in the concrete one-place model, conditional only on its
rank-`n+1` classification direction. -/
theorem local_theorem15_of_rank_succ_necessity
    (hSucc : ∀ (X : Model K) (n : Nat),
      2 ≤ n → X.rank = n + 1 → X.IsNADC n → X.IsOMaximal)
    (M : Model K) (n : Nat) (hTwo : 2 ≤ n)
    (hRank : M.rank = n ∨ M.rank = n + 1) :
    (system K).IsNADCAt M () n ↔
      (system K).localMaximal (p := ()) M :=
  (localMaximalityLaws_of_rank_succ_necessity K hSucc).local_theorem15
    M () n hTwo hRank

end He2023ADCDyadicLocalModel

end Bong
