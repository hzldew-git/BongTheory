/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019PrimeIndexBasis

/-!
# Prime-index chains from Smith power bases

The sum of the Smith exponents is a decreasing measure.  Strong induction on
that sum factors every lattice inclusion into one-coordinate uniformizer
steps.  Thus the purely lattice-theoretic prime chain used in Section 5 is
constructed from the DVR and no longer belongs to the local-law boundary.
-/

namespace Bong.Lattice

open Module
open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

/-- Extending any integral basis of a lattice recovers that lattice as its
integral basis lattice. -/
theorem basisLattice_extendOfIntegralBasis
    (L : Lattice K V)
    (b : Basis (Fin (finrank K V)) (IntegerRing K) L.toSubmodule) :
    basisLattice (b.extendOfIsLattice K) = L := by
  apply Lattice.ext
  change Submodule.span (IntegerRing K)
      (Set.range (b.extendOfIsLattice K)) = L.toSubmodule
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    simpa [Basis.extendOfIsLattice_apply] using (b i).property
  · intro x hx
    have hx' : (⟨x, hx⟩ : L.toSubmodule) ∈
        Submodule.span (IntegerRing K) (Set.range b) := by
      rw [b.span_eq]
      trivial
    rw [Submodule.mem_span_range_iff_exists_fun] at hx' ⊢
    rcases hx' with ⟨f, hf⟩
    refine ⟨f, ?_⟩
    simpa [Basis.extendOfIsLattice_apply] using congrArg Subtype.val hf

/-- A finite chain of literal index-`\mathfrak p` inclusions. -/
inductive IndexPChain (q : QuadraticSpace K V) :
    Lattice K V → Lattice K V → Prop
  | refl (L : Lattice K V) : IndexPChain q L L
  | step {L M N : Lattice K V} (prior : IndexPChain q L M)
      (next : Beli2019IndexPInclusion q M N) : IndexPChain q L N

/-- Scale each coordinate of a basis by its prescribed nonnegative
uniformizer power. -/
noncomputable def powerBasis
    (b : Basis (Fin (finrank K V)) K V)
    (e : Fin (finrank K V) → Nat) : Basis (Fin (finrank K V)) K V :=
  b.unitsSMul (fun i => uniformizerUnit K ^ e i)

@[simp]
theorem powerBasis_zero
    (b : Basis (Fin (finrank K V)) K V) :
    powerBasis b (fun _ => 0) = b := by
  ext i
  rw [powerBasis, Basis.unitsSMul_apply]
  simp

/-- Increasing one power exponent is exactly one coordinate-scale step. -/
theorem coordinateScaleBasis_powerBasis
    (b : Basis (Fin (finrank K V)) K V)
    (e : Fin (finrank K V) → Nat) (i : Fin (finrank K V)) :
    coordinateScaleBasis (powerBasis b e) i =
      powerBasis b (Function.update e i (e i + 1)) := by
  classical
  ext j
  by_cases hji : j = i
  · subst j
    rw [coordinateScaleBasis_apply_same]
    simp only [powerBasis, Basis.unitsSMul_apply]
    rw [Function.update_self]
    simp only [Units.smul_def, Units.val_pow_eq_pow_val,
      coe_uniformizerUnit, smul_smul]
    rw [pow_succ, mul_comm]
  · rw [coordinateScaleBasis_apply_of_ne _ hji]
    simp only [powerBasis, Basis.unitsSMul_apply]
    rw [Function.update_of_ne hji]

/-- Every nonnegative power vector is reached by a finite sequence of
one-coordinate index-`\mathfrak p` steps. -/
theorem indexPChain_powerBasis
    (q : QuadraticSpace K V)
    (b : Basis (Fin (finrank K V)) K V)
    (e : Fin (finrank K V) → Nat) :
    IndexPChain q (basisLattice b) (basisLattice (powerBasis b e)) := by
  classical
  generalize htotal : (∑ i, e i) = total
  induction total using Nat.strong_induction_on generalizing e with
  | h total ih =>
      by_cases hzero : total = 0
      · have hsum : ∑ i, e i = 0 := by omega
        have he : e = fun _ => 0 := by
          funext i
          have hall := (Finset.sum_eq_zero_iff_of_nonneg
            (s := Finset.univ) (f := e) (by simp)).mp hsum
          exact hall i (Finset.mem_univ i)
        rw [he, powerBasis_zero]
        exact IndexPChain.refl (basisLattice b)
      · have hsumpos : 0 < ∑ i, e i := by omega
        rcases Finset.sum_pos_iff.mp hsumpos with ⟨i, _, hi⟩
        let e' := Function.update e i (e i - 1)
        have heRecover : Function.update e' i (e' i + 1) = e := by
          funext j
          by_cases hji : j = i
          · subst j
            simp [e', Function.update]
            omega
          · simp [e', Function.update, hji]
        have hsumlt : ∑ j, e' j < total := by
          rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
          have hdecomp := Finset.sum_erase_add Finset.univ e
            (Finset.mem_univ i)
          simp only [Finset.sdiff_singleton_eq_erase] at *
          omega
        have prior := ih (∑ j, e' j) hsumlt e' rfl
        have next := indexPInclusion_coordinateScaleBasis q
          (powerBasis b e') i
        have chain := IndexPChain.step prior next
        rw [coordinateScaleBasis_powerBasis, heRecover] at chain
        exact chain

namespace SmithPowerBasisData

/-- The ambient field basis extending the Smith basis of the larger
lattice. -/
noncomputable def topAmbientBasis {N M : Lattice K V}
    (D : SmithPowerBasisData N M) :
    Basis (Fin (finrank K V)) K V :=
  D.topBasis.extendOfIsLattice K

/-- The ambient field basis extending the normalized Smith basis of the
smaller lattice. -/
noncomputable def botAmbientBasis {N M : Lattice K V}
    (D : SmithPowerBasisData N M) :
    Basis (Fin (finrank K V)) K V :=
  D.botBasis.extendOfIsLattice K

theorem basisLattice_topAmbientBasis {N M : Lattice K V}
    (D : SmithPowerBasisData N M) :
    basisLattice D.topAmbientBasis = M :=
  basisLattice_extendOfIntegralBasis M D.topBasis

theorem basisLattice_botAmbientBasis {N M : Lattice K V}
    (D : SmithPowerBasisData N M) :
    basisLattice D.botAmbientBasis = N :=
  basisLattice_extendOfIntegralBasis N D.botBasis

theorem powerBasis_top_eq_bot {N M : Lattice K V}
    (D : SmithPowerBasisData N M) :
    powerBasis D.topAmbientBasis D.exponent = D.botAmbientBasis := by
  ext i
  rw [powerBasis, Basis.unitsSMul_apply]
  rw [topAmbientBasis, botAmbientBasis,
    Basis.extendOfIsLattice_apply, Basis.extendOfIsLattice_apply]
  rw [D.botBasis_eq, Units.smul_def]
  congr 1

/-- The Smith power data gives the required finite prime chain. -/
theorem indexPChain {N M : Lattice K V}
    (q : QuadraticSpace K V) (D : SmithPowerBasisData N M) :
    IndexPChain q M N := by
  have chain := indexPChain_powerBasis q D.topAmbientBasis D.exponent
  rw [D.basisLattice_topAmbientBasis, D.powerBasis_top_eq_bot,
    D.basisLattice_botAmbientBasis] at chain
  exact chain

end SmithPowerBasisData

/-- Every lattice inclusion factors into a finite chain of literal
index-`\mathfrak p` inclusions. -/
theorem indexPChain_of_le
    (q : QuadraticSpace K V) (N M : Lattice K V) (hNM : N ≤ M) :
    IndexPChain q M N := by
  let D := Classical.choice (exists_smithPowerBasisData N M hNM)
  exact D.indexPChain q

end Bong.Lattice
