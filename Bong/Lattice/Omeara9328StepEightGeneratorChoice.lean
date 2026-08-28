/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328StepEightBoundaryIdeals
import Bong.Lattice.Omeara9328GeneratorChoice

/-!
# Coherent generators through O'Meara 93:28, Step 8

The inserted fundamental scale uses the displayed generator `pi² a₀`;
all old choices are retained at their raised indices.  This is the coherent
generator family needed to transfer conditions (ii) and (iii).
-/

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
  (J : JordanDecomposition q L (n + 2))

/-- O'Meara's inserted generator formed from an arbitrary coherent old
choice. -/
noncomputable def stepEightRaisedNormGeneratorWith
    (A : FundamentalNormGeneratorChoice J) : Kˣ :=
  uniformizerUnit K ^ 2 * A.value 0

@[simp]
theorem stepEightRaisedNormGeneratorWith_order
    (A : FundamentalNormGeneratorChoice J) :
    ordUnit K (J.stepEightRaisedNormGeneratorWith A) =
      ordUnit K (A.value 0) + 2 := by
  have hpi : ordUnit K (uniformizerUnit K) = 1 := by
    apply WithTop.coe_injective
    rw [coe_ordUnit, coe_uniformizerUnit, ord_uniformizer]
    norm_num
  rw [stepEightRaisedNormGeneratorWith, ordUnit_mul, ordUnit_pow, hpi]
  omega

/-- The displayed `pi² a₀` is a norm generator at the inserted scale
for every coherent old choice, not only for the canonical choice. -/
theorem stepEightRaisedNormGeneratorWith_spec
    (A : FundamentalNormGeneratorChoice J)
    (hJ : J.IsSaturated)
    (hscaleGap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0))
    (hnormGap : ordUnit K (J.fundamentalNormGenerator 0) + 2 ≤
      ordUnit K (J.fundamentalNormGenerator 1))
    (hfirst : ordUnit K (J.fundamentalNormGenerator 0) <
      J.fundamentalScaleOrder 0 + (ramificationIndex K : Int)) :
    IsNormGeneratorValue
      (BONG.blockOrthogonalForm (n + 2)
        J.stepEightCarrier J.stepEightForm)
      ((J.stepEightJordan hscaleGap).fundamentalLattice 1)
      (J.stepEightRaisedNormGeneratorWith A) := by
  constructor
  · exact J.stepEightJordan_sq_uniformizer_mem_insertedNormGroup
      hscaleGap (A.spec 0).1
  · have hcanonical :=
      J.stepEightJordan_fundamentalNormGenerator_order_inserted
        hJ hscaleGap hnormGap hfirst
    have hchoice : ordUnit K (A.value 0) =
        ordUnit K (J.fundamentalNormGenerator 0) := by
      apply (principalIdeal_eq_iff_ordUnit_eq _ _).mp
      exact (A.spec 0).2.symm.trans
        (J.fundamentalNormGenerator_spec 0).2
    have hideal : principalIdeal (K := K)
          ((J.stepEightJordan hscaleGap).fundamentalNormGenerator 1 : K) =
        principalIdeal (K := K)
          (J.stepEightRaisedNormGeneratorWith A : K) := by
      apply (principalIdeal_eq_iff_ordUnit_eq _ _).2
      rw [hcanonical, J.stepEightRaisedNormGeneratorWith_order, hchoice]
    exact ((J.stepEightJordan hscaleGap).fundamentalNormGenerator_spec 1).2.trans
      hideal

/-- Coherent fundamental norm generators for the raw Step-8 splitting. -/
noncomputable def stepEightFundamentalNormGeneratorChoice
    (A : FundamentalNormGeneratorChoice J)
    (hJ : J.IsSaturated)
    (hscaleGap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0))
    (hnormGap : ordUnit K (J.fundamentalNormGenerator 0) + 2 ≤
      ordUnit K (J.fundamentalNormGenerator 1))
    (hfirst : ordUnit K (J.fundamentalNormGenerator 0) <
      J.fundamentalScaleOrder 0 + (ramificationIndex K : Int)) :
    FundamentalNormGeneratorChoice (J.stepEightJordan hscaleGap) where
  value := Fin.cases (A.value 0)
    (Fin.cases (J.stepEightRaisedNormGeneratorWith A)
      (fun i => A.value i.succ))
  spec := by
    intro i
    cases i using Fin.cases with
    | zero =>
        have hidx : (0 : Fin (n + 3)) =
            (1 : Fin (n + 3)).succAbove (0 : Fin (n + 2)) := by
          apply Fin.ext
          simp
        apply isNormGeneratorValue_of_normGroupSet_eq (A.spec 0)
        · change J.fundamentalNormGroup 0 =
            (J.stepEightJordan hscaleGap).fundamentalNormGroup 0
          rw [hidx, J.stepEightJordan_fundamentalNormGroup_old]
        · exact (J.stepEightJordan hscaleGap).exists_fundamentalNormGenerator 0
    | succ i =>
        cases i using Fin.cases with
        | zero =>
            exact J.stepEightRaisedNormGeneratorWith_spec A hJ hscaleGap
              hnormGap hfirst
        | succ i =>
            have hidx : (i.succ.succ : Fin (n + 3)) =
                (1 : Fin (n + 3)).succAbove (i.succ : Fin (n + 2)) := by
              apply Fin.ext
              simp
            apply isNormGeneratorValue_of_normGroupSet_eq (A.spec i.succ)
            · change J.fundamentalNormGroup i.succ =
                (J.stepEightJordan hscaleGap).fundamentalNormGroup i.succ.succ
              rw [hidx, J.stepEightJordan_fundamentalNormGroup_old]
            · exact (J.stepEightJordan hscaleGap).exists_fundamentalNormGenerator
                i.succ.succ

@[simp]
theorem stepEightFundamentalNormGeneratorChoice_inserted
    (A : FundamentalNormGeneratorChoice J)
    (hJ : J.IsSaturated)
    (hscaleGap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0))
    (hnormGap : ordUnit K (J.fundamentalNormGenerator 0) + 2 ≤
      ordUnit K (J.fundamentalNormGenerator 1))
    (hfirst : ordUnit K (J.fundamentalNormGenerator 0) <
      J.fundamentalScaleOrder 0 + (ramificationIndex K : Int)) :
    (J.stepEightFundamentalNormGeneratorChoice A hJ hscaleGap hnormGap hfirst).value 1 =
      J.stepEightRaisedNormGeneratorWith A := by
  rfl

@[simp]
theorem stepEightFundamentalNormGeneratorChoice_old
    (A : FundamentalNormGeneratorChoice J)
    (hJ : J.IsSaturated)
    (hscaleGap : 1 < ordUnit K (J.scaleGenerator 1) -
      ordUnit K (J.scaleGenerator 0))
    (hnormGap : ordUnit K (J.fundamentalNormGenerator 0) + 2 ≤
      ordUnit K (J.fundamentalNormGenerator 1))
    (hfirst : ordUnit K (J.fundamentalNormGenerator 0) <
      J.fundamentalScaleOrder 0 + (ramificationIndex K : Int))
    (i : Fin (n + 2)) :
    (J.stepEightFundamentalNormGeneratorChoice A hJ hscaleGap hnormGap hfirst).value
        ((1 : Fin (n + 3)).succAbove i) = A.value i := by
  cases i using Fin.cases with
  | zero => rfl
  | succ i => simp [stepEightFundamentalNormGeneratorChoice]

end Lattice.JordanDecomposition

end Bong
