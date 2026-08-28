/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328HyperbolicizedComponents
import Bong.Lattice.OmearaComponentwiseFundamentalTransfer

/-!
# Rank-four Jordan systems in O'Meara 93:28

The componentwise reductions of the negatively adjoined source and target
are assembled here into actual Jordan decompositions.  Both decompositions
are saturated, have the same fundamental type, and every component has rank
four.  Every source component space is explicitly identified with a pair of
scaled hyperbolic planes.
-/

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [DyadicDiscriminantClassLaws K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}

/-- Hypotheses and concrete data for the simultaneous rank-four reduction
of two saturated Jordan splittings. -/
structure Omeara9328RankFourReductionSystem
    (J : JordanDecomposition q L (n + 2))
    (H : JordanDecomposition r M (n + 2)) where
  sourceSaturated : J.IsSaturated
  targetSaturated : H.IsSaturated
  fundamentalType : SameFundamentalType J H
  componentRank_atLeastTwo : ∀ i, 2 ≤ J.componentRank i

namespace Omeara9328RankFourReductionSystem

variable {J : JordanDecomposition q L (n + 2)}
  {H : JordanDecomposition r M (n + 2)}
  (S : Omeara9328RankFourReductionSystem J H)

/-- The paired 93:18(v) reduction at one Jordan scale. -/
noncomputable def pair (i : Fin (n + 2)) :
    Omeara9328RankFourComponentPairData J H i :=
  Omeara9328RankFourComponentPairData.ofSaturated J H i
    S.sourceSaturated S.targetSaturated S.fundamentalType
    (S.componentRank_atLeastTwo i)

/-- Carrier family of the source rank-four residuals. -/
noncomputable abbrev sourceCarrier (i : Fin (n + 2)) : Type v :=
  (S.pair i).source.Carrier

/-- Source rank-four residual forms. -/
noncomputable abbrev sourceForm (i : Fin (n + 2)) :
    QuadraticSpace K (S.sourceCarrier i) :=
  (S.pair i).source.form

/-- Source rank-four residual lattices. -/
noncomputable abbrev sourceLattice (i : Fin (n + 2)) :
    Lattice K (S.sourceCarrier i) :=
  (S.pair i).source.lattice

/-- Carrier family of the target rank-four residuals. -/
noncomputable abbrev targetCarrier (i : Fin (n + 2)) : Type (max v w) :=
  (S.pair i).target.Carrier

/-- Target rank-four residual forms. -/
noncomputable abbrev targetForm (i : Fin (n + 2)) :
    QuadraticSpace K (S.targetCarrier i) :=
  (S.pair i).target.form

/-- Target rank-four residual lattices. -/
noncomputable abbrev targetLattice (i : Fin (n + 2)) :
    Lattice K (S.targetCarrier i) :=
  (S.pair i).target.lattice

theorem source_modular (i : Fin (n + 2)) :
    IsModular (S.sourceForm i) (S.sourceLattice i)
      (J.scaleGenerator i) :=
  (S.pair i).source.residual_modular

theorem target_modular (i : Fin (n + 2)) :
    IsModular (S.targetForm i) (S.targetLattice i)
      (J.scaleGenerator i) :=
  (S.pair i).target.residual_modular

theorem source_finrank (i : Fin (n + 2)) :
    finrank K (S.sourceCarrier i) = 4 :=
  (S.pair i).source.residual_finrank

theorem target_finrank (i : Fin (n + 2)) :
    finrank K (S.targetCarrier i) = 4 :=
  (S.pair i).target.residual_finrank

/-- A chosen norm generator on one source residual. -/
noncomputable def sourceNormGeneratorVector (i : Fin (n + 2)) :
    S.sourceCarrier i :=
  Classical.choose <| exists_isNormGenerator_of_finrank_pos
    (S.sourceForm i) (S.sourceLattice i) (by rw [S.source_finrank i]; omega)

theorem sourceNormGeneratorVector_spec (i : Fin (n + 2)) :
    IsNormGenerator (S.sourceForm i) (S.sourceLattice i)
        (S.sourceNormGeneratorVector i) ∧
      (S.sourceForm i).IsAnisotropic (S.sourceNormGeneratorVector i) :=
  Classical.choose_spec <| exists_isNormGenerator_of_finrank_pos
    (S.sourceForm i) (S.sourceLattice i) (by rw [S.source_finrank i]; omega)

noncomputable def sourceNormGenerator (i : Fin (n + 2)) : Kˣ :=
  Units.mk0 ((S.sourceForm i).quadratic (S.sourceNormGeneratorVector i))
    (S.sourceNormGeneratorVector_spec i).2

theorem source_normIdeal_eq (i : Fin (n + 2)) :
    normIdeal (S.sourceForm i) (S.sourceLattice i) =
      principalIdeal (K := K) (S.sourceNormGenerator i : K) :=
  (S.sourceNormGeneratorVector_spec i).1.normIdeal_eq

theorem source_scaleIdeal_eq (i : Fin (n + 2)) :
    scaleIdeal (S.sourceForm i) (S.sourceLattice i) =
      principalIdeal (K := K) (J.scaleGenerator i : K) :=
  (S.source_modular i).scaleIdeal_eq_principal
    (by rw [S.source_finrank i]; omega)

/-- A chosen norm generator on one target residual. -/
noncomputable def targetNormGeneratorVector (i : Fin (n + 2)) :
    S.targetCarrier i :=
  Classical.choose <| exists_isNormGenerator_of_finrank_pos
    (S.targetForm i) (S.targetLattice i) (by rw [S.target_finrank i]; omega)

theorem targetNormGeneratorVector_spec (i : Fin (n + 2)) :
    IsNormGenerator (S.targetForm i) (S.targetLattice i)
        (S.targetNormGeneratorVector i) ∧
      (S.targetForm i).IsAnisotropic (S.targetNormGeneratorVector i) :=
  Classical.choose_spec <| exists_isNormGenerator_of_finrank_pos
    (S.targetForm i) (S.targetLattice i) (by rw [S.target_finrank i]; omega)

noncomputable def targetNormGenerator (i : Fin (n + 2)) : Kˣ :=
  Units.mk0 ((S.targetForm i).quadratic (S.targetNormGeneratorVector i))
    (S.targetNormGeneratorVector_spec i).2

theorem target_normIdeal_eq (i : Fin (n + 2)) :
    normIdeal (S.targetForm i) (S.targetLattice i) =
      principalIdeal (K := K) (S.targetNormGenerator i : K) :=
  (S.targetNormGeneratorVector_spec i).1.normIdeal_eq

theorem target_scaleIdeal_eq (i : Fin (n + 2)) :
    scaleIdeal (S.targetForm i) (S.targetLattice i) =
      principalIdeal (K := K) (J.scaleGenerator i : K) :=
  (S.target_modular i).scaleIdeal_eq_principal
    (by rw [S.target_finrank i]; omega)

/-- Jordan decomposition of all source rank-four residuals. -/
noncomputable def sourceJordan :
    JordanDecomposition
      (BONG.blockOrthogonalForm (n + 1) S.sourceCarrier S.sourceForm)
      (BONG.blockProductLattice (n + 1) S.sourceCarrier S.sourceLattice)
      (n + 2) :=
  BONG.blockProductJordanDecomposition S.sourceCarrier S.sourceForm
    S.sourceLattice J.scaleGenerator S.sourceNormGenerator
    S.source_modular S.source_scaleIdeal_eq S.source_normIdeal_eq
    (fun _ _ hij => J.scaleOrder_strict hij)

/-- Jordan decomposition of all target rank-four residuals. -/
noncomputable def targetJordan :
    JordanDecomposition
      (BONG.blockOrthogonalForm (n + 1) S.targetCarrier S.targetForm)
      (BONG.blockProductLattice (n + 1) S.targetCarrier S.targetLattice)
      (n + 2) :=
  BONG.blockProductJordanDecomposition S.targetCarrier S.targetForm
    S.targetLattice J.scaleGenerator S.targetNormGenerator
    S.target_modular S.target_scaleIdeal_eq S.target_normIdeal_eq
    (fun _ _ hij => J.scaleOrder_strict hij)

@[simp]
theorem sourceJordan_scaleGenerator (i : Fin (n + 2)) :
    S.sourceJordan.scaleGenerator i = J.scaleGenerator i := rfl

@[simp]
theorem targetJordan_scaleGenerator (i : Fin (n + 2)) :
    S.targetJordan.scaleGenerator i = J.scaleGenerator i := rfl

@[simp]
theorem sourceJordan_componentRank (i : Fin (n + 2)) :
    S.sourceJordan.componentRank i = 4 := by
  rw [sourceJordan, BONG.blockProductJordanDecomposition_componentRank,
    S.source_finrank]

@[simp]
theorem targetJordan_componentRank (i : Fin (n + 2)) :
    S.targetJordan.componentRank i = 4 := by
  rw [targetJordan, BONG.blockProductJordanDecomposition_componentRank,
    S.target_finrank]

/-- Each displayed source residual component has the original source
component norm group. -/
theorem sourceJordan_component_normGroupSet (i : Fin (n + 2)) :
    normGroupSet (S.sourceJordan.component i).space
        (S.sourceJordan.component i).lattice =
      normGroupSet (J.component i).space (J.component i).lattice := by
  let f := BONG.blockProductComponentIsometry S.sourceCarrier S.sourceForm
    S.sourceLattice i
  calc
    normGroupSet (S.sourceJordan.component i).space
        (S.sourceJordan.component i).lattice =
        normGroupSet (S.sourceForm i) (S.sourceLattice i) :=
      normGroupSet_eq_of_latticeIsometry f
    _ = normGroupSet (J.component i).space (J.component i).lattice :=
      (S.pair i).sourceResidualNormGroupSet_eq

/-- Each displayed target residual component has the same source component
norm group. -/
theorem targetJordan_component_normGroupSet (i : Fin (n + 2)) :
    normGroupSet (S.targetJordan.component i).space
        (S.targetJordan.component i).lattice =
      normGroupSet (J.component i).space (J.component i).lattice := by
  let f := BONG.blockProductComponentIsometry S.targetCarrier S.targetForm
    S.targetLattice i
  calc
    normGroupSet (S.targetJordan.component i).space
        (S.targetJordan.component i).lattice =
        normGroupSet (S.targetForm i) (S.targetLattice i) :=
      normGroupSet_eq_of_latticeIsometry f
    _ = normGroupSet (J.component i).space (J.component i).lattice :=
      (S.pair i).targetResidualNormGroupSet_eq

theorem sourceJordan_component_scaleIdeal (i : Fin (n + 2)) :
    scaleIdeal (S.sourceJordan.component i).space
        (S.sourceJordan.component i).lattice =
      scaleIdeal (J.component i).space (J.component i).lattice := by
  rw [S.sourceJordan.scaleIdeal_eq i, J.scaleIdeal_eq i,
    S.sourceJordan_scaleGenerator i]

theorem targetJordan_component_scaleIdeal (i : Fin (n + 2)) :
    scaleIdeal (S.targetJordan.component i).space
        (S.targetJordan.component i).lattice =
      scaleIdeal (J.component i).space (J.component i).lattice := by
  rw [S.targetJordan.scaleIdeal_eq i, J.scaleIdeal_eq i,
    S.targetJordan_scaleGenerator i]

/-- Source residualization preserves all fundamental norm groups. -/
theorem sourceJordan_fundamentalNormGroup (i : Fin (n + 2)) :
    S.sourceJordan.fundamentalNormGroup i = J.fundamentalNormGroup i :=
  fundamentalNormGroup_eq_of_componentwise_eq
    (J := J) (H := S.sourceJordan)
    S.sourceJordan_scaleGenerator S.sourceJordan_component_scaleIdeal
      S.sourceJordan_component_normGroupSet i

/-- Target residualization preserves the source fundamental norm groups. -/
theorem targetJordan_fundamentalNormGroup (i : Fin (n + 2)) :
    S.targetJordan.fundamentalNormGroup i = J.fundamentalNormGroup i :=
  fundamentalNormGroup_eq_of_componentwise_eq
    (J := J) (H := S.targetJordan)
    S.targetJordan_scaleGenerator S.targetJordan_component_scaleIdeal
      S.targetJordan_component_normGroupSet i

/-- The assembled source rank-four splitting is saturated. -/
theorem sourceJordan_isSaturated : S.sourceJordan.IsSaturated := by
  intro i
  calc
    normGroupSet (S.sourceJordan.component i).space
        (S.sourceJordan.component i).lattice =
        normGroupSet (J.component i).space (J.component i).lattice :=
      S.sourceJordan_component_normGroupSet i
    _ = J.fundamentalNormGroup i := S.sourceSaturated i
    _ = S.sourceJordan.fundamentalNormGroup i :=
      (S.sourceJordan_fundamentalNormGroup i).symm

/-- The assembled target rank-four splitting is saturated. -/
theorem targetJordan_isSaturated : S.targetJordan.IsSaturated := by
  intro i
  calc
    normGroupSet (S.targetJordan.component i).space
        (S.targetJordan.component i).lattice =
        normGroupSet (J.component i).space (J.component i).lattice :=
      S.targetJordan_component_normGroupSet i
    _ = J.fundamentalNormGroup i := S.sourceSaturated i
    _ = S.targetJordan.fundamentalNormGroup i :=
      (S.targetJordan_fundamentalNormGroup i).symm

/-- The two assembled rank-four Jordan splittings have the same complete
fundamental type. -/
noncomputable def residualFundamentalType :
    SameFundamentalType S.sourceJordan S.targetJordan where
  indexEquiv := Equiv.refl (Fin (n + 2))
  index_val := fun _ => rfl
  componentRank_eq := by intro i; simp
  scaleOrder_eq := by
    intro i
    unfold fundamentalScaleOrder
    simp
  normGroup_eq := by
    intro i
    exact (S.targetJordan_fundamentalNormGroup i).trans
      (S.sourceJordan_fundamentalNormGroup i).symm

/-- Every source residual component space is a pair of scaled hyperbolic
planes. -/
theorem sourceJordan_componentSpace_hyperbolic (i : Fin (n + 2)) :
    (S.sourceJordan.component i).space.IsIsometric
      (QuadraticSpace.scaledZeroOmearaTowerForm (J.scaleGenerator i) 2) := by
  let f := BONG.blockProductComponentIsometry S.sourceCarrier S.sourceForm
    S.sourceLattice i
  exact ⟨f.symm.toQuadraticSpaceIsometry.trans
    (S.pair i).sourceResidualSpaceIsometry⟩

end Omeara9328RankFourReductionSystem

end Lattice.JordanDecomposition

end Bong
