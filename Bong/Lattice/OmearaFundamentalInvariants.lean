/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.JordanDecompositionInvariants
import Bong.Bong.Beli2009WeightIdealIsometry
import Bong.Lattice.JordanIsometry

/-!
# O'Meara's fundamental invariants under lattice isometry

For a Jordan component of scale `s_i`, O'Meara defines the fundamental norm
group and weight using the intrinsic lattice `L^{s_i}`.  This file gives those
objects their direct Lean definitions and proves that integral isometries
preserve the component scale, rank, norm group, weight, and admissible norm
generators after the canonical matching of Jordan components by scale.
-/

namespace Bong

open Dyadic
open Module

namespace Lattice.JordanDecomposition

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

/-- Match the Jordan components of isometric lattices by their scale. -/
noncomputable def scaleIndexEquivOfIsometry {s t : Nat}
    (J : JordanDecomposition q L t) (H : JordanDecomposition r M s)
    (f : Lattice.Isometry q r L M) : Fin t ≃ Fin s :=
  (J.mapIsometry f).scaleIndexEquiv H

@[simp]
theorem scaleOrder_scaleIndexEquivOfIsometry {s t : Nat}
    (J : JordanDecomposition q L t) (H : JordanDecomposition r M s)
    (f : Lattice.Isometry q r L M) (i : Fin t) :
    ordUnit K (H.scaleGenerator (J.scaleIndexEquivOfIsometry H f i)) =
      ordUnit K (J.scaleGenerator i) := by
  exact (J.mapIsometry f).scaleOrder_scaleIndexEquiv H i

@[simp]
theorem componentRank_scaleIndexEquivOfIsometry {s t : Nat}
    (J : JordanDecomposition q L t) (H : JordanDecomposition r M s)
    (f : Lattice.Isometry q r L M) (i : Fin t) :
    H.componentRank (J.scaleIndexEquivOfIsometry H f i) =
      J.componentRank i := by
  calc
    H.componentRank (J.scaleIndexEquivOfIsometry H f i) =
        (J.mapIsometry f).componentRank i :=
      (J.mapIsometry f).componentRank_scaleIndexEquiv H i
    _ = J.componentRank i := J.mapIsometry_componentRank f i

@[simp]
theorem scaleIndexEquivOfIsometry_val {s t : Nat}
    (J : JordanDecomposition q L t) (H : JordanDecomposition r M s)
    (f : Lattice.Isometry q r L M) (i : Fin t) :
    (J.scaleIndexEquivOfIsometry H f i).val = i.val :=
  (J.mapIsometry f).scaleIndexEquiv_val H i

/-- The scale order attached to a Jordan component. -/
noncomputable def fundamentalScaleOrder {t : Nat}
    (J : JordanDecomposition q L t) (i : Fin t) : Int :=
  ordUnit K (J.scaleGenerator i)

/-- O'Meara's intrinsic lattice `L^{s_i}` at the scale of the `i`th Jordan
component. -/
noncomputable def fundamentalLattice {t : Nat}
    (J : JordanDecomposition q L t) (i : Fin t) : Lattice K V :=
  Lattice.scaleTruncation q L (J.fundamentalScaleOrder i)

/-- The `i`th fundamental norm group. -/
noncomputable def fundamentalNormGroup {t : Nat}
    (J : JordanDecomposition q L t) (i : Fin t) : Set K :=
  Lattice.normGroupSet q (J.fundamentalLattice i)

/-- The `i`th fundamental weight ideal. -/
noncomputable def fundamentalWeightIdeal {t : Nat}
    (J : JordanDecomposition q L t) (i : Fin t) :
    CoefficientIdeal (K := K) :=
  Lattice.weightIdeal q (J.fundamentalLattice i)

/-- The valuation order of the `i`th fundamental weight ideal. -/
noncomputable def fundamentalWeightOrder {t : Nat}
    (J : JordanDecomposition q L t) (i : Fin t) : Int :=
  Lattice.weightIdealOrder q (J.fundamentalLattice i)

/-- Any nonempty Jordan decomposition witnesses positive ambient rank. -/
theorem ambient_finrank_pos_of_index {t : Nat}
    (J : JordanDecomposition q L t) (i : Fin t) :
    0 < finrank K V := by
  letI : Module.Finite K V := L.moduleFinite
  exact lt_of_lt_of_le (J.component_finrank_pos i) (Submodule.finrank_le _)

/-- Integral isometry preserves the fundamental norm group after the
canonical matching by scale. -/
theorem fundamentalNormGroup_scaleIndexEquivOfIsometry {s t : Nat}
    (J : JordanDecomposition q L t) (H : JordanDecomposition r M s)
    (f : Lattice.Isometry q r L M) (i : Fin t) :
    H.fundamentalNormGroup (J.scaleIndexEquivOfIsometry H f i) =
      J.fundamentalNormGroup i := by
  unfold fundamentalNormGroup fundamentalLattice fundamentalScaleOrder
  rw [J.scaleOrder_scaleIndexEquivOfIsometry H f i]
  exact Lattice.normGroupSet_scaleTruncation_eq_of_isometry f _

/-- Integral isometry preserves the fundamental weight ideal after the
canonical matching by scale. -/
theorem fundamentalWeightIdeal_scaleIndexEquivOfIsometry {s t : Nat}
    (J : JordanDecomposition q L t) (H : JordanDecomposition r M s)
    (f : Lattice.Isometry q r L M) (i : Fin t) :
    H.fundamentalWeightIdeal (J.scaleIndexEquivOfIsometry H f i) =
      J.fundamentalWeightIdeal i := by
  unfold fundamentalWeightIdeal fundamentalLattice fundamentalScaleOrder
  rw [J.scaleOrder_scaleIndexEquivOfIsometry H f i]
  exact Lattice.weightIdeal_scaleTruncation_eq_of_isometry f _
    (J.ambient_finrank_pos_of_index i)

/-- Integral isometry preserves the orders of all fundamental weights. -/
theorem fundamentalWeightOrder_scaleIndexEquivOfIsometry {s t : Nat}
    (J : JordanDecomposition q L t) (H : JordanDecomposition r M s)
    (f : Lattice.Isometry q r L M) (i : Fin t) :
    H.fundamentalWeightOrder (J.scaleIndexEquivOfIsometry H f i) =
      J.fundamentalWeightOrder i := by
  unfold fundamentalWeightOrder fundamentalLattice fundamentalScaleOrder
  rw [J.scaleOrder_scaleIndexEquivOfIsometry H f i]
  exact Lattice.weightIdealOrder_scaleTruncation_eq_of_isometry f _
    (J.ambient_finrank_pos_of_index i)

/-- The same scalar is a fundamental norm generator on both sides of an
integral isometry. -/
theorem isNormGeneratorValue_fundamentalLattice_iff_of_isometry
    {s t : Nat}
    (J : JordanDecomposition q L t) (H : JordanDecomposition r M s)
    (f : Lattice.Isometry q r L M) (i : Fin t) (a : Kˣ) :
    Lattice.IsNormGeneratorValue r
        (H.fundamentalLattice (J.scaleIndexEquivOfIsometry H f i)) a ↔
      Lattice.IsNormGeneratorValue q (J.fundamentalLattice i) a := by
  unfold fundamentalLattice fundamentalScaleOrder
  rw [J.scaleOrder_scaleIndexEquivOfIsometry H f i]
  exact Lattice.isNormGeneratorValue_scaleTruncation_iff_of_isometry f _ a

/-- Equality of O'Meara norm groups transports scalar norm generators.

The norm group itself is only a scalar set, so equality of norm groups does
not rewrite the norm-ideal field in `IsNormGeneratorValue` directly.  The
missing argument is valuation-theoretic: choose a norm generator on the
target, observe that both generators lie in both norm groups, and use
`gL ⊆ nL` in both directions.  The resulting equality of generator orders
identifies the two principal norm ideals. -/
theorem isNormGeneratorValue_of_normGroupSet_eq
    {a : Kˣ}
    (ha : Lattice.IsNormGeneratorValue q L a)
    (hgroup : Lattice.normGroupSet q L = Lattice.normGroupSet r M)
    (hexists : ∃ b : Kˣ, Lattice.IsNormGeneratorValue r M b) :
    Lattice.IsNormGeneratorValue r M a := by
  rcases hexists with ⟨b, hb⟩
  have haGroupM : (a : K) ∈ Lattice.normGroupSet r M := by
    rw [← hgroup]
    exact ha.1
  have hbGroupL : (b : K) ∈ Lattice.normGroupSet q L := by
    rw [hgroup]
    exact hb.1
  have haIdealM : (a : K) ∈ Lattice.normIdeal r M :=
    Lattice.normGroupSet_subset_normIdeal r M haGroupM
  have hbIdealL : (b : K) ∈ Lattice.normIdeal q L :=
    Lattice.normGroupSet_subset_normIdeal q L hbGroupL
  have hba : ordUnit K b ≤ ordUnit K a := by
    rw [hb.2, Lattice.principalIdeal_eq_powerIdeal,
      Lattice.mem_powerIdeal_iff, ← coe_ordUnit] at haIdealM
    exact WithTop.coe_le_coe.mp haIdealM
  have hab : ordUnit K a ≤ ordUnit K b := by
    rw [ha.2, Lattice.principalIdeal_eq_powerIdeal,
      Lattice.mem_powerIdeal_iff, ← coe_ordUnit] at hbIdealL
    exact WithTop.coe_le_coe.mp hbIdealL
  have hord : ordUnit K b = ordUnit K a := le_antisymm hba hab
  refine ⟨haGroupM, hb.2.trans ?_⟩
  exact (Lattice.principalIdeal_eq_iff_ordUnit_eq b a).2 hord

/-- O'Meara's relation of having the same fundamental type: the ordered
Jordan components have the same dimensions, scales, and fundamental norm
groups.  The index equivalence records equality of the component counts. -/
structure SameFundamentalType {s t : Nat}
    (J : JordanDecomposition q L t) (H : JordanDecomposition r M s) where
  indexEquiv : Fin t ≃ Fin s
  index_val (i : Fin t) : (indexEquiv i).val = i.val
  componentRank_eq (i : Fin t) :
    H.componentRank (indexEquiv i) = J.componentRank i
  scaleOrder_eq (i : Fin t) :
    H.fundamentalScaleOrder (indexEquiv i) = J.fundamentalScaleOrder i
  normGroup_eq (i : Fin t) :
    H.fundamentalNormGroup (indexEquiv i) = J.fundamentalNormGroup i

/-- Integral isometry implies equality of O'Meara's complete fundamental
type, without any classification axiom. -/
noncomputable def sameFundamentalTypeOfIsometry {s t : Nat}
    (J : JordanDecomposition q L t) (H : JordanDecomposition r M s)
    (f : Lattice.Isometry q r L M) : SameFundamentalType J H where
  indexEquiv := J.scaleIndexEquivOfIsometry H f
  index_val := J.scaleIndexEquivOfIsometry_val H f
  componentRank_eq := J.componentRank_scaleIndexEquivOfIsometry H f
  scaleOrder_eq := J.scaleOrder_scaleIndexEquivOfIsometry H f
  normGroup_eq := J.fundamentalNormGroup_scaleIndexEquivOfIsometry H f

/-- Every fundamental lattice in a nonempty Jordan decomposition has a scalar
norm generator. -/
theorem exists_fundamentalNormGenerator {t : Nat}
    (J : JordanDecomposition q L t) (i : Fin t) :
    ∃ a : Kˣ,
      Lattice.IsNormGeneratorValue q (J.fundamentalLattice i) a := by
  rcases Lattice.exists_isNormGenerator_of_finrank_pos
      q (J.fundamentalLattice i) (J.ambient_finrank_pos_of_index i) with
    ⟨x, hx, hne⟩
  let a : Kˣ := Units.mk0 (q.quadratic x) hne
  exact ⟨a, hx.isNormGeneratorValue hne⟩

/-- A chosen fundamental norm generator at a Jordan scale. -/
noncomputable def fundamentalNormGenerator {t : Nat}
    (J : JordanDecomposition q L t) (i : Fin t) : Kˣ :=
  Classical.choose (J.exists_fundamentalNormGenerator i)

theorem fundamentalNormGenerator_spec {t : Nat}
    (J : JordanDecomposition q L t) (i : Fin t) :
    Lattice.IsNormGeneratorValue q (J.fundamentalLattice i)
      (J.fundamentalNormGenerator i) :=
  Classical.choose_spec (J.exists_fundamentalNormGenerator i)

/-- The generators chosen on the source side of an isometry are simultaneously
valid fundamental norm generators on the target side.  Thus isometric lattices
admit one common set of O'Meara fundamental invariants. -/
theorem fundamentalNormGenerator_spec_of_isometry {s t : Nat}
    (J : JordanDecomposition q L t) (H : JordanDecomposition r M s)
    (f : Lattice.Isometry q r L M) (i : Fin t) :
    Lattice.IsNormGeneratorValue r
      (H.fundamentalLattice (J.scaleIndexEquivOfIsometry H f i))
      (J.fundamentalNormGenerator i) :=
  (J.isNormGeneratorValue_fundamentalLattice_iff_of_isometry H f i
    (J.fundamentalNormGenerator i)).2 (J.fundamentalNormGenerator_spec i)

namespace SameFundamentalType

variable {s t : Nat}
  {J : JordanDecomposition q L t} {H : JordanDecomposition r M s}

/-- A chosen fundamental norm generator on the left is simultaneously a
fundamental norm generator on the right whenever the decompositions have the
same fundamental type.  This formalizes O'Meara's convention that one may
choose the same set of fundamental norm generators on both lattices. -/
theorem fundamentalNormGenerator_spec_right
    (F : SameFundamentalType J H) (i : Fin t) :
    Lattice.IsNormGeneratorValue r
      (H.fundamentalLattice (F.indexEquiv i))
      (J.fundamentalNormGenerator i) := by
  apply isNormGeneratorValue_of_normGroupSet_eq
    (J.fundamentalNormGenerator_spec i)
  · exact (F.normGroup_eq i).symm
  · exact H.exists_fundamentalNormGenerator (F.indexEquiv i)

end SameFundamentalType

end Lattice.JordanDecomposition

end Bong
