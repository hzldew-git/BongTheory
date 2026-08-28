/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemmas45To47
import Bong.Lattice.AsymmetricBinaryModular
import Bong.Lattice.ModularPrimitivePairing
import Bong.Lattice.ModularDecompositionSort
import Bong.Lattice.ModularSplitting
import Bong.Lattice.NormRescale
import Bong.Lattice.OrthogonalDecompositionIdeals
import Bong.Lattice.OrthogonalDecompositionScale
import Bong.Lattice.OrthogonalDecompositionVolume
import Bong.Lattice.VolumeRigidity

/-!
# Beli (2003), Lemma 4.5

This file proves the two modular-pair replacement statements.  The direct
replacement uses Beli's vectors `x`, `y`, and `z`, with the asymmetric basis
`y, x + z`; the reverse statement follows by duality.
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

namespace Lattice

/-- An anisotropic norm generator is primitive.  Otherwise division by one
uniformizer would produce a lattice vector whose norm has two smaller
valuation steps, contradicting minimality of the norm generator. -/
theorem IsNormGenerator.not_mem_uniformizer_rescale
    {q : QuadraticSpace K V} {L : Lattice K V} {x : V}
    (generator : IsNormGenerator q L x) (hx : q.IsAnisotropic x) :
    x ∉ Lattice.rescale (uniformizerUnit K) L := by
  intro hscaled
  rw [mem_rescale_iff] at hscaled
  rcases hscaled with ⟨y, hy, hxy⟩
  have hyAnisotropic : q.IsAnisotropic y := by
    intro hyZero
    apply hx
    rw [← hxy, q.quadratic_smul, hyZero, mul_zero]
  have hqyMem : q.quadratic y ∈
      principalIdeal (K := K) (q.quadratic x) := by
    rw [← generator.normIdeal_eq]
    exact quadratic_mem_normIdeal_of_mem q L hy
  have hord := ord_le_of_mem_principalIdeal hx hqyMem
  rw [← hxy, q.quadratic_smul, ord_mul, ord_pow,
    coe_uniformizerUnit, ord_uniformizer] at hord
  have hyFinite : ord K (q.quadratic y) ≠ ⊤ :=
    (ord_eq_top_iff K).not.mpr hyAnisotropic
  obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp hyFinite
  rw [← hd] at hord
  have hdImpossible : (2 : Int) + d ≤ d := by
    apply WithTop.coe_le_coe.mp
    simpa [two_nsmul] using hord
  omega

/-- In a binary modular lattice, a scale-generating pair whose two norms
have larger order is an integral basis of the whole lattice. -/
theorem asymmetricBinaryScaleComponent_ambientSubmodule_eq_of_finrank_two
    {q : QuadraticSpace K V} {L : Lattice K V} {x y : V}
    (hfin : finrank K V = 2)
    (hxy : q.bilin x y ≠ 0)
    (hx : ord K (q.bilin x y) < ord K (q.quadratic x))
    (hy : ord K (q.bilin x y) < ord K (q.quadratic y))
    (hxL : x ∈ L) (hyL : y ∈ L)
    (hmodular : IsModular q L (Units.mk0 (q.bilin x y) hxy)) :
    (asymmetricBinaryScaleComponent (q := q) hxy hx hy.le).ambientSubmodule =
      L.toSubmodule := by
  letI : Module.Finite K V := L.moduleFinite
  let C := asymmetricBinaryScaleComponent (q := q) hxy hx hy.le
  let hli := binaryPair_linearIndependent_of_left_strict hxy hx hy.le
  let b := BONG.binaryPairBasis (K := K) x y hli
  have hcarrierFinrank :
      finrank K (BONG.binaryPairSpan (K := K) x y) = 2 := by
    rw [finrank_eq_card_basis b, Fintype.card_fin]
  have hcarrierTop : BONG.binaryPairSpan (K := K) x y = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    omega
  have hcontained : C.ambientSubmodule ≤ L.toSubmodule := by
    exact asymmetricBinaryScaleComponent_ambientSubmodule_le
      hxy hx hy.le hxL hyL
  have hCmodular : IsModular C.space C.lattice
      (Units.mk0 (q.bilin x y) hxy) :=
    asymmetricBinaryScaleComponent_isModular hxy hx hy.le
  apply le_antisymm hcontained
  intro w hw
  rw [QuadraticSublattice.mem_ambientSubmodule_iff]
  have hwCarrier : w ∈ BONG.binaryPairSpan (K := K) x y := by
    rw [hcarrierTop]
    exact Submodule.mem_top
  let wC : C.carrier := ⟨w, hwCarrier⟩
  refine ⟨wC, ?_, rfl⟩
  apply (hCmodular.mem_iff_pairing_mem_principal wC).2
  intro z hz
  change q.bilin w (z : V) ∈
    principalIdeal (K := K) (q.bilin x y)
  exact hmodular.scaleIdeal_le_principal
    (bilin_mem_scaleIdeal_of_mem q L hw
      (hcontained ⟨z, hz, rfl⟩))

/-- A nonzero principal norm ideal forces positive rank. -/
theorem finrank_pos_of_normIdeal_eq_principal
    (q : QuadraticSpace K V) (L : Lattice K V) (a : Kˣ)
    (hnorm : normIdeal q L = principalIdeal (K := K) (a : K)) :
    0 < finrank K V := by
  letI : Module.Finite K V := L.moduleFinite
  by_contra hpos
  have hzero : finrank K V = 0 := Nat.eq_zero_of_not_pos hpos
  letI : Subsingleton V := Module.finrank_zero_iff.mp hzero
  have hle : normIdeal q L ≤ ⊥ := by
    rw [normIdeal, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    have hx : (x : V) = 0 := Subsingleton.elim _ _
    simp [hx]
  have haMem : (a : K) ∈ normIdeal q L := by
    rw [hnorm]
    exact generator_mem_principalIdeal _
  have haZero : (a : K) = 0 := by
    simpa only [Submodule.mem_bot] using hle haMem
  exact (Units.ne_zero a) haZero

/-- Pairing with a vector is controlled on a binary basis once it is
controlled on the two basis vectors. -/
theorem pairing_mem_of_asymmetricBinaryScaleComponent_ambient_eq
    {q : QuadraticSpace K V} {L : Lattice K V} {x y w : V}
    (hxy : q.bilin x y ≠ 0)
    (hx : ord K (q.bilin x y) < ord K (q.quadratic x))
    (hy : ord K (q.bilin x y) ≤ ord K (q.quadratic y))
    (hambient :
      (asymmetricBinaryScaleComponent (q := q) hxy hx hy).ambientSubmodule =
        L.toSubmodule)
    (I : CoefficientIdeal (K := K))
    (hwx : q.bilin w x ∈ I) (hwy : q.bilin w y ∈ I)
    {z : V} (hz : z ∈ L) : q.bilin w z ∈ I := by
  classical
  let C := asymmetricBinaryScaleComponent (q := q) hxy hx hy
  have hzC : z ∈ C.ambientSubmodule := by
    rw [hambient]
    exact hz
  rw [QuadraticSublattice.mem_ambientSubmodule_iff] at hzC
  rcases hzC with ⟨zC, hzCLattice, rfl⟩
  let hli := binaryPair_linearIndependent_of_left_strict hxy hx hy
  let b := BONG.binaryPairBasis (K := K) x y hli
  change zC ∈ basisLattice b at hzCLattice
  change zC ∈ Submodule.span (IntegerRing K) (Set.range b) at hzCLattice
  refine Submodule.span_induction (R := IntegerRing K) (M := C.carrier)
    (s := Set.range b)
    (p := fun zC _ ↦ q.bilin w (zC : V) ∈ I) ?_ ?_ ?_ ?_ hzCLattice
  · rintro _ ⟨i, rfl⟩
    rw [BONG.coe_binaryPairBasis]
    fin_cases i
    · exact hwx
    · exact hwy
  · simpa using I.zero_mem
  · intro a b _ _ ha hb
    simpa only [Submodule.coe_add, LinearMap.BilinForm.add_right] using
      I.add_mem ha hb
  · intro a zC _ hzC
    have h := I.smul_mem a hzC
    change q.bilin w ((algebraMap (IntegerRing K) K a) • (zC : V)) ∈ I
    rw [LinearMap.BilinForm.smul_right]
    simpa only [Algebra.smul_def] using h

namespace ModularPairSplitting

variable {q : QuadraticSpace K V} {L : Lattice K V}

/-- Every chosen component norm order is at least its scale order. -/
theorem scaleOrder_le_normOrder (P : ModularPairSplitting q L) (i : Fin 2) :
    P.scaleOrder i ≤ P.normOrder i := by
  have hle : principalIdeal (K := K) (P.normGenerator i : K) ≤
      principalIdeal (K := K) (P.scaleGenerator i : K) := by
    rw [← P.normIdeal_eq i, ← P.scaleIdeal_eq i]
    exact normIdeal_le_scaleIdeal (P.component i).space
      (P.component i).lattice
  have hord := (principalIdeal_le_iff_ord_ge
    (Units.ne_zero (P.normGenerator i))
    (Units.ne_zero (P.scaleGenerator i))).mp hle
  change ordUnit K (P.scaleGenerator i) ≤ ordUnit K (P.normGenerator i)
  apply WithTop.coe_le_coe.mp
  rw [coe_ordUnit, coe_ordUnit]
  exact hord

/-- Under increasing scale orders, the ambient scale is the old first
component scale. -/
theorem ambientScaleIdeal_eq_first (P : ModularPairSplitting q L)
    (hscale : P.scaleOrder 0 ≤ P.scaleOrder 1) :
    scaleIdeal q L = principalIdeal (K := K) (P.scaleGenerator 0 : K) := by
  rw [P.toOrthogonalDecomposition.scaleIdeal_eq_iSup_component]
  apply le_antisymm
  · apply iSup_le
    rw [Fin.forall_fin_two]
    constructor
    · rw [P.scaleIdeal_eq 0]
    · rw [P.scaleIdeal_eq 1]
      apply (principalIdeal_le_iff_ord_ge
        (Units.ne_zero (P.scaleGenerator 1))
        (Units.ne_zero (P.scaleGenerator 0))).2
      rw [← coe_ordUnit, ← coe_ordUnit]
      exact_mod_cast hscale
  · apply le_iSup_of_le 0
    rw [P.scaleIdeal_eq 0]

/-- If the second norm order is smaller, the ambient norm is the old second
component norm. -/
theorem ambientNormIdeal_eq_second (P : ModularPairSplitting q L)
    (hnorm : P.normOrder 1 < P.normOrder 0) :
    normIdeal q L = principalIdeal (K := K) (P.normGenerator 1 : K) := by
  rw [P.toOrthogonalDecomposition.normIdeal_eq_iSup_component]
  apply le_antisymm
  · apply iSup_le
    rw [Fin.forall_fin_two]
    constructor
    · rw [P.normIdeal_eq 0]
      apply (principalIdeal_le_iff_ord_ge
        (Units.ne_zero (P.normGenerator 0))
        (Units.ne_zero (P.normGenerator 1))).2
      rw [← coe_ordUnit, ← coe_ordUnit]
      exact_mod_cast hnorm.le
    · rw [P.normIdeal_eq 1]
  · apply le_iSup_of_le 1
    rw [P.normIdeal_eq 1]

/-- Ranks add across a two-component orthogonal decomposition. -/
theorem componentRank_zero_add_one (P : ModularPairSplitting q L) :
    P.componentRank 0 + P.componentRank 1 = finrank K V := by
  letI : Module.Finite K (P.component 0).carrier :=
    (P.component 0).lattice.moduleFinite
  letI : Module.Finite K (P.component 1).carrier :=
    (P.component 1).lattice.moduleFinite
  change finrank K (P.component 0).carrier +
      finrank K (P.component 1).carrier = finrank K V
  rw [← Module.finrank_prod]
  exact P.toOrthogonalDecomposition.pairToAmbientLinearEquiv.finrank_eq

/-- A chosen anisotropic norm generator of the first binary component. -/
noncomputable def firstNormVector (P : ModularPairSplitting q L) :
    (P.component 0).carrier :=
  Classical.choose <| exists_isNormGenerator_of_finrank_pos
    (P.component 0).space (P.component 0).lattice (by
      rw [P.first_rank]
      decide)

theorem firstNormVector_spec (P : ModularPairSplitting q L) :
    IsNormGenerator (P.component 0).space (P.component 0).lattice
        P.firstNormVector ∧
      (P.component 0).space.IsAnisotropic P.firstNormVector :=
  Classical.choose_spec <| exists_isNormGenerator_of_finrank_pos
    (P.component 0).space (P.component 0).lattice (by
      rw [P.first_rank]
      decide)

/-- A scale-pairing companion to the first norm generator. -/
noncomputable def firstPairVector (P : ModularPairSplitting q L) :
    (P.component 0).carrier :=
  Classical.choose <| (P.modular 0).exists_pairing_eq_of_not_mem_rescale
    P.firstNormVector_spec.1.mem
    (P.firstNormVector_spec.1.not_mem_uniformizer_rescale
      P.firstNormVector_spec.2)

theorem firstPairVector_spec (P : ModularPairSplitting q L) :
    P.firstPairVector ∈ (P.component 0).lattice ∧
      (P.component 0).space.bilin P.firstNormVector P.firstPairVector =
        (P.scaleGenerator 0 : K) :=
  Classical.choose_spec <|
    (P.modular 0).exists_pairing_eq_of_not_mem_rescale
      P.firstNormVector_spec.1.mem
      (P.firstNormVector_spec.1.not_mem_uniformizer_rescale
        P.firstNormVector_spec.2)

/-- The second component has positive rank because its recorded norm ideal
has a nonzero generator. -/
theorem second_componentRank_pos (P : ModularPairSplitting q L) :
    0 < P.componentRank 1 := by
  exact finrank_pos_of_normIdeal_eq_principal
    (P.component 1).space (P.component 1).lattice (P.normGenerator 1)
      (P.normIdeal_eq 1)

/-- A chosen anisotropic norm generator of the second component. -/
noncomputable def secondNormVector (P : ModularPairSplitting q L) :
    (P.component 1).carrier :=
  Classical.choose <| exists_isNormGenerator_of_finrank_pos
    (P.component 1).space (P.component 1).lattice P.second_componentRank_pos

theorem secondNormVector_spec (P : ModularPairSplitting q L) :
    IsNormGenerator (P.component 1).space (P.component 1).lattice
        P.secondNormVector ∧
      (P.component 1).space.IsAnisotropic P.secondNormVector :=
  Classical.choose_spec <| exists_isNormGenerator_of_finrank_pos
    (P.component 1).space (P.component 1).lattice P.second_componentRank_pos

/-- The field unit represented by the first chosen norm vector. -/
noncomputable def firstNormValueUnit (P : ModularPairSplitting q L) : Kˣ :=
  Units.mk0 ((P.component 0).space.quadratic P.firstNormVector)
    P.firstNormVector_spec.2

/-- The field unit represented by the second chosen norm vector. -/
noncomputable def secondNormValueUnit (P : ModularPairSplitting q L) : Kˣ :=
  Units.mk0 ((P.component 1).space.quadratic P.secondNormVector)
    P.secondNormVector_spec.2

theorem ordUnit_firstNormValueUnit (P : ModularPairSplitting q L) :
    ordUnit K P.firstNormValueUnit = P.normOrder 0 := by
  change ordUnit K P.firstNormValueUnit = ordUnit K (P.normGenerator 0)
  apply (principalIdeal_eq_iff_ordUnit_eq
    P.firstNormValueUnit (P.normGenerator 0)).mp
  calc
    principalIdeal (K := K) (P.firstNormValueUnit : K) =
        normIdeal (P.component 0).space (P.component 0).lattice :=
      P.firstNormVector_spec.1.normIdeal_eq.symm
    _ = principalIdeal (K := K) (P.normGenerator 0 : K) :=
      P.normIdeal_eq 0

theorem ordUnit_secondNormValueUnit (P : ModularPairSplitting q L) :
    ordUnit K P.secondNormValueUnit = P.normOrder 1 := by
  change ordUnit K P.secondNormValueUnit = ordUnit K (P.normGenerator 1)
  apply (principalIdeal_eq_iff_ordUnit_eq
    P.secondNormValueUnit (P.normGenerator 1)).mp
  calc
    principalIdeal (K := K) (P.secondNormValueUnit : K) =
        normIdeal (P.component 1).space (P.component 1).lattice :=
      P.secondNormVector_spec.1.normIdeal_eq.symm
    _ = principalIdeal (K := K) (P.normGenerator 1 : K) :=
      P.normIdeal_eq 1

theorem ord_quadratic_firstNormVector (P : ModularPairSplitting q L) :
    ord K (q.quadratic (P.firstNormVector : V)) =
      ((P.normOrder 0 : Int) : WithTop Int) := by
  change ord K (P.firstNormValueUnit : K) = _
  rw [← coe_ordUnit, P.ordUnit_firstNormValueUnit]

theorem ord_quadratic_secondNormVector (P : ModularPairSplitting q L) :
    ord K (q.quadratic (P.secondNormVector : V)) =
      ((P.normOrder 1 : Int) : WithTop Int) := by
  change ord K (P.secondNormValueUnit : K) = _
  rw [← coe_ordUnit, P.ordUnit_secondNormValueUnit]

theorem bilin_firstNormVector_firstPairVector
    (P : ModularPairSplitting q L) :
    q.bilin (P.firstNormVector : V) (P.firstPairVector : V) =
      (P.scaleGenerator 0 : K) := by
  exact P.firstPairVector_spec.2

theorem normOrder_le_ord_quadratic_firstPairVector
    (P : ModularPairSplitting q L) :
    ((P.normOrder 0 : Int) : WithTop Int) ≤
      ord K (q.quadratic (P.firstPairVector : V)) := by
  have hmem : (P.component 0).space.quadratic P.firstPairVector ∈
      principalIdeal (K := K) (P.normGenerator 0 : K) := by
    rw [← P.normIdeal_eq 0]
    exact quadratic_mem_normIdeal_of_mem
      (P.component 0).space (P.component 0).lattice
        P.firstPairVector_spec.1
  have hord := ord_le_of_mem_principalIdeal
    (Units.ne_zero (P.normGenerator 0)) hmem
  change ((P.normOrder 0 : Int) : WithTop Int) ≤
    ord K ((P.component 0).space.quadratic P.firstPairVector)
  calc
    ((P.normOrder 0 : Int) : WithTop Int) =
        ord K (P.normGenerator 0 : K) := by
      exact coe_ordUnit K (P.normGenerator 0)
    _ ≤ _ := hord

/-- The selected norm vector and scale-pairing companion are an integral
basis of the old binary first component. -/
theorem first_asymmetricBinaryScaleComponent_ambientSubmodule_eq
    (P : ModularPairSplitting q L)
    (hscale : P.scaleOrder 0 ≤ P.scaleOrder 1)
    (hnorm : P.normOrder 1 < P.normOrder 0) :
    (asymmetricBinaryScaleComponent
      (q := (P.component 0).space)
      (x := P.firstNormVector) (y := P.firstPairVector)
      (by
        rw [P.firstPairVector_spec.2]
        exact Units.ne_zero (P.scaleGenerator 0))
      (by
        rw [P.firstPairVector_spec.2]
        rw [← coe_ordUnit]
        change ((P.scaleOrder 0 : Int) : WithTop Int) <
          ord K ((P.component 0).space.quadratic P.firstNormVector)
        have hqx : ord K ((P.component 0).space.quadratic P.firstNormVector) =
            ((P.normOrder 0 : Int) : WithTop Int) :=
          P.ord_quadratic_firstNormVector
        rw [hqx]
        exact_mod_cast lt_of_le_of_lt
          (hscale.trans (P.scaleOrder_le_normOrder 1)) hnorm)
      (by
        rw [P.firstPairVector_spec.2]
        rw [← coe_ordUnit]
        change ((P.scaleOrder 0 : Int) : WithTop Int) ≤
          ord K ((P.component 0).space.quadratic P.firstPairVector)
        exact (show ((P.normOrder 0 : Int) : WithTop Int) ≤ _ from
          P.normOrder_le_ord_quadratic_firstPairVector).trans' <| by
            exact_mod_cast (lt_of_le_of_lt
              (hscale.trans (P.scaleOrder_le_normOrder 1)) hnorm).le)).ambientSubmodule =
      (P.component 0).lattice.toSubmodule := by
  let hxy : (P.component 0).space.bilin P.firstNormVector P.firstPairVector ≠ 0 := by
    rw [P.firstPairVector_spec.2]
    exact Units.ne_zero (P.scaleGenerator 0)
  let hx : ord K ((P.component 0).space.bilin
      P.firstNormVector P.firstPairVector) <
      ord K ((P.component 0).space.quadratic P.firstNormVector) := by
    rw [P.firstPairVector_spec.2]
    rw [← coe_ordUnit]
    change ((P.scaleOrder 0 : Int) : WithTop Int) < _
    have hqx : ord K ((P.component 0).space.quadratic P.firstNormVector) =
        ((P.normOrder 0 : Int) : WithTop Int) :=
      P.ord_quadratic_firstNormVector
    rw [hqx]
    exact_mod_cast lt_of_le_of_lt
      (hscale.trans (P.scaleOrder_le_normOrder 1)) hnorm
  let hy : ord K ((P.component 0).space.bilin
      P.firstNormVector P.firstPairVector) <
      ord K ((P.component 0).space.quadratic P.firstPairVector) := by
    rw [P.firstPairVector_spec.2]
    rw [← coe_ordUnit]
    change ((P.scaleOrder 0 : Int) : WithTop Int) < _
    exact lt_of_lt_of_le (by
      exact_mod_cast lt_of_le_of_lt
        (hscale.trans (P.scaleOrder_le_normOrder 1)) hnorm)
      P.normOrder_le_ord_quadratic_firstPairVector
  have hunit : Units.mk0
      ((P.component 0).space.bilin P.firstNormVector P.firstPairVector) hxy =
      P.scaleGenerator 0 := by
    apply Units.ext
    exact P.firstPairVector_spec.2
  exact asymmetricBinaryScaleComponent_ambientSubmodule_eq_of_finrank_two
    P.first_rank hxy hx hy P.firstNormVector_spec.1.mem
      P.firstPairVector_spec.1 (by simpa [hunit] using P.modular 0)

theorem rebalancedPair_bilin_eq (P : ModularPairSplitting q L) :
    q.bilin (P.firstPairVector : V)
        ((P.firstNormVector : V) + (P.secondNormVector : V)) =
      (P.scaleGenerator 0 : K) := by
  rw [LinearMap.BilinForm.add_right,
    P.toOrthogonalDecomposition.orthogonal 0 1 (by decide)
      P.firstPairVector P.secondNormVector,
    add_zero, q.isSymm.eq]
  exact P.bilin_firstNormVector_firstPairVector

theorem rebalancedPair_ne_zero (P : ModularPairSplitting q L) :
    q.bilin (P.firstPairVector : V)
        ((P.firstNormVector : V) + (P.secondNormVector : V)) ≠ 0 := by
  rw [P.rebalancedPair_bilin_eq]
  exact Units.ne_zero (P.scaleGenerator 0)

theorem ord_quadratic_rebalancedSum
    (P : ModularPairSplitting q L)
    (hnorm : P.normOrder 1 < P.normOrder 0) :
    ord K (q.quadratic
        ((P.firstNormVector : V) + (P.secondNormVector : V))) =
      ((P.normOrder 1 : Int) : WithTop Int) := by
  rw [q.quadratic_add,
    P.toOrthogonalDecomposition.orthogonal 0 1 (by decide)
      P.firstNormVector P.secondNormVector,
    mul_zero, add_zero]
  have hlt : ord K (q.quadratic (P.secondNormVector : V)) <
      ord K (q.quadratic (P.firstNormVector : V)) := by
    rw [P.ord_quadratic_secondNormVector,
      P.ord_quadratic_firstNormVector]
    exact_mod_cast hnorm
  rw [(ord K).map_add_eq_of_lt_right hlt,
    P.ord_quadratic_secondNormVector]

theorem rebalancedPair_left_strict
    (P : ModularPairSplitting q L)
    (hscale : P.scaleOrder 0 ≤ P.scaleOrder 1)
    (hnorm : P.normOrder 1 < P.normOrder 0) :
    ord K (q.bilin (P.firstPairVector : V)
        ((P.firstNormVector : V) + (P.secondNormVector : V))) <
      ord K (q.quadratic (P.firstPairVector : V)) := by
  rw [P.rebalancedPair_bilin_eq, ← coe_ordUnit]
  change ((P.scaleOrder 0 : Int) : WithTop Int) < _
  exact lt_of_lt_of_le (by
    exact_mod_cast lt_of_le_of_lt
      (hscale.trans (P.scaleOrder_le_normOrder 1)) hnorm)
    P.normOrder_le_ord_quadratic_firstPairVector

theorem rebalancedPair_right_weak
    (P : ModularPairSplitting q L)
    (hscale : P.scaleOrder 0 ≤ P.scaleOrder 1)
    (hnorm : P.normOrder 1 < P.normOrder 0) :
    ord K (q.bilin (P.firstPairVector : V)
        ((P.firstNormVector : V) + (P.secondNormVector : V))) ≤
      ord K (q.quadratic
        ((P.firstNormVector : V) + (P.secondNormVector : V))) := by
  rw [P.rebalancedPair_bilin_eq, ← coe_ordUnit,
    P.ord_quadratic_rebalancedSum hnorm]
  exact_mod_cast hscale.trans (P.scaleOrder_le_normOrder 1)

/-- Beli's replacement binary component, generated by `y` and `x + z`. -/
noncomputable def rebalancedFirstComponent
    (P : ModularPairSplitting q L)
    (hscale : P.scaleOrder 0 ≤ P.scaleOrder 1)
    (hnorm : P.normOrder 1 < P.normOrder 0) :
    QuadraticSublattice q :=
  asymmetricBinaryScaleComponent
    P.rebalancedPair_ne_zero
    (P.rebalancedPair_left_strict hscale hnorm)
    (P.rebalancedPair_right_weak hscale hnorm)

theorem rebalancedFirstComponent_contained
    (P : ModularPairSplitting q L)
    (hscale : P.scaleOrder 0 ≤ P.scaleOrder 1)
    (hnorm : P.normOrder 1 < P.normOrder 0) :
    (P.rebalancedFirstComponent hscale hnorm).ambientSubmodule ≤
      L.toSubmodule := by
  apply asymmetricBinaryScaleComponent_ambientSubmodule_le
  · exact P.toOrthogonalDecomposition.component_ambientSubmodule_le 0
      ⟨P.firstPairVector, P.firstPairVector_spec.1, rfl⟩
  · exact L.add_mem
      (P.toOrthogonalDecomposition.component_ambientSubmodule_le 0
        ⟨P.firstNormVector, P.firstNormVector_spec.1.mem, rfl⟩)
      (P.toOrthogonalDecomposition.component_ambientSubmodule_le 1
        ⟨P.secondNormVector, P.secondNormVector_spec.1.mem, rfl⟩)

theorem rebalancedFirstComponent_isModular
    (P : ModularPairSplitting q L)
    (hscale : P.scaleOrder 0 ≤ P.scaleOrder 1)
    (hnorm : P.normOrder 1 < P.normOrder 0) :
    IsModular (P.rebalancedFirstComponent hscale hnorm).space
      (P.rebalancedFirstComponent hscale hnorm).lattice
      (P.scaleGenerator 0) := by
  have hunit : Units.mk0
      (q.bilin (P.firstPairVector : V)
        ((P.firstNormVector : V) + (P.secondNormVector : V)))
      P.rebalancedPair_ne_zero = P.scaleGenerator 0 := by
    apply Units.ext
    exact P.rebalancedPair_bilin_eq
  unfold rebalancedFirstComponent
  rw [← hunit]
  exact asymmetricBinaryScaleComponent_isModular
    P.rebalancedPair_ne_zero
    (P.rebalancedPair_left_strict hscale hnorm)
    (P.rebalancedPair_right_weak hscale hnorm)

theorem rebalancedFirstComponent_rank
    (P : ModularPairSplitting q L)
    (hscale : P.scaleOrder 0 ≤ P.scaleOrder 1)
    (hnorm : P.normOrder 1 < P.normOrder 0) :
    finrank K (P.rebalancedFirstComponent hscale hnorm).carrier = 2 := by
  change finrank K (BONG.binaryPairSpan (K := K)
      (P.firstPairVector : V)
      ((P.firstNormVector : V) + (P.secondNormVector : V))) = 2
  simpa using Module.finrank_eq_card_basis
    (BONG.binaryPairBasis (K := K)
      (P.firstPairVector : V)
      ((P.firstNormVector : V) + (P.secondNormVector : V))
      (binaryPair_linearIndependent_of_left_strict
        P.rebalancedPair_ne_zero
        (P.rebalancedPair_left_strict hscale hnorm)
        (P.rebalancedPair_right_weak hscale hnorm)))

theorem rebalancedSum_anisotropic
    (P : ModularPairSplitting q L)
    (hnorm : P.normOrder 1 < P.normOrder 0) :
    q.IsAnisotropic
      ((P.firstNormVector : V) + (P.secondNormVector : V)) := by
  intro hzero
  have hord := P.ord_quadratic_rebalancedSum hnorm
  rw [hzero, ord_zero] at hord
  exact WithTop.coe_ne_top hord.symm

theorem rebalancedFirstComponent_normIdeal_eq
    (P : ModularPairSplitting q L)
    (hscale : P.scaleOrder 0 ≤ P.scaleOrder 1)
    (hnorm : P.normOrder 1 < P.normOrder 0) :
    normIdeal (P.rebalancedFirstComponent hscale hnorm).space
        (P.rebalancedFirstComponent hscale hnorm).lattice =
      principalIdeal (K := K) (P.normGenerator 1 : K) := by
  apply le_antisymm
  · rw [← P.ambientNormIdeal_eq_second hnorm]
    exact QuadraticSublattice.normIdeal_le_of_ambientSubmodule_le
      (P.rebalancedFirstComponent hscale hnorm)
      (P.rebalancedFirstComponent_contained hscale hnorm)
  · have hsumMem : q.quadratic
        ((P.firstNormVector : V) + (P.secondNormVector : V)) ∈
        normIdeal (P.rebalancedFirstComponent hscale hnorm).space
          (P.rebalancedFirstComponent hscale hnorm).lattice := by
      have hcarrier :
          (P.firstNormVector : V) + (P.secondNormVector : V) ∈
            BONG.binaryPairSpan (K := K) (P.firstPairVector : V)
              ((P.firstNormVector : V) + (P.secondNormVector : V)) := by
        apply Submodule.subset_span
        exact ⟨1, BONG.binaryPairFamily_one _ _⟩
      let w : (P.rebalancedFirstComponent hscale hnorm).carrier :=
        ⟨(P.firstNormVector : V) + (P.secondNormVector : V), hcarrier⟩
      have hw : w ∈ (P.rebalancedFirstComponent hscale hnorm).lattice := by
        let hli := binaryPair_linearIndependent_of_left_strict
          P.rebalancedPair_ne_zero
          (P.rebalancedPair_left_strict hscale hnorm)
          (P.rebalancedPair_right_weak hscale hnorm)
        let b := BONG.binaryPairBasis (K := K)
          (P.firstPairVector : V)
          ((P.firstNormVector : V) + (P.secondNormVector : V)) hli
        unfold rebalancedFirstComponent asymmetricBinaryScaleComponent
          basisQuadraticSublattice
        change (⟨(P.firstNormVector : V) + (P.secondNormVector : V),
          hcarrier⟩ :
          BONG.binaryPairSpan (K := K) (P.firstPairVector : V)
            ((P.firstNormVector : V) + (P.secondNormVector : V))) ∈
          basisLattice b
        have heq : (⟨(P.firstNormVector : V) + (P.secondNormVector : V),
            hcarrier⟩ :
            BONG.binaryPairSpan (K := K) (P.firstPairVector : V)
              ((P.firstNormVector : V) + (P.secondNormVector : V))) = b 1 := by
          apply Subtype.ext
          simp [b]
        rw [heq, mem_basisLattice_iff_repr_mem_integerRing]
        intro i
        fin_cases i
        · simpa using (show (0 : K) ∈ IntegerRing K from
            (0 : IntegerRing K).property)
        · simpa using (show (1 : K) ∈ IntegerRing K from
            (1 : IntegerRing K).property)
      have hmem := quadratic_mem_normIdeal_of_mem
        (P.rebalancedFirstComponent hscale hnorm).space
        (P.rebalancedFirstComponent hscale hnorm).lattice hw
      exact hmem
    have hprincipal : principalIdeal (K := K) (P.normGenerator 1 : K) =
        principalIdeal (K := K)
          (q.quadratic ((P.firstNormVector : V) +
            (P.secondNormVector : V))) := by
      apply le_antisymm
      · apply (principalIdeal_le_iff_ord_ge
          (Units.ne_zero (P.normGenerator 1))
          (P.rebalancedSum_anisotropic hnorm)).2
        rw [P.ord_quadratic_rebalancedSum hnorm, ← coe_ordUnit]
        rfl
      · apply (principalIdeal_le_iff_ord_ge
          (P.rebalancedSum_anisotropic hnorm)
          (Units.ne_zero (P.normGenerator 1))).2
        rw [P.ord_quadratic_rebalancedSum hnorm, ← coe_ordUnit]
        rfl
    rw [hprincipal, principalIdeal,
      Submodule.span_singleton_le_iff_mem]
    exact hsumMem

/-- The orthogonal decomposition obtained by splitting off the replacement
binary component. -/
noncomputable def rebalancedDecomposition
    (P : ModularPairSplitting q L)
    (hscale : P.scaleOrder 0 ≤ P.scaleOrder 1)
    (hnorm : P.normOrder 1 < P.normOrder 0) :
    OrthogonalDecomposition q L 2 :=
  omearaModularSplittingOfScaleIdealLe
    (P.rebalancedFirstComponent hscale hnorm)
    (P.rebalancedFirstComponent_contained hscale hnorm)
    (P.rebalancedFirstComponent_isModular hscale hnorm)
    (by rw [P.ambientScaleIdeal_eq_first hscale])

@[simp]
theorem rebalancedDecomposition_component_zero
    (P : ModularPairSplitting q L)
    (hscale : P.scaleOrder 0 ≤ P.scaleOrder 1)
    (hnorm : P.normOrder 1 < P.normOrder 0) :
    (P.rebalancedDecomposition hscale hnorm).component 0 =
      P.rebalancedFirstComponent hscale hnorm :=
  rfl

/-- Coordinates of an ambient vector in the old two-component splitting. -/
noncomputable def oldCoordinates (P : ModularPairSplitting q L) (w : V) :
    (P.component 0).carrier × (P.component 1).carrier :=
  P.toOrthogonalDecomposition.pairToAmbientLinearEquiv.symm w

theorem oldCoordinates_decomposition
    (P : ModularPairSplitting q L) (w : V) :
    ((P.oldCoordinates w).1 : V) + ((P.oldCoordinates w).2 : V) = w := by
  change P.toOrthogonalDecomposition.pairToAmbientLinearEquiv
    (P.toOrthogonalDecomposition.pairToAmbientLinearEquiv.symm w) = w
  exact P.toOrthogonalDecomposition.pairToAmbientLinearEquiv.apply_symm_apply w

theorem oldCoordinates_mem
    (P : ModularPairSplitting q L) {w : V} (hw : w ∈ L) :
    (P.oldCoordinates w).1 ∈ (P.component 0).lattice ∧
      (P.oldCoordinates w).2 ∈ (P.component 1).lattice := by
  rw [← mem_product_iff]
  apply (P.toOrthogonalDecomposition.pairProductLatticeIsometry.map_mem
    (P.oldCoordinates w)).2
  change P.toOrthogonalDecomposition.pairToAmbientLinearEquiv
    (P.toOrthogonalDecomposition.pairToAmbientLinearEquiv.symm w) ∈ L
  rw [LinearEquiv.apply_symm_apply]
  exact hw

theorem rebalancedComplement_orthogonal_firstPair
    (P : ModularPairSplitting q L)
    (hscale : P.scaleOrder 0 ≤ P.scaleOrder 1)
    (hnorm : P.normOrder 1 < P.normOrder 0)
    (w : (P.rebalancedDecomposition hscale hnorm).component 1 |>.carrier) :
    q.bilin (P.firstPairVector : V) (w : V) = 0 := by
  have hcarrier : (P.firstPairVector : V) ∈
      BONG.binaryPairSpan (K := K) (P.firstPairVector : V)
        ((P.firstNormVector : V) + (P.secondNormVector : V)) := by
    apply Submodule.subset_span
    exact ⟨0, BONG.binaryPairFamily_zero _ _⟩
  let yC : (P.rebalancedFirstComponent hscale hnorm).carrier :=
    ⟨P.firstPairVector, hcarrier⟩
  exact P.rebalancedDecomposition hscale hnorm |>.orthogonal
    0 1 (by decide) yC w

theorem rebalancedComplement_orthogonal_sum
    (P : ModularPairSplitting q L)
    (hscale : P.scaleOrder 0 ≤ P.scaleOrder 1)
    (hnorm : P.normOrder 1 < P.normOrder 0)
    (w : (P.rebalancedDecomposition hscale hnorm).component 1 |>.carrier) :
    q.bilin ((P.firstNormVector : V) + (P.secondNormVector : V))
      (w : V) = 0 := by
  have hcarrier :
      (P.firstNormVector : V) + (P.secondNormVector : V) ∈
        BONG.binaryPairSpan (K := K) (P.firstPairVector : V)
          ((P.firstNormVector : V) + (P.secondNormVector : V)) := by
    apply Submodule.subset_span
    exact ⟨1, BONG.binaryPairFamily_one _ _⟩
  let sC : (P.rebalancedFirstComponent hscale hnorm).carrier :=
    ⟨(P.firstNormVector : V) + (P.secondNormVector : V), hcarrier⟩
  exact P.rebalancedDecomposition hscale hnorm |>.orthogonal
    0 1 (by decide) sC w

/-- Pairing with an old first-component vector is controlled by its values
on the selected integral binary basis. -/
theorem pairing_mem_oldFirst_of_pairings
    (P : ModularPairSplitting q L)
    (hscale : P.scaleOrder 0 ≤ P.scaleOrder 1)
    (hnorm : P.normOrder 1 < P.normOrder 0)
    (I : CoefficientIdeal (K := K))
    (w : (P.component 0).carrier)
    (hwx : q.bilin (w : V) (P.firstNormVector : V) ∈ I)
    (hwy : q.bilin (w : V) (P.firstPairVector : V) ∈ I)
    {v : (P.component 0).carrier}
    (hv : v ∈ (P.component 0).lattice) :
    q.bilin (w : V) (v : V) ∈ I := by
  let hxy : (P.component 0).space.bilin
      P.firstNormVector P.firstPairVector ≠ 0 := by
    rw [P.firstPairVector_spec.2]
    exact Units.ne_zero (P.scaleGenerator 0)
  let hx : ord K ((P.component 0).space.bilin
      P.firstNormVector P.firstPairVector) <
      ord K ((P.component 0).space.quadratic P.firstNormVector) := by
    rw [P.firstPairVector_spec.2, ← coe_ordUnit]
    have hqx : ord K ((P.component 0).space.quadratic P.firstNormVector) =
        ((P.normOrder 0 : Int) : WithTop Int) :=
      P.ord_quadratic_firstNormVector
    rw [hqx]
    exact_mod_cast lt_of_le_of_lt
      (hscale.trans (P.scaleOrder_le_normOrder 1)) hnorm
  let hy : ord K ((P.component 0).space.bilin
      P.firstNormVector P.firstPairVector) ≤
      ord K ((P.component 0).space.quadratic P.firstPairVector) := by
    rw [P.firstPairVector_spec.2, ← coe_ordUnit]
    change ((P.scaleOrder 0 : Int) : WithTop Int) ≤ _
    exact (show ((P.normOrder 0 : Int) : WithTop Int) ≤ _ from
      P.normOrder_le_ord_quadratic_firstPairVector).trans' <| by
        exact_mod_cast (lt_of_le_of_lt
          (hscale.trans (P.scaleOrder_le_normOrder 1)) hnorm).le
  have hambient :
      (asymmetricBinaryScaleComponent
        (q := (P.component 0).space)
        (x := P.firstNormVector) (y := P.firstPairVector)
        hxy hx hy).ambientSubmodule =
      (P.component 0).lattice.toSubmodule := by
    simpa only using
      P.first_asymmetricBinaryScaleComponent_ambientSubmodule_eq hscale hnorm
  exact pairing_mem_of_asymmetricBinaryScaleComponent_ambient_eq
    hxy hx hy hambient I hwx hwy hv

theorem bilin_firstPair_oldFirstCoordinate_eq_zero
    (P : ModularPairSplitting q L)
    (hscale : P.scaleOrder 0 ≤ P.scaleOrder 1)
    (hnorm : P.normOrder 1 < P.normOrder 0)
    (w : (P.rebalancedDecomposition hscale hnorm).component 1 |>.carrier) :
    q.bilin (P.firstPairVector : V)
      ((P.oldCoordinates (w : V)).1 : V) = 0 := by
  have hcross : q.bilin (P.firstPairVector : V)
      ((P.oldCoordinates (w : V)).2 : V) = 0 :=
    P.toOrthogonalDecomposition.orthogonal 0 1 (by decide)
      P.firstPairVector (P.oldCoordinates (w : V)).2
  calc
    q.bilin (P.firstPairVector : V)
        ((P.oldCoordinates (w : V)).1 : V) =
      q.bilin (P.firstPairVector : V)
        (((P.oldCoordinates (w : V)).1 : V) +
          ((P.oldCoordinates (w : V)).2 : V)) := by
            rw [LinearMap.BilinForm.add_right, hcross, add_zero]
    _ = q.bilin (P.firstPairVector : V) (w : V) := by
      rw [P.oldCoordinates_decomposition]
    _ = 0 := P.rebalancedComplement_orthogonal_firstPair hscale hnorm w

theorem bilin_oldFirstCoordinate_firstNorm_mem_secondScale
    (P : ModularPairSplitting q L)
    (hscale : P.scaleOrder 0 ≤ P.scaleOrder 1)
    (hnorm : P.normOrder 1 < P.normOrder 0)
    (w : ((P.rebalancedDecomposition hscale hnorm).component 1).carrier)
    (hw : w ∈ ((P.rebalancedDecomposition hscale hnorm).component 1).lattice) :
    q.bilin ((P.oldCoordinates (w : V)).1 : V)
        (P.firstNormVector : V) ∈
      principalIdeal (K := K) (P.scaleGenerator 1 : K) := by
  have hwAmbient : (w : V) ∈ L :=
    (P.rebalancedDecomposition hscale hnorm).component_ambientSubmodule_le 1
      ⟨w, hw, rfl⟩
  have hcoordsMem := P.oldCoordinates_mem hwAmbient
  have hsecond : q.bilin (P.secondNormVector : V)
      ((P.oldCoordinates (w : V)).2 : V) ∈
      principalIdeal (K := K) (P.scaleGenerator 1 : K) := by
    rw [← P.scaleIdeal_eq 1]
    exact bilin_mem_scaleIdeal
      (P.component 1).space (P.component 1).lattice
      ⟨P.secondNormVector, P.secondNormVector_spec.1.mem⟩
      ⟨(P.oldCoordinates (w : V)).2, hcoordsMem.2⟩
  have hrelation : q.bilin (P.firstNormVector : V)
      ((P.oldCoordinates (w : V)).1 : V) +
      q.bilin (P.secondNormVector : V)
        ((P.oldCoordinates (w : V)).2 : V) = 0 := by
    have horth := P.rebalancedComplement_orthogonal_sum hscale hnorm w
    rw [← P.oldCoordinates_decomposition (w : V)] at horth
    simpa only [LinearMap.BilinForm.add_left,
      LinearMap.BilinForm.add_right,
      P.toOrthogonalDecomposition.orthogonal 0 1 (by decide)
        P.firstNormVector (P.oldCoordinates (w : V)).2,
      P.toOrthogonalDecomposition.orthogonal 1 0 (by decide)
        P.secondNormVector (P.oldCoordinates (w : V)).1,
      add_zero, zero_add] using horth
  have heq : q.bilin ((P.oldCoordinates (w : V)).1 : V)
      (P.firstNormVector : V) =
      -q.bilin (P.secondNormVector : V)
        ((P.oldCoordinates (w : V)).2 : V) := by
    rw [q.isSymm.eq]
    linear_combination hrelation
  rw [heq]
  exact (principalIdeal (K := K) (P.scaleGenerator 1 : K)).neg_mem hsecond

theorem oldFirstCoordinate_pairing_mem_secondScale
    (P : ModularPairSplitting q L)
    (hscale : P.scaleOrder 0 ≤ P.scaleOrder 1)
    (hnorm : P.normOrder 1 < P.normOrder 0)
    (w : ((P.rebalancedDecomposition hscale hnorm).component 1).carrier)
    (hw : w ∈ ((P.rebalancedDecomposition hscale hnorm).component 1).lattice)
    {v : (P.component 0).carrier}
    (hv : v ∈ (P.component 0).lattice) :
    q.bilin ((P.oldCoordinates (w : V)).1 : V) (v : V) ∈
      principalIdeal (K := K) (P.scaleGenerator 1 : K) := by
  apply P.pairing_mem_oldFirst_of_pairings hscale hnorm
  · exact P.bilin_oldFirstCoordinate_firstNorm_mem_secondScale
      hscale hnorm w hw
  · rw [q.isSymm.eq]
    rw [P.bilin_firstPair_oldFirstCoordinate_eq_zero hscale hnorm w]
    exact (principalIdeal (K := K) (P.scaleGenerator 1 : K)).zero_mem
  · exact hv

theorem rebalancedComplement_scaleIdeal_le
    (P : ModularPairSplitting q L)
    (hscale : P.scaleOrder 0 ≤ P.scaleOrder 1)
    (hnorm : P.normOrder 1 < P.normOrder 0) :
    scaleIdeal
        ((P.rebalancedDecomposition hscale hnorm).component 1).space
        ((P.rebalancedDecomposition hscale hnorm).component 1).lattice ≤
      principalIdeal (K := K) (P.scaleGenerator 1 : K) := by
  apply scaleIdeal_le_of_bilin_mem
  intro w v hw hv
  change q.bilin (w : V) (v : V) ∈
    principalIdeal (K := K) (P.scaleGenerator 1 : K)
  have hwAmbient : (w : V) ∈ L :=
    (P.rebalancedDecomposition hscale hnorm).component_ambientSubmodule_le 1
      ⟨w, hw, rfl⟩
  have hvAmbient : (v : V) ∈ L :=
    (P.rebalancedDecomposition hscale hnorm).component_ambientSubmodule_le 1
      ⟨v, hv, rfl⟩
  have hwMem := P.oldCoordinates_mem hwAmbient
  have hvMem := P.oldCoordinates_mem hvAmbient
  have hfirst : q.bilin ((P.oldCoordinates (w : V)).1 : V)
      ((P.oldCoordinates (v : V)).1 : V) ∈
      principalIdeal (K := K) (P.scaleGenerator 1 : K) :=
    P.oldFirstCoordinate_pairing_mem_secondScale hscale hnorm w hw hvMem.1
  have hsecond : q.bilin ((P.oldCoordinates (w : V)).2 : V)
      ((P.oldCoordinates (v : V)).2 : V) ∈
      principalIdeal (K := K) (P.scaleGenerator 1 : K) := by
    rw [← P.scaleIdeal_eq 1]
    exact bilin_mem_scaleIdeal
      (P.component 1).space (P.component 1).lattice
      ⟨(P.oldCoordinates (w : V)).2, hwMem.2⟩
      ⟨(P.oldCoordinates (v : V)).2, hvMem.2⟩
  rw [← P.oldCoordinates_decomposition (w : V),
    ← P.oldCoordinates_decomposition (v : V)]
  simpa only [LinearMap.BilinForm.add_left,
    LinearMap.BilinForm.add_right,
    P.toOrthogonalDecomposition.orthogonal 0 1 (by decide)
      (P.oldCoordinates (w : V)).1 (P.oldCoordinates (v : V)).2,
    P.toOrthogonalDecomposition.orthogonal 1 0 (by decide)
      (P.oldCoordinates (w : V)).2 (P.oldCoordinates (v : V)).1,
    add_zero, zero_add] using
      (principalIdeal (K := K) (P.scaleGenerator 1 : K)).add_mem
        hfirst hsecond

theorem rebalancedComplement_rank_eq
    (P : ModularPairSplitting q L)
    (hscale : P.scaleOrder 0 ≤ P.scaleOrder 1)
    (hnorm : P.normOrder 1 < P.normOrder 0) :
    finrank K ((P.rebalancedDecomposition hscale hnorm).component 1).carrier =
      P.componentRank 1 := by
  let D := P.rebalancedDecomposition hscale hnorm
  letI : Module.Finite K (D.component 0).carrier :=
    (D.component 0).lattice.moduleFinite
  letI : Module.Finite K (D.component 1).carrier :=
    (D.component 1).lattice.moduleFinite
  have hnew : finrank K (D.component 0).carrier +
      finrank K (D.component 1).carrier = finrank K V := by
    rw [← Module.finrank_prod]
    exact D.pairToAmbientLinearEquiv.finrank_eq
  have hnewFirst : finrank K (D.component 0).carrier = 2 := by
    change finrank K (P.rebalancedFirstComponent hscale hnorm).carrier = 2
    exact P.rebalancedFirstComponent_rank hscale hnorm
  have hold := P.componentRank_zero_add_one
  unfold componentRank at hold ⊢
  rw [P.first_rank] at hold
  change finrank K (D.component 1).carrier =
    finrank K (P.component 1).carrier
  omega

theorem rebalancedComplement_volumeOrder_eq
    (P : ModularPairSplitting q L)
    (hscale : P.scaleOrder 0 ≤ P.scaleOrder 1)
    (hnorm : P.normOrder 1 < P.normOrder 0) :
    volumeOrder
        ((P.rebalancedDecomposition hscale hnorm).component 1).space
        ((P.rebalancedDecomposition hscale hnorm).component 1).lattice =
      (finrank K
        ((P.rebalancedDecomposition hscale hnorm).component 1).carrier : Int) *
        ordUnit K (P.scaleGenerator 1) := by
  let D := P.rebalancedDecomposition hscale hnorm
  have hold := P.toOrthogonalDecomposition.volumeOrder_eq_add_components
  rw [(P.modular 0).volumeOrder_eq,
    (P.modular 1).volumeOrder_eq, P.first_rank] at hold
  have hnew := D.volumeOrder_eq_add_components
  have hnewFirst : IsModular (D.component 0).space
      (D.component 0).lattice (P.scaleGenerator 0) := by
    exact P.rebalancedFirstComponent_isModular hscale hnorm
  rw [hnewFirst.volumeOrder_eq] at hnew
  have hnewRank : finrank K (D.component 0).carrier = 2 := by
    exact P.rebalancedFirstComponent_rank hscale hnorm
  rw [hnewRank] at hnew
  have hrank := P.rebalancedComplement_rank_eq hscale hnorm
  change volumeOrder (D.component 1).space (D.component 1).lattice = _
  rw [hrank]
  unfold componentRank
  exact add_left_cancel (hnew.symm.trans hold)

theorem rebalancedComplement_isModular
    (P : ModularPairSplitting q L)
    (hscale : P.scaleOrder 0 ≤ P.scaleOrder 1)
    (hnorm : P.normOrder 1 < P.normOrder 0) :
    IsModular
      ((P.rebalancedDecomposition hscale hnorm).component 1).space
      ((P.rebalancedDecomposition hscale hnorm).component 1).lattice
      (P.scaleGenerator 1) := by
  apply isModular_of_scaleIdeal_le_of_volumeOrder_eq
  · exact P.rebalancedComplement_scaleIdeal_le hscale hnorm
  · exact P.rebalancedComplement_volumeOrder_eq hscale hnorm

/-- The mixed-pairing condition used by the modular splitting. -/
theorem rebalancedFirstComponent_mixedPairing
    (P : ModularPairSplitting q L)
    (hscale : P.scaleOrder 0 ≤ P.scaleOrder 1)
    (hnorm : P.normOrder 1 < P.normOrder 0) :
    ∀ (y : (P.rebalancedFirstComponent hscale hnorm).carrier),
      y ∈ (P.rebalancedFirstComponent hscale hnorm).lattice →
      ∀ x : V, x ∈ L →
        q.bilin (y : V) x ∈
          principalIdeal (K := K) (P.scaleGenerator 0 : K) := by
  intro y hy x hx
  rw [← P.ambientScaleIdeal_eq_first hscale]
  exact bilin_mem_scaleIdeal_of_mem q L
    (P.rebalancedFirstComponent_contained hscale hnorm ⟨y, hy, rfl⟩) hx

/-- The concrete integral basis `(y, x + z)` of the replacement component. -/
noncomputable def rebalancedFirstBasis
    (P : ModularPairSplitting q L)
    (hscale : P.scaleOrder 0 ≤ P.scaleOrder 1)
    (hnorm : P.normOrder 1 < P.normOrder 0) :
    Basis (Fin 2) K (P.rebalancedFirstComponent hscale hnorm).carrier :=
  BONG.binaryPairBasis (K := K)
    (P.firstPairVector : V)
    ((P.firstNormVector : V) + (P.secondNormVector : V))
    (binaryPair_linearIndependent_of_left_strict
      P.rebalancedPair_ne_zero
      (P.rebalancedPair_left_strict hscale hnorm)
      (P.rebalancedPair_right_weak hscale hnorm))

theorem rebalancedFirstComponent_lattice_eq_basisLattice
    (P : ModularPairSplitting q L)
    (hscale : P.scaleOrder 0 ≤ P.scaleOrder 1)
    (hnorm : P.normOrder 1 < P.normOrder 0) :
    (P.rebalancedFirstComponent hscale hnorm).lattice =
      basisLattice (P.rebalancedFirstBasis hscale hnorm) :=
  rfl

/-- Projection of the old second norm vector to the replacement component. -/
noncomputable def rebalancedCarrierProjection
    (P : ModularPairSplitting q L)
    (hscale : P.scaleOrder 0 ≤ P.scaleOrder 1)
    (hnorm : P.normOrder 1 < P.normOrder 0) :
    (P.rebalancedFirstComponent hscale hnorm).carrier := by
  letI : Module.Finite K V := L.moduleFinite
  exact (P.rebalancedFirstComponent hscale hnorm).carrierProjection
    (P.secondNormVector : V)

theorem rebalancedCarrierProjection_mem
    (P : ModularPairSplitting q L)
    (hscale : P.scaleOrder 0 ≤ P.scaleOrder 1)
    (hnorm : P.normOrder 1 < P.normOrder 0) :
    P.rebalancedCarrierProjection hscale hnorm ∈
      (P.rebalancedFirstComponent hscale hnorm).lattice := by
  letI : Module.Finite K V := L.moduleFinite
  exact QuadraticSublattice.carrierProjection_mem_lattice_of_pairing
    (P.rebalancedFirstComponent hscale hnorm)
    (P.rebalancedFirstComponent_isModular hscale hnorm)
    (P.rebalancedFirstComponent_mixedPairing hscale hnorm)
    (P.toOrthogonalDecomposition.component_ambientSubmodule_le 1
      ⟨P.secondNormVector, P.secondNormVector_spec.1.mem, rfl⟩)

/-- The complementary projection of the old second norm generator. -/
noncomputable def rebalancedComplementNormVector
    (P : ModularPairSplitting q L)
    (hscale : P.scaleOrder 0 ≤ P.scaleOrder 1)
    (hnorm : P.normOrder 1 < P.normOrder 0) :
    ((P.rebalancedDecomposition hscale hnorm).component 1).carrier := by
  letI : Module.Finite K V := L.moduleFinite
  exact (P.rebalancedFirstComponent hscale hnorm).orthogonalProjection
    (P.secondNormVector : V)

theorem rebalancedComplementNormVector_mem
    (P : ModularPairSplitting q L)
    (hscale : P.scaleOrder 0 ≤ P.scaleOrder 1)
    (hnorm : P.normOrder 1 < P.normOrder 0) :
    P.rebalancedComplementNormVector hscale hnorm ∈
      ((P.rebalancedDecomposition hscale hnorm).component 1).lattice := by
  letI : Module.Finite K V := L.moduleFinite
  change ((P.rebalancedFirstComponent hscale hnorm).orthogonalProjection
      (P.secondNormVector : V) : V) ∈ L
  exact QuadraticSublattice.orthogonalProjection_mem_lattice
    (P.rebalancedFirstComponent hscale hnorm)
    (P.rebalancedFirstComponent_contained hscale hnorm)
    (P.rebalancedFirstComponent_isModular hscale hnorm)
    (P.rebalancedFirstComponent_mixedPairing hscale hnorm)
    (P.toOrthogonalDecomposition.component_ambientSubmodule_le 1
      ⟨P.secondNormVector, P.secondNormVector_spec.1.mem, rfl⟩)

/-- The two integral coordinates of the carrier projection. -/
noncomputable def rebalancedProjectionCoefficient
    (P : ModularPairSplitting q L)
    (hscale : P.scaleOrder 0 ≤ P.scaleOrder 1)
    (hnorm : P.normOrder 1 < P.normOrder 0) (i : Fin 2) : K :=
  (P.rebalancedFirstBasis hscale hnorm).repr
    (P.rebalancedCarrierProjection hscale hnorm) i

theorem rebalancedProjectionCoefficient_mem_integerRing
    (P : ModularPairSplitting q L)
    (hscale : P.scaleOrder 0 ≤ P.scaleOrder 1)
    (hnorm : P.normOrder 1 < P.normOrder 0) (i : Fin 2) :
    P.rebalancedProjectionCoefficient hscale hnorm i ∈ IntegerRing K := by
  have hp := P.rebalancedCarrierProjection_mem hscale hnorm
  rw [P.rebalancedFirstComponent_lattice_eq_basisLattice hscale hnorm,
    mem_basisLattice_iff_repr_mem_integerRing] at hp
  exact hp i

@[simp]
theorem coe_rebalancedFirstBasis_zero
    (P : ModularPairSplitting q L)
    (hscale : P.scaleOrder 0 ≤ P.scaleOrder 1)
    (hnorm : P.normOrder 1 < P.normOrder 0) :
    ((P.rebalancedFirstBasis hscale hnorm 0 :
      (P.rebalancedFirstComponent hscale hnorm).carrier) : V) =
      (P.firstPairVector : V) := by
  exact BONG.coe_binaryPairBasis _ _ _ 0

@[simp]
theorem coe_rebalancedFirstBasis_one
    (P : ModularPairSplitting q L)
    (hscale : P.scaleOrder 0 ≤ P.scaleOrder 1)
    (hnorm : P.normOrder 1 < P.normOrder 0) :
    ((P.rebalancedFirstBasis hscale hnorm 1 :
      (P.rebalancedFirstComponent hscale hnorm).carrier) : V) =
      (P.firstNormVector : V) + (P.secondNormVector : V) := by
  exact BONG.coe_binaryPairBasis _ _ _ 1

theorem rebalancedCarrierProjection_decomposition
    (P : ModularPairSplitting q L)
    (hscale : P.scaleOrder 0 ≤ P.scaleOrder 1)
    (hnorm : P.normOrder 1 < P.normOrder 0) :
    P.rebalancedProjectionCoefficient hscale hnorm 0 •
        (P.firstPairVector : V) +
      P.rebalancedProjectionCoefficient hscale hnorm 1 •
        ((P.firstNormVector : V) + (P.secondNormVector : V)) =
      (P.rebalancedCarrierProjection hscale hnorm : V) := by
  have h := (P.rebalancedFirstBasis hscale hnorm).sum_repr
    (P.rebalancedCarrierProjection hscale hnorm)
  rw [Fin.sum_univ_two] at h
  simpa only [rebalancedProjectionCoefficient,
    Submodule.coe_add, Submodule.coe_smul_of_tower,
    P.coe_rebalancedFirstBasis_zero hscale hnorm,
    P.coe_rebalancedFirstBasis_one hscale hnorm] using
      congrArg Subtype.val h

theorem rebalancedProjection_decomposition
    (P : ModularPairSplitting q L)
    (hscale : P.scaleOrder 0 ≤ P.scaleOrder 1)
    (hnorm : P.normOrder 1 < P.normOrder 0) :
    (P.rebalancedCarrierProjection hscale hnorm : V) +
        (P.rebalancedComplementNormVector hscale hnorm : V) =
      (P.secondNormVector : V) := by
  letI : Module.Finite K V := L.moduleFinite
  exact QuadraticSublattice.carrierProjection_add_orthogonalProjection
    (P.rebalancedFirstComponent hscale hnorm) (P.secondNormVector : V)

theorem rebalancedProjection_orthogonal
    (P : ModularPairSplitting q L)
    (hscale : P.scaleOrder 0 ≤ P.scaleOrder 1)
    (hnorm : P.normOrder 1 < P.normOrder 0) :
    q.bilin (P.rebalancedCarrierProjection hscale hnorm : V)
      (P.rebalancedComplementNormVector hscale hnorm : V) = 0 := by
  letI : Module.Finite K V := L.moduleFinite
  exact (P.rebalancedFirstComponent hscale hnorm).orthogonalProjection
    (P.secondNormVector : V) |>.property
      (P.rebalancedCarrierProjection hscale hnorm : V)
      (P.rebalancedCarrierProjection hscale hnorm).property

theorem rebalancedProjectionCoefficient_relation
    (P : ModularPairSplitting q L)
    (hscale : P.scaleOrder 0 ≤ P.scaleOrder 1)
    (hnorm : P.normOrder 1 < P.normOrder 0) :
    P.rebalancedProjectionCoefficient hscale hnorm 0 *
        q.quadratic (P.firstPairVector : V) +
      P.rebalancedProjectionCoefficient hscale hnorm 1 *
        (P.scaleGenerator 0 : K) = 0 := by
  have hpairProjection : q.bilin (P.firstPairVector : V)
      (P.rebalancedCarrierProjection hscale hnorm : V) = 0 := by
    calc
      q.bilin (P.firstPairVector : V)
          (P.rebalancedCarrierProjection hscale hnorm : V) =
        q.bilin (P.firstPairVector : V)
          ((P.rebalancedCarrierProjection hscale hnorm : V) +
            (P.rebalancedComplementNormVector hscale hnorm : V)) := by
              rw [LinearMap.BilinForm.add_right]
              have horth : q.bilin (P.firstPairVector : V)
                  (P.rebalancedComplementNormVector hscale hnorm : V) = 0 :=
                P.rebalancedComplement_orthogonal_firstPair hscale hnorm
                  (P.rebalancedComplementNormVector hscale hnorm)
              rw [horth, add_zero]
      _ = q.bilin (P.firstPairVector : V)
          (P.secondNormVector : V) := by
        rw [P.rebalancedProjection_decomposition hscale hnorm]
      _ = 0 := P.toOrthogonalDecomposition.orthogonal 0 1 (by decide)
        P.firstPairVector P.secondNormVector
  rw [← P.rebalancedCarrierProjection_decomposition hscale hnorm] at hpairProjection
  simpa only [LinearMap.BilinForm.add_right,
    LinearMap.BilinForm.smul_right, Algebra.smul_def,
    P.rebalancedPair_bilin_eq, QuadraticSpace.quadratic] using hpairProjection

theorem quadratic_rebalancedCarrierProjection
    (P : ModularPairSplitting q L)
    (hscale : P.scaleOrder 0 ≤ P.scaleOrder 1)
    (hnorm : P.normOrder 1 < P.normOrder 0) :
    q.quadratic (P.rebalancedCarrierProjection hscale hnorm : V) =
      P.rebalancedProjectionCoefficient hscale hnorm 1 *
        q.quadratic (P.secondNormVector : V) := by
  have hpair : q.bilin (P.rebalancedCarrierProjection hscale hnorm : V)
      (P.secondNormVector : V) =
      q.quadratic (P.rebalancedCarrierProjection hscale hnorm : V) := by
    rw [← P.rebalancedProjection_decomposition hscale hnorm,
      LinearMap.BilinForm.add_right,
      P.rebalancedProjection_orthogonal hscale hnorm, add_zero]
    rfl
  rw [← hpair,
    ← P.rebalancedCarrierProjection_decomposition hscale hnorm,
    LinearMap.BilinForm.add_left,
    LinearMap.BilinForm.smul_left,
    LinearMap.BilinForm.smul_left]
  rw [P.toOrthogonalDecomposition.orthogonal 0 1 (by decide)
      P.firstPairVector P.secondNormVector,
    LinearMap.BilinForm.add_left,
    P.toOrthogonalDecomposition.orthogonal 0 1 (by decide)
      P.firstNormVector P.secondNormVector]
  simp only [mul_zero, zero_add]
  rw [QuadraticSpace.quadratic]

theorem rebalancedProjectionCoefficient_one_order_pos
    (P : ModularPairSplitting q L)
    (hscale : P.scaleOrder 0 ≤ P.scaleOrder 1)
    (hnorm : P.normOrder 1 < P.normOrder 0)
    (hbeta : P.rebalancedProjectionCoefficient hscale hnorm 1 ≠ 0) :
    0 < ordUnit K (Units.mk0
      (P.rebalancedProjectionCoefficient hscale hnorm 1) hbeta) := by
  let alpha := P.rebalancedProjectionCoefficient hscale hnorm 0
  let beta := P.rebalancedProjectionCoefficient hscale hnorm 1
  have hrelation := P.rebalancedProjectionCoefficient_relation hscale hnorm
  have heq : alpha * q.quadratic (P.firstPairVector : V) =
      -(beta * (P.scaleGenerator 0 : K)) := by
    dsimp only [alpha, beta]
    linear_combination hrelation
  have hrhs : -(beta * (P.scaleGenerator 0 : K)) ≠ 0 := by
    exact neg_ne_zero.mpr (mul_ne_zero hbeta
      (Units.ne_zero (P.scaleGenerator 0)))
  have hlhs : alpha * q.quadratic (P.firstPairVector : V) ≠ 0 := by
    rw [heq]
    exact hrhs
  have halpha : alpha ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hlhs
    exact hlhs rfl
  have hqy : q.quadratic (P.firstPairVector : V) ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hlhs
    exact hlhs rfl
  let alphaUnit : Kˣ := Units.mk0 alpha halpha
  let betaUnit : Kˣ := Units.mk0 beta hbeta
  let qyUnit : Kˣ := Units.mk0
    (q.quadratic (P.firstPairVector : V)) hqy
  have hunitEq : alphaUnit * qyUnit =
      -(betaUnit * P.scaleGenerator 0) := by
    apply Units.ext
    exact heq
  have horderEq := congrArg (ordUnit K) hunitEq
  rw [ordUnit_mul, ordUnit_neg, ordUnit_mul] at horderEq
  have halphaNonneg : 0 ≤ ordUnit K alphaUnit :=
    ordUnit_nonneg_of_mem_integerRing alphaUnit (by
      change alpha ∈ IntegerRing K
      exact P.rebalancedProjectionCoefficient_mem_integerRing
        hscale hnorm 0)
  have hqyLower : P.normOrder 0 ≤ ordUnit K qyUnit := by
    have h := P.normOrder_le_ord_quadratic_firstPairVector
    change ((P.normOrder 0 : Int) : WithTop Int) ≤
      ord K (qyUnit : K) at h
    rw [← coe_ordUnit] at h
    exact_mod_cast h
  change 0 < ordUnit K betaUnit
  have hscaleNorm : P.scaleOrder 0 < P.normOrder 0 :=
    lt_of_le_of_lt (hscale.trans (P.scaleOrder_le_normOrder 1)) hnorm
  change ordUnit K alphaUnit + ordUnit K qyUnit =
      ordUnit K betaUnit + P.scaleOrder 0 at horderEq
  omega

theorem ord_quadratic_rebalancedCarrierProjection_gt
    (P : ModularPairSplitting q L)
    (hscale : P.scaleOrder 0 ≤ P.scaleOrder 1)
    (hnorm : P.normOrder 1 < P.normOrder 0) :
    ord K (q.quadratic (P.secondNormVector : V)) <
      ord K (q.quadratic (P.rebalancedCarrierProjection hscale hnorm : V)) := by
  let beta := P.rebalancedProjectionCoefficient hscale hnorm 1
  by_cases hbeta : beta = 0
  · rw [P.quadratic_rebalancedCarrierProjection hscale hnorm,
      show P.rebalancedProjectionCoefficient hscale hnorm 1 = 0 from hbeta,
      zero_mul, ord_zero, P.ord_quadratic_secondNormVector]
    exact WithTop.coe_lt_top _
  · let betaUnit : Kˣ := Units.mk0 beta hbeta
    have hpos : 0 < ordUnit K betaUnit :=
      P.rebalancedProjectionCoefficient_one_order_pos hscale hnorm hbeta
    rw [P.quadratic_rebalancedCarrierProjection hscale hnorm,
      ord_mul, P.ord_quadratic_secondNormVector]
    change ((P.normOrder 1 : Int) : WithTop Int) <
      ord K (betaUnit : K) + ((P.normOrder 1 : Int) : WithTop Int)
    rw [← coe_ordUnit]
    exact_mod_cast (show P.normOrder 1 <
      ordUnit K betaUnit + P.normOrder 1 by omega)

theorem quadratic_secondNormVector_eq_projection_add
    (P : ModularPairSplitting q L)
    (hscale : P.scaleOrder 0 ≤ P.scaleOrder 1)
    (hnorm : P.normOrder 1 < P.normOrder 0) :
    q.quadratic (P.secondNormVector : V) =
      q.quadratic (P.rebalancedCarrierProjection hscale hnorm : V) +
        q.quadratic (P.rebalancedComplementNormVector hscale hnorm : V) := by
  rw [← P.rebalancedProjection_decomposition hscale hnorm,
    q.quadratic_add, P.rebalancedProjection_orthogonal hscale hnorm,
    mul_zero, add_zero]

theorem ord_quadratic_rebalancedComplementNormVector
    (P : ModularPairSplitting q L)
    (hscale : P.scaleOrder 0 ≤ P.scaleOrder 1)
    (hnorm : P.normOrder 1 < P.normOrder 0) :
    ord K (q.quadratic
      (P.rebalancedComplementNormVector hscale hnorm : V)) =
      ((P.normOrder 1 : Int) : WithTop Int) := by
  have hquad := P.quadratic_secondNormVector_eq_projection_add hscale hnorm
  have hvalue : q.quadratic
      (P.rebalancedComplementNormVector hscale hnorm : V) =
      q.quadratic (P.secondNormVector : V) -
        q.quadratic (P.rebalancedCarrierProjection hscale hnorm : V) := by
    rw [eq_sub_iff_add_eq]
    simpa only [add_comm] using hquad.symm
  rw [hvalue, sub_eq_add_neg]
  have hlt : ord K (q.quadratic (P.secondNormVector : V)) <
      ord K (-q.quadratic
        (P.rebalancedCarrierProjection hscale hnorm : V)) := by
    rw [ord_neg]
    exact P.ord_quadratic_rebalancedCarrierProjection_gt hscale hnorm
  rw [(ord K).map_add_eq_of_lt_left hlt,
    P.ord_quadratic_secondNormVector]

theorem rebalancedComplementNormVector_anisotropic
    (P : ModularPairSplitting q L)
    (hscale : P.scaleOrder 0 ≤ P.scaleOrder 1)
    (hnorm : P.normOrder 1 < P.normOrder 0) :
    q.IsAnisotropic
      (P.rebalancedComplementNormVector hscale hnorm : V) := by
  intro hzero
  have hord := P.ord_quadratic_rebalancedComplementNormVector hscale hnorm
  rw [hzero, ord_zero] at hord
  exact WithTop.coe_ne_top hord.symm

theorem rebalancedComplement_normIdeal_eq
    (P : ModularPairSplitting q L)
    (hscale : P.scaleOrder 0 ≤ P.scaleOrder 1)
    (hnorm : P.normOrder 1 < P.normOrder 0) :
    normIdeal
        ((P.rebalancedDecomposition hscale hnorm).component 1).space
        ((P.rebalancedDecomposition hscale hnorm).component 1).lattice =
      principalIdeal (K := K) (P.normGenerator 1 : K) := by
  apply le_antisymm
  · rw [← P.ambientNormIdeal_eq_second hnorm]
    exact QuadraticSublattice.normIdeal_le_of_ambientSubmodule_le
      ((P.rebalancedDecomposition hscale hnorm).component 1)
      ((P.rebalancedDecomposition hscale hnorm).component_ambientSubmodule_le 1)
  · have hwValue : q.quadratic
        (P.rebalancedComplementNormVector hscale hnorm : V) ∈
        normIdeal
          ((P.rebalancedDecomposition hscale hnorm).component 1).space
          ((P.rebalancedDecomposition hscale hnorm).component 1).lattice := by
      exact quadratic_mem_normIdeal_of_mem
        ((P.rebalancedDecomposition hscale hnorm).component 1).space
        ((P.rebalancedDecomposition hscale hnorm).component 1).lattice
        (P.rebalancedComplementNormVector_mem hscale hnorm)
    have hprincipal : principalIdeal (K := K) (P.normGenerator 1 : K) =
        principalIdeal (K := K) (q.quadratic
          (P.rebalancedComplementNormVector hscale hnorm : V)) := by
      apply le_antisymm
      · apply (principalIdeal_le_iff_ord_ge
          (Units.ne_zero (P.normGenerator 1))
          (P.rebalancedComplementNormVector_anisotropic hscale hnorm)).2
        rw [P.ord_quadratic_rebalancedComplementNormVector hscale hnorm,
          ← coe_ordUnit]
        rfl
      · apply (principalIdeal_le_iff_ord_ge
          (P.rebalancedComplementNormVector_anisotropic hscale hnorm)
          (Units.ne_zero (P.normGenerator 1))).2
        rw [P.ord_quadratic_rebalancedComplementNormVector hscale hnorm,
          ← coe_ordUnit]
        rfl
    rw [hprincipal, principalIdeal,
      Submodule.span_singleton_le_iff_mem]
    exact hwValue

/-- The full replacement splitting of Lemma 4.5(i). -/
noncomputable def rebalancedPairSplitting
    (P : ModularPairSplitting q L)
    (hscale : P.scaleOrder 0 ≤ P.scaleOrder 1)
    (hnorm : P.normOrder 1 < P.normOrder 0) :
    ModularPairSplitting q L where
  toOrthogonalDecomposition := P.rebalancedDecomposition hscale hnorm
  scaleGenerator := P.scaleGenerator
  normGenerator := fun _ ↦ P.normGenerator 1
  modular := by
    intro i
    fin_cases i
    · exact P.rebalancedFirstComponent_isModular hscale hnorm
    · exact P.rebalancedComplement_isModular hscale hnorm
  scaleIdeal_eq := by
    intro i
    have hi : i = 0 ∨ i = 1 := by omega
    rcases hi with rfl | rfl
    · exact IsModular.scaleIdeal_eq_principal
        (P.rebalancedFirstComponent_isModular hscale hnorm) (by
          change 0 < finrank K
            (P.rebalancedFirstComponent hscale hnorm).carrier
          rw [P.rebalancedFirstComponent_rank hscale hnorm]
          decide)
    · exact IsModular.scaleIdeal_eq_principal
        (P.rebalancedComplement_isModular hscale hnorm) (by
          rw [P.rebalancedComplement_rank_eq hscale hnorm]
          exact P.second_componentRank_pos)
  normIdeal_eq := by
    intro i
    fin_cases i
    · exact P.rebalancedFirstComponent_normIdeal_eq hscale hnorm
    · exact P.rebalancedComplement_normIdeal_eq hscale hnorm
  first_rank := P.rebalancedFirstComponent_rank hscale hnorm

theorem rebalancedPairSplitting_preservesRanksAndScales
    (P : ModularPairSplitting q L)
    (hscale : P.scaleOrder 0 ≤ P.scaleOrder 1)
    (hnorm : P.normOrder 1 < P.normOrder 0) :
    P.PreservesRanksAndScales
      (P.rebalancedPairSplitting hscale hnorm) := by
  intro i
  have hi : i = 0 ∨ i = 1 := by
    omega
  rcases hi with rfl | rfl
  · constructor
    · unfold componentRank
      rw [(P.rebalancedPairSplitting hscale hnorm).first_rank,
        P.first_rank]
    · rw [(P.rebalancedPairSplitting hscale hnorm).scaleIdeal_eq 0,
        P.scaleIdeal_eq 0]
      rfl
  · constructor
    · unfold componentRank
      exact P.rebalancedComplement_rank_eq hscale hnorm
    · rw [(P.rebalancedPairSplitting hscale hnorm).scaleIdeal_eq 1,
        P.scaleIdeal_eq 1]
      rfl

theorem rebalancedPairSplitting_normsEqualOldSecond
    (P : ModularPairSplitting q L)
    (hscale : P.scaleOrder 0 ≤ P.scaleOrder 1)
    (hnorm : P.normOrder 1 < P.normOrder 0) :
    P.NormsEqualOldSecond
      (P.rebalancedPairSplitting hscale hnorm) := by
  intro i
  rw [(P.rebalancedPairSplitting hscale hnorm).normIdeal_eq,
    P.normIdeal_eq 1]
  rfl

/-- Unconditional proof of Beli (2003), Lemma 4.5(i). -/
theorem beliLemma45_i_proved
    (P : ModularPairSplitting q L)
    (hscale : P.scaleOrder 0 ≤ P.scaleOrder 1)
    (hnorm : P.normOrder 1 < P.normOrder 0) :
    ∃ P' : ModularPairSplitting q L,
      P.PreservesRanksAndScales P' ∧ P.NormsEqualOldSecond P' :=
  ⟨P.rebalancedPairSplitting hscale hnorm,
    P.rebalancedPairSplitting_preservesRanksAndScales hscale hnorm,
    P.rebalancedPairSplitting_normsEqualOldSecond hscale hnorm⟩

/-- Componentwise dualization without changing the component order. -/
noncomputable def componentwiseDualDecomposition
    (P : ModularPairSplitting q L) :
    OrthogonalDecomposition q (dualLattice q L) 2 :=
  P.toOrthogonalDecomposition.reverseDual.reindex Fin.revPerm

@[simp]
theorem componentwiseDualDecomposition_component
    (P : ModularPairSplitting q L) (i : Fin 2) :
    (P.componentwiseDualDecomposition.component i) =
      (P.component i).dual := by
  simp [componentwiseDualDecomposition,
    OrthogonalDecomposition.reverseDualComponent]

/-- Scale generator of a componentwise dual. -/
noncomputable def componentwiseDualScaleGenerator
    (P : ModularPairSplitting q L) (i : Fin 2) : Kˣ :=
  (P.scaleGenerator i)⁻¹

/-- Norm generator of a componentwise dual. -/
noncomputable def componentwiseDualNormGenerator
    (P : ModularPairSplitting q L) (i : Fin 2) : Kˣ :=
  (P.scaleGenerator i)⁻¹ ^ 2 * P.normGenerator i

theorem componentRank_pos (P : ModularPairSplitting q L) (i : Fin 2) :
    0 < P.componentRank i := by
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  · unfold componentRank
    rw [P.first_rank]
    decide
  · exact P.second_componentRank_pos

theorem componentwiseDual_isModular
    (P : ModularPairSplitting q L) (i : Fin 2) :
    IsModular (P.componentwiseDualDecomposition.component i).space
      (P.componentwiseDualDecomposition.component i).lattice
      (P.componentwiseDualScaleGenerator i) := by
  rw [P.componentwiseDualDecomposition_component]
  exact (P.modular i).dual

theorem componentwiseDual_scaleIdeal_eq
    (P : ModularPairSplitting q L) (i : Fin 2) :
    scaleIdeal (P.componentwiseDualDecomposition.component i).space
        (P.componentwiseDualDecomposition.component i).lattice =
      principalIdeal (K := K) (P.componentwiseDualScaleGenerator i : K) := by
  apply (P.componentwiseDual_isModular i).scaleIdeal_eq_principal
  rw [P.componentwiseDualDecomposition_component]
  exact P.componentRank_pos i

theorem componentwiseDual_normIdeal_eq
    (P : ModularPairSplitting q L) (i : Fin 2) :
    normIdeal (P.componentwiseDualDecomposition.component i).space
        (P.componentwiseDualDecomposition.component i).lattice =
      principalIdeal (K := K) (P.componentwiseDualNormGenerator i : K) := by
  rw [P.componentwiseDualDecomposition_component]
  change normIdeal (P.component i).space
      (dualLattice (P.component i).space (P.component i).lattice) = _
  rw [P.modular i]
  exact normIdeal_rescale_eq_principal_of_finrank_pos
    (P.componentRank_pos i) (P.scaleGenerator i)⁻¹
      (P.normGenerator i) (P.normIdeal_eq i)

/-- A modular pair splitting of the integral dual, in the same component
order as the source splitting. -/
noncomputable def componentwiseDual
    (P : ModularPairSplitting q L) :
    ModularPairSplitting q (dualLattice q L) where
  toOrthogonalDecomposition := P.componentwiseDualDecomposition
  scaleGenerator := P.componentwiseDualScaleGenerator
  normGenerator := P.componentwiseDualNormGenerator
  modular := P.componentwiseDual_isModular
  scaleIdeal_eq := P.componentwiseDual_scaleIdeal_eq
  normIdeal_eq := P.componentwiseDual_normIdeal_eq
  first_rank := by
    rw [P.componentwiseDualDecomposition_component]
    exact P.first_rank

theorem componentwiseDual_componentRank
    (P : ModularPairSplitting q L) (i : Fin 2) :
    P.componentwiseDual.componentRank i = P.componentRank i := by
  unfold componentRank
  rw [componentwiseDual, P.componentwiseDualDecomposition_component]
  rw [QuadraticSublattice.dual_carrier]

theorem componentwiseDual_scaleOrder
    (P : ModularPairSplitting q L) (i : Fin 2) :
    P.componentwiseDual.scaleOrder i = -P.scaleOrder i := by
  simp only [scaleOrder, componentwiseDual,
    componentwiseDualScaleGenerator, ordUnit_inv]

theorem componentwiseDual_normOrder
    (P : ModularPairSplitting q L) (i : Fin 2) :
    P.componentwiseDual.normOrder i = P.dualNormOrder i := by
  simp only [normOrder, dualNormOrder, componentwiseDual,
    componentwiseDualNormGenerator, ordUnit_mul, ordUnit_pow,
    ordUnit_inv, scaleOrder]
  ring

/-- Dualize a splitting of `L♯` componentwise and identify `L♯♯` with
`L`.  The record is written explicitly so all component data remain
definitionally visible after the identification. -/
noncomputable def doubleDualReturn
    (Q : ModularPairSplitting q (dualLattice q L)) :
    ModularPairSplitting q L where
  toOrthogonalDecomposition := {
    component := Q.componentwiseDual.component
    orthogonal := Q.componentwiseDual.orthogonal
    sum_eq := by
      rw [Q.componentwiseDual.sum_eq, dualLattice_dualLattice]
  }
  scaleGenerator := Q.componentwiseDual.scaleGenerator
  normGenerator := Q.componentwiseDual.normGenerator
  modular := Q.componentwiseDual.modular
  scaleIdeal_eq := Q.componentwiseDual.scaleIdeal_eq
  normIdeal_eq := Q.componentwiseDual.normIdeal_eq
  first_rank := Q.componentwiseDual.first_rank

@[simp]
theorem doubleDualReturn_component
    (Q : ModularPairSplitting q (dualLattice q L)) (i : Fin 2) :
    (Q.doubleDualReturn.component i) = Q.componentwiseDual.component i :=
  rfl

theorem doubleDualReturn_componentRank
    (Q : ModularPairSplitting q (dualLattice q L)) (i : Fin 2) :
    Q.doubleDualReturn.componentRank i = Q.componentRank i :=
  Q.componentwiseDual_componentRank i

theorem doubleDualReturn_scaleOrder
    (Q : ModularPairSplitting q (dualLattice q L)) (i : Fin 2) :
    Q.doubleDualReturn.scaleOrder i = -Q.scaleOrder i :=
  Q.componentwiseDual_scaleOrder i

theorem doubleDualReturn_normOrder
    (Q : ModularPairSplitting q (dualLattice q L)) (i : Fin 2) :
    Q.doubleDualReturn.normOrder i = Q.dualNormOrder i :=
  Q.componentwiseDual_normOrder i

theorem doubleDualReturn_dualNormOrder
    (Q : ModularPairSplitting q (dualLattice q L)) (i : Fin 2) :
    Q.doubleDualReturn.dualNormOrder i = Q.normOrder i := by
  unfold dualNormOrder
  rw [Q.doubleDualReturn_normOrder, Q.doubleDualReturn_scaleOrder]
  unfold dualNormOrder
  ring

/-- Unconditional proof of Beli (2003), Lemma 4.5(ii), obtained by applying
part (i) to the componentwise dual splitting and dualizing back. -/
theorem beliLemma45_ii_proved
    (P : ModularPairSplitting q L)
    (hscale : P.scaleOrder 1 ≤ P.scaleOrder 0)
    (hnorm : P.dualNormOrder 1 < P.dualNormOrder 0) :
    ∃ P' : ModularPairSplitting q L,
      P.PreservesRanksAndScales P' ∧
        P.DualNormOrdersEqualOldSecond P' := by
  let Pd := P.componentwiseDual
  have hdScale : Pd.scaleOrder 0 ≤ Pd.scaleOrder 1 := by
    rw [P.componentwiseDual_scaleOrder,
      P.componentwiseDual_scaleOrder]
    omega
  have hdNorm : Pd.normOrder 1 < Pd.normOrder 0 := by
    rw [P.componentwiseDual_normOrder,
      P.componentwiseDual_normOrder]
    exact hnorm
  rcases Pd.beliLemma45_i_proved hdScale hdNorm with
    ⟨Q, hpreserves, hnorms⟩
  refine ⟨Q.doubleDualReturn, ?_, ?_⟩
  · intro i
    constructor
    · calc
        Q.doubleDualReturn.componentRank i = Q.componentRank i :=
          Q.doubleDualReturn_componentRank i
        _ = Pd.componentRank i := (hpreserves i).1
        _ = P.componentRank i := P.componentwiseDual_componentRank i
    · have hideals := (hpreserves i).2
      have hprincipal : principalIdeal (K := K) (Q.scaleGenerator i : K) =
          principalIdeal (K := K) (Pd.scaleGenerator i : K) := by
        rw [← Q.scaleIdeal_eq i, ← Pd.scaleIdeal_eq i]
        exact hideals
      have horders := (principalIdeal_eq_iff_ordUnit_eq
        (Q.scaleGenerator i) (Pd.scaleGenerator i)).mp hprincipal
      change Q.scaleOrder i = Pd.scaleOrder i at horders
      rw [P.componentwiseDual_scaleOrder] at horders
      rw [Q.doubleDualReturn.scaleIdeal_eq i, P.scaleIdeal_eq i]
      apply (principalIdeal_eq_iff_ordUnit_eq
        (Q.doubleDualReturn.scaleGenerator i)
        (P.scaleGenerator i)).2
      change Q.doubleDualReturn.scaleOrder i = P.scaleOrder i
      rw [Q.doubleDualReturn_scaleOrder]
      omega
  · intro i
    have hideals := hnorms i
    have hprincipal : principalIdeal (K := K) (Q.normGenerator i : K) =
        principalIdeal (K := K) (Pd.normGenerator 1 : K) := by
      rw [← Q.normIdeal_eq i, ← Pd.normIdeal_eq 1]
      exact hideals
    have horders := (principalIdeal_eq_iff_ordUnit_eq
      (Q.normGenerator i) (Pd.normGenerator 1)).mp hprincipal
    change Q.normOrder i = Pd.normOrder 1 at horders
    calc
      Q.doubleDualReturn.dualNormOrder i = Q.normOrder i :=
        Q.doubleDualReturn_dualNormOrder i
      _ = Pd.normOrder 1 := horders
      _ = P.dualNormOrder 1 := P.componentwiseDual_normOrder 1

end ModularPairSplitting

/-- Beli (2003), Lemma 4.5 has no remaining local-law hypothesis. -/
instance beliLemma45LawsProved : BeliLemma45Laws.{u, v} K where
  rebalance_norms := fun P hscale hnorm ↦
    P.beliLemma45_i_proved hscale hnorm
  rebalance_dualNorms := fun P hscale hnorm ↦
    P.beliLemma45_ii_proved hscale hnorm

end Lattice

end Bong
