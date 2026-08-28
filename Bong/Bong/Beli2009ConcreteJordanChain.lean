/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma41PropertyAProof
import Bong.Bong.Beli2009JordanWeightOrderProof
import Bong.Bong.Beli2009NormGeneratorSignsProof
import Bong.Bong.JordanScaleTruncation
import Bong.Lattice.OmearaFundamentalInvariants

/-!
# Concrete Jordan-chain data for Beli (2009)

The early statement modules for Lemmas 2.13--2.17 used records whose Jordan
component and scale layer were arbitrary fields.  Such records cannot support
unconditional theorems: the asserted norm generator need not have any
relationship to either arbitrary lattice.  This module starts the corrected
proof layer from `PropertyAJordanWitness`, where the components literally form
an adapted Jordan decomposition of the original lattice.

The first result identifies the first value in every selected component BONG
as a norm generator both of the actual component and of O'Meara's intrinsic
scale layer `L^{s_i}`.  The second assertion uses property A to show that the
component norm order is the minimum norm order in that scale layer.
-/

namespace Bong

open Dyadic Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

namespace BONG

/-- If the two values of a binary BONG have the same order, the second
value is a scalar norm generator as well.  In this branch the BONG lattice
is its orthogonal basis lattice, so the assertion is integral rather than
merely a statement about the ambient quadratic space. -/
theorem valueUnit_one_isNormGeneratorValue_of_orders_eq
    (b : BONG V q L 2) (horder : b.order 1 = b.order 0) :
    Lattice.IsNormGeneratorValue q L (b.valueUnit 1) := by
  have hgap : b.binaryOrderGap = 0 := by
    rw [binaryOrderGap]
    omega
  have hlattice := b.lattice_eq_basisLattice_of_binaryOrderGap_nonneg
    (show 0 ≤ b.binaryOrderGap by rw [hgap])
  have hmem : b.ambientVector 1 ∈ L := by
    have hsub : L.toSubmodule =
        (Lattice.basisLattice b.basis).toSubmodule :=
      congrArg Lattice.toSubmodule hlattice
    change b.ambientVector 1 ∈ L.toSubmodule
    rw [hsub]
    change b.basis 1 ∈ Lattice.basisLattice b.basis
    exact Submodule.subset_span ⟨1, rfl⟩
  constructor
  · refine ⟨b.ambientVector 1, hmem, 0, Submodule.zero_mem _, ?_⟩
    rw [b.quadratic_ambientVector]
    simp
  · calc
      Lattice.normIdeal q L =
          Lattice.principalIdeal (K := K) (b.valueUnit 0 : K) := by
        simpa only [b.coe_valueUnit, b.value_zero_eq_quadratic_head] using
          b.head_isNormGenerator.normIdeal_eq
      _ = Lattice.principalIdeal (K := K) (b.valueUnit 1 : K) := by
        apply (Lattice.principalIdeal_eq_iff_ordUnit_eq
          (b.valueUnit 0) (b.valueUnit 1)).2
        rw [← b.order_eq_ordUnit, ← b.order_eq_ordUnit]
        exact horder.symm

/-- Beli's rescaled terminal value for a modular binary BONG. -/
noncomputable def modularTerminalNormValue
    (b : BONG V q L 2) (scaleGenerator : Kˣ) : Kˣ :=
  uniformizerPowerUnit K
      (2 * b.order 0 - 2 * ordUnit K scaleGenerator) * b.valueUnit 1

/-- The terminal value in Beli (2009), Lemma 2.13(iii), is an actual scalar
norm generator of every modular binary component.  The strict branch uses
the integral clearing vector; the equal-order branch uses the orthogonal
basis lattice directly. -/
theorem modularTerminalNormValue_isNormGeneratorValue
    (b : BONG V q L 2) (scaleGenerator : Kˣ)
    (hmodular : Lattice.IsModular q L scaleGenerator) :
    Lattice.IsNormGeneratorValue q L
      (b.modularTerminalNormValue scaleGenerator) := by
  have hle := b.order_one_le_order_zero_of_isModular
    scaleGenerator hmodular
  by_cases heq : b.order 1 = b.order 0
  · have hscale : b.order 0 = ordUnit K scaleGenerator := by
      have hsum := b.two_mul_modularOrder_eq_order_add
        scaleGenerator hmodular
      omega
    simpa only [modularTerminalNormValue, hscale, sub_self,
      uniformizerPowerUnit, zpow_zero, one_mul] using
        b.valueUnit_one_isNormGeneratorValue_of_orders_eq heq
  · have hstrict : b.order 1 < b.order 0 := lt_of_le_of_ne hle heq
    let s := b.terminalMultiplierUnit hstrict
    let canonical : Kˣ := s ^ 2 * b.valueUnit 1
    have hcanonical : Lattice.IsNormGeneratorValue q L canonical := by
      have hgen := b.terminalNormVector_isNormGenerator hstrict
      have hne : q.quadratic (b.terminalNormVector hstrict) ≠ 0 := by
        rw [b.quadratic_terminalNormVector hstrict]
        exact Units.ne_zero _
      have hvalue := hgen.isNormGeneratorValue hne
      convert hvalue using 1
      apply Units.ext
      change (canonical : K) = q.quadratic (b.terminalNormVector hstrict)
      exact (b.quadratic_terminalNormVector hstrict).symm
    have hsOrder : ordUnit K s =
        b.order 0 - ordUnit K scaleGenerator := by
      have hmult := b.two_mul_ordUnit_terminalMultiplierUnit hstrict
      have hsum := b.two_mul_modularOrder_eq_order_add
        scaleGenerator hmodular
      dsimp only [s]
      omega
    let p : Kˣ := uniformizerPowerUnit K
      (b.order 0 - ordUnit K scaleGenerator)
    let z : Kˣ := p / s
    have hzOrder : ordUnit K z = 0 := by
      dsimp only [z, p]
      rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv,
        ordUnit_uniformizerPowerUnit, hsOrder]
      omega
    have hpower : uniformizerPowerUnit K
          (2 * b.order 0 - 2 * ordUnit K scaleGenerator) = p ^ 2 := by
      dsimp only [p]
      unfold uniformizerPowerUnit
      rw [pow_two, ← zpow_add]
      congr 1
      omega
    have hscaled := hcanonical.mul_square_of_ordUnit_zero z hzOrder
    convert hscaled using 1
    dsimp only [modularTerminalNormValue, canonical, z]
    rw [hpower]
    apply Units.ext
    simp only [Units.val_mul, Units.val_pow_eq_pow_val,
      Units.val_div_eq_div_val]
    field_simp [Units.ne_zero s]

end BONG

namespace BONG.PropertyAJordanWitness

variable {b : BONG V q L n} (P : PropertyAJordanWitness b)

/-- The first local coordinate of the selected BONG in a genuine Jordan
component. -/
def componentFirstIndex (i : Fin (P.blockCount + 1)) :
    Fin (P.jordan.componentRank i) :=
  ⟨0, P.jordan.component_finrank_pos i⟩

/-- The first scalar value of the selected component BONG. -/
noncomputable def componentFirstValue (i : Fin (P.blockCount + 1)) : Kˣ :=
  (P.componentBONG i).valueUnit (P.componentFirstIndex i)

/-- The first selected value really generates the norm of its Jordan
component. -/
theorem componentFirstValue_isNormGeneratorValue
    (i : Fin (P.blockCount + 1)) :
    Lattice.IsNormGeneratorValue
      (P.jordan.component i).space (P.jordan.component i).lattice
      (P.componentFirstValue i) := by
  let c := P.componentBONG i
  let first : Fin (P.jordan.componentRank i) := P.componentFirstIndex i
  have hx : Lattice.IsNormGenerator
      (P.jordan.component i).space (P.jordan.component i).lattice
      (c.ambientVector first) :=
    c.ambientVector_first_isNormGenerator (P.jordan.component_finrank_pos i)
  have hne : (P.jordan.component i).space.quadratic
      (c.ambientVector first) ≠ 0 := by
    rw [c.quadratic_ambientVector]
    exact c.value_ne_zero first
  have hvalue := hx.isNormGeneratorValue hne
  convert hvalue using 1
  apply Units.ext
  simp only [componentFirstValue, componentFirstIndex, c, first,
    BONG.coe_valueUnit, Units.val_mk0, c.quadratic_ambientVector]

/-- The first selected component order is the chosen Jordan norm order. -/
theorem componentFirstOrder_eq_normGeneratorOrder
    (i : Fin (P.blockCount + 1)) :
    (P.componentBONG i).order (P.componentFirstIndex i) =
      ordUnit K (P.jordan.normGenerator i) := by
  rw [BONG.order_eq_ordUnit]
  apply (Lattice.principalIdeal_eq_iff_ordUnit_eq
    ((P.componentBONG i).valueUnit (P.componentFirstIndex i))
    (P.jordan.normGenerator i)).mp
  calc
    Lattice.principalIdeal (K := K)
        ((P.componentBONG i).valueUnit (P.componentFirstIndex i) : K) =
        Lattice.normIdeal (P.jordan.component i).space
          (P.jordan.component i).lattice :=
      (P.componentFirstValue_isNormGeneratorValue i).2.symm
    _ = Lattice.principalIdeal (K := K)
        (P.jordan.normGenerator i : K) := P.jordan.normIdeal_eq i

/-- The last local coordinate in a genuine unary-or-binary Jordan
component. -/
noncomputable def componentLastIndex (i : Fin (P.blockCount + 1)) :
    Fin (P.jordan.componentRank i) :=
  ⟨P.jordan.componentRank i - 1, by
    exact Nat.sub_lt (P.jordan.component_finrank_pos i) Nat.zero_lt_one⟩

/-- The paper's terminal scalar attached to a genuine Jordan component. -/
noncomputable def componentTerminalValue
    (i : Fin (P.blockCount + 1)) : Kˣ :=
  uniformizerPowerUnit K
      (2 * ordUnit K (P.jordan.normGenerator i) -
        2 * ordUnit K (P.jordan.scaleGenerator i)) *
    (P.componentBONG i).valueUnit (P.componentLastIndex i)

/-- The terminal scalar of every genuine Jordan component is a norm
generator of that component. -/
theorem componentTerminalValue_isNormGeneratorValue
    (i : Fin (P.blockCount + 1)) :
    Lattice.IsNormGeneratorValue
      (P.jordan.component i).space (P.jordan.component i).lattice
      (P.componentTerminalValue i) := by
  rcases P.propertyA.1 i with hOne | hTwo
  · have hlast : P.componentLastIndex i = P.componentFirstIndex i := by
      apply Fin.ext
      simp only [componentLastIndex, componentFirstIndex]
      omega
    have hnormScale : ordUnit K (P.jordan.normGenerator i) =
        ordUnit K (P.jordan.scaleGenerator i) :=
      Lattice.ordUnit_normGenerator_eq_scaleGenerator_of_finrank_eq_one
        (P.jordan.component i).space (P.jordan.component i).lattice
        (P.jordan.scaleGenerator i) (P.jordan.normGenerator i)
        hOne (P.jordan.modular i) (P.jordan.normIdeal_eq i)
    simpa only [componentTerminalValue, hnormScale, sub_self,
      uniformizerPowerUnit, zpow_zero, one_mul, hlast,
      componentFirstValue] using
        P.componentFirstValue_isNormGeneratorValue i
  · let c₂ := (P.componentBONG i).castLength hTwo
    have hmodular : Lattice.IsModular
        (P.jordan.component i).space (P.jordan.component i).lattice
        (P.jordan.scaleGenerator i) := P.jordan.modular i
    have hterminal := c₂.modularTerminalNormValue_isNormGeneratorValue
      (P.jordan.scaleGenerator i) hmodular
    have hzero :
        (⟨0, by omega⟩ : Fin (P.jordan.componentRank i)) =
          P.componentFirstIndex i := by
      apply Fin.ext
      rfl
    have horderZero : c₂.order 0 =
        ordUnit K (P.jordan.normGenerator i) := by
      calc
        c₂.order 0 = (P.componentBONG i).order
            ⟨0, P.jordan.component_finrank_pos i⟩ := by
          exact BONG.order_castLength (P.componentBONG i) hTwo 0
        _ = (P.componentBONG i).order
            (P.componentFirstIndex i) := by
          apply congrArg (P.componentBONG i).order
          exact Fin.ext rfl
        _ = ordUnit K (P.jordan.normGenerator i) :=
          P.componentFirstOrder_eq_normGeneratorOrder i
    have hlast : P.componentLastIndex i =
        (⟨1, by omega⟩ : Fin (P.jordan.componentRank i)) := by
      apply Fin.ext
      simp only [componentLastIndex]
      omega
    convert hterminal using 1
    apply Units.ext
    simp only [componentTerminalValue, modularTerminalNormValue,
      Units.val_mul]
    rw [horderZero]
    congr 1
    rw [BONG.coe_valueUnit, BONG.coe_valueUnit,
      BONG.value_castLength]
    congr 1

/-- The first selected component value is also a norm generator of the
intrinsic fundamental lattice `L^{s_i}`. -/
theorem componentFirstValue_isNormGeneratorValue_fundamentalLattice
    (i : Fin (P.blockCount + 1)) :
    Lattice.IsNormGeneratorValue q
      (P.jordan.fundamentalLattice i) (P.componentFirstValue i) := by
  let D := P.jordan.scaleTruncationDecomposition
    (P.jordan.fundamentalScaleOrder i)
  have hcomponent := P.componentFirstValue_isNormGeneratorValue i
  have hcomponentD : Lattice.IsNormGeneratorValue
      (D.component i).space (D.component i).lattice
      (P.componentFirstValue i) := by
    have hDi : D.component i = P.jordan.component i := by
      simpa only [D, Lattice.JordanDecomposition.fundamentalScaleOrder] using
        P.jordan.scaleTruncationDecomposition_component_self i
    rw [hDi]
    exact hcomponent
  have hmember : (P.componentFirstValue i : K) ∈
      Lattice.normGroupSet q (P.jordan.fundamentalLattice i) := by
    have hsubset := D.component_normGroupSet_subset i hcomponentD.1
    simpa only [D, Lattice.JordanDecomposition.fundamentalLattice,
      Lattice.JordanDecomposition.fundamentalScaleOrder,
      Lattice.JordanDecomposition.scaleTruncationDecomposition_component_self]
      using hsubset
  have hprincipal :
      Lattice.principalIdeal (K := K) (P.componentFirstValue i : K) =
        Lattice.principalIdeal (K := K) (P.jordan.normGenerator i : K) := by
    calc
      Lattice.principalIdeal (K := K) (P.componentFirstValue i : K) =
          Lattice.normIdeal (P.jordan.component i).space
            (P.jordan.component i).lattice := hcomponent.2.symm
      _ = Lattice.principalIdeal (K := K)
          (P.jordan.normGenerator i : K) := P.jordan.normIdeal_eq i
  have horder : ordUnit K (P.componentFirstValue i) =
      ordUnit K (P.jordan.normGenerator i) :=
    (Lattice.principalIdeal_eq_iff_ordUnit_eq
      (P.componentFirstValue i) (P.jordan.normGenerator i)).mp hprincipal
  refine ⟨hmember, ?_⟩
  calc
    Lattice.normIdeal q (P.jordan.fundamentalLattice i) =
        Lattice.powerIdeal (K := K)
          (BONG.jordanEffectiveNormOrder P.jordan i) := by
      exact P.jordan.normIdeal_scaleTruncation_eq_powerIdeal i
        (P.jordan.fundamentalScaleOrder i)
    _ = Lattice.powerIdeal (K := K)
          (ordUnit K (P.jordan.normGenerator i)) := by
      rw [P.propertyA.jordanEffectiveNormOrder_eq_normGenerator]
    _ = Lattice.powerIdeal (K := K)
          (ordUnit K (P.componentFirstValue i)) := by rw [horder]
    _ = Lattice.principalIdeal (K := K)
          (P.componentFirstValue i : K) :=
      (Lattice.principalIdeal_eq_powerIdeal
        (P.componentFirstValue i)).symm

/-- The terminal component value is also a norm generator of the intrinsic
fundamental scale layer. -/
theorem componentTerminalValue_isNormGeneratorValue_fundamentalLattice
    (i : Fin (P.blockCount + 1)) :
    Lattice.IsNormGeneratorValue q
      (P.jordan.fundamentalLattice i) (P.componentTerminalValue i) := by
  let D := P.jordan.scaleTruncationDecomposition
    (P.jordan.fundamentalScaleOrder i)
  have hcomponent := P.componentTerminalValue_isNormGeneratorValue i
  have hcomponentD : Lattice.IsNormGeneratorValue
      (D.component i).space (D.component i).lattice
      (P.componentTerminalValue i) := by
    have hDi : D.component i = P.jordan.component i := by
      simpa only [D, Lattice.JordanDecomposition.fundamentalScaleOrder] using
        P.jordan.scaleTruncationDecomposition_component_self i
    rw [hDi]
    exact hcomponent
  have hmember : (P.componentTerminalValue i : K) ∈
      Lattice.normGroupSet q (P.jordan.fundamentalLattice i) := by
    have hsubset := D.component_normGroupSet_subset i hcomponentD.1
    simpa only [D, Lattice.JordanDecomposition.fundamentalLattice,
      Lattice.JordanDecomposition.fundamentalScaleOrder,
      Lattice.JordanDecomposition.scaleTruncationDecomposition_component_self]
      using hsubset
  have hprincipal :
      Lattice.principalIdeal (K := K) (P.componentTerminalValue i : K) =
        Lattice.principalIdeal (K := K) (P.jordan.normGenerator i : K) := by
    calc
      Lattice.principalIdeal (K := K) (P.componentTerminalValue i : K) =
          Lattice.normIdeal (P.jordan.component i).space
            (P.jordan.component i).lattice := hcomponent.2.symm
      _ = Lattice.principalIdeal (K := K)
          (P.jordan.normGenerator i : K) := P.jordan.normIdeal_eq i
  have horder : ordUnit K (P.componentTerminalValue i) =
      ordUnit K (P.jordan.normGenerator i) :=
    (Lattice.principalIdeal_eq_iff_ordUnit_eq
      (P.componentTerminalValue i) (P.jordan.normGenerator i)).mp hprincipal
  refine ⟨hmember, ?_⟩
  calc
    Lattice.normIdeal q (P.jordan.fundamentalLattice i) =
        Lattice.powerIdeal (K := K)
          (BONG.jordanEffectiveNormOrder P.jordan i) := by
      exact P.jordan.normIdeal_scaleTruncation_eq_powerIdeal i
        (P.jordan.fundamentalScaleOrder i)
    _ = Lattice.powerIdeal (K := K)
        (ordUnit K (P.jordan.normGenerator i)) := by
      rw [P.propertyA.jordanEffectiveNormOrder_eq_normGenerator]
    _ = Lattice.powerIdeal (K := K)
        (ordUnit K (P.componentTerminalValue i)) := by rw [horder]
    _ = Lattice.principalIdeal (K := K)
        (P.componentTerminalValue i : K) :=
      (Lattice.principalIdeal_eq_powerIdeal
        (P.componentTerminalValue i)).symm

/-- Both signs of the first selected component value are norm generators of
the component and of its fundamental scale layer, as required in the first
half of Beli's Lemma 2.13(iii). -/
theorem componentFirstValue_bothSigns
    (i : Fin (P.blockCount + 1)) :
    Lattice.BothSignsNormGeneratorValue
        (P.jordan.component i).space (P.jordan.component i).lattice
        (P.componentFirstValue i) ∧
      Lattice.BothSignsNormGeneratorValue q
        (P.jordan.fundamentalLattice i) (P.componentFirstValue i) :=
  ⟨(P.componentFirstValue_isNormGeneratorValue i).bothSigns,
    (P.componentFirstValue_isNormGeneratorValue_fundamentalLattice i).bothSigns⟩

/-- Concrete Beli (2009), Lemma 2.13(iii), for every block of the adapted
Jordan decomposition.  Unlike `JordanBlockLatticeData`, all four lattices
and both endpoint values here are tied to the same decomposition witness. -/
theorem beli2009Lemma213_iii_concrete
    (i : Fin (P.blockCount + 1)) :
    Lattice.BothSignsNormGeneratorValue
        (P.jordan.component i).space (P.jordan.component i).lattice
        (P.componentFirstValue i) ∧
      Lattice.BothSignsNormGeneratorValue q
        (P.jordan.fundamentalLattice i) (P.componentFirstValue i) ∧
      Lattice.BothSignsNormGeneratorValue
        (P.jordan.component i).space (P.jordan.component i).lattice
        (P.componentTerminalValue i) ∧
      Lattice.BothSignsNormGeneratorValue q
        (P.jordan.fundamentalLattice i) (P.componentTerminalValue i) := by
  refine ⟨(P.componentFirstValue_isNormGeneratorValue i).bothSigns,
    (P.componentFirstValue_isNormGeneratorValue_fundamentalLattice i).bothSigns,
    (P.componentTerminalValue_isNormGeneratorValue i).bothSigns,
    ?_⟩
  exact (P.componentTerminalValue_isNormGeneratorValue_fundamentalLattice i).bothSigns

end BONG.PropertyAJordanWitness

end Bong
