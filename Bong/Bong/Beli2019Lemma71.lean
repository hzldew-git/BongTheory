/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma319
import Bong.Bong.BeliLemma411
import Bong.Bong.BeliCorollary44
import Bong.Bong.BeliCorollary44ScaleProof
import Bong.Bong.Beli2019ProjectionNormIdeal
import Bong.Lattice.DVRFactorization

/-!
# Beli (2019), Lemma 7.1

Let `R` be the order of the norm of `L`.  Under the strict scale bound
`sL ⊆ p^(R-e+1)`, the vectors whose quadratic values have order above `R`
form a full sublattice.  These are exactly the vectors which are not norm
generators.

The key addition argument is not postulated: the polarization step already
proved in Beli (2003), Lemma 3.19 forces a mixed pairing of order `R-e`,
contradicting the strict scale bound.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace Lattice

/-- Every quadratic value in a lattice has order at least the order of its
norm ideal. -/
theorem normOrder_le_ord_quadratic
    (R : Int) (hnorm : normIdeal q L = powerIdeal (K := K) R)
    {x : V} (hx : x ∈ L) :
    (R : WithTop Int) ≤ ord K (q.quadratic x) := by
  have hmem := quadratic_mem_normIdeal_of_mem q L hx
  rw [hnorm, mem_powerIdeal_iff] at hmem
  exact hmem

/-- Relative to a specified nonzero norm ideal, a lattice vector is a norm
generator exactly when its quadratic value has the minimal possible order. -/
theorem isNormGenerator_iff_ord_quadratic_eq
    (R : Int) (hnorm : normIdeal q L = powerIdeal (K := K) R)
    {x : V} (hx : x ∈ L) :
    IsNormGenerator q L x ↔
      ord K (q.quadratic x) = (R : WithTop Int) := by
  constructor
  · intro generator
    have hprincipal :
        principalIdeal (K := K) (q.quadratic x) =
          powerIdeal (K := K) R :=
      generator.normIdeal_eq.symm.trans hnorm
    have hxne : q.quadratic x ≠ 0 := by
      intro hzero
      have hmem :
          (uniformizerPowerUnit K R : K) ∈
            principalIdeal (K := K) (q.quadratic x) := by
        rw [hprincipal]
        exact generator_mem_principalIdeal _
      rw [hzero, principalIdeal] at hmem
      exact Units.ne_zero (uniformizerPowerUnit K R) (by simpa using hmem)
    let xu : Kˣ := Units.mk0 (q.quadratic x) hxne
    have hpower :
        powerIdeal (K := K) (ordUnit K xu) =
          powerIdeal (K := K) R :=
      (principalIdeal_eq_powerIdeal xu).symm.trans hprincipal
    have hge : R ≤ ordUnit K xu :=
      (powerIdeal_le_iff (K := K) (ordUnit K xu) R).mp hpower.le
    have hle : ordUnit K xu ≤ R :=
      (powerIdeal_le_iff (K := K) R (ordUnit K xu)).mp hpower.ge
    have horder : ordUnit K xu = R := le_antisymm hle hge
    calc
      ord K (q.quadratic x) = (ordUnit K xu : WithTop Int) := by
        simpa [xu] using (coe_ordUnit K xu).symm
      _ = (R : WithTop Int) := by rw [horder]
  · intro horder
    have hxne : q.quadratic x ≠ 0 := by
      intro hzero
      rw [hzero, ord_zero] at horder
      exact WithTop.top_ne_coe horder
    let xu : Kˣ := Units.mk0 (q.quadratic x) hxne
    have horderUnit : ordUnit K xu = R := by
      apply WithTop.coe_injective
      rw [coe_ordUnit]
      exact horder
    refine ⟨hx, ?_⟩
    calc
      normIdeal q L = powerIdeal (K := K) R := hnorm
      _ = powerIdeal (K := K) (ordUnit K xu) := by rw [horderUnit]
      _ = principalIdeal (K := K) (q.quadratic x) :=
        (principalIdeal_eq_powerIdeal xu).symm

/-- The non-norm-generators are precisely the vectors with quadratic order
strictly above the norm order. -/
theorem not_isNormGenerator_iff_ord_quadratic_gt
    (R : Int) (hnorm : normIdeal q L = powerIdeal (K := K) R)
    {x : V} (hx : x ∈ L) :
    ¬IsNormGenerator q L x ↔
      (R : WithTop Int) < ord K (q.quadratic x) := by
  have hlower := normOrder_le_ord_quadratic R hnorm hx
  rw [isNormGenerator_iff_ord_quadratic_eq R hnorm hx]
  constructor
  · intro hne
    exact lt_of_le_of_ne hlower (Ne.symm hne)
  · intro hlt heq
    exact hlt.ne' heq

/-- Multiplication by the selected uniformizer raises every lattice-vector
quadratic order strictly above the norm order. -/
theorem normOrder_lt_ord_quadratic_uniformizer_smul
    (R : Int) (hnorm : normIdeal q L = powerIdeal (K := K) R)
    {x : V} (hx : x ∈ L) :
    (R : WithTop Int) <
      ord K (q.quadratic (uniformizer K • x)) := by
  by_cases hzero : q.quadratic x = 0
  · rw [q.quadratic_smul, hzero, mul_zero, ord_zero]
    exact WithTop.coe_lt_top R
  · let xu : Kˣ := Units.mk0 (q.quadratic x) hzero
    have hlower := normOrder_le_ord_quadratic R hnorm hx
    have hlowerInt : R ≤ ordUnit K xu := by
      apply WithTop.coe_le_coe.mp
      simpa [xu] using hlower
    have hxOrder : ord K (q.quadratic x) =
        (ordUnit K xu : WithTop Int) := by
      simpa [xu] using (coe_ordUnit K xu).symm
    have hstrictInt : R < 2 + ordUnit K xu := by omega
    have hstrict : (R : WithTop Int) <
        ((2 + ordUnit K xu : Int) : WithTop Int) := by
      exact_mod_cast hstrictInt
    rw [q.quadratic_smul, ord_mul, ord_pow, ord_uniformizer,
      hxOrder]
    simpa using hstrict

/-- The high-norm vectors, as an integral submodule of the ambient space. -/
noncomputable def nonNormGeneratorSubmodule
    (R : Int) (hnorm : normIdeal q L = powerIdeal (K := K) R)
    (hscale : scaleIdeal q L ≤
      powerIdeal (K := K) (R - ramificationIndex K + 1)) :
    Submodule (IntegerRing K) V where
  carrier := {x | x ∈ L ∧ (R : WithTop Int) < ord K (q.quadratic x)}
  zero_mem' := by simp
  add_mem' := by
    rintro x y ⟨hxL, hx⟩ ⟨hyL, hy⟩
    refine ⟨L.add_mem hxL hyL, ?_⟩
    have hlower := normOrder_le_ord_quadratic R hnorm
      (L.add_mem hxL hyL)
    by_contra hnot
    have hupper : ord K (q.quadratic (x + y)) ≤ (R : WithTop Int) :=
      le_of_not_gt hnot
    have hsum : ord K (q.quadratic (x + y)) = (R : WithTop Int) :=
      le_antisymm hupper hlower
    rcases BONG.mixedPairing_order_eq_sub_ramificationIndex
        (q := q) x y R hx hy hsum with ⟨hne, horder⟩
    have hmem := hscale (bilin_mem_scaleIdeal_of_mem q L hxL hyL)
    rw [mem_powerIdeal_iff] at hmem
    have hpairing : ord K (q.bilin x y) =
        ((R - ramificationIndex K : Int) : WithTop Int) := by
      calc
        ord K (q.bilin x y) =
            (ordUnit K (Units.mk0 (q.bilin x y) hne) : WithTop Int) := by
          simpa using
            (coe_ordUnit K (Units.mk0 (q.bilin x y) hne)).symm
        _ = ((R - ramificationIndex K : Int) : WithTop Int) := by
          rw [horder]
    rw [hpairing] at hmem
    have hbad := WithTop.coe_le_coe.mp hmem
    omega
  smul_mem' := by
    rintro a x ⟨hxL, hx⟩
    refine ⟨L.smul_mem a hxL, ?_⟩
    by_cases ha : ((a : IntegerRing K) : K) = 0
    · have haMap : algebraMap (IntegerRing K) K a = 0 := ha
      rw [← IsScalarTower.algebraMap_smul K a x, haMap, zero_smul,
        q.quadratic_zero, ord_zero]
      exact WithTop.coe_lt_top R
    · let au : Kˣ := Units.mk0 ((a : IntegerRing K) : K) ha
      have haIntegral : 0 ≤ ordUnit K au := by
        have haField : Dyadic.IsIntegral K ((a : IntegerRing K) : K) :=
          (mem_integerRing_iff K).1 a.property
        change 0 ≤ ord K ((a : IntegerRing K) : K) at haField
        apply WithTop.coe_le_coe.mp
        simpa [au] using haField
      by_cases hxzero : q.quadratic x = 0
      · rw [← IsScalarTower.algebraMap_smul K a x,
          q.quadratic_smul, hxzero, mul_zero, ord_zero]
        exact WithTop.coe_lt_top R
      · let xu : Kˣ := Units.mk0 (q.quadratic x) hxzero
        have hxInt : R < ordUnit K xu := by
          apply WithTop.coe_lt_coe.mp
          simpa [xu] using hx
        have haOrder : ord K (algebraMap (IntegerRing K) K a) =
            (ordUnit K au : WithTop Int) := by
          simpa [au] using (coe_ordUnit K au).symm
        have hxOrder : ord K (q.quadratic x) =
            (ordUnit K xu : WithTop Int) := by
          simpa [xu] using (coe_ordUnit K xu).symm
        have hstrictInt :
            R < 2 • ordUnit K au + ordUnit K xu := by
          simp only [two_nsmul]
          omega
        have hstrict : (R : WithTop Int) <
            2 • (ordUnit K au : WithTop Int) +
              (ordUnit K xu : WithTop Int) := by
          exact_mod_cast hstrictInt
        rw [← IsScalarTower.algebraMap_smul K a x,
          q.quadratic_smul, ord_mul, ord_pow, haOrder, hxOrder]
        simpa using hstrict

@[simp]
theorem mem_nonNormGeneratorSubmodule_iff
    (R : Int) (hnorm : normIdeal q L = powerIdeal (K := K) R)
    (hscale : scaleIdeal q L ≤
      powerIdeal (K := K) (R - ramificationIndex K + 1))
    (x : V) :
    x ∈ nonNormGeneratorSubmodule R hnorm hscale ↔
      x ∈ L ∧ ¬IsNormGenerator q L x := by
  constructor
  · rintro ⟨hxL, hx⟩
    exact ⟨hxL,
      (not_isNormGenerator_iff_ord_quadratic_gt R hnorm hxL).2 hx⟩
  · rintro ⟨hxL, hx⟩
    exact ⟨hxL,
      (not_isNormGenerator_iff_ord_quadratic_gt R hnorm hxL).1 hx⟩

/-- The high-norm submodule is full, since it contains the uniformizer
multiple of every vector of `L`. -/
theorem span_nonNormGeneratorSubmodule_eq_top
    (R : Int) (hnorm : normIdeal q L = powerIdeal (K := K) R)
    (hscale : scaleIdeal q L ≤
      powerIdeal (K := K) (R - ramificationIndex K + 1)) :
    Submodule.span K
        (nonNormGeneratorSubmodule R hnorm hscale : Set V) = ⊤ := by
  apply top_unique
  rw [← L.span_eq_top]
  rw [Submodule.span_le]
  intro x hxL
  have hpiL : uniformizer K • x ∈ L := by
    have hmem := L.smul_mem (uniformizerInteger K) hxL
    have heq : (uniformizerInteger K) • x = uniformizer K • x := by
      rw [← IsScalarTower.algebraMap_smul K (uniformizerInteger K) x]
      have hscalar :
          algebraMap (IntegerRing K) K (uniformizerInteger K) =
            uniformizer K := rfl
      rw [hscalar]
    rwa [heq] at hmem
  have hpi : uniformizer K • x ∈
      nonNormGeneratorSubmodule R hnorm hscale :=
    ⟨hpiL,
      normOrder_lt_ord_quadratic_uniformizer_smul R hnorm hxL⟩
  have hspan := (Submodule.span K
    (nonNormGeneratorSubmodule R hnorm hscale : Set V)).smul_mem
      (uniformizer K)⁻¹ (Submodule.subset_span hpi)
  simpa [smul_smul, uniformizer_ne_zero K] using hspan

/-- Beli's set of non-norm-generators is a full lattice. -/
noncomputable def nonNormGeneratorLattice
    (R : Int) (hnorm : normIdeal q L = powerIdeal (K := K) R)
    (hscale : scaleIdeal q L ≤
      powerIdeal (K := K) (R - ramificationIndex K + 1)) :
    Lattice K V where
  toSubmodule := nonNormGeneratorSubmodule R hnorm hscale
  fg := L.fg.of_le (fun _ hx ↦ hx.1)
  span_eq_top := span_nonNormGeneratorSubmodule_eq_top R hnorm hscale

@[simp]
theorem mem_nonNormGeneratorLattice_iff
    (R : Int) (hnorm : normIdeal q L = powerIdeal (K := K) R)
    (hscale : scaleIdeal q L ≤
      powerIdeal (K := K) (R - ramificationIndex K + 1))
    (x : V) :
    x ∈ nonNormGeneratorLattice R hnorm hscale ↔
      x ∈ L ∧ ¬IsNormGenerator q L x :=
  mem_nonNormGeneratorSubmodule_iff R hnorm hscale x

/-- The non-norm-generator lattice is contained in the original lattice. -/
theorem nonNormGeneratorLattice_le
    (R : Int) (hnorm : normIdeal q L = powerIdeal (K := K) R)
    (hscale : scaleIdeal q L ≤
      powerIdeal (K := K) (R - ramificationIndex K + 1)) :
    nonNormGeneratorLattice R hnorm hscale ≤ L := by
  intro x hx
  exact hx.1

/-! ## The index-`p` quotient -/

variable [PerfectResidueFieldLaws K]

/-- Two norm generators differ modulo the non-norm-generator lattice by an
integral multiple of either one of them.  This is the residue-field square
root calculation in the second half of Lemma 7.1. -/
theorem exists_sub_smul_mem_nonNormGeneratorLattice_of_isNormGenerator
    (R : Int) (hnorm : normIdeal q L = powerIdeal (K := K) R)
    (hscale : scaleIdeal q L ≤
      powerIdeal (K := K) (R - ramificationIndex K + 1))
    {x y : V} (generatorX : IsNormGenerator q L x)
    (generatorY : IsNormGenerator q L y) :
    ∃ a : IntegerRing K,
      y - a • x ∈ nonNormGeneratorLattice R hnorm hscale := by
  let A := q.quadratic x
  let C := q.quadratic y
  let D := q.bilin y x
  have hAOrder : ord K A = (R : WithTop Int) := by
    exact (isNormGenerator_iff_ord_quadratic_eq
      R hnorm generatorX.mem).mp generatorX
  have hCOrder : ord K C = (R : WithTop Int) := by
    exact (isNormGenerator_iff_ord_quadratic_eq
      R hnorm generatorY.mem).mp generatorY
  have hAne : A ≠ 0 := by
    intro hzero
    rw [hzero, ord_zero] at hAOrder
    exact WithTop.top_ne_coe hAOrder
  have hCne : C ≠ 0 := by
    intro hzero
    rw [hzero, ord_zero] at hCOrder
    exact WithTop.top_ne_coe hCOrder
  let Au : Kˣ := Units.mk0 A hAne
  let Cu : Kˣ := Units.mk0 C hCne
  have hAuOrder : ordUnit K Au = R := by
    apply WithTop.coe_injective
    simpa [Au] using hAOrder
  have hCuOrder : ordUnit K Cu = R := by
    apply WithTop.coe_injective
    simpa [Cu] using hCOrder
  let ratio : Kˣ := -(Cu / Au)
  have ordUnit_neg_eq (u : Kˣ) : ordUnit K (-u) = ordUnit K u := by
    apply WithTop.coe_injective
    rw [coe_ordUnit, coe_ordUnit]
    simpa using ord_neg K (u : K)
  have hratioOrder : ordUnit K ratio = 0 := by
    change ordUnit K (-(Cu / Au)) = 0
    rw [ordUnit_neg_eq, div_eq_mul_inv, ordUnit_mul,
      ordUnit_inv, hAuOrder, hCuOrder]
    omega
  have hratioUnit : IsValuationUnit K (ratio : K) :=
    (isValuationUnit_iff_ordUnit_eq_zero K ratio).2 hratioOrder
  rcases exists_unit_squareRoot_mod_maximal K ratio hratioUnit with
    ⟨z, hzUnit, hzError⟩
  have hzIntegral : z ∈ IntegerRing K := by
    apply (mem_integerRing_iff K).2
    change 0 ≤ ord K z
    rw [hzUnit]
  let a : IntegerRing K := ⟨z, hzIntegral⟩
  refine ⟨a, ?_⟩
  have hsubL : y - a • x ∈ L :=
    L.sub_mem generatorY.mem (L.smul_mem a generatorX.mem)
  refine ⟨hsubL, ?_⟩
  have herror : IsInMaximalIdeal K (C / A + z ^ 2) := by
    simpa [ratio, Au, Cu, sub_eq_add_neg, add_comm] using hzError
  have hfactor : C + z ^ 2 * A = A * (C / A + z ^ 2) := by
    field_simp [hAne]
  have hfirst : (R : WithTop Int) < ord K (C + z ^ 2 * A) := by
    by_cases hzero : C / A + z ^ 2 = 0
    · rw [hfactor, hzero, mul_zero, ord_zero]
      exact WithTop.coe_lt_top R
    · let Eu : Kˣ := Units.mk0 (C / A + z ^ 2) hzero
      have hEOrder : ord K (C / A + z ^ 2) =
          (ordUnit K Eu : WithTop Int) := by
        simpa [Eu] using (coe_ordUnit K Eu).symm
      have hEPos : 0 < ordUnit K Eu := by
        change 0 < ord K (C / A + z ^ 2) at herror
        apply WithTop.coe_lt_coe.mp
        rw [hEOrder] at herror
        exact herror
      have hstrictInt : R < R + ordUnit K Eu := by omega
      have hstrict : (R : WithTop Int) <
          ((R + ordUnit K Eu : Int) : WithTop Int) := by
        exact_mod_cast hstrictInt
      rw [hfactor, ord_mul, hAOrder, hEOrder]
      simpa using hstrict
  have hDmem := hscale
    (bilin_mem_scaleIdeal_of_mem q L generatorY.mem generatorX.mem)
  rw [mem_powerIdeal_iff] at hDmem
  have hcross : (R : WithTop Int) < ord K ((2 : K) * z * D) := by
    by_cases hzero : D = 0
    · rw [hzero, mul_zero, ord_zero]
      exact WithTop.coe_lt_top R
    · let Du : Kˣ := Units.mk0 D hzero
      have hDOrder : ord K D = (ordUnit K Du : WithTop Int) := by
        simpa [Du] using (coe_ordUnit K Du).symm
      have hDLower : R - ramificationIndex K + 1 ≤ ordUnit K Du := by
        change ((R - ramificationIndex K + 1 : Int) : WithTop Int) ≤
          ord K D at hDmem
        apply WithTop.coe_le_coe.mp
        rw [hDOrder] at hDmem
        exact hDmem
      have hstrictInt :
          R < (ramificationIndex K : Int) + 0 + ordUnit K Du := by
        omega
      have hstrict : (R : WithTop Int) <
          (((ramificationIndex K : Int) + 0 + ordUnit K Du : Int) :
            WithTop Int) := by
        exact_mod_cast hstrictInt
      rw [ord_mul, ord_mul, ← ramificationIndex_spec, hzUnit, hDOrder]
      simpa using hstrict
  have hvector : y - a • x = y - z • x := by
    rfl
  have hquadratic : q.quadratic (y - z • x) =
      (C + z ^ 2 * A) - (2 : K) * z * D := by
    dsimp [A, C, D]
    rw [sub_eq_add_neg, q.quadratic_add, q.quadratic_neg,
      q.quadratic_smul, LinearMap.BilinForm.neg_right,
      LinearMap.BilinForm.smul_right]
    ring
  rw [hvector, hquadratic, sub_eq_add_neg]
  have hcrossNeg :
      (R : WithTop Int) < ord K (-((2 : K) * z * D)) := by
    simpa using hcross
  exact (lt_min hfirst hcrossNeg).trans_le
    (min_ord_le_ord_add K (C + z ^ 2 * A) (-((2 : K) * z * D)))

/-- Every vector of `L` has a representative on the norm-generator line
modulo the non-norm-generator lattice. -/
theorem exists_sub_smul_mem_nonNormGeneratorLattice
    (R : Int) (hnorm : normIdeal q L = powerIdeal (K := K) R)
    (hscale : scaleIdeal q L ≤
      powerIdeal (K := K) (R - ramificationIndex K + 1))
    {x : V} (generator : IsNormGenerator q L x)
    {y : V} (hy : y ∈ L) :
    ∃ a : IntegerRing K,
      y - a • x ∈ nonNormGeneratorLattice R hnorm hscale := by
  by_cases hyGenerator : IsNormGenerator q L y
  · exact exists_sub_smul_mem_nonNormGeneratorLattice_of_isNormGenerator
      R hnorm hscale generator hyGenerator
  · refine ⟨0, ?_⟩
    simpa using
      (show y ∈ nonNormGeneratorLattice R hnorm hscale from
        (mem_nonNormGeneratorLattice_iff R hnorm hscale y).2
          ⟨hy, hyGenerator⟩)

/-- An inspectable algebraic certificate for the assertion `[L : N] = p`:
`x` is a nonzero residue direction, its uniformizer multiple lies in `N`,
and every vector of `L` is congruent modulo `N` to an integral multiple of
`x`. -/
structure IndexPGeneratorCertificate
    (N L : Lattice K V) (x : V) : Prop where
  generator_mem : x ∈ L
  lattice_le : N ≤ L
  generator_not_mem : x ∉ N
  uniformizer_smul_mem : (uniformizerInteger K) • x ∈ N
  reduce (y : V) : y ∈ L → ∃ a : IntegerRing K, y - a • x ∈ N

/-- Lemma 7.1 supplies an explicit index-`p` generator certificate. -/
theorem nonNormGeneratorLattice_indexPCertificate
    (R : Int) (hnorm : normIdeal q L = powerIdeal (K := K) R)
    (hscale : scaleIdeal q L ≤
      powerIdeal (K := K) (R - ramificationIndex K + 1))
    {x : V} (generator : IsNormGenerator q L x) :
    IndexPGeneratorCertificate
      (nonNormGeneratorLattice R hnorm hscale) L x where
  generator_mem := generator.mem
  lattice_le := nonNormGeneratorLattice_le R hnorm hscale
  generator_not_mem := by
    intro hx
    exact ((mem_nonNormGeneratorLattice_iff R hnorm hscale x).1 hx).2
      generator
  uniformizer_smul_mem := by
    refine ⟨L.smul_mem (uniformizerInteger K) generator.mem, ?_⟩
    have hfield := normOrder_lt_ord_quadratic_uniformizer_smul
      R hnorm generator.mem
    have heq : (uniformizerInteger K) • x = uniformizer K • x := by
      rw [← IsScalarTower.algebraMap_smul K (uniformizerInteger K) x]
      rfl
    rwa [heq]
  reduce y hy :=
    exists_sub_smul_mem_nonNormGeneratorLattice
      R hnorm hscale generator hy

end Lattice

namespace BONG.GoodBONG

variable [BeliCorollary44Laws.{u, v} K]

/-- For a good BONG of rank at least two, the nonexceptional first gap is
equivalent to the strict scale bound used to construct the lattice in
Lemma 7.1. -/
theorem strictScaleBound_iff_firstGap_gt_negTwoE
    {n : Nat} (b : GoodBONG q L (n + 2)) :
    Lattice.scaleIdeal q L ≤
        Lattice.powerIdeal (K := K)
          (b.order 0 - ramificationIndex K + 1) ↔
      -(2 * (ramificationIndex K : Int)) <
        b.order 1 - b.order 0 := by
  rcases b.toBONG.beliCorollary44_iv_unconditional b.good with
    ⟨s, hscale, hs⟩
  change 2 * ordUnit K s =
    min (2 * b.order 0) (b.order 0 + b.order 1) at hs
  have hePos : 0 < (ramificationIndex K : Int) := by
    exact_mod_cast ramificationIndex_pos K
  constructor
  · intro hstrict
    have hpower : Lattice.powerIdeal (K := K) (ordUnit K s) ≤
        Lattice.powerIdeal (K := K)
          (b.order 0 - ramificationIndex K + 1) := by
      rw [← Lattice.principalIdeal_eq_powerIdeal s, ← hscale]
      exact hstrict
    have hsLower :
        b.order 0 - ramificationIndex K + 1 ≤ ordUnit K s :=
      (Lattice.powerIdeal_le_iff (K := K) _ _).mp hpower
    have hdouble :
        2 * (b.order 0 - ramificationIndex K) < 2 * ordUnit K s := by
      omega
    rw [hs] at hdouble
    have hsecond :
        2 * (b.order 0 - ramificationIndex K) <
          b.order 0 + b.order 1 :=
      hdouble.trans_le (min_le_right _ _)
    omega
  · intro hgap
    have hfirst :
        2 * (b.order 0 - ramificationIndex K) < 2 * b.order 0 := by
      omega
    have hsecond :
        2 * (b.order 0 - ramificationIndex K) <
          b.order 0 + b.order 1 := by
      omega
    have hminimum :
        2 * (b.order 0 - ramificationIndex K) <
          min (2 * b.order 0) (b.order 0 + b.order 1) :=
      lt_min hfirst hsecond
    rw [← hs] at hminimum
    have hsLower :
        b.order 0 - ramificationIndex K + 1 ≤ ordUnit K s := by
      omega
    calc
      Lattice.scaleIdeal q L =
          Lattice.principalIdeal (K := K) (s : K) := hscale
      _ = Lattice.powerIdeal (K := K) (ordUnit K s) :=
        Lattice.principalIdeal_eq_powerIdeal s
      _ ≤ Lattice.powerIdeal (K := K)
          (b.order 0 - ramificationIndex K + 1) :=
        (Lattice.powerIdeal_le_iff (K := K) _ _).2 hsLower

/-- The hypothesis as printed in Lemma 7.1 implies the strict scale bound,
using the universal lower bound `R₂-R₁ ≥ -2e` for BONGs. -/
theorem strictScaleBound_of_firstGap_ne_negTwoE
    {n : Nat} (b : GoodBONG q L (n + 2))
    (hgap : b.order 1 - b.order 0 ≠
      -(2 * (ramificationIndex K : Int))) :
    Lattice.scaleIdeal q L ≤
      Lattice.powerIdeal (K := K)
        (b.order 0 - ramificationIndex K + 1) := by
  apply (b.strictScaleBound_iff_firstGap_gt_negTwoE).2
  let i0 : Fin (n + 2) := ⟨0, by omega⟩
  have hi0 : i0.val + 1 < n + 2 := by
    simp [i0]
  have hlower := b.toBONG.adjacentOrderGap_ge_neg_two_mul_e
    i0 hi0
  change -(2 * (ramificationIndex K : Int)) ≤
    b.order ⟨i0.val + 1, hi0⟩ - b.order i0 at hlower
  have hi0Eq : i0 = (0 : Fin (n + 2)) := by
    apply Fin.ext
    simp [i0]
  have hi1Eq : (⟨i0.val + 1, hi0⟩ : Fin (n + 2)) = 1 := by
    apply Fin.ext
    simp [i0]
  have hlower' : -(2 * (ramificationIndex K : Int)) ≤
      b.order 1 - b.order 0 := by
    calc
      -(2 * (ramificationIndex K : Int)) ≤
          b.order ⟨i0.val + 1, hi0⟩ - b.order i0 := hlower
      _ = b.order 1 - b.order 0 := by rw [hi1Eq, hi0Eq]
  exact lt_of_le_of_ne hlower' (Ne.symm hgap)

/-- The concrete output of Beli (2019), Lemma 7.1 for a chosen good BONG. -/
structure Beli2019Lemma71Data
    {n : Nat} (b : GoodBONG q L (n + 2)) where
  gap_ne : b.order 1 - b.order 0 ≠
    -(2 * (ramificationIndex K : Int))
  lattice : Lattice K V
  lattice_eq : lattice = Lattice.nonNormGeneratorLattice
    (b.order 0) b.toBONG.normIdeal_eq_powerIdeal_order_zero
      (b.strictScaleBound_of_firstGap_ne_negTwoE gap_ne)
  head_not_mem : b.toBONG.head ∉ lattice
  indexP : Lattice.IndexPGeneratorCertificate lattice L b.toBONG.head

/-- Lemma 7.1 constructs the non-norm-generator lattice and its
index-`p` certificate from the printed first-gap hypothesis. -/
noncomputable def beli2019Lemma71
    [PerfectResidueFieldLaws K]
    {n : Nat} (b : GoodBONG q L (n + 2))
    (hgap : b.order 1 - b.order 0 ≠
      -(2 * (ramificationIndex K : Int))) :
    Beli2019Lemma71Data b where
  gap_ne := hgap
  lattice := Lattice.nonNormGeneratorLattice
    (b.order 0) b.toBONG.normIdeal_eq_powerIdeal_order_zero
      (b.strictScaleBound_of_firstGap_ne_negTwoE hgap)
  lattice_eq := rfl
  head_not_mem := by
    rw [Lattice.mem_nonNormGeneratorLattice_iff]
    exact fun h ↦ h.2 b.toBONG.head_isNormGenerator
  indexP := Lattice.nonNormGeneratorLattice_indexPCertificate
    (b.order 0) b.toBONG.normIdeal_eq_powerIdeal_order_zero
      (b.strictScaleBound_of_firstGap_ne_negTwoE hgap)
      b.toBONG.head_isNormGenerator

end BONG.GoodBONG

end Bong
