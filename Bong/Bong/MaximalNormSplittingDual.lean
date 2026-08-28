/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryDualModular
import Bong.Bong.BeliLemma41
import Bong.Bong.BeliLemma43
import Bong.Bong.GoodExistence
import Bong.Lattice.OrthogonalDecompositionDual

/-!
# Reverse duals of maximal norm splittings

This file lifts the unconditional unary and binary reverse-dual BONGs to the
components of a maximal norm splitting.  Components are dualized and their
order is reversed, exactly as in Beli (2003), Lemma 4.8.
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {t : Nat}

namespace BONG

/-- Transporting the length index commutes with normalized reverse-dual
vectors. -/
@[simp]
theorem reverseDualVector_castLength {m n : Nat}
    (b : BONG V q L m) (h : m = n) (i : Fin n) :
    (b.castLength h).reverseDualVector i =
      b.reverseDualVector ⟨i.1, by omega⟩ := by
  subst n
  rfl

/-- Casting the length index does not change BONG values. -/
@[simp]
theorem value_castLength {m n : Nat}
    (b : BONG V q L m) (h : m = n) (i : Fin n) :
    (b.castLength h).value i = b.value ⟨i.1, by omega⟩ := by
  subst n
  rfl

/-- Casting the length index does not change BONG orders. -/
@[simp]
theorem order_castLength {m n : Nat}
    (b : BONG V q L m) (h : m = n) (i : Fin n) :
    (b.castLength h).order i = b.order ⟨i.1, by omega⟩ := by
  subst n
  rfl

/-- In every nonempty BONG, the first ambient vector is the norm generator
chosen at the first recursive step. -/
theorem ambientVector_first_isNormGenerator {m : Nat}
    (b : BONG V q L m) (h : 0 < m) :
    Lattice.IsNormGenerator q L (b.ambientVector ⟨0, h⟩) := by
  cases b with
  | nil => omega
  | cons x generator anisotropic tail =>
      simpa using generator

end BONG

namespace Lattice.MaximalNormSplitting

open Lattice.OrthogonalDecomposition

variable (M : Lattice.MaximalNormSplitting q L t)
  (c : M.toOrthogonalDecomposition.ComponentBONGFamily)

/-- The first local coordinate of a nonzero maximal-norm component. -/
noncomputable def componentFirstIndex (i : Fin t) :
    Fin (M.toOrthogonalDecomposition.componentRank i) :=
  ⟨0, M.componentRank_pos i⟩

/-- The first vector selected by a component BONG generates the component
norm ideal. -/
theorem componentFirst_isNormGenerator (i : Fin t) :
    Lattice.IsNormGenerator
      (M.toOrthogonalDecomposition.component i).space
      (M.toOrthogonalDecomposition.component i).lattice
      ((c i).ambientVector (M.componentFirstIndex i)) :=
  (c i).ambientVector_first_isNormGenerator (M.componentRank_pos i)

private theorem ordUnit_eq_of_principalIdeal_eq (a b : Kˣ)
    (h : Lattice.principalIdeal (K := K) (a : K) =
      Lattice.principalIdeal (K := K) (b : K)) :
    ordUnit K a = ordUnit K b := by
  have hab : ord K (a : K) ≤ ord K (b : K) :=
    (Lattice.principalIdeal_le_iff_ord_ge
      (Units.ne_zero b) (Units.ne_zero a)).1 h.ge
  have hba : ord K (b : K) ≤ ord K (a : K) :=
    (Lattice.principalIdeal_le_iff_ord_ge
      (Units.ne_zero a) (Units.ne_zero b)).1 h.le
  apply WithTop.coe_injective
  rw [coe_ordUnit, coe_ordUnit]
  exact le_antisymm hab hba

/-- The first component BONG order is the chosen component norm order. -/
theorem componentFirst_order_eq_normGeneratorOrder (i : Fin t) :
    (c i).order (M.componentFirstIndex i) =
      ordUnit K (M.normGenerator i) := by
  rw [BONG.order_eq_ordUnit]
  apply ordUnit_eq_of_principalIdeal_eq
  calc
    Lattice.principalIdeal (K := K)
        ((c i).valueUnit (M.componentFirstIndex i) : K) =
        Lattice.principalIdeal (K := K)
          ((M.toOrthogonalDecomposition.component i).space.quadratic
            ((c i).ambientVector (M.componentFirstIndex i))) := by
      rw [(c i).quadratic_ambientVector]
      rfl
    _ = Lattice.normIdeal
          (M.toOrthogonalDecomposition.component i).space
          (M.toOrthogonalDecomposition.component i).lattice :=
      (M.componentFirst_isNormGenerator c i).normIdeal_eq.symm
    _ = Lattice.principalIdeal (K := K) (M.normGenerator i : K) :=
      M.normIdeal_eq i

section ComponentModular

include c

/-- Every component of a maximal norm splitting is modular at its selected
scale.  The binary case is part of the definition; in the unary case the
single BONG value generates the scale ideal. -/
theorem component_isModular (i : Fin t) :
    Lattice.IsModular
      (M.toOrthogonalDecomposition.component i).space
      (M.toOrthogonalDecomposition.component i).lattice
      (M.scaleGenerator i) := by
  rcases M.unary_or_modular_binary i with h₁ | h₂
  · let b₁ := (c i).castLength h₁
    have hL : (M.toOrthogonalDecomposition.component i).lattice =
        Lattice.basisLattice b₁.basis :=
      b₁.lattice_eq_basisLattice
    have hrange : Set.range b₁.value = {b₁.value 0} := by
      ext x
      constructor
      · rintro ⟨j, rfl⟩
        have hj : j = 0 := Subsingleton.elim j 0
        subst j
        simp
      · intro hx
        rw [Set.mem_singleton_iff] at hx
        exact ⟨0, hx.symm⟩
    have hideal :
        Lattice.principalIdeal (K := K) (b₁.valueUnit 0 : K) =
          Lattice.principalIdeal (K := K) (M.scaleGenerator i : K) := by
      calc
        Lattice.principalIdeal (K := K) (b₁.valueUnit 0 : K) =
            Submodule.span (IntegerRing K) (Set.range b₁.value) := by
          rw [hrange]
          rfl
        _ = Lattice.scaleIdeal
            (M.toOrthogonalDecomposition.component i).space
            (Lattice.basisLattice b₁.basis) :=
          b₁.scaleIdeal_basisLattice.symm
        _ = Lattice.scaleIdeal
            (M.toOrthogonalDecomposition.component i).space
            (M.toOrthogonalDecomposition.component i).lattice := by
          exact congrArg
            (Lattice.scaleIdeal
              (M.toOrthogonalDecomposition.component i).space) hL.symm
        _ = Lattice.principalIdeal (K := K) (M.scaleGenerator i : K) :=
          M.scaleIdeal_eq i
    have horderZero : b₁.order 0 = ordUnit K (M.scaleGenerator i) := by
      rw [BONG.order_eq_ordUnit]
      exact ordUnit_eq_of_principalIdeal_eq _ _ hideal
    have hne : ∀ j : Fin 1,
        (M.toOrthogonalDecomposition.component i).space.quadratic
          (b₁.basis j) ≠ 0 := by
      intro j
      change (M.toOrthogonalDecomposition.component i).space.quadratic
        (b₁.ambientVector j) ≠ 0
      rw [b₁.quadratic_ambientVector]
      exact b₁.value_ne_zero j
    have horders : ∀ j : Fin 1,
        ordUnit K (Units.mk0
          ((M.toOrthogonalDecomposition.component i).space.quadratic
            (b₁.basis j)) (hne j)) =
          ordUnit K (M.scaleGenerator i) := by
      intro j
      have hj : j = 0 := Subsingleton.elim j 0
      subst j
      have hunit : Units.mk0
          ((M.toOrthogonalDecomposition.component i).space.quadratic
            (b₁.basis 0)) (hne 0) = b₁.valueUnit 0 := by
        apply Units.ext
        exact b₁.quadratic_ambientVector 0
      rw [hunit]
      simpa only [BONG.order_eq_ordUnit] using horderZero
    have hmodBasis : Lattice.IsModular
        (M.toOrthogonalDecomposition.component i).space
        (Lattice.basisLattice b₁.basis) (M.scaleGenerator i) :=
      Lattice.isModular_basisLattice_of_iIsOrtho_of_orders_eq
        (M.toOrthogonalDecomposition.component i).space b₁.basis
        b₁.ambientVector_iIsOrtho hne (M.scaleGenerator i) horders
    exact (congrArg
      (fun N => Lattice.IsModular
        (M.toOrthogonalDecomposition.component i).space N
          (M.scaleGenerator i)) hL).mpr hmodBasis
  · exact h₂.2

end ComponentModular

/-- The reversed component has the rank of the corresponding original
component.  We name this definitional equality because making it explicit
keeps all subsequent dependent index transports stable. -/
@[simp]
theorem reverseDual_componentRank_eq (i : Fin t) :
    M.toOrthogonalDecomposition.reverseDual.componentRank i =
      M.toOrthogonalDecomposition.componentRank (Fin.rev i) :=
  rfl

/-- Reverse-dualize the component corresponding to `i`, retaining the
original component rank as the explicit length index. -/
noncomputable def reverseDualComponentBONG (i : Fin t) :
    BONG
      (M.toOrthogonalDecomposition.reverseDual.component i).carrier
      (M.toOrthogonalDecomposition.reverseDual.component i).space
      (M.toOrthogonalDecomposition.reverseDual.component i).lattice
      (M.toOrthogonalDecomposition.componentRank (Fin.rev i)) := by
  let k : Fin t := Fin.rev i
  by_cases h₁ : M.toOrthogonalDecomposition.componentRank k = 1
  · let b₁ := (c k).castLength h₁
    exact b₁.reverseDualUnary.castLength h₁.symm
  · have h₂ : M.toOrthogonalDecomposition.componentRank k = 2 := by
      change M.componentRank k = 2
      exact (M.componentRank_eq_one_or_two k).resolve_left h₁
    let b₂ := (c k).castLength h₂
    exact b₂.reverseDualBinaryGood.toBONG.castLength h₂.symm

/-- The rank-stable component construction has exactly the reversed normalized
dual vectors of the corresponding original component. -/
@[simp]
theorem ambientVector_reverseDualComponentBONG
    (i : Fin t)
    (j : Fin
      (M.toOrthogonalDecomposition.componentRank (Fin.rev i))) :
    (M.reverseDualComponentBONG c i).ambientVector j =
      (c (Fin.rev i)).reverseDualVector j := by
  unfold reverseDualComponentBONG
  dsimp only
  split
  · next h₁ =>
      let j₁ : Fin 1 := ⟨j.1, by omega⟩
      calc
        (((c (Fin.rev i)).castLength h₁).reverseDualUnary.castLength
            h₁.symm).ambientVector j =
            ((c (Fin.rev i)).castLength h₁).reverseDualUnary.ambientVector j₁ := by
          simpa [j₁] using BONG.ambientVector_castLength
            ((c (Fin.rev i)).castLength h₁).reverseDualUnary h₁.symm j
        _ = ((c (Fin.rev i)).castLength h₁).reverseDualVector j₁ :=
          ((c (Fin.rev i)).castLength h₁).ambientVector_reverseDualUnary j₁
        _ = (c (Fin.rev i)).reverseDualVector j := by
          simpa [j₁] using BONG.reverseDualVector_castLength
            (c (Fin.rev i)) h₁ j₁
  · next h₁ =>
      have h₂ : M.toOrthogonalDecomposition.componentRank (Fin.rev i) = 2 := by
        change M.componentRank (Fin.rev i) = 2
        exact (M.componentRank_eq_one_or_two (Fin.rev i)).resolve_left h₁
      let j₂ : Fin 2 := ⟨j.1, by omega⟩
      calc
        (((c (Fin.rev i)).castLength h₂).reverseDualBinaryGood.toBONG.castLength
            h₂.symm).ambientVector j =
            ((c (Fin.rev i)).castLength h₂).reverseDualBinaryGood.toBONG.ambientVector j₂ := by
          simpa [j₂] using BONG.ambientVector_castLength
            ((c (Fin.rev i)).castLength h₂).reverseDualBinaryGood.toBONG h₂.symm j
        _ = ((c (Fin.rev i)).castLength h₂).reverseDualVector j₂ :=
          ((c (Fin.rev i)).castLength h₂).ambientVector_reverseDualBinaryGood j₂
        _ = (c (Fin.rev i)).reverseDualVector j := by
          simpa [j₂] using BONG.reverseDualVector_castLength
            (c (Fin.rev i)) h₂ j₂

/-- Reverse-dualize each unary or binary component and reverse the component
index. -/
noncomputable def reverseDualComponentBONGFamily :
    M.toOrthogonalDecomposition.reverseDual.ComponentBONGFamily :=
  fun i => (M.reverseDualComponentBONG c i).castLength
    (M.reverseDual_componentRank_eq i).symm

/-- Each constructed component BONG has the reversed normalized dual vectors
of the corresponding original component. -/
@[simp]
theorem ambientVector_reverseDualComponentBONGFamily
    (i : Fin t)
    (j : Fin (M.toOrthogonalDecomposition.reverseDual.componentRank i)) :
    (M.reverseDualComponentBONGFamily c i).ambientVector j =
      (c (Fin.rev i)).reverseDualVector
        (Fin.cast (M.reverseDual_componentRank_eq i) j) := by
  rw [reverseDualComponentBONGFamily, BONG.ambientVector_castLength,
    M.ambientVector_reverseDualComponentBONG c]
  apply congrArg
  apply Fin.ext
  rfl

/-- Component orders are reversed and negated by the componentwise dual
construction. -/
@[simp]
theorem order_reverseDualComponentBONGFamily
    (i : Fin t)
    (j : Fin (M.toOrthogonalDecomposition.reverseDual.componentRank i)) :
    (M.reverseDualComponentBONGFamily c i).order j =
      -(c (Fin.rev i)).order
        (Fin.rev (Fin.cast (M.reverseDual_componentRank_eq i) j)) := by
  apply WithTop.coe_injective
  rw [BONG.coe_order]
  calc
    ord K ((M.reverseDualComponentBONGFamily c i).value j) =
        ord K (q.restrict
          (M.toOrthogonalDecomposition.reverseDual.component i).carrier
          (M.toOrthogonalDecomposition.reverseDual.component i).nondegenerate
          |>.quadratic
            ((M.reverseDualComponentBONGFamily c i).ambientVector j)) := by
      exact congrArg (ord K)
        ((M.reverseDualComponentBONGFamily c i).quadratic_ambientVector j).symm
    _ = ord K ((M.toOrthogonalDecomposition.component (Fin.rev i)).space.quadratic
          ((c (Fin.rev i)).reverseDualVector
            (Fin.cast (M.reverseDual_componentRank_eq i) j))) := by
      rw [M.ambientVector_reverseDualComponentBONGFamily c i j]
      rfl
    _ = ((-(c (Fin.rev i)).order
          (Fin.rev (Fin.cast (M.reverseDual_componentRank_eq i) j)) : Int) :
          WithTop Int) :=
      (c (Fin.rev i)).ord_quadratic_reverseDualVector
        (Fin.cast (M.reverseDual_componentRank_eq i) j)

/-- The scale of a reversed dual component is the inverse of the original
scale at the reversed component index. -/
noncomputable def reverseDualScaleGenerator (i : Fin t) : Kˣ :=
  (M.scaleGenerator (Fin.rev i))⁻¹

/-- A norm generator value for a reversed dual component.  It is the value
of the original first norm generator after scaling its vector by the inverse
component scale. -/
noncomputable def reverseDualNormGenerator (i : Fin t) : Kˣ :=
  (M.scaleGenerator (Fin.rev i))⁻¹ ^ 2 *
    (c (Fin.rev i)).valueUnit (M.componentFirstIndex (Fin.rev i))

@[simp]
theorem ordUnit_reverseDualScaleGenerator (i : Fin t) :
    ordUnit K (M.reverseDualScaleGenerator i) =
      -ordUnit K (M.scaleGenerator (Fin.rev i)) := by
  rw [reverseDualScaleGenerator, ordUnit_inv]

@[simp]
theorem ordUnit_reverseDualNormGenerator (i : Fin t) :
    ordUnit K (M.reverseDualNormGenerator c i) =
      ordUnit K (M.normGenerator (Fin.rev i)) -
        2 * ordUnit K (M.scaleGenerator (Fin.rev i)) := by
  rw [reverseDualNormGenerator, ordUnit_mul, ordUnit_pow, ordUnit_inv,
    ← BONG.order_eq_ordUnit,
    M.componentFirst_order_eq_normGeneratorOrder c]
  ring

section ReverseDualModular

include c

/-- Each reversed component is modular at the inverse original scale. -/
theorem reverseDualComponent_isModular (i : Fin t) :
    Lattice.IsModular
      (M.toOrthogonalDecomposition.reverseDual.component i).space
      (M.toOrthogonalDecomposition.reverseDual.component i).lattice
      (M.reverseDualScaleGenerator i) := by
  change Lattice.IsModular
    (M.toOrthogonalDecomposition.component (Fin.rev i)).space
    (Lattice.dualLattice
      (M.toOrthogonalDecomposition.component (Fin.rev i)).space
      (M.toOrthogonalDecomposition.component (Fin.rev i)).lattice)
    (M.scaleGenerator (Fin.rev i))⁻¹
  exact (M.component_isModular c (Fin.rev i)).dual

/-- The selected inverse scale generates the reversed component scale ideal. -/
theorem reverseDual_scaleIdeal_eq (i : Fin t) :
    Lattice.scaleIdeal
      (M.toOrthogonalDecomposition.reverseDual.component i).space
      (M.toOrthogonalDecomposition.reverseDual.component i).lattice =
      Lattice.principalIdeal (K := K)
        (M.reverseDualScaleGenerator i : K) := by
  apply (M.reverseDualComponent_isModular c i).scaleIdeal_eq_principal
  change 0 < M.componentRank (Fin.rev i)
  exact M.componentRank_pos (Fin.rev i)

/-- The selected scaled first value generates the reversed component norm
ideal. -/
theorem reverseDual_normIdeal_eq (i : Fin t) :
    Lattice.normIdeal
      (M.toOrthogonalDecomposition.reverseDual.component i).space
      (M.toOrthogonalDecomposition.reverseDual.component i).lattice =
      Lattice.principalIdeal (K := K)
        (M.reverseDualNormGenerator c i : K) := by
  let k : Fin t := Fin.rev i
  have hgenerator := (M.component_isModular c k).normGenerator_dual
    (M.componentFirst_isNormGenerator c k)
  change Lattice.normIdeal
      (M.toOrthogonalDecomposition.component k).space
      (Lattice.dualLattice
        (M.toOrthogonalDecomposition.component k).space
        (M.toOrthogonalDecomposition.component k).lattice) =
    Lattice.principalIdeal (K := K)
      (((M.scaleGenerator k)⁻¹ ^ 2 *
        (c k).valueUnit (M.componentFirstIndex k) : Kˣ) : K)
  calc
    _ = Lattice.principalIdeal (K := K)
        ((M.toOrthogonalDecomposition.component k).space.quadratic
          (((M.scaleGenerator k)⁻¹ : Kˣ) •
            (c k).ambientVector (M.componentFirstIndex k))) :=
      hgenerator.normIdeal_eq
    _ = _ := by
      congr 1
      rw [Units.smul_def, QuadraticSpace.quadratic_smul,
        (c k).quadratic_ambientVector]
      rfl

/-- Reversed components are again unary or modular binary. -/
theorem reverseDual_unary_or_modular_binary (i : Fin t) :
    finrank K
        (M.toOrthogonalDecomposition.reverseDual.component i).carrier = 1 ∨
      (finrank K
          (M.toOrthogonalDecomposition.reverseDual.component i).carrier = 2 ∧
        Lattice.IsModular
          (M.toOrthogonalDecomposition.reverseDual.component i).space
          (M.toOrthogonalDecomposition.reverseDual.component i).lattice
          (M.reverseDualScaleGenerator i)) := by
  rcases M.unary_or_modular_binary (Fin.rev i) with h₁ | h₂
  · exact Or.inl h₁
  · exact Or.inr ⟨h₂.1, M.reverseDualComponent_isModular c i⟩

end ReverseDualModular

/-- Reversing the components and inverting their scales preserves the
nondecreasing scale-order condition. -/
theorem reverseDual_scaleOrder_mono {i j : Fin t} (hij : i < j) :
    ordUnit K (M.reverseDualScaleGenerator i) ≤
      ordUnit K (M.reverseDualScaleGenerator j) := by
  have hrev : Fin.rev j < Fin.rev i := Fin.rev_lt_rev.mpr hij
  have hsource := M.scaleOrder_mono hrev
  rw [M.ordUnit_reverseDualScaleGenerator,
    M.ordUnit_reverseDualScaleGenerator]
  omega

/-- Beli's norm-gap inequalities are invariant under the affine order
transformation `u ↦ u - 2r` and reversal of component order. -/
theorem reverseDual_normGap_bounds {i j : Fin t} (hij : i < j) :
    0 ≤ ordUnit K (M.reverseDualNormGenerator c j) -
        ordUnit K (M.reverseDualNormGenerator c i) ∧
      ordUnit K (M.reverseDualNormGenerator c j) -
          ordUnit K (M.reverseDualNormGenerator c i) ≤
        2 * (ordUnit K (M.reverseDualScaleGenerator j) -
          ordUnit K (M.reverseDualScaleGenerator i)) := by
  have hrev : Fin.rev j < Fin.rev i := Fin.rev_lt_rev.mpr hij
  have hsource := M.normGap_bounds hrev
  rw [M.ordUnit_reverseDualNormGenerator c,
    M.ordUnit_reverseDualNormGenerator c,
    M.ordUnit_reverseDualScaleGenerator,
    M.ordUnit_reverseDualScaleGenerator]
  omega

/-- The reversed componentwise dual is itself a maximal norm splitting of
the integral dual lattice. -/
noncomputable def reverseDual :
    Lattice.MaximalNormSplitting q (Lattice.dualLattice q L) t where
  toOrthogonalDecomposition := M.toOrthogonalDecomposition.reverseDual
  scaleGenerator := M.reverseDualScaleGenerator
  normGenerator := M.reverseDualNormGenerator c
  scaleIdeal_eq := M.reverseDual_scaleIdeal_eq c
  normIdeal_eq := M.reverseDual_normIdeal_eq c
  unary_or_modular_binary := M.reverseDual_unary_or_modular_binary c
  scaleOrder_mono := M.reverseDual_scaleOrder_mono
  normGap_bounds := M.reverseDual_normGap_bounds c

@[simp]
theorem reverseDual_toOrthogonalDecomposition :
    (M.reverseDual c).toOrthogonalDecomposition =
      M.toOrthogonalDecomposition.reverseDual :=
  rfl

@[simp]
theorem reverseDual_scaleGenerator (i : Fin t) :
    (M.reverseDual c).scaleGenerator i =
      (M.scaleGenerator (Fin.rev i))⁻¹ :=
  rfl

@[simp]
theorem reverseDual_normGenerator (i : Fin t) :
    (M.reverseDual c).normGenerator i =
      (M.scaleGenerator (Fin.rev i))⁻¹ ^ 2 *
        (c (Fin.rev i)).valueUnit (M.componentFirstIndex (Fin.rev i)) :=
  rfl

/-- Reverse both the component index and the local index of a dependent
component coordinate. -/
noncomputable def reverseDualComponentIndex
    (a : Σ i : Fin t,
      Fin (M.toOrthogonalDecomposition.reverseDual.componentRank i)) :
    Σ i : Fin t, Fin (M.toOrthogonalDecomposition.componentRank i) :=
  ⟨Fin.rev a.1,
    Fin.rev (Fin.cast (M.reverseDual_componentRank_eq a.1) a.2)⟩

/-- Reversing both levels of a lexicographic component coordinate reverses
the component-index order. -/
theorem componentIndexBefore_reverseDualComponentIndex
    (a b : Σ i : Fin t,
      Fin (M.toOrthogonalDecomposition.reverseDual.componentRank i))
    (hab : BONG.ComponentIndexBefore
      M.toOrthogonalDecomposition.reverseDual a b) :
    BONG.ComponentIndexBefore M.toOrthogonalDecomposition
      (M.reverseDualComponentIndex b)
      (M.reverseDualComponentIndex a) := by
  rcases a with ⟨ia, ja⟩
  rcases b with ⟨ib, jb⟩
  unfold BONG.ComponentIndexBefore at hab ⊢
  rcases hab with hab | ⟨hi, hj⟩
  · exact Or.inl (Fin.rev_lt_rev.mpr hab)
  · change ia = ib at hi
    subst ib
    unfold reverseDualComponentIndex
    refine Or.inr ⟨rfl, ?_⟩
    apply Fin.rev_lt_rev.mpr
    change ja.1 < jb.1
    exact hj

theorem strictMono_fin_eq_self {m : Nat} (f : Fin m → Fin m)
    (hf : StrictMono f) (i : Fin m) : f i = i := by
  have hcard : (Finset.univ : Finset (Fin m)).card = m := by simp
  have hfun := Finset.orderEmbOfFin_unique hcard
    (f := f) (fun x => Finset.mem_univ (f x)) hf
  have hid := Finset.orderEmbOfFin_unique hcard
    (f := fun x : Fin m => x) (fun x => Finset.mem_univ x)
      Fin.val_strictMono
  exact (congrFun hfun i).trans (congrFun hid i).symm

/-- A strictly decreasing endomap of `Fin m` is necessarily `Fin.rev`. -/
theorem strictAnti_fin_eq_rev {m : Nat} (f : Fin m → Fin m)
    (hf : StrictAnti f) (i : Fin m) : f i = Fin.rev i := by
  have hg : StrictMono (fun j => Fin.rev (f j)) := by
    intro a b hab
    exact Fin.rev_lt_rev.mpr (hf hab)
  have hi := strictMono_fin_eq_self (fun j => Fin.rev (f j)) hg i
  have hirev := congrArg Fin.rev hi
  simpa using hirev

end Lattice.MaximalNormSplitting

namespace BONG.PutTogetherWitness

open Lattice.OrthogonalDecomposition

variable {n : Nat} {b : BONG V q L n}
  {D : Lattice.OrthogonalDecomposition q L t}
  {c : D.ComponentBONGFamily}

/-- A put-together witness identifies each global normalized dual vector with
the normalized dual vector in its component. -/
theorem dualVector_eq_component
    (h : BONG.PutTogetherWitness b D c) (i : Fin n) :
    b.dualVector i =
      ((c (h.componentIndex i)).dualVector (h.localIndex i) : V) := by
  have hunit : b.valueUnit i =
      (c (h.componentIndex i)).valueUnit (h.localIndex i) := by
    apply Units.ext
    exact h.value_eq i
  rw [BONG.dualVector, BONG.dualVector, hunit, h.ambientVector_eq i]
  rfl

end BONG.PutTogetherWitness

namespace Lattice.MaximalNormSplitting

open Lattice.OrthogonalDecomposition

/-- If a BONG and a reversed-dual BONG are obtained by concatenating the
corresponding component families, then their global vectors occur in exact
reverse-dual order. -/
theorem ambientVector_eq_reverseDualVector_of_putTogether
    {n : Nat} (M : Lattice.MaximalNormSplitting q L t)
    (c : M.toOrthogonalDecomposition.ComponentBONGFamily)
    (b : BONG V q L n)
    (h : BONG.PutTogetherWitness b M.toOrthogonalDecomposition c)
    (d : BONG V q (Lattice.dualLattice q L) (finrank K V))
    (hd : BONG.PutTogetherWitness d
      (M.reverseDual c).toOrthogonalDecomposition
      (M.reverseDualComponentBONGFamily c))
    (i : Fin n) :
    d.ambientVector (Fin.cast b.length_eq_finrank i) =
      b.reverseDualVector i := by
  let lift : Fin n → Fin (finrank K V) := Fin.cast b.length_eq_finrank
  let f : Fin n → Fin n := fun j =>
    h.indexEquiv.symm
      (M.reverseDualComponentIndex (hd.indexEquiv (lift j)))
  have hf : StrictAnti f := by
    intro x y hxy
    apply (h.order_iff (f y) (f x)).2
    simp only [f, Equiv.apply_symm_apply]
    apply M.componentIndexBefore_reverseDualComponentIndex
    apply (hd.order_iff (lift x) (lift y)).1
    exact Fin.cast_strictMono b.length_eq_finrank hxy
  have hfi : f i = Fin.rev i :=
    strictAnti_fin_eq_rev f hf i
  let u : Fin (finrank K V) := lift i
  let a := hd.indexEquiv u
  let s := M.reverseDualComponentIndex a
  calc
    d.ambientVector u =
        ((M.reverseDualComponentBONGFamily c
          (hd.componentIndex u)).ambientVector (hd.localIndex u) : V) :=
      hd.ambientVector_eq u
    _ = ((c (Fin.rev (hd.componentIndex u))).reverseDualVector
          (Fin.cast (M.reverseDual_componentRank_eq (hd.componentIndex u))
            (hd.localIndex u)) : V) := by
      exact congrArg Subtype.val
        (M.ambientVector_reverseDualComponentBONGFamily c
          (hd.componentIndex u) (hd.localIndex u))
    _ = ((c s.1).dualVector s.2 : V) := by
      rfl
    _ = b.dualVector (f i) := by
      symm
      have hsigma : h.indexEquiv (f i) = s := by
        simp [f, s, a, u, lift]
      have hdual := h.dualVector_eq_component (f i)
      change b.dualVector (f i) =
        ((c (h.indexEquiv (f i)).1).dualVector
          (h.indexEquiv (f i)).2 : V) at hdual
      rw [hsigma] at hdual
      exact hdual
    _ = b.reverseDualVector i := by
      rw [hfi]
      rfl

end Lattice.MaximalNormSplitting

namespace BONG.GoodBONG

variable [BeliSectionFourLaws.{u, v} K]
  [BeliLemma43ConstructionLaws.{u, v} K]

/--
Beli (2003), Lemma 4.8, derived from the maximal-norm splitting supplied by
Lemma 4.3(iii) and the component concatenation theorem of Lemma 4.1(i).

The resulting good BONG of the integral dual lattice has, coordinate by
coordinate, the normalized dual vectors of the original BONG in reverse
order.
-/
theorem exists_reverseDual_of_beli (b : BONG.GoodBONG q L n) :
    ∃ d : BONG.GoodBONG q (Lattice.dualLattice q L) n,
      ∀ i, d.toBONG.ambientVector i = b.toBONG.reverseDualVector i := by
  rcases b.toBONG.beliLemma43_iii b.good with
    ⟨t, M, c, hbPut, _⟩
  rcases hbPut with ⟨hb⟩
  rcases BeliSectionFourLaws.maximalNorm_putTogether
      (M.reverseDual c) (M.reverseDualComponentBONGFamily c) with
    ⟨d, hdPut⟩
  rcases hdPut with ⟨hd⟩
  have hdgood : d.IsGood :=
    BeliSectionFourLaws.maximalNorm_putTogether_isGood
      (M.reverseDual c) (M.reverseDualComponentBONGFamily c) d ⟨hd⟩
  have hlength : n = finrank K V := b.toBONG.length_eq_finrank
  subst n
  refine ⟨⟨d, hdgood⟩, ?_⟩
  intro i
  simpa using M.ambientVector_eq_reverseDualVector_of_putTogether
    c b.toBONG hb d hd i

end BONG.GoodBONG

/--
The reverse-dual law package is a theorem-level consequence of Beli's
explicit Section 4 construction interfaces; it need not be postulated as an
independent input.
-/
theorem bongReverseDualLawsOfBeli
    [BeliSectionFourLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K] :
    BONGReverseDualLaws.{u, v} K where
  reverse_dual_good := fun b => b.exists_reverseDual_of_beli

end Bong
