/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.ModularScale
import Bong.Lattice.OrthogonalSupNorm
import Bong.Lattice.WeakJordanDecomposition

/-!
# Amalgamating a weak Jordan decomposition

Repeatedly amalgamating equal-scale neighbours terminates because every step
reduces the finite number of components.  The resulting scale orders are
strictly increasing.  Positive rank then supplies a norm generator for each
final component.
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

namespace Lattice
namespace WeakJordanDecomposition

variable {q : QuadraticSpace K V} {L : Lattice K V}

/-- A chosen anisotropic norm-generating vector in a positive-rank weak
Jordan component.  Naming this choice makes the norm data retained by
`toJordan` available to later amalgamation calculations. -/
noncomputable def normGeneratorVector {t : Nat}
    (W : WeakJordanDecomposition q L t) (i : Fin t) :
    (W.component i).carrier :=
  Classical.choose <|
    exists_isNormGenerator_of_finrank_pos
      (W.component i).space (W.component i).lattice
      (W.component_finrank_pos i)

/-- The chosen vector is a norm generator and is anisotropic. -/
theorem normGeneratorVector_spec {t : Nat}
    (W : WeakJordanDecomposition q L t) (i : Fin t) :
    IsNormGenerator (W.component i).space
        (W.component i).lattice (W.normGeneratorVector i) ∧
      (W.component i).space.IsAnisotropic (W.normGeneratorVector i) :=
  Classical.choose_spec <|
    exists_isNormGenerator_of_finrank_pos
      (W.component i).space (W.component i).lattice
      (W.component_finrank_pos i)

/-- The nonzero quadratic value of the chosen component norm generator. -/
noncomputable def normGeneratorUnit {t : Nat}
    (W : WeakJordanDecomposition q L t) (i : Fin t) : Kˣ :=
  Units.mk0
    ((W.component i).space.quadratic (W.normGeneratorVector i))
    (W.normGeneratorVector_spec i).2

/-- The chosen unit generates the component norm ideal. -/
theorem normIdeal_eq_normGeneratorUnit {t : Nat}
    (W : WeakJordanDecomposition q L t) (i : Fin t) :
    normIdeal (W.component i).space (W.component i).lattice =
      principalIdeal (K := K) (W.normGeneratorUnit i : K) :=
  (W.normGeneratorVector_spec i).1.normIdeal_eq

/-- The only possible equality of distinct scale positions is the indicated
adjacent pair. -/
def OnlyScaleCollisionAt {t : Nat}
    (W : WeakJordanDecomposition q L (t + 1)) (k : Fin t) : Prop :=
  ∀ ⦃i j : Fin (t + 1)⦄,
    i < j →
      ordUnit K (W.scaleGenerator i) =
        ordUnit K (W.scaleGenerator j) →
      i = k.castSucc ∧ j = k.succ

/-- Merge an adjacent pair in a decomposition indexed by `t + 1`.  The
index itself excludes the vacuous `t = 0` case. -/
noncomputable def mergeAdjacentAt {t : Nat}
    (W : WeakJordanDecomposition q L (t + 1)) (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ)) :
    WeakJordanDecomposition q L t := by
  cases t with
  | zero => exact Fin.elim0 k
  | succ n => exact W.mergeAdjacent k heq

/-- The distinguished component after an adjacent merge is the orthogonal
sum of the two old neighbours. -/
@[simp]
theorem mergeAdjacentAt_component_self {t : Nat}
    (W : WeakJordanDecomposition q L (t + 1)) (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ)) :
    (W.mergeAdjacentAt k heq).component k =
      W.toOrthogonalDecomposition.orthogonalSup
        k.castSucc_lt_succ.ne := by
  cases t with
  | zero => exact Fin.elim0 k
  | succ n =>
      change W.toOrthogonalDecomposition.mergeComponents k k = _
      exact W.toOrthogonalDecomposition.mergeComponents_self k

/-- A component away from the merge position is unchanged; its old index is
obtained by skipping the removed second neighbour. -/
@[simp]
theorem mergeAdjacentAt_component_of_ne {t : Nat}
    (W : WeakJordanDecomposition q L (t + 1)) (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ))
    (j : Fin t) (hjk : j ≠ k) :
    (W.mergeAdjacentAt k heq).component j =
      W.component (k.succ.succAbove j) := by
  cases t with
  | zero => exact Fin.elim0 k
  | succ n =>
      induction j using Fin.succAboveCases k with
      | x => exact (hjk rfl).elim
      | p r =>
          change W.toOrthogonalDecomposition.mergeComponents k
              (k.succAbove r) = _
          exact W.toOrthogonalDecomposition.mergeComponents_other k r

/-- Every component strictly before the amalgamated pair is literally the
old component with the same numerical index. -/
@[simp]
theorem mergeAdjacentAt_component_of_lt {t : Nat}
    (W : WeakJordanDecomposition q L (t + 1)) (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ))
    (j : Fin t) (hjk : j < k) :
    (W.mergeAdjacentAt k heq).component j = W.component j.castSucc := by
  rw [W.mergeAdjacentAt_component_of_ne k heq j (ne_of_lt hjk)]
  rw [Fin.succAbove_of_castSucc_lt]
  exact Fin.castSucc_lt_succ_iff.mpr hjk.le

/-- The retained scale at every new position is the scale at the old index
which skips the removed second neighbour. -/
@[simp]
theorem mergeAdjacentAt_scaleGenerator {t : Nat}
    (W : WeakJordanDecomposition q L (t + 1)) (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ)) (j : Fin t) :
    (W.mergeAdjacentAt k heq).scaleGenerator j =
      W.scaleGenerator (k.succ.succAbove j) := by
  cases t with
  | zero => exact Fin.elim0 k
  | succ n => rfl

/-- Amalgamation adds the ranks of exactly the two merged neighbours. -/
theorem mergeAdjacentAt_componentRank_self {t : Nat}
    (W : WeakJordanDecomposition q L (t + 1)) (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ)) :
    finrank K ((W.mergeAdjacentAt k heq).component k).carrier =
      finrank K (W.component k.castSucc).carrier +
        finrank K (W.component k.succ).carrier := by
  rw [W.mergeAdjacentAt_component_self k heq,
    W.toOrthogonalDecomposition.orthogonalSup_finrank]

/-- The chosen norm order of a nonmerged component is unchanged.  The
chosen generators themselves need not be definitionally identical, so the
proof passes through equality of their principal norm ideals. -/
theorem ordUnit_normGeneratorUnit_mergeAdjacentAt_of_ne {t : Nat}
    (W : WeakJordanDecomposition q L (t + 1)) (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ))
    (j : Fin t) (hjk : j ≠ k) :
    ordUnit K ((W.mergeAdjacentAt k heq).normGeneratorUnit j) =
      ordUnit K (W.normGeneratorUnit (k.succ.succAbove j)) := by
  apply (principalIdeal_eq_iff_ordUnit_eq _ _).mp
  calc
    principalIdeal (K := K)
        (((W.mergeAdjacentAt k heq).normGeneratorUnit j : K)) =
        normIdeal ((W.mergeAdjacentAt k heq).component j).space
          ((W.mergeAdjacentAt k heq).component j).lattice :=
      ((W.mergeAdjacentAt k heq).normIdeal_eq_normGeneratorUnit j).symm
    _ = normIdeal (W.component (k.succ.succAbove j)).space
          (W.component (k.succ.succAbove j)).lattice := by
      rw [W.mergeAdjacentAt_component_of_ne k heq j hjk]
    _ = principalIdeal (K := K)
        (W.normGeneratorUnit (k.succ.succAbove j) : K) :=
      W.normIdeal_eq_normGeneratorUnit (k.succ.succAbove j)

/-- The norm order of the amalgamated component is the minimum of the two
old norm orders. -/
theorem ordUnit_normGeneratorUnit_mergeAdjacentAt_self {t : Nat}
    (W : WeakJordanDecomposition q L (t + 1)) (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ)) :
    ordUnit K ((W.mergeAdjacentAt k heq).normGeneratorUnit k) =
      min (ordUnit K (W.normGeneratorUnit k.castSucc))
        (ordUnit K (W.normGeneratorUnit k.succ)) := by
  apply W.toOrthogonalDecomposition.ordUnit_normGenerator_orthogonalSup
    k.castSucc_lt_succ.ne
    (W.normGeneratorUnit k.castSucc)
    (W.normGeneratorUnit k.succ)
    ((W.mergeAdjacentAt k heq).normGeneratorUnit k)
    (W.normIdeal_eq_normGeneratorUnit k.castSucc)
    (W.normIdeal_eq_normGeneratorUnit k.succ)
  rw [← W.mergeAdjacentAt_component_self k heq]
  exact (W.mergeAdjacentAt k heq).normIdeal_eq_normGeneratorUnit k

/-- Merging the unique equal-scale adjacent pair leaves strictly increasing
scales. -/
theorem mergeAdjacentAt_scaleOrder_strict {t : Nat}
    (W : WeakJordanDecomposition q L (t + 1)) (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ))
    (honly : OnlyScaleCollisionAt W k) :
    StrictMono (fun i ↦
      ordUnit K ((W.mergeAdjacentAt k heq).scaleGenerator i)) := by
  cases t with
  | zero => exact Fin.elim0 k
  | succ n =>
      apply (Fin.strictMono_iff_lt_succ).2
      intro i
      change ordUnit K
          (W.scaleGenerator (k.succ.succAbove i.castSucc)) <
        ordUnit K (W.scaleGenerator (k.succ.succAbove i.succ))
      have hindices : k.succ.succAbove i.castSucc <
          k.succ.succAbove i.succ :=
        Fin.strictMono_succAbove k.succ i.castSucc_lt_succ
      have hle := W.scaleOrder_mono hindices.le
      apply lt_of_le_of_ne hle
      intro hEq
      have hpair := honly hindices hEq
      exact (Fin.succAbove_ne k.succ i.succ) hpair.2

/-- Repeated equal-scale amalgamation produces a weak decomposition with
strictly increasing scales. -/
theorem exists_strict :
    ∀ (t : Nat) (_W : WeakJordanDecomposition q L t),
      ∃ (s : Nat) (S : WeakJordanDecomposition q L s),
        StrictMono (fun i ↦ ordUnit K (S.scaleGenerator i)) := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
      intro W
      let f : Fin t → Int := fun i ↦ ordUnit K (W.scaleGenerator i)
      by_cases hstrict : StrictMono f
      · exact ⟨t, W, hstrict⟩
      · cases t with
        | zero =>
            exfalso
            apply hstrict
            exact fun i ↦ Fin.elim0 i
        | succ t =>
            cases t with
            | zero =>
                exfalso
                apply hstrict
                intro i j hij
                omega
            | succ n =>
                have hadj : ¬∀ k : Fin (n + 1),
                    f k.castSucc < f k.succ := by
                  intro h
                  exact hstrict ((Fin.strictMono_iff_lt_succ).2 h)
                push Not at hadj
                obtain ⟨k, hk⟩ := hadj
                have hle : f k.castSucc ≤ f k.succ :=
                  W.scaleOrder_mono k.castSucc_lt_succ.le
                have heq : ordUnit K (W.scaleGenerator k.castSucc) =
                    ordUnit K (W.scaleGenerator k.succ) :=
                  le_antisymm hle hk
                exact ih (n + 1) (by omega) (W.mergeAdjacent k heq)

/-- Choose norm generators on a strict weak decomposition and obtain a
Jordan decomposition. -/
noncomputable def toJordan {t : Nat}
    (W : WeakJordanDecomposition q L t)
    (hstrict : StrictMono
      (fun i ↦ ordUnit K (W.scaleGenerator i))) :
    JordanDecomposition q L t := by
  exact {
    toOrthogonalDecomposition := W.toOrthogonalDecomposition
    scaleGenerator := W.scaleGenerator
    normGenerator := W.normGeneratorUnit
    modular := W.modular
    scaleIdeal_eq := fun i ↦
      (W.modular i).scaleIdeal_eq_principal
        (W.component_finrank_pos i)
    normIdeal_eq := W.normIdeal_eq_normGeneratorUnit
    scaleOrder_strict := fun hij ↦ hstrict hij
  }

@[simp]
theorem toJordan_component {t : Nat}
    (W : WeakJordanDecomposition q L t)
    (hstrict : StrictMono
      (fun i ↦ ordUnit K (W.scaleGenerator i))) (i : Fin t) :
    (W.toJordan hstrict).component i = W.component i :=
  rfl

@[simp]
theorem toJordan_scaleGenerator {t : Nat}
    (W : WeakJordanDecomposition q L t)
    (hstrict : StrictMono
      (fun i ↦ ordUnit K (W.scaleGenerator i))) (i : Fin t) :
    (W.toJordan hstrict).scaleGenerator i = W.scaleGenerator i :=
  rfl

@[simp]
theorem toJordan_normGenerator {t : Nat}
    (W : WeakJordanDecomposition q L t)
    (hstrict : StrictMono
      (fun i ↦ ordUnit K (W.scaleGenerator i))) (i : Fin t) :
    (W.toJordan hstrict).normGenerator i = W.normGeneratorUnit i :=
  rfl

/-- A weak Jordan decomposition has a strict Jordan refinement obtained only
by amalgamating equal-scale neighbours. -/
theorem exists_jordan {t : Nat}
    (W : WeakJordanDecomposition q L t) :
    ∃ (s : Nat), Nonempty (JordanDecomposition q L s) := by
  obtain ⟨s, S, hstrict⟩ := exists_strict t W
  exact ⟨s, ⟨S.toJordan hstrict⟩⟩

/-- A chosen strict weak refinement, retaining positivity and the modular
component data before norm generators are chosen.  This is useful when a
later construction inserts one additional modular block: the old component
scales remain strictly ordered, so at most one amalgamation can be needed. -/
noncomputable def strictWitness {t : Nat}
    (W : WeakJordanDecomposition q L t) :
    Σ s : Nat, {S : WeakJordanDecomposition q L s //
      StrictMono (fun i ↦ ordUnit K (S.scaleGenerator i))} := by
  let h := exists_strict t W
  exact ⟨h.choose, ⟨h.choose_spec.choose,
    h.choose_spec.choose_spec⟩⟩

/-- A chosen strict Jordan refinement of a weak Jordan decomposition. -/
noncomputable def jordanWitness {t : Nat}
    (W : WeakJordanDecomposition q L t) :
    Σ s : Nat, JordanDecomposition q L s := by
  let h := exists_strict t W
  let s := h.choose
  let S := h.choose_spec.choose
  exact ⟨s, S.toJordan h.choose_spec.choose_spec⟩

end WeakJordanDecomposition
end Lattice
end Bong
