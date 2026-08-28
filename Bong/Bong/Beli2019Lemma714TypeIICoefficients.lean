/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma714TypeIIBoundary

/-!
# Beli (2019), Lemma 7.14(ii): the complete replacement coefficients

After removing the initial binary factor, the product has the same rank as
the original lattice.  In zero-based indexing its target coefficients are

`x₃, ..., x_s, y_(s-1), y_s, y_(s+1), x_(s+2), ..., x_N`.

The replacement has net length two, exactly compensating for the removed
initial binary factor.  Consequently the unchanged suffix again carries its
original zero-based index.  This file records that coefficient family and
its exact order profile.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- The full coefficient list in the type-II branch of Lemma 7.14. -/
noncomputable def lemma714TypeIITargetValues
    [DyadicDiscriminantClassLaws K]
    (b : GoodBONG q L (n + 3)) (s : Nat)
    (hsTwo : 2 ≤ s) (hsCurrent : s < n + 3)
    (ε η : Kˣ) : Fin (n + 3) → Kˣ := fun i =>
  if hprefix : i.val < s - 2 then
    b.valueUnit ⟨i.val + 2, by omega⟩
  else if hzero : i.val = s - 2 then
    lemma712TargetValues (b.valueUnit ⟨s, hsCurrent⟩) ε η 0
  else if hone : i.val = s - 1 then
    lemma712TargetValues (b.valueUnit ⟨s, hsCurrent⟩) ε η 1
  else if htwo : i.val = s then
    lemma712TargetValues (b.valueUnit ⟨s, hsCurrent⟩) ε η 2
  else
    b.valueUnit i

@[simp]
theorem lemma714TypeIITargetValues_prefix
    [DyadicDiscriminantClassLaws K]
    (b : GoodBONG q L (n + 3)) (s : Nat)
    (hsTwo : 2 ≤ s) (hsCurrent : s < n + 3)
    (ε η : Kˣ) (i : Fin (n + 3)) (hi : i.val < s - 2) :
    lemma714TypeIITargetValues b s hsTwo hsCurrent ε η i =
      b.valueUnit ⟨i.val + 2, by omega⟩ := by
  simp [lemma714TypeIITargetValues, hi]

@[simp]
theorem lemma714TypeIITargetValues_zero
    [DyadicDiscriminantClassLaws K]
    (b : GoodBONG q L (n + 3)) (s : Nat)
    (hsTwo : 2 ≤ s) (hsCurrent : s < n + 3)
    (ε η : Kˣ) :
    lemma714TypeIITargetValues b s hsTwo hsCurrent ε η
        ⟨s - 2, by omega⟩ =
      lemma712TargetValues (b.valueUnit ⟨s, hsCurrent⟩) ε η 0 := by
  simp [lemma714TypeIITargetValues]

@[simp]
theorem lemma714TypeIITargetValues_one
    [DyadicDiscriminantClassLaws K]
    (b : GoodBONG q L (n + 3)) (s : Nat)
    (hsTwo : 2 ≤ s) (hsCurrent : s < n + 3)
    (ε η : Kˣ) :
    lemma714TypeIITargetValues b s hsTwo hsCurrent ε η
        ⟨s - 1, by omega⟩ =
      lemma712TargetValues (b.valueUnit ⟨s, hsCurrent⟩) ε η 1 := by
  have hnotPrefix : ¬s - 1 < s - 2 := by omega
  have hnotZero : s - 1 ≠ s - 2 := by omega
  simp [lemma714TypeIITargetValues, hnotPrefix, hnotZero]

@[simp]
theorem lemma714TypeIITargetValues_two
    [DyadicDiscriminantClassLaws K]
    (b : GoodBONG q L (n + 3)) (s : Nat)
    (hsTwo : 2 ≤ s) (hsCurrent : s < n + 3)
    (ε η : Kˣ) :
    lemma714TypeIITargetValues b s hsTwo hsCurrent ε η
        ⟨s, hsCurrent⟩ =
      lemma712TargetValues (b.valueUnit ⟨s, hsCurrent⟩) ε η 2 := by
  have hnotPrefix : ¬s < s - 2 := by omega
  have hnotZero : s ≠ s - 2 := by omega
  have hnotOne : s ≠ s - 1 := by omega
  simp [lemma714TypeIITargetValues, hnotPrefix, hnotZero, hnotOne]

@[simp]
theorem lemma714TypeIITargetValues_suffix
    [DyadicDiscriminantClassLaws K]
    (b : GoodBONG q L (n + 3)) (s : Nat)
    (hsTwo : 2 ≤ s) (hsCurrent : s < n + 3)
    (ε η : Kˣ) (i : Fin (n + 3)) (hi : s < i.val) :
    lemma714TypeIITargetValues b s hsTwo hsCurrent ε η i =
      b.valueUnit i := by
  have hnotPrefix : ¬i.val < s - 2 := by omega
  have hnotZero : i.val ≠ s - 2 := by omega
  have hnotOne : i.val ≠ s - 1 := by omega
  have hnotTwo : i.val ≠ s := by omega
  simp [lemma714TypeIITargetValues, hnotPrefix, hnotZero, hnotOne,
    hnotTwo]

@[simp]
theorem ordUnit_lemma714TypeIITargetValues_prefix
    [DyadicDiscriminantClassLaws K]
    (b : GoodBONG q L (n + 3)) (s : Nat)
    (hsTwo : 2 ≤ s) (hsCurrent : s < n + 3)
    (ε η : Kˣ) (i : Fin (n + 3)) (hi : i.val < s - 2) :
    ordUnit K (lemma714TypeIITargetValues b s hsTwo hsCurrent ε η i) =
      b.order ⟨i.val + 2, by omega⟩ := by
  rw [lemma714TypeIITargetValues_prefix b s hsTwo hsCurrent ε η i hi]
  exact (b.toBONG.order_eq_ordUnit ⟨i.val + 2, by omega⟩).symm

@[simp]
theorem ordUnit_lemma714TypeIITargetValues_zero
    [laws : DyadicDiscriminantClassLaws K]
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (hsTwo : 2 ≤ s) (hsCurrent : s < n + 3)
    (hcurrent : b.order ⟨s, hsCurrent⟩ = R + 1)
    (ε η : Kˣ) (hεUnit : IsValuationUnit K (ε : K))
    (hηUnit : IsValuationUnit K (η : K)) :
    ordUnit K (lemma714TypeIITargetValues b s hsTwo hsCurrent ε η
      ⟨s - 2, by omega⟩) = R + 1 := by
  rw [lemma714TypeIITargetValues_zero]
  have horders := lemma712TargetValues_orders
    (b.valueUnit ⟨s, hsCurrent⟩) ε η hεUnit hηUnit
  rw [horders (0 : Fin 3)]
  have hcurrentOrder : ordUnit K (b.valueUnit ⟨s, hsCurrent⟩) =
      R + 1 := by
    change ordUnit K (b.toBONG.valueUnit ⟨s, hsCurrent⟩) = R + 1
    rw [← b.toBONG.order_eq_ordUnit]
    exact hcurrent
  exact hcurrentOrder

@[simp]
theorem ordUnit_lemma714TypeIITargetValues_one
    [laws : DyadicDiscriminantClassLaws K]
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (hsTwo : 2 ≤ s) (hsCurrent : s < n + 3)
    (hcurrent : b.order ⟨s, hsCurrent⟩ = R + 1)
    (ε η : Kˣ) (hεUnit : IsValuationUnit K (ε : K))
    (hηUnit : IsValuationUnit K (η : K)) :
    ordUnit K (lemma714TypeIITargetValues b s hsTwo hsCurrent ε η
      ⟨s - 1, by omega⟩) =
      R - 2 * (ramificationIndex K : Int) + 3 := by
  rw [lemma714TypeIITargetValues_one]
  have horders := lemma712TargetValues_orders
    (b.valueUnit ⟨s, hsCurrent⟩) ε η hεUnit hηUnit
  rw [horders (1 : Fin 3)]
  change ordUnit K (b.valueUnit ⟨s, hsCurrent⟩) + 2 -
      2 * (ramificationIndex K : Int) = _
  have hcurrentOrder : ordUnit K (b.valueUnit ⟨s, hsCurrent⟩) =
      R + 1 := by
    change ordUnit K (b.toBONG.valueUnit ⟨s, hsCurrent⟩) = R + 1
    rw [← b.toBONG.order_eq_ordUnit]
    exact hcurrent
  rw [hcurrentOrder]
  ring

@[simp]
theorem ordUnit_lemma714TypeIITargetValues_two
    [laws : DyadicDiscriminantClassLaws K]
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (hsTwo : 2 ≤ s) (hsCurrent : s < n + 3)
    (hcurrent : b.order ⟨s, hsCurrent⟩ = R + 1)
    (ε η : Kˣ) (hεUnit : IsValuationUnit K (ε : K))
    (hηUnit : IsValuationUnit K (η : K)) :
    ordUnit K (lemma714TypeIITargetValues b s hsTwo hsCurrent ε η
      ⟨s, hsCurrent⟩) = R + 1 := by
  rw [lemma714TypeIITargetValues_two]
  have horders := lemma712TargetValues_orders
    (b.valueUnit ⟨s, hsCurrent⟩) ε η hεUnit hηUnit
  rw [horders (2 : Fin 3)]
  have hcurrentOrder : ordUnit K (b.valueUnit ⟨s, hsCurrent⟩) =
      R + 1 := by
    change ordUnit K (b.toBONG.valueUnit ⟨s, hsCurrent⟩) = R + 1
    rw [← b.toBONG.order_eq_ordUnit]
    exact hcurrent
  exact hcurrentOrder

@[simp]
theorem ordUnit_lemma714TypeIITargetValues_suffix
    [DyadicDiscriminantClassLaws K]
    (b : GoodBONG q L (n + 3)) (s : Nat)
    (hsTwo : 2 ≤ s) (hsCurrent : s < n + 3)
    (ε η : Kˣ) (i : Fin (n + 3)) (hi : s < i.val) :
    ordUnit K (lemma714TypeIITargetValues b s hsTwo hsCurrent ε η i) =
      b.order i := by
  rw [lemma714TypeIITargetValues_suffix b s hsTwo hsCurrent ε η i hi]
  exact (b.toBONG.order_eq_ordUnit i).symm

end BONG.GoodBONG

end Bong
