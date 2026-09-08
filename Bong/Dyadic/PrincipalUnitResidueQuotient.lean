/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Dyadic.CongruenceSubgroup
import Bong.Dyadic.PowerIdealResidueQuotient

/-!
# Successive principal-unit quotients

For every positive depth `n`, the quotient of the principal units of depth
`n` by those of depth `n+1` is the additive group of the residue field.  The
map is the leading coefficient of `u - 1`.
-/

namespace Bong.Dyadic

open Lattice

universe u

variable (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The error `u - 1`, regarded as an element of `p^n`. -/
noncomputable def principalUnitError (n : Nat)
    (u : principalUnitSubgroup K n) :
    powerIdeal (K := K) (n : Int) :=
  ⟨((u : Kˣ) : K) - 1, u.property.2⟩

@[simp]
theorem coe_principalUnitError (n : Nat)
    (u : principalUnitSubgroup K n) :
    (principalUnitError K n u : K) = ((u : Kˣ) : K) - 1 :=
  rfl

private theorem principalUnitError_mul_mem_succ
    (n : Nat) (hn : 0 < n)
    (u v : principalUnitSubgroup K n) :
    (principalUnitError K n u : K) *
        (principalUnitError K n v : K) ∈
      powerIdeal (K := K) ((n + 1 : Nat) : Int) := by
  rw [mem_powerIdeal_iff, ord_mul]
  have hu :=
    (mem_powerIdeal_iff (K := K) (n : Int)
      (principalUnitError K n u : K)).1
      (principalUnitError K n u).property
  have hv :=
    (mem_powerIdeal_iff (K := K) (n : Int)
      (principalUnitError K n v : K)).1
      (principalUnitError K n v).property
  calc
    (((n + 1 : Nat) : Int) : WithTop Int) ≤
        (((n + n : Nat) : Int) : WithTop Int) := by
      exact_mod_cast (show n + 1 ≤ n + n by omega)
    _ = (n : WithTop Int) + (n : WithTop Int) := by norm_num
    _ ≤ ord K (principalUnitError K n u : K) +
        ord K (principalUnitError K n v : K) := add_le_add hu hv

private theorem principalUnitError_mul_mem
    (n : Nat) (hn : 0 < n)
    (u v : principalUnitSubgroup K n) :
    (principalUnitError K n u : K) *
        (principalUnitError K n v : K) ∈
      powerIdeal (K := K) (n : Int) := by
  apply (powerIdeal_le_iff (K := K)
    ((n + 1 : Nat) : Int) (n : Int)).2 (by omega)
  exact principalUnitError_mul_mem_succ K n hn u v

/-- The leading residue coefficient of a principal unit.  The additive
residue group is written multiplicatively so this is a monoid homomorphism. -/
noncomputable def principalUnitLeadingCoefficient
    (n : Nat) (hn : 0 < n) :
    principalUnitSubgroup K n →* Multiplicative (normalizedResidueField K) where
  toFun u := Multiplicative.ofAdd
    (powerIdealLeadingCoefficient K (n : Int) (principalUnitError K n u))
  map_one' := by
    change Multiplicative.ofAdd
      (powerIdealLeadingCoefficient K (n : Int)
        (principalUnitError K n 1)) = Multiplicative.ofAdd 0
    congr 1
    apply (powerIdealLeadingCoefficient_eq_zero_iff K
      (n : Int) (principalUnitError K n 1)).2
    simp [principalUnitError]
  map_mul' u v := by
    apply Multiplicative.toAdd.injective
    change powerIdealLeadingCoefficient K (n : Int)
        (principalUnitError K n (u * v)) =
      powerIdealLeadingCoefficient K (n : Int)
          (principalUnitError K n u) +
        powerIdealLeadingCoefficient K (n : Int)
          (principalUnitError K n v)
    let cross : powerIdeal (K := K) (n : Int) :=
      ⟨(principalUnitError K n u : K) *
          (principalUnitError K n v : K),
        principalUnitError_mul_mem K n hn u v⟩
    have hcross : powerIdealLeadingCoefficient K (n : Int) cross = 0 := by
      apply (powerIdealLeadingCoefficient_eq_zero_iff K (n : Int) cross).2
      exact principalUnitError_mul_mem_succ K n hn u v
    have herror : principalUnitError K n (u * v) =
        principalUnitError K n u + principalUnitError K n v + cross := by
      apply Subtype.ext
      change ((u : Kˣ) : K) * ((v : Kˣ) : K) - 1 =
        (((u : Kˣ) : K) - 1) + (((v : Kˣ) : K) - 1) +
          ((((u : Kˣ) : K) - 1) * (((v : Kˣ) : K) - 1))
      ring
    rw [herror, map_add, map_add, hcross, add_zero]

@[simp]
theorem principalUnitLeadingCoefficient_apply
    (n : Nat) (hn : 0 < n) (u : principalUnitSubgroup K n) :
    Multiplicative.toAdd (principalUnitLeadingCoefficient K n hn u) =
      powerIdealLeadingCoefficient K (n : Int)
        (principalUnitError K n u) :=
  rfl

/-- Every residue coefficient occurs as the leading coefficient of a
principal unit. -/
theorem principalUnitLeadingCoefficient_surjective
    (n : Nat) (hn : 0 < n) :
    Function.Surjective (principalUnitLeadingCoefficient K n hn) := by
  intro z
  let zAdd : normalizedResidueField K := Multiplicative.toAdd z
  obtain ⟨x, hx⟩ := powerIdealLeadingCoefficient_surjective K (n : Int) zAdd
  have hxOrder : (n : WithTop Int) ≤ ord K (x : K) :=
    (mem_powerIdeal_iff (K := K) (n : Int) (x : K)).1 x.property
  have hxPos : (0 : WithTop Int) < ord K (x : K) := by
    exact (show (0 : WithTop Int) < n by exact_mod_cast hn).trans_le hxOrder
  have huOrder : ord K (1 + (x : K)) = 0 := by
    have honeLt : ord K (1 : K) < ord K (x : K) := by
      simpa only [ord_one] using hxPos
    simpa only [ord_one] using (ord K).map_add_eq_of_lt_left honeLt
  have huNe : 1 + (x : K) ≠ 0 := by
    apply (ord_eq_top_iff K).not.mp
    rw [huOrder]
    exact WithTop.coe_ne_top
  let u : Kˣ := Units.mk0 (1 + (x : K)) huNe
  have huUnit : IsValuationUnit K (u : K) := by
    exact huOrder
  have huError : (u : K) - 1 ∈ powerIdeal (K := K) (n : Int) := by
    change (1 + (x : K)) - 1 ∈ powerIdeal (K := K) (n : Int)
    convert x.property using 1
    ring
  let un : principalUnitSubgroup K n := ⟨u, huUnit, huError⟩
  refine ⟨un, ?_⟩
  apply Multiplicative.toAdd.injective
  change powerIdealLeadingCoefficient K (n : Int)
      (principalUnitError K n un) = zAdd
  have herror : principalUnitError K n un = x := by
    apply Subtype.ext
    simp [un, u, principalUnitError]
  rw [herror]
  exact hx

/-- The kernel of the principal-unit leading coefficient. -/
noncomputable abbrev principalUnitResidueKernel
    (n : Nat) (hn : 0 < n) : Subgroup (principalUnitSubgroup K n) :=
  (principalUnitLeadingCoefficient K n hn).ker

theorem mem_principalUnitResidueKernel_iff
    (n : Nat) (hn : 0 < n) (u : principalUnitSubgroup K n) :
    u ∈ principalUnitResidueKernel K n hn ↔
      (u : Kˣ) ∈ principalUnitSubgroup K (n + 1) := by
  change principalUnitLeadingCoefficient K n hn u = 1 ↔ _
  constructor
  · intro h
    have hzero := congrArg Multiplicative.toAdd h
    change powerIdealLeadingCoefficient K (n : Int)
        (principalUnitError K n u) = 0 at hzero
    have herror :=
      (powerIdealLeadingCoefficient_eq_zero_iff K
        (n : Int) (principalUnitError K n u)).1 hzero
    exact ⟨u.property.1, by simpa using herror⟩
  · intro hnext
    apply Multiplicative.toAdd.injective
    change powerIdealLeadingCoefficient K (n : Int)
        (principalUnitError K n u) = 0
    apply (powerIdealLeadingCoefficient_eq_zero_iff K
      (n : Int) (principalUnitError K n u)).2
    simpa using hnext.2

/-- The quotient of two successive positive-depth principal-unit groups is
the additive residue group. -/
noncomputable def principalUnitQuotientEquivResidueField
    (n : Nat) (hn : 0 < n) :
    (principalUnitSubgroup K n ⧸ principalUnitResidueKernel K n hn) ≃*
      Multiplicative (normalizedResidueField K) :=
  QuotientGroup.quotientKerEquivOfSurjective
    (principalUnitLeadingCoefficient K n hn)
    (principalUnitLeadingCoefficient_surjective K n hn)

/-- Every positive-depth successive principal-unit quotient has residue
cardinality. -/
theorem card_principalUnitQuotient
    (n : Nat) (hn : 0 < n) :
    Nat.card
        (principalUnitSubgroup K n ⧸ principalUnitResidueKernel K n hn) =
      Nat.card (normalizedResidueField K) :=
  Nat.card_congr (principalUnitQuotientEquivResidueField K n hn).toEquiv

end Bong.Dyadic
