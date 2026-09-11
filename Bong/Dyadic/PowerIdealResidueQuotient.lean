/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Dyadic.ResidueArtinSchreier
import Bong.Lattice.PowerIdeal
import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Successive power-ideal quotients

For the normalized valuation of a dyadic local field, every successive
quotient `p^n / p^(n+1)` is additively equivalent to the residue field.  The
equivalence sends `x` to the residue of `pi^(-n) x`.
-/

namespace Bong.Dyadic

open Lattice

universe u

variable (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

private theorem powerIdeal_normalized_isIntegral
    (n : Int) (x : powerIdeal (K := K) n) :
    IsIntegral K
      ((uniformizerPowerUnit K n : K)⁻¹ * (x : K)) := by
  unfold IsIntegral
  have hx : (n : WithTop Int) ≤ ord K (x : K) :=
    (mem_powerIdeal_iff (K := K) n (x : K)).1 x.property
  have hshift := add_le_add_left hx ((-n : Int) : WithTop Int)
  rw [ord_mul, AddValuation.map_inv, ← coe_ordUnit,
    ordUnit_uniformizerPowerUnit]
  change ((0 : Int) : WithTop Int) ≤
    ((-n : Int) : WithTop Int) + ord K (x : K)
  simpa only [← WithTop.coe_add, add_comm, add_neg_cancel] using hshift

/-- Division by `pi^n`, with codomain restricted to the normalized
valuation ring. -/
noncomputable def powerIdealNormalized (n : Int) :
    powerIdeal (K := K) n →+ normalizedValuationRing K where
  toFun x :=
    ⟨(uniformizerPowerUnit K n : K)⁻¹ * (x : K),
      (mem_normalizedValuationRing_iff K).2
        (powerIdeal_normalized_isIntegral K n x)⟩
  map_zero' := by
    apply Subtype.ext
    simp
  map_add' x y := by
    apply Subtype.ext
    change
      (uniformizerPowerUnit K n : K)⁻¹ * ((x : K) + (y : K)) =
        (uniformizerPowerUnit K n : K)⁻¹ * (x : K) +
          (uniformizerPowerUnit K n : K)⁻¹ * (y : K)
    ring

/-- The leading residue coefficient of an element of `p^n`. -/
noncomputable def powerIdealLeadingCoefficient (n : Int) :
    powerIdeal (K := K) n →+ normalizedResidueField K :=
  (IsLocalRing.residue (normalizedValuationRing K)).toAddMonoidHom.comp
    (powerIdealNormalized K n)

@[simp]
theorem powerIdealLeadingCoefficient_apply (n : Int)
    (x : powerIdeal (K := K) n) :
    powerIdealLeadingCoefficient K n x =
      IsLocalRing.residue (normalizedValuationRing K)
        (powerIdealNormalized K n x) :=
  rfl

theorem powerIdealLeadingCoefficient_eq_zero_iff
    (n : Int) (x : powerIdeal (K := K) n) :
    powerIdealLeadingCoefficient K n x = 0 ↔
      (x : K) ∈ powerIdeal (K := K) (n + 1) := by
  rw [powerIdealLeadingCoefficient_apply,
    IsLocalRing.residue_eq_zero_iff,
    mem_normalizedMaximalIdeal_iff,
    mem_powerIdeal_iff]
  by_cases hx : (x : K) = 0
  · have hnormalized : (powerIdealNormalized K n x : K) = 0 := by
      simp [powerIdealNormalized, hx]
    change (0 : WithTop Int) < ord K (powerIdealNormalized K n x : K) ↔
      ((n + 1 : Int) : WithTop Int) ≤ ord K (x : K)
    rw [hnormalized, hx, ord_zero]
    simp
  · let xu : Kˣ := Units.mk0 (x : K) hx
    have hxOrder : ord K (x : K) = (ordUnit K xu : WithTop Int) := by
      exact (coe_ordUnit K xu).symm
    change (0 : WithTop Int) <
        ord K ((uniformizerPowerUnit K n : K)⁻¹ * (x : K)) ↔
      ((n + 1 : Int) : WithTop Int) ≤ ord K (x : K)
    rw [ord_mul, AddValuation.map_inv, ← coe_ordUnit,
      ordUnit_uniformizerPowerUnit, hxOrder]
    norm_cast
    omega

/-- The leading-coefficient map is onto the residue field. -/
theorem powerIdealLeadingCoefficient_surjective (n : Int) :
    Function.Surjective (powerIdealLeadingCoefficient K n) := by
  intro z
  obtain ⟨a, ha⟩ :=
    IsLocalRing.residue_surjective
      (R := normalizedValuationRing K) z
  have haIntegral : IsIntegral K (a : K) :=
    (mem_normalizedValuationRing_iff K).1 a.property
  let pi : Kˣ := uniformizerPowerUnit K n
  have hxMem : (pi : K) * (a : K) ∈ powerIdeal (K := K) n := by
    rw [mem_powerIdeal_iff, ord_mul, ← coe_ordUnit,
      ordUnit_uniformizerPowerUnit]
    have hnonnegative : (0 : WithTop Int) ≤ ord K (a : K) := haIntegral
    simpa [add_comm] using
      add_le_add_left hnonnegative (n : WithTop Int)
  let x : powerIdeal (K := K) n := ⟨(pi : K) * (a : K), hxMem⟩
  refine ⟨x, ?_⟩
  rw [powerIdealLeadingCoefficient_apply]
  have hnormalized :
      (uniformizerPowerUnit K n : K)⁻¹ * (x : K) = (a : K) := by
    dsimp only [x, pi]
    rw [← mul_assoc, inv_mul_cancel₀
      (Units.ne_zero (uniformizerPowerUnit K n)), one_mul]
  have hnormalizedA : powerIdealNormalized K n x = a :=
    Subtype.ext hnormalized
  change IsLocalRing.residue (normalizedValuationRing K)
    (powerIdealNormalized K n x) = z
  rw [hnormalizedA]
  exact ha

/-- The subgroup of `p^n` killed by the leading residue coefficient. -/
noncomputable abbrev powerIdealResidueKernel (n : Int) :
    AddSubgroup (powerIdeal (K := K) n) :=
  (powerIdealLeadingCoefficient K n).ker

theorem mem_powerIdealResidueKernel_iff (n : Int)
    (x : powerIdeal (K := K) n) :
    x ∈ powerIdealResidueKernel K n ↔
      (x : K) ∈ powerIdeal (K := K) (n + 1) := by
  exact powerIdealLeadingCoefficient_eq_zero_iff K n x

/-- The additive quotient `p^n / p^(n+1)` identified with the residue
field through its leading coefficient. -/
noncomputable def powerIdealQuotientEquivResidueField (n : Int) :
    (powerIdeal (K := K) n ⧸ powerIdealResidueKernel K n) ≃+
      normalizedResidueField K :=
  QuotientAddGroup.quotientKerEquivOfSurjective
    (powerIdealLeadingCoefficient K n)
    (powerIdealLeadingCoefficient_surjective K n)

/-- Every successive power-ideal quotient has cardinality equal to the
residue-field norm. -/
theorem card_powerIdealQuotient (n : Int) :
    Nat.card (powerIdeal (K := K) n ⧸ powerIdealResidueKernel K n) =
      Nat.card (normalizedResidueField K) :=
  Nat.card_congr (powerIdealQuotientEquivResidueField K n).toEquiv

end Bong.Dyadic
