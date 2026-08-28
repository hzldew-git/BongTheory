/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryEndpointClass
import Bong.Dyadic.HilbertSymbol

/-!
# Norms from the unramified quadratic extension

The distinguished discriminant unit `Delta` defines the unramified quadratic
extension of a dyadic local field.  Its norm group consists exactly of the
elements of even valuation.  This local-field fact is kept as a reusable
interface, independently of any result in Beli (2019).
-/

namespace Bong.Dyadic

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The norm group of the distinguished unramified quadratic extension is
the subgroup of elements of even valuation. -/
class DyadicUnramifiedNormLaws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    [discriminant : DyadicDiscriminantClassLaws K] : Prop where
  discriminant_norm_iff_even_order (b : Kˣ) :
    IsQuadraticNorm K discriminant.discriminantUnit b ↔
      Even (ordUnit K b)

variable [discriminant : DyadicDiscriminantClassLaws K]
  [DyadicUnramifiedNormLaws K]

/-- Public form of the norm-group classification for the distinguished
discriminant unit. -/
theorem isQuadraticNorm_discriminant_iff_even_order (b : Kˣ) :
    IsQuadraticNorm K discriminant.discriminantUnit b ↔
      Even (ordUnit K b) :=
  DyadicUnramifiedNormLaws.discriminant_norm_iff_even_order b

/-- Hilbert-symbol form of the unramified norm-group classification. -/
theorem hilbertSymbol_discriminant_eq_one_iff_even_order (b : Kˣ) :
    hilbertSymbol K discriminant.discriminantUnit b = 1 ↔
      Even (ordUnit K b) := by
  rw [hilbertSymbol_eq_one_iff]
  exact isQuadraticNorm_discriminant_iff_even_order b

/-- An element of odd valuation is not a norm from the distinguished
unramified quadratic extension. -/
theorem hilbertSymbol_discriminant_ne_one_of_odd_order
    (b : Kˣ) (hodd : Odd (ordUnit K b)) :
    hilbertSymbol K discriminant.discriminantUnit b ≠ 1 := by
  intro h
  have heven :=
    (hilbertSymbol_discriminant_eq_one_iff_even_order b).mp h
  exact Int.not_even_iff_odd.mpr hodd heven

omit [DyadicUnramifiedNormLaws K] in
/-- A coefficient whose product with the discriminant is a square has the
same left Hilbert character as the discriminant. -/
theorem hilbertSymbol_eq_discriminant_of_isSquare_mul_discriminant
    [HilbertSymbolLaws K] {a b : Kˣ}
    (ha : IsSquare (a * discriminant.discriminantUnit)) :
    hilbertSymbol K a b =
      hilbertSymbol K discriminant.discriminantUnit b := by
  rcases ha with ⟨s, hs⟩
  have haeq : a = discriminant.discriminantUnit *
      (s * discriminant.discriminantUnit⁻¹) ^ 2 := by
    calc
      a = (a * discriminant.discriminantUnit) *
          discriminant.discriminantUnit⁻¹ := by simp
      _ = s ^ 2 * discriminant.discriminantUnit⁻¹ := by
        rw [hs, pow_two]
      _ = discriminant.discriminantUnit *
          (s * discriminant.discriminantUnit⁻¹) ^ 2 := by
        simp [pow_two, mul_assoc, mul_left_comm, mul_comm]
  rw [haeq, hilbertSymbol_mul_square_left]

/-- The discriminant square class cannot pair trivially with an odd-order
element. -/
theorem hilbertSymbol_ne_one_of_isSquare_mul_discriminant_of_odd_order
    [HilbertSymbolLaws K] {a b : Kˣ}
    (ha : IsSquare (a * discriminant.discriminantUnit))
    (hodd : Odd (ordUnit K b)) :
    hilbertSymbol K a b ≠ 1 := by
  rw [hilbertSymbol_eq_discriminant_of_isSquare_mul_discriminant ha]
  exact hilbertSymbol_discriminant_ne_one_of_odd_order b hodd

end Bong.Dyadic
