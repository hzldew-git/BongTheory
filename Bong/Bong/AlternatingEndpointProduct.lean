/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryEndpointProduct
import Bong.Bong.Beli2009ClassificationPropagation

/-!
# Products of alternating binary endpoints

An even prefix is grouped into adjacent binary pairs.  If each signed pair
is a square or becomes a square after multiplication by the fixed
discriminant unit, then the same dichotomy holds for the signed product of
the complete prefix.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- The signed determinant representative of the first `2 * pairs` BONG
values. -/
noncomputable def signedEvenPrefixProduct
    (b : BONG V q L n) (pairs : Nat) : Kˣ :=
  (-1) ^ pairs * b.prefixProduct (2 * pairs)

/-- Adding one adjacent pair multiplies the signed prefix product by the
negative of that pair's value product. -/
theorem signedEvenPrefixProduct_succ
    (b : BONG V q L n) (pairs : Nat) (hbound : 2 * pairs + 1 < n) :
    b.signedEvenPrefixProduct (pairs + 1) =
      b.signedEvenPrefixProduct pairs *
        (-(b.valueUnit ⟨2 * pairs, by omega⟩ *
          b.valueUnit ⟨2 * pairs + 1, hbound⟩)) := by
  unfold signedEvenPrefixProduct
  have hlength : 2 * (pairs + 1) = (2 * pairs + 1) + 1 := by omega
  rw [hlength]
  rw [b.prefixProduct_succ (2 * pairs + 1) hbound,
    b.prefixProduct_succ (2 * pairs) (by omega)]
  apply Units.ext
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg,
    Units.val_one]
  ring

/-- Pairwise endpoint alternatives propagate to the complete signed even
prefix. -/
theorem signedEvenPrefixProduct_endpoint_cases
    [laws : DyadicDiscriminantClassLaws K]
    (b : BONG V q L n) (pairs : Nat) (hbound : 2 * pairs ≤ n)
    (hendpoint : ∀ (t : Nat) (ht : t < pairs),
      IsSquare (-(b.valueUnit ⟨2 * t, by omega⟩ *
        b.valueUnit ⟨2 * t + 1, by omega⟩)) ∨
      IsSquare (-(b.valueUnit ⟨2 * t, by omega⟩ *
          b.valueUnit ⟨2 * t + 1, by omega⟩) *
        laws.discriminantUnit)) :
    IsSquare (b.signedEvenPrefixProduct pairs) ∨
      IsSquare (b.signedEvenPrefixProduct pairs *
        laws.discriminantUnit) := by
  induction pairs with
  | zero =>
      left
      refine ⟨1, ?_⟩
      simp [signedEvenPrefixProduct]
  | succ pairs ih =>
      have hboundPrevious : 2 * pairs ≤ n := by omega
      have hprevious := ih hboundPrevious (fun t ht =>
        hendpoint t (Nat.lt_succ_of_lt ht))
      have hcurrent := hendpoint pairs (Nat.lt_succ_self pairs)
      have hpairBound : 2 * pairs + 1 < n := by omega
      have hrecurrence := b.signedEvenPrefixProduct_succ pairs hpairBound
      let x := b.signedEvenPrefixProduct pairs
      let y := -(b.valueUnit ⟨2 * pairs, by omega⟩ *
        b.valueUnit ⟨2 * pairs + 1, hpairBound⟩)
      let delta := laws.discriminantUnit
      have hrecurrence' : b.signedEvenPrefixProduct (pairs + 1) = x * y := by
        simpa only [x, y] using hrecurrence
      rcases hprevious with hx | hxDelta
      · rcases hcurrent with hy | hyDelta
        · left
          rw [hrecurrence']
          exact hx.mul hy
        · right
          rw [hrecurrence']
          have hreorder : (x * y) * delta = x * (y * delta) := by
            group
          rw [hreorder]
          exact hx.mul hyDelta
      · rcases hcurrent with hy | hyDelta
        · right
          rw [hrecurrence']
          have hreorder : (x * y) * delta = (x * delta) * y := by
            apply Units.ext
            simp only [Units.val_mul]
            ring
          rw [hreorder]
          exact hxDelta.mul hy
        · left
          rw [hrecurrence']
          have hdeltaSquare : IsSquare (delta ^ 2) :=
            ⟨delta, by simp [pow_two]⟩
          have hquotient := (hxDelta.mul hyDelta).div hdeltaSquare
          have hreorder : ((x * delta) * (y * delta)) / delta ^ 2 =
              x * y := by
            apply Units.ext
            simp only [Units.val_div_eq_div_val, Units.val_mul,
              Units.val_pow_eq_pow_val]
            field_simp [Units.ne_zero delta]
          rw [hreorder] at hquotient
          exact hquotient

/-- Two objects with the same signed endpoint dichotomy have either square
product or discriminant-twisted square product. -/
theorem endpointSquareCases_product
    [laws : DyadicDiscriminantClassLaws K]
    (sign x y : Kˣ)
    (hx : IsSquare (sign * x) ∨
      IsSquare (sign * x * laws.discriminantUnit))
    (hy : IsSquare (sign * y) ∨
      IsSquare (sign * y * laws.discriminantUnit)) :
    IsSquare (x * y) ∨
      IsSquare (x * y * laws.discriminantUnit) := by
  rcases hx with hx | hxDelta
  · rcases hy with hy | hyDelta
    · left
      have hquotient := (hx.mul hy).div
        (show IsSquare (sign ^ 2) from ⟨sign, by simp [pow_two]⟩)
      have hcancel : ((sign * x) * (sign * y)) / sign ^ 2 = x * y := by
        apply Units.ext
        simp only [Units.val_div_eq_div_val, Units.val_mul,
          Units.val_pow_eq_pow_val]
        field_simp [Units.ne_zero sign]
      rw [hcancel] at hquotient
      exact hquotient
    · right
      have hquotient := (hx.mul hyDelta).div
        (show IsSquare (sign ^ 2) from ⟨sign, by simp [pow_two]⟩)
      have hcancel : ((sign * x) *
            (sign * y * laws.discriminantUnit)) / sign ^ 2 =
          x * y * laws.discriminantUnit := by
        apply Units.ext
        simp only [Units.val_div_eq_div_val, Units.val_mul,
          Units.val_pow_eq_pow_val]
        field_simp [Units.ne_zero sign]
      rw [hcancel] at hquotient
      exact hquotient
  · rcases hy with hy | hyDelta
    · right
      have hquotient := (hxDelta.mul hy).div
        (show IsSquare (sign ^ 2) from ⟨sign, by simp [pow_two]⟩)
      have hcancel : ((sign * x * laws.discriminantUnit) *
            (sign * y)) / sign ^ 2 =
          x * y * laws.discriminantUnit := by
        apply Units.ext
        simp only [Units.val_div_eq_div_val, Units.val_mul,
          Units.val_pow_eq_pow_val]
        field_simp [Units.ne_zero sign]
      rw [hcancel] at hquotient
      exact hquotient
    · left
      let common := sign * laws.discriminantUnit
      have hquotient := (hxDelta.mul hyDelta).div
        (show IsSquare (common ^ 2) from ⟨common, by simp [pow_two]⟩)
      have hcancel : ((sign * x * laws.discriminantUnit) *
            (sign * y * laws.discriminantUnit)) / common ^ 2 =
          x * y := by
        apply Units.ext
        simp only [common, Units.val_div_eq_div_val, Units.val_mul,
          Units.val_pow_eq_pow_val]
        field_simp [Units.ne_zero sign, Units.ne_zero laws.discriminantUnit]
      rw [hcancel] at hquotient
      exact hquotient

/-- The endpoint alternatives for two even prefixes give the corresponding
dichotomy for their ordinary product. -/
theorem signedEvenPrefixProduct_comparison_cases
    [laws : DyadicDiscriminantClassLaws K]
    (b : BONG V q L n) (c : BONG V q M n) (pairs : Nat)
    (hb : IsSquare (b.signedEvenPrefixProduct pairs) ∨
      IsSquare (b.signedEvenPrefixProduct pairs * laws.discriminantUnit))
    (hc : IsSquare (c.signedEvenPrefixProduct pairs) ∨
      IsSquare (c.signedEvenPrefixProduct pairs * laws.discriminantUnit)) :
    IsSquare (b.prefixProduct (2 * pairs) * c.prefixProduct (2 * pairs)) ∨
      IsSquare (b.prefixProduct (2 * pairs) * c.prefixProduct (2 * pairs) *
        laws.discriminantUnit) := by
  simpa only [signedEvenPrefixProduct] using
    endpointSquareCases_product ((-1 : Kˣ) ^ pairs)
      (b.prefixProduct (2 * pairs)) (c.prefixProduct (2 * pairs)) hb hc

end BONG

end Bong
