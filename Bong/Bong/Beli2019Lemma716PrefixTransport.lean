/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma716OrderComplete
import Bong.Bong.DiagonalRepresentationDeterminant

/-!
# Beli (2019), Lemma 7.16: transport along isometric prefixes

Lemma 7.15 identifies the sufficiently long prefixes of the original BONG
and of the BONG constructed in Lemma 7.14.  This file turns that geometric
statement into the exact scalar identities needed in condition 2.1(ii).

The key point is elementary and contains no new local-field assumption: an
isometry of two equal-rank diagonal spaces is an invertible diagonal
representation, so their determinant products differ by a square.  Hence
every mixed quadratic defect using either prefix is the same.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n k j : Nat}

/-- An isometry between two canonical diagonal prefixes gives a diagonal
representation in the same direction. -/
theorem diagonalRepresents_prefixValues_of_prefix_isometric
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (k : Nat) (hk : k ≤ n + 1)
    (h : (a.prefixDiagonalSpace k hk).IsIsometric
      (b.prefixDiagonalSpace k hk)) :
    DiagonalRepresents (a.prefixValues k hk) (b.prefixValues k hk) := by
  rcases h with ⟨f⟩
  refine ⟨f.toLinearEquiv.toLinearMap, f.toLinearEquiv.injective, ?_⟩
  intro x
  have hquadratic := f.map_quadratic x
  change diagonalQuadratic (b.prefixValues k hk) (f.toLinearEquiv x) =
    diagonalQuadratic (a.prefixValues k hk) x
  simpa only [prefixDiagonalSpace,
    QuadraticSpace.finiteDiagonal_quadratic_apply] using hquadratic

/-- Isometric canonical prefixes have determinant representatives that
differ by an explicit square. -/
theorem exists_prefixProduct_eq_mul_square_of_prefix_isometric
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (k : Nat) (hk : k ≤ n + 1)
    (h : (a.prefixDiagonalSpace k hk).IsIsometric
      (b.prefixDiagonalSpace k hk)) :
    ∃ p : Kˣ, a.prefixProduct k = b.prefixProduct k * p ^ 2 := by
  have hrep := diagonalRepresents_prefixValues_of_prefix_isometric
    a b k hk h
  rcases DiagonalRepresents.exists_prod_eq_mul_square_of_sameRank hrep with
    ⟨p, hp⟩
  rw [a.prod_prefixValues_eq_coe_prefixProduct k hk,
    b.prod_prefixValues_eq_coe_prefixProduct k hk] at hp
  refine ⟨p, ?_⟩
  apply Units.ext
  simpa only [Units.val_mul, Units.val_pow_eq_pow_val] using hp

/-- Replacing the left prefix in a mixed defect by an isometric prefix does
not change its quadratic-defect order. -/
theorem defectOrder_mixedPrefix_eq_of_prefix_isometric
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1)) (epsilon : Kˣ)
    (k j : Nat) (hk : k ≤ n + 1)
    (h : (a.prefixDiagonalSpace k hk).IsIsometric
      (b.prefixDiagonalSpace k hk)) :
    defectOrder (K := K)
        (epsilon * a.prefixProduct k * c.prefixProduct j) =
      defectOrder (K := K)
        (epsilon * b.prefixProduct k * c.prefixProduct j) := by
  rcases a.exists_prefixProduct_eq_mul_square_of_prefix_isometric
      b k hk h with ⟨p, hp⟩
  rw [hp]
  have hfactor :
      epsilon * (b.prefixProduct k * p ^ 2) * c.prefixProduct j =
        (epsilon * b.prefixProduct k * c.prefixProduct j) * p ^ 2 := by
    ac_rfl
  rw [hfactor, defectOrder_mul_square]

/-- Equality of the left prefix cap and isometry of the left prefix transport
the corresponding capped mixed defect exactly. -/
theorem truncatedPrefixDefect_eq_of_prefix_isometric
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1)) (epsilon : Kˣ)
    (k j : Nat) (hk : k ≤ n + 1)
    (hcap : a.prefixAlphaCap k = b.prefixAlphaCap k)
    (h : (a.prefixDiagonalSpace k hk).IsIsometric
      (b.prefixDiagonalSpace k hk)) :
    a.truncatedPrefixDefect c epsilon k j =
      b.truncatedPrefixDefect c epsilon k j := by
  unfold truncatedPrefixDefect
  rw [a.defectOrder_mixedPrefix_eq_of_prefix_isometric
    b c epsilon k j hk h, hcap]

/-- At an internal prefix, equality of the alpha at the preceding boundary
is exactly equality of the prefix cap. -/
theorem prefixAlphaCap_eq_of_internal_alpha_eq
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (k : Nat) (hkPos : 0 < k) (hkLt : k < n + 1)
    (halpha : a.alphaValue ⟨k - 1, by omega⟩ =
      b.alphaValue ⟨k - 1, by omega⟩) :
    a.prefixAlphaCap k = b.prefixAlphaCap k := by
  rw [a.prefixAlphaCap_of_internal hkPos hkLt,
    b.prefixAlphaCap_of_internal hkPos hkLt, halpha]

end BONG.GoodBONG

end Bong
