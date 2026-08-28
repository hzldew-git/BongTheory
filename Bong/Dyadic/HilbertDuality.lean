/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Dyadic.CongruenceSubgroup
import Bong.Dyadic.UnitDefectClassification

/-!
# Hilbert duality on square classes

This file formalizes the character-theoretic content of Beli (2003), Lemmas
1.2(iii) and 1.3.  The concrete congruence criterion remains an explicit
dyadic local-field interface; all subgroup identities are proved from it and
the bimultiplicativity of the Hilbert symbol.
-/

namespace Bong.Dyadic

universe u v

variable (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The Hilbert character descends from `Kˣ` to field square classes. -/
noncomputable def squareClassHilbertCharacter [HilbertSymbolLaws K]
    (a : Kˣ) : SquareClass K →* ℤˣ :=
  QuotientGroup.lift (Subgroup.square Kˣ) (hilbertCharacter K a) (by
    intro s hs
    change IsSquare s at hs
    change hilbertSymbol K a s = 1
    exact hilbertSymbol_eq_one_of_isSquare_right K hs)

@[simp]
theorem squareClassHilbertCharacter_apply [HilbertSymbolLaws K]
    (a x : Kˣ) :
    squareClassHilbertCharacter K a (squareClass K x) =
      hilbertSymbol K a x := by
  apply QuotientGroup.lift_mk'

/-- The square-class norm subgroup is the kernel of its Hilbert character. -/
theorem quadraticNormSquareClassSubgroup_eq_ker [HilbertSymbolLaws K]
    (a : Kˣ) :
    quadraticNormSquareClassSubgroup K a =
      (squareClassHilbertCharacter K a).ker := by
  ext z
  obtain ⟨x, rfl⟩ := Quotient.exists_rep z
  constructor
  · rintro ⟨y, hy, hyx⟩
    change squareClass K y = squareClass K x at hyx
    change squareClassHilbertCharacter K a (squareClass K x) = 1
    rw [← hyx, squareClassHilbertCharacter_apply]
    exact (hilbertSymbol_eq_one_iff K a y).2 hy
  · intro hx
    refine ⟨x, ?_, rfl⟩
    apply (hilbertSymbol_eq_one_iff K a x).1
    change squareClassHilbertCharacter K a (squareClass K x) = 1 at hx
    rw [squareClassHilbertCharacter_apply] at hx
    exact hx

section CharacterAlgebra

variable {G : Type v} [CommGroup G]

/-- For two quadratic characters, inclusion of one restricted kernel in the
other has exactly the two alternatives appearing in Beli's Lemma 1.3(i). -/
theorem ker_inf_le_ker_iff (f g : G →* ℤˣ) (H : Subgroup G) :
    f.ker ⊓ H ≤ g.ker ↔ H ≤ g.ker ∨ H ≤ (f * g).ker := by
  constructor
  · intro h
    by_cases htrivial : H ≤ g.ker
    · exact Or.inl htrivial
    · apply Or.inr
      rcases SetLike.not_le_iff_exists.mp htrivial with
        ⟨x, hxH, hxg⟩
      have hgx : g x = -1 :=
        (Int.units_eq_one_or (g x)).resolve_left hxg
      have hfx : f x = -1 := by
        rcases Int.units_eq_one_or (f x) with hfx | hfx
        · have hxker : x ∈ f.ker ⊓ H := ⟨hfx, hxH⟩
          exact (hxg (h hxker)).elim
        · exact hfx
      intro y hyH
      change f y * g y = 1
      rcases Int.units_eq_one_or (f y) with hfy | hfy
      · have hyker : y ∈ f.ker ⊓ H := ⟨hfy, hyH⟩
        have hgy : g y = 1 := h hyker
        rw [hfy, hgy, one_mul]
      · have hxyker : x * y ∈ f.ker ⊓ H := by
          constructor
          · change f (x * y) = 1
            rw [map_mul, hfx, hfy]
            norm_num
          · exact H.mul_mem hxH hyH
        have hgxy : g (x * y) = 1 := h hxyker
        rw [map_mul, hgx] at hgxy
        have hgy : g y = -1 := by
          rcases Int.units_eq_one_or (g y) with hgy | hgy
          · rw [hgy] at hgxy
            norm_num at hgxy
          · exact hgy
        rw [hfy, hgy]
        norm_num
  · rintro (hg | hfg)
    · exact fun z hz => hg hz.2
    · intro z hz
      have hzfg := hfg hz.2
      change f z * g z = 1 at hzfg
      change g z = 1
      rw [show f z = 1 from hz.1] at hzfg
      simpa using hzfg

/-- Equality of two restricted quadratic kernels is detected by the product
character, which is Beli's Lemma 1.3(ii) in character form. -/
theorem inf_ker_eq_inf_ker_iff (f g : G →* ℤˣ) (H : Subgroup G) :
    H ⊓ f.ker = H ⊓ g.ker ↔ H ≤ (f * g).ker := by
  constructor
  · intro heq y hyH
    change f y * g y = 1
    rcases Int.units_eq_one_or (f y) with hfy | hfy
    · have hyLeft : y ∈ H ⊓ f.ker := ⟨hyH, hfy⟩
      have hgy : g y = 1 := (show y ∈ H ⊓ g.ker from heq ▸ hyLeft).2
      rw [hfy, hgy, one_mul]
    · rcases Int.units_eq_one_or (g y) with hgy | hgy
      · have hyRight : y ∈ H ⊓ g.ker := ⟨hyH, hgy⟩
        have hfyOne : f y = 1 :=
          (show y ∈ H ⊓ f.ker from heq.symm ▸ hyRight).2
        rw [hfyOne] at hfy
        norm_num at hfy
      · rw [hfy, hgy]
        norm_num
  · intro hfg
    ext y
    constructor
    · rintro ⟨hyH, hfy⟩
      refine ⟨hyH, ?_⟩
      have hy := hfg hyH
      change f y * g y = 1 at hy
      rw [hfy] at hy
      simpa using hy
    · rintro ⟨hyH, hgy⟩
      refine ⟨hyH, ?_⟩
      have hy := hfg hyH
      change f y * g y = 1 at hy
      rw [hgy, mul_one] at hy
      exact hy

/-- A subgroup not killed by a quadratic character supplies the missing
coset of its kernel. -/
theorem inf_ker_sup_eq_of_le_of_not_le
    (f : G →* ℤˣ) (H J : Subgroup G)
    (hJ : J ≤ H) (hnot : ¬J ≤ f.ker) :
    (H ⊓ f.ker) ⊔ J = H := by
  apply le_antisymm
  · exact sup_le inf_le_left hJ
  · rcases SetLike.not_le_iff_exists.mp hnot with ⟨x, hxJ, hfx⟩
    have hfxNeg : f x = -1 :=
      (Int.units_eq_one_or (f x)).resolve_left hfx
    intro y hyH
    rcases Int.units_eq_one_or (f y) with hfy | hfy
    · exact Subgroup.mem_sup.mpr ⟨y, ⟨hyH, hfy⟩, 1,
        J.one_mem, by simp⟩
    · have hyx : y * x⁻¹ ∈ H ⊓ f.ker := by
        constructor
        · exact H.mul_mem hyH (H.inv_mem (hJ hxJ))
        · change f (y * x⁻¹) = 1
          rw [map_mul, map_inv, hfy, hfxNeg]
          norm_num
      exact Subgroup.mem_sup.mpr ⟨y * x⁻¹, hyx, x, hxJ, by group⟩

end CharacterAlgebra

/-- The remaining local congruence input from Beli (2003), Lemma 1.2(iii). -/
class BeliHilbertCongruenceLaws : Prop extends HilbertSymbolLaws K where
  principalUnit_le_norm_iff (a : Kˣ) (k : Nat) (hk : 0 < k) :
    principalUnitSquareClassSubgroup K k ≤
        quadraticNormSquareClassSubgroup K a ↔
      ((2 * ramificationIndex K : Nat) : ℕ∞) <
        quadraticDefect K a + k

/-- Public form of Beli (2003), Lemma 1.2(iii). -/
theorem principalUnitSquareClassSubgroup_le_quadraticNorm_iff
    [BeliHilbertCongruenceLaws K] (a : Kˣ) (k : Nat) (hk : 0 < k) :
    principalUnitSquareClassSubgroup K k ≤
        quadraticNormSquareClassSubgroup K a ↔
      ((2 * ramificationIndex K : Nat) : ℕ∞) <
        quadraticDefect K a + k :=
  BeliHilbertCongruenceLaws.principalUnit_le_norm_iff a k hk

/-- The genuine depth-zero principal-unit layer is the valuation-unit
square-class subgroup.  Its norm criterion is the non-strict endpoint form
`2e ≤ d(a)`, obtained by identifying depth zero with depth one. -/
theorem principalUnitSquareClassSubgroup_zero_le_quadraticNorm_iff
    [BeliHilbertCongruenceLaws K] (a : Kˣ) :
    principalUnitSquareClassSubgroup K 0 ≤
        quadraticNormSquareClassSubgroup K a ↔
      ((2 * ramificationIndex K : Nat) : ℕ∞) ≤
        quadraticDefect K a := by
  rw [principalUnitSquareClassSubgroup_zero_eq_one,
    principalUnitSquareClassSubgroup_le_quadraticNorm_iff K a 1 (by omega)]
  cases hdefect : quadraticDefect K a with
  | top =>
      constructor
      · intro _
        exact le_top
      · intro _
        simpa using ENat.coe_lt_top (2 * ramificationIndex K)
  | coe d =>
      norm_cast
      omega

/-- Uniform norm criterion for the actual principal-unit filtration.  The
only special case is depth zero, where the inequality is non-strict. -/
theorem principalUnitSquareClassSubgroup_le_quadraticNorm_iff_all
    [BeliHilbertCongruenceLaws K] (a : Kˣ) (k : Nat) :
    principalUnitSquareClassSubgroup K k ≤
        quadraticNormSquareClassSubgroup K a ↔
      if k = 0 then
        ((2 * ramificationIndex K : Nat) : ℕ∞) ≤
          quadraticDefect K a
      else
        ((2 * ramificationIndex K : Nat) : ℕ∞) <
          quadraticDefect K a + k := by
  by_cases hk : k = 0
  · subst k
    simpa using
      (principalUnitSquareClassSubgroup_zero_le_quadraticNorm_iff
        (K := K) a)
  · simpa [hk] using
      (principalUnitSquareClassSubgroup_le_quadraticNorm_iff
        (K := K) a k (Nat.pos_of_ne_zero hk))

/-- Beli (2003), Lemma 1.3(i), for square-class norm groups. -/
theorem quadraticNorm_inf_le_quadraticNorm_iff
    [BeliHilbertCongruenceLaws K]
    (a b : Kˣ) (H : Subgroup (SquareClass K)) :
    quadraticNormSquareClassSubgroup K a ⊓ H ≤
        quadraticNormSquareClassSubgroup K b ↔
      H ≤ quadraticNormSquareClassSubgroup K b ∨
        H ≤ quadraticNormSquareClassSubgroup K (a * b) := by
  have hcharacter : squareClassHilbertCharacter K (a * b) =
      squareClassHilbertCharacter K a *
        squareClassHilbertCharacter K b := by
    ext z
    change (hilbertSymbol K (a * b) z : Int) =
      (hilbertSymbol K a z : Int) * (hilbertSymbol K b z : Int)
    rw [hilbertSymbol_mul_left]
    rfl
  rw [quadraticNormSquareClassSubgroup_eq_ker,
    quadraticNormSquareClassSubgroup_eq_ker,
    quadraticNormSquareClassSubgroup_eq_ker,
    ker_inf_le_ker_iff, hcharacter]

/-- Beli (2003), Lemma 1.3(ii), for square-class norm groups. -/
theorem quadraticNorm_inf_eq_quadraticNorm_inf_iff
    [BeliHilbertCongruenceLaws K]
    (a b : Kˣ) (H : Subgroup (SquareClass K)) :
    H ⊓ quadraticNormSquareClassSubgroup K a =
        H ⊓ quadraticNormSquareClassSubgroup K b ↔
      H ≤ quadraticNormSquareClassSubgroup K (a * b) := by
  have hcharacter : squareClassHilbertCharacter K (a * b) =
      squareClassHilbertCharacter K a *
        squareClassHilbertCharacter K b := by
    ext z
    change (hilbertSymbol K (a * b) z : Int) =
      (hilbertSymbol K a z : Int) * (hilbertSymbol K b z : Int)
    rw [hilbertSymbol_mul_left]
    rfl
  rw [quadraticNormSquareClassSubgroup_eq_ker,
    quadraticNormSquareClassSubgroup_eq_ker,
    quadraticNormSquareClassSubgroup_eq_ker,
    inf_ker_eq_inf_ker_iff, hcharacter]

end Bong.Dyadic
