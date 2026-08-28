/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Dyadic.HilbertDuality
import Bong.Bong.HilbertDefectChoiceProof

/-!
# The principal-unit Hilbert orthogonality criterion

This proves Beli (2003), Lemma 1.2(iii), for its stated positive depths.
The forward implication uses the explicit complementary-defect negative
Hilbert partner constructed in `HilbertDefectChoiceProof`; a nonzero-defect
partner is then normalized to a valuation unit without changing its square
class or Hilbert sign.  The reverse implication is the already proved local
square theorem applied to a principal-unit representative.

Depth zero is deliberately absent: Beli declares `(1 + p^0)F^times^2` to be
all field square classes, whereas the genuine depth-zero principal-unit
subgroup in this project is the valuation-unit subgroup.
-/

namespace Bong.Dyadic

open Bong

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- Normalize a nonzero-defect class to a valuation unit while preserving
its defect and its Hilbert pairing with a fixed first argument. -/
private theorem exists_valuationUnit_same_defect_same_hilbert_local
    (a x : Kˣ) (hx : quadraticDefect K x ≠ 0) :
    ∃ u : Kˣ,
      IsValuationUnit K (u : K) ∧
        quadraticDefect K u = quadraticDefect K x ∧
        hilbertSymbol K a u = hilbertSymbol K a x := by
  have heven : Even (ordUnit K x) := by
    rcases Int.even_or_odd (ordUnit K x) with heven | hodd
    · exact heven
    · exact (hx (quadraticDefect_eq_zero_of_odd_ordUnit x hodd)).elim
  rcases heven with ⟨m, hm⟩
  let s : Kˣ := uniformizerPowerUnit K m
  let u : Kˣ := x / s ^ 2
  have hsOrder : ordUnit K s = m :=
    ordUnit_uniformizerPowerUnit (K := K) m
  have huOrder : ordUnit K u = 0 := by
    dsimp only [u]
    rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv, ordUnit_pow,
      hsOrder]
    omega
  have huUnit : IsValuationUnit K (u : K) :=
    (isValuationUnit_iff_ordUnit_eq_zero K u).2 huOrder
  have hfactor : u * s ^ 2 = x := by
    dsimp only [u]
    simp
  refine ⟨u, huUnit, ?_, ?_⟩
  · calc
      quadraticDefect K u = quadraticDefect K (u * s ^ 2) :=
        (quadraticDefect_mul_square K u s).symm
      _ = quadraticDefect K x := congrArg (quadraticDefect K) hfactor
  · calc
      hilbertSymbol K a u = hilbertSymbol K a (u * s ^ 2) :=
        (hilbertSymbol_mul_square_right (K := K) a u s).symm
      _ = hilbertSymbol K a x := congrArg (hilbertSymbol K a) hfactor

private theorem principalUnit_le_quadraticNorm_iff_proved
    (a : Kˣ) (k : Nat) (hk : 0 < k) :
    principalUnitSquareClassSubgroup K k ≤
        quadraticNormSquareClassSubgroup K a ↔
      ((2 * ramificationIndex K : Nat) : ℕ∞) <
        quadraticDefect K a + k := by
  constructor
  · intro hsubgroup
    by_contra hnot
    have hsumLe : quadraticDefect K a + (k : ℕ∞) ≤
        ((2 * ramificationIndex K : Nat) : ℕ∞) :=
      le_of_not_gt hnot
    have haNotSquare : ¬IsSquare a := by
      intro haSquare
      have haTop := quadraticDefect_eq_top_of_isSquare K haSquare
      have htopLe : (⊤ : ℕ∞) ≤
          ((2 * ramificationIndex K : Nat) : ℕ∞) := by
        simpa [haTop] using hsumLe
      exact ENat.coe_ne_top _ (top_unique htopLe)
    have haFinite : quadraticDefect K a ≠ ⊤ := by
      intro haTop
      exact haNotSquare
        ((quadraticDefect_eq_top_iff_isSquare (K := K) a).mp haTop)
    rcases Bong.BONG.exists_complementary_defect_hilbert_neg_proved
        a haNotSquare with ⟨c, hcSum, hcNeg⟩
    have hkLe : (k : ℕ∞) ≤ quadraticDefect K c := by
      apply (ENat.add_le_add_iff_left haFinite).mp
      rw [hcSum]
      exact hsumLe
    have hcNonzero : quadraticDefect K c ≠ 0 := by
      intro hcZero
      rw [hcZero] at hkLe
      have hkNonpos : k ≤ 0 := by exact_mod_cast hkLe
      have hkZero : k = 0 := Nat.eq_zero_of_le_zero hkNonpos
      omega
    rcases exists_valuationUnit_same_defect_same_hilbert_local
        a c hcNonzero with ⟨u, huUnit, huDefect, huHilbert⟩
    have huNeg : hilbertSymbol K a u = -1 :=
      huHilbert.trans hcNeg
    let uu : valuationUnitSubgroup K := ⟨u, huUnit⟩
    have huDepth : (k : ℕ∞) ≤ quadraticDefect K (u : Kˣ) := by
      rw [huDefect]
      exact hkLe
    have huUnitClass : valuationUnitClassHom K uu ∈
        principalUnitValuationClassSubgroup K k :=
      valuationUnitClassHom_mem_principalUnitValuationClassSubgroup_of_defect
        K uu k huDepth
    have huPrincipal : squareClass K u ∈
        principalUnitSquareClassSubgroup K k := by
      rw [← valuationUnitClassSubgroupSquareImage_principalUnit K k]
      exact valuationUnitClassToSquareClass_mem_image K huUnitClass
    have huNorm := hsubgroup huPrincipal
    rw [quadraticNormSquareClassSubgroup_eq_ker] at huNorm
    change squareClassHilbertCharacter K a (squareClass K u) = 1 at huNorm
    rw [squareClassHilbertCharacter_apply, huNeg] at huNorm
    norm_num at huNorm
  · intro hstrict z hz
    rcases hz with ⟨p, hp, rfl⟩
    let pu : valuationUnitSubgroup K := ⟨p, hp.1⟩
    have hpUnitClass : valuationUnitClassHom K pu ∈
        principalUnitValuationClassSubgroup K k := by
      exact ⟨pu, hp, rfl⟩
    have hpDepth : (k : ℕ∞) ≤ quadraticDefect K (p : Kˣ) :=
      natCast_le_quadraticDefect_of_unitClass_mem pu k hpUnitClass
    have hsumMono : quadraticDefect K a + (k : ℕ∞) ≤
        quadraticDefect K a + quadraticDefect K p := by
      simpa only [add_comm] using
        (add_le_add_left hpDepth (quadraticDefect K a))
    have hdefect : ((2 * ramificationIndex K : Nat) : ℕ∞) <
        quadraticDefect K a + quadraticDefect K p :=
      hstrict.trans_le hsumMono
    refine ⟨p, ?_, rfl⟩
    exact (hilbertSymbol_eq_one_iff K a p).1
      (hilbertSymbol_eq_one_of_defect_add_gt_two_mul_e
        (K := K) hdefect)

noncomputable instance beliHilbertCongruenceLawsProved :
    BeliHilbertCongruenceLaws K where
  toHilbertSymbolLaws := inferInstance
  principalUnit_le_norm_iff :=
    principalUnit_le_quadraticNorm_iff_proved

end Bong.Dyadic
