/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9318RankFourModels

/-!
# Deriving the scalar hypotheses in O'Meara 93:18(iii)

The two quaternary models in 93:18(iii) were first packaged with their
ordinary scalar-integrality hypotheses visible.  This file proves that all
of those hypotheses follow from the four pieces of data used in O'Meara's
argument:

* `a` and `b` are integral;
* `b O ⊆ a O` and `2 O ⊆ b O`;
* `alpha ∈ ab O`;
* `ord(a) + ord(b)` is odd.

In particular, this is a theorem about principal ideals, not a new local-law
or classification interface.
-/

namespace Bong

open Dyadic

namespace Lattice

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [laws : DyadicDiscriminantClassLaws K]

private theorem valuationUnit_one_add_of_maximal {c : K}
    (hc : IsInMaximalIdeal K c) : IsValuationUnit K (1 + c) := by
  rw [IsValuationUnit]
  have hlt : ord K (1 : K) < ord K c := by
    simpa only [ord_one, IsInMaximalIdeal] using hc
  simpa only [ord_one] using (ord K).map_add_eq_of_lt_left hlt

private theorem maximal_neg {c : K}
    (hc : IsInMaximalIdeal K c) : IsInMaximalIdeal K (-c) := by
  simpa only [IsInMaximalIdeal, ord_neg] using hc

private theorem maximal_sub {c d : K}
    (hc : IsInMaximalIdeal K c) (hd : IsInMaximalIdeal K d) :
    IsInMaximalIdeal K (c - d) := by
  simpa only [sub_eq_add_neg] using
    isInMaximalIdeal_add K hc (maximal_neg hd)

/-- If `2` lies in both principal ideals `a O` and `b O`, then `4 rho`
lies in `ab O` for every integral `rho`. -/
private theorem four_mul_mem_product_principalIdeal
    (a b rho : K) (hrho : rho ∈ IntegerRing K)
    (h2a : (2 : K) ∈ principalIdeal (K := K) a)
    (h2b : (2 : K) ∈ principalIdeal (K := K) b) :
    (4 : K) * rho ∈ principalIdeal (K := K) (a * b) := by
  rw [principalIdeal, Submodule.mem_span_singleton] at h2a h2b ⊢
  rcases h2a with ⟨ca, hca⟩
  rcases h2b with ⟨cb, hcb⟩
  let rhoO : IntegerRing K := ⟨rho, hrho⟩
  refine ⟨ca * cb * rhoO, ?_⟩
  have hcaField : algebraMap (IntegerRing K) K ca * a = 2 := by
    simpa only [Algebra.smul_def] using hca
  have hcbField : algebraMap (IntegerRing K) K cb * b = 2 := by
    simpa only [Algebra.smul_def] using hcb
  change
    (algebraMap (IntegerRing K) K ca *
        algebraMap (IntegerRing K) K cb * rho) * (a * b) =
      (4 : K) * rho
  calc
    (algebraMap (IntegerRing K) K ca *
          algebraMap (IntegerRing K) K cb * rho) * (a * b) =
        (algebraMap (IntegerRing K) K ca * a) *
          (algebraMap (IntegerRing K) K cb * b) * rho := by ring
    _ = (2 : K) * 2 * rho := by rw [hcaField, hcbField]
    _ = (4 : K) * rho := by ring

/-- Dividing an element of `ab O` by `a` produces an integral element in
`b O`.  The statement also covers the zero numerator. -/
private theorem div_left_mem_integerRing_and_ideal
    (a b : Kˣ) (x : K) (hb : (b : K) ∈ IntegerRing K)
    (hx : x ∈ principalIdeal (K := K) ((a : K) * (b : K))) :
    x * (a : K)⁻¹ ∈ IntegerRing K ∧
      principalIdeal (K := K) (x * (a : K)⁻¹) ≤
        principalIdeal (K := K) (b : K) := by
  rw [principalIdeal, Submodule.mem_span_singleton] at hx
  rcases hx with ⟨c, hc⟩
  have hxField : algebraMap (IntegerRing K) K c *
      ((a : K) * (b : K)) = x := by
    simpa only [Algebra.smul_def] using hc
  have hquotient : x * (a : K)⁻¹ =
      algebraMap (IntegerRing K) K c * (b : K) := by
    rw [← hxField]
    field_simp [Units.ne_zero a]
  constructor
  · rw [hquotient]
    exact (IntegerRing K).toSubring.mul_mem c.property hb
  · rw [principalIdeal, Submodule.span_singleton_le_iff_mem,
      hquotient]
    have hcoe : algebraMap (IntegerRing K) K c = (c : K) := rfl
    rw [hcoe]
    simpa only [mul_comm] using
      mul_mem_principalIdeal_of_mem_integerRing
        (K := K) (b : K) (c : K) c.property

/-- All ordinary model parameters in O'Meara 93:18(iii) follow from the
displayed ideal chain and `alpha ∈ ab O`. -/
noncomputable def omeara9318RankFourModelParametersOfAlphaIdeal
    (a b : Kˣ) (alpha : K)
    (halpha : IsInMaximalIdeal K alpha)
    (haIntegral : (a : K) ∈ IntegerRing K)
    (hbIntegral : (b : K) ∈ IntegerRing K)
    (hbLeA : principalIdeal (K := K) (b : K) ≤
      principalIdeal (K := K) (a : K))
    (hTwoLeB : principalIdeal (K := K) (2 : K) ≤
      principalIdeal (K := K) (b : K))
    (halphaAB : principalIdeal (K := K) alpha ≤
      principalIdeal (K := K) ((a : K) * (b : K)))
    (hodd : Odd (ordUnit K a + ordUnit K b)) :
    Omeara9318RankFourModelParameters K := by
  have hrhoIntegral : laws.rho ∈ IntegerRing K :=
    (mem_integerRing_iff K).2 laws.rho_isValuationUnit.ge
  have hTwoMemB : (2 : K) ∈ principalIdeal (K := K) (b : K) :=
    hTwoLeB (generator_mem_principalIdeal (K := K) (2 : K))
  have hTwoMemA : (2 : K) ∈ principalIdeal (K := K) (a : K) :=
    hbLeA hTwoMemB
  have hFourAB : (4 : K) * laws.rho ∈
      principalIdeal (K := K) ((a : K) * (b : K)) :=
    four_mul_mem_product_principalIdeal
      (a : K) (b : K) laws.rho hrhoIntegral hTwoMemA hTwoMemB
  have hFourBB : (4 : K) * laws.rho ∈
      principalIdeal (K := K) ((b : K) * (b : K)) :=
    four_mul_mem_product_principalIdeal
      (b : K) (b : K) laws.rho hrhoIntegral hTwoMemB hTwoMemB
  have halphaMem : alpha ∈
      principalIdeal (K := K) ((a : K) * (b : K)) :=
    halphaAB (generator_mem_principalIdeal (K := K) alpha)
  have hshiftMem : alpha - 4 * laws.rho ∈
      principalIdeal (K := K) ((a : K) * (b : K)) := by
    exact Submodule.sub_mem _ halphaMem (by simpa using hFourAB)
  have hFourMax : IsInMaximalIdeal K ((4 : K) * laws.rho) := by
    have hTwoRhoIntegral : (2 : K) * laws.rho ∈ IntegerRing K :=
      (IntegerRing K).toSubring.mul_mem (by norm_num) hrhoIntegral
    have h := isInMaximalIdeal_mul_isIntegral K
      (two_isInMaximalIdeal K)
      ((mem_integerRing_iff K).1 hTwoRhoIntegral)
    convert h using 1 <;> ring
  have hshiftMax : IsInMaximalIdeal K (alpha - 4 * laws.rho) :=
    maximal_sub halpha hFourMax
  have hjFacts := div_left_mem_integerRing_and_ideal
    a b (-alpha) hbIntegral (Submodule.neg_mem _ halphaMem)
  have hkLeftFacts := div_left_mem_integerRing_and_ideal
    a b (-(alpha - 4 * laws.rho)) hbIntegral
      (Submodule.neg_mem _ hshiftMem)
  have hkRightFacts := div_left_mem_integerRing_and_ideal
    b b (4 * laws.rho) hbIntegral (by simpa using hFourBB)
  exact
    { a := a
      b := b
      alpha := alpha
      alpha_maximal := halpha
      discriminant_unit := valuationUnit_one_add_of_maximal halpha
      shifted_discriminant_unit := by
        convert valuationUnit_one_add_of_maximal hshiftMax using 1 <;> ring
      a_integral := haIntegral
      b_integral := hbIntegral
      bIdeal_le_aIdeal := hbLeA
      twoIdeal_le_bIdeal := hTwoLeB
      jLeftTail_integral := by
        simpa only [neg_mul] using hjFacts.1
      kLeftTail_integral := hkLeftFacts.1
      kRightTail_integral := hkRightFacts.1
      jLeftTailIdeal_le_bIdeal := by
        simpa only [neg_mul] using hjFacts.2
      kLeftTailIdeal_le_bIdeal := hkLeftFacts.2
      kRightTailIdeal_le_bIdeal := hkRightFacts.2
      odd_orders := hodd }

end Lattice

end Bong
