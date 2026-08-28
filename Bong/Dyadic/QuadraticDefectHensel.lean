/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Dyadic.QuadraticDefect
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Valuation.Discrete.Basic

/-!
# The dyadic square theorem from Hensel's lemma

This file closes `QuadraticDefectLaws` for every field carrying the project's
`DyadicContext`.  If a principal unit differs from one to order greater than
`2e`, divide its error by four and apply Hensel's lemma to `X^2 + X - c` over
the normalized valuation ring.  The resulting square theorem gives both the
finite `2e` bound for nonsquares and the characterization of infinite defect.
-/

namespace Bong.Dyadic

open scoped Pointwise
open Polynomial

variable (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

noncomputable instance normalizedValuationRingHenselian :
    HenselianRing
      (AddValuation.toValuation (ord K)).valuationSubring
      (IsLocalRing.maximalIdeal
        (AddValuation.toValuation (ord K)).valuationSubring) := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  haveI : IsTopologicalDivisionRing K := inferInstance
  let v := AddValuation.toValuation (ord K)
  let A := v.valuationSubring
  change HenselianRing A (IsLocalRing.maximalIdeal A)
  have hA : A = (ValuativeRel.valuation K).valuationSubring := by
    apply (Valuation.isEquiv_iff_valuationSubring _ _).mp
    exact ValuativeRel.isEquiv _ _
  letI : CompactSpace A := by
    rw [hA]
    change CompactSpace (ValuativeRel.valuation K).integer
    infer_instance
  letI : IsPrincipalIdealRing A :=
    Valuation.valuationSubring_isPrincipalIdealRing v
  letI : IsTopologicalRing A :=
    Subring.instIsTopologicalRing A.toSubring
  let I := IsLocalRing.maximalIdeal A
  change HenselianRing A I
  letI : IsAdicComplete I A := by
    refine { prec' := ?_ }
    intro f hf
    let S n : Set A := f n +ᵥ ((I ^ n : Ideal A) : Set A)
    have hS n : S (n + 1) ⊆ S n := by
      apply (Set.vadd_set_subset_vadd_set_iff.mpr
        (Ideal.pow_le_pow_right n.le_succ)).trans
      simpa [S] using (hf n.le_succ).symm
    have h n : IsClosed (S n) :=
      (IsNoetherianRing.isClosed_ideal (I ^ n)).vadd (f n)
    obtain ⟨a, ha⟩ :=
      (h 0).isCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
        S hS (by simp [S]) h
    refine ⟨a, fun n => ?_⟩
    obtain ⟨b, hb, rfl⟩ := Set.mem_iInter.mp ha n
    simpa [SModEq.sub_mem] using hb
  infer_instance

theorem mem_henselValuationRing_iff {x : K} :
    x ∈ (AddValuation.toValuation (ord K)).valuationSubring ↔
      0 ≤ ord K x := by
  change
    Multiplicative.ofAdd (OrderDual.toDual (ord K x)) ≤
        Multiplicative.ofAdd (OrderDual.toDual 0) ↔
      0 ≤ ord K x
  simp only [Multiplicative.ofAdd_le, OrderDual.toDual_le_toDual]

private theorem ord_two_sq :
    ord K ((2 : K) ^ 2) =
      (((2 * ramificationIndex K : ℕ) : ℤ) : WithTop ℤ) := by
  rw [ord_pow, ← ramificationIndex_spec]
  have htwo : 2 * ramificationIndex K =
      ramificationIndex K + ramificationIndex K := by omega
  rw [htwo]
  norm_num [two_nsmul]

/-- A principal unit strictly deeper than `2e` is a square. -/
theorem isSquare_of_ord_sub_one_gt_two_mul_e
    (u : Kˣ)
    (hdeep :
      (((2 * ramificationIndex K : ℕ) : ℤ) : WithTop ℤ) <
        ord K ((u : K) - 1)) :
    IsSquare u := by
  let v := AddValuation.toValuation (ord K)
  let A := v.valuationSubring
  let cK : K := ((u : K) - 1) / (2 : K) ^ 2
  have hcOrder :
      ord K cK = ord K ((u : K) - 1) +
        -
        (((2 * ramificationIndex K : ℕ) : ℤ) : WithTop ℤ) := by
    simp only [cK, div_eq_mul_inv, ord_mul, AddValuation.map_inv,
      ord_two_sq]
  have hcPos : 0 < ord K cK := by
    rw [hcOrder]
    generalize hq : ord K ((u : K) - 1) = d at hdeep
    cases d with
    | top => simp
    | coe z =>
        norm_cast at hdeep ⊢
        omega
  let c : A :=
    ⟨cK, (mem_henselValuationRing_iff K).2 hcPos.le⟩
  have hcMax : c ∈ IsLocalRing.maximalIdeal A := by
    apply (Valuation.mem_maximalIdeal_iff K v).mpr
    change Multiplicative.ofAdd (OrderDual.toDual (ord K cK)) <
      Multiplicative.ofAdd (OrderDual.toDual 0)
    simpa only [Multiplicative.ofAdd_lt,
      OrderDual.toDual_lt_toDual] using hcPos
  let f : A[X] := Polynomial.X ^ 2 + Polynomial.X - Polynomial.C c
  have hfMonic : f.Monic := by
    dsimp [f]
    rw [add_sub_assoc]
    apply monic_X_pow_add
    simp
  have hfZero : f.eval 0 ∈ IsLocalRing.maximalIdeal A := by
    simpa [f] using (IsLocalRing.maximalIdeal A).neg_mem hcMax
  have hfDerivative : IsUnit (f.derivative.eval 0) := by
    have hderivative : f.derivative.eval 0 = 1 := by
      simp [f]
    rw [hderivative]
    exact isUnit_one
  obtain ⟨z, hzRoot, _⟩ :=
    HenselianRing.is_henselian f hfMonic 0 hfZero
      (hfDerivative.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)))
  have hz : (z : K) ^ 2 + (z : K) = cK := by
    have hzA : z ^ 2 + z - c = 0 := by
      simpa [f] using hzRoot
    have hzA' : z ^ 2 + z = c := sub_eq_zero.mp hzA
    have hzK := congrArg (fun a : A => (a : K)) hzA'
    simpa [c] using hzK
  let y : K := 1 + 2 * (z : K)
  have hySq : y ^ 2 = (u : K) := by
    dsimp [y]
    rw [show (u : K) = 1 + (2 : K) ^ 2 * cK by
      simp only [cK]
      field_simp
      ring]
    rw [← hz]
    ring
  have hyNe : y ≠ 0 := by
    intro hy
    have : (u : K) = 0 := by simpa [hy] using hySq.symm
    exact Units.ne_zero u this
  refine ⟨Units.mk0 y hyNe, ?_⟩
  apply Units.ext
  simpa [pow_two] using hySq.symm

/-- A relative quadratic approximation deeper than `2e` forces a square. -/
theorem isSquare_of_quadraticDefect_gt_two_mul_e
    (a : Kˣ)
    (hdefect :
      ((2 * ramificationIndex K : ℕ) : ℕ∞) < quadraticDefect K a) :
    IsSquare a := by
  let depth : ℕ := 2 * ramificationIndex K + 1
  have hdepth : (depth : ℕ∞) ≤ quadraticDefect K a := by
    have hnext :=
      (ENat.add_one_le_iff
        (ENat.coe_ne_top (2 * ramificationIndex K))).2 hdefect
    simpa [depth] using hnext
  rcases (isQuadraticApproximation_iff_le_defect K).2 hdepth with
    ⟨x, hx⟩
  have herror :
      (((2 * ramificationIndex K : ℕ) : ℤ) : WithTop ℤ) <
        ord K (1 - x ^ 2 / (a : K)) := by
    have hstep :
        (((2 * ramificationIndex K : ℕ) : ℤ) : WithTop ℤ) <
          (depth : WithTop ℤ) := by
      exact_mod_cast Nat.lt_succ_self (2 * ramificationIndex K)
    exact hstep.trans_le hx
  have hxNe : x ≠ 0 := by
    intro hzero
    subst x
    norm_num at herror
    have hnonneg :
        (0 : WithTop ℤ) ≤
          (((2 * ramificationIndex K : ℕ) : ℤ) : WithTop ℤ) := by
      exact_mod_cast Nat.zero_le (2 * ramificationIndex K)
    exact (not_lt_of_ge hnonneg) herror
  let xu : Kˣ := Units.mk0 x hxNe
  let r : Kˣ := xu ^ 2 / a
  have hrVal : (r : K) = x ^ 2 / (a : K) := by
    dsimp only [r]
    rw [Units.val_div_eq_div_val, Units.val_pow_eq_pow_val]
    rfl
  have hrOrder :
      ord K ((r : K) - 1) = ord K (1 - x ^ 2 / (a : K)) := by
    have heq : x ^ 2 / (a : K) - 1 =
        -(1 - x ^ 2 / (a : K)) :=
      (neg_sub 1 (x ^ 2 / (a : K))).symm
    rw [hrVal, heq, ord_neg]
  have hrSquare : IsSquare r :=
    isSquare_of_ord_sub_one_gt_two_mul_e K r (hrOrder ▸ herror)
  have hxSquare : IsSquare (xu ^ 2) := by
    refine ⟨xu, ?_⟩
    exact pow_two xu
  have hproduct : IsSquare (r⁻¹ * xu ^ 2) :=
    hrSquare.inv.mul hxSquare
  simpa [r] using hproduct

/-- The concrete relative defect satisfies the dyadic local square theorem. -/
noncomputable instance quadraticDefectLawsOfHensel :
    QuadraticDefectLaws K where
  eq_top_iff_isSquare a := by
    constructor
    · intro htop
      apply isSquare_of_quadraticDefect_gt_two_mul_e K a
      rw [htop]
      exact ENat.coe_lt_top _
    · exact quadraticDefect_eq_top_of_isSquare K
  le_two_mul_e_of_not_isSquare a ha := by
    by_contra hle
    have hgt :
        ((2 * ramificationIndex K : ℕ) : ℕ∞) < quadraticDefect K a :=
      lt_of_not_ge hle
    exact ha (isSquare_of_quadraticDefect_gt_two_mul_e K a hgt)

end Bong.Dyadic
