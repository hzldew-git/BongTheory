import Bong.Dyadic.QuadraticDefectHensel

namespace Bong.Dyadic

open scoped Pointwise
open Polynomial

variable (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

set_option maxHeartbeats 4000000 in

/-- Newton's two-segment criterion for the quadratic equation
`D b² - d b + t = 0`.  If `t/d` is integral and `ord(Dt) > 2 ord(d)`,
Hensel lifting supplies an integral root.  This is the root calculation used
in the high-defect branch of Beli (2003), Lemma 3.11. -/
theorem exists_integral_quadratic_root_of_newton
    (D d t : Kˣ)
    (hdt : ordUnit K d ≤ ordUnit K t)
    (hnewton : 2 * ordUnit K d < ordUnit K D + ordUnit K t) :
    ∃ b : K, 0 ≤ ord K b ∧
      (D : K) * b ^ 2 - (d : K) * b + (t : K) = 0 := by
  let v := AddValuation.toValuation (ord K)
  let A := v.valuationSubring
  let δu : Kˣ := D * t / d ^ 2
  have hδOrder : ordUnit K δu =
      ordUnit K D + ordUnit K t - 2 * ordUnit K d := by
    dsimp [δu]
    rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv, ordUnit_mul, ordUnit_pow]
    omega
  have hδPos : 0 < ordUnit K δu := by
    rw [hδOrder]
    omega
  have hδFieldPos : 0 < ord K (δu : K) := by
    rw [← coe_ordUnit]
    exact_mod_cast hδPos
  let δ : A :=
    ⟨(δu : K), (mem_henselValuationRing_iff K).2 hδFieldPos.le⟩
  have hδMax : δ ∈ IsLocalRing.maximalIdeal A := by
    apply (Valuation.mem_maximalIdeal_iff K v).mpr
    change Multiplicative.ofAdd (OrderDual.toDual (ord K (δu : K))) <
      Multiplicative.ofAdd (OrderDual.toDual 0)
    simpa only [Multiplicative.ofAdd_lt,
      OrderDual.toDual_lt_toDual] using hδFieldPos
  let f : A[X] :=
    Polynomial.X ^ 2 + Polynomial.C (2 * δ - 1) * Polynomial.X +
      Polynomial.C (δ ^ 2)
  have hfMonic : f.Monic := by
    dsimp [f]
    monicity
    all_goals norm_num
  have hfZero : f.eval 0 ∈ IsLocalRing.maximalIdeal A := by
    have hsq : δ ^ 2 ∈ IsLocalRing.maximalIdeal A :=
      by simpa [pow_two] using
        (IsLocalRing.maximalIdeal A).mul_mem_left δ hδMax
    simpa [f] using hsq
  have htwoδMax : 2 * δ ∈ IsLocalRing.maximalIdeal A :=
    (IsLocalRing.maximalIdeal A).mul_mem_left 2 hδMax
  have hcoefUnit : IsUnit (2 * δ - 1) := by
    by_contra hnotUnit
    have hmem : 2 * δ - 1 ∈ IsLocalRing.maximalIdeal A :=
      by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        exact hnotUnit
    have hone : (1 : A) ∈ IsLocalRing.maximalIdeal A := by
      have hsub := (IsLocalRing.maximalIdeal A).sub_mem htwoδMax hmem
      simpa using hsub
    exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top
      ((Ideal.eq_top_iff_one _).mpr hone)
  have hfDerivative : IsUnit
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)
        (f.derivative.eval 0)) := by
    have heval : f.derivative.eval 0 = 2 * δ - 1 := by
      simp [f, pow_two]
    rw [heval]
    exact hcoefUnit.map _
  obtain ⟨w, hwRoot, hwMax⟩ :=
    HenselianRing.is_henselian f hfMonic 0 hfZero hfDerivative
  have hwEquation :
      (w : K) ^ 2 + ((2 : K) * (δu : K) - 1) * (w : K) +
        (δu : K) ^ 2 = 0 := by
    have hwA : w ^ 2 + (2 * δ - 1) * w + δ ^ 2 = 0 := by
      simpa [f] using hwRoot
    exact congrArg (fun z : A => (z : K)) hwA
  have hwPos : 0 < ord K (w : K) := by
    have hwMax' : w ∈ IsLocalRing.maximalIdeal A := by simpa using hwMax
    have := (Valuation.mem_maximalIdeal_iff K v).mp hwMax'
    change Multiplicative.ofAdd (OrderDual.toDual (ord K (w : K))) <
      Multiplicative.ofAdd (OrderDual.toDual 0) at this
    simpa only [Multiplicative.ofAdd_lt,
      OrderDual.toDual_lt_toDual] using this
  have hwNe : (w : K) ≠ 0 := by
    intro hw
    have hδNe : (δu : K) ^ 2 ≠ 0 :=
      pow_ne_zero 2 (Units.ne_zero δu)
    apply hδNe
    simpa [hw] using hwEquation
  have hcoefOrder : ord K ((2 : K) * (δu : K) - 1) = 0 := by
    have htwoδPos : 0 < ord K ((2 : K) * (δu : K)) := by
      rw [ord_mul, ← ramificationIndex_spec, ← coe_ordUnit]
      exact_mod_cast (show 0 < (ramificationIndex K : Int) + ordUnit K δu by
        have he : 0 < (ramificationIndex K : Int) := by
          exact_mod_cast ramificationIndex_pos K
        omega)
    have hlt : ord K (1 : K) < ord K ((2 : K) * (δu : K)) := by
      simpa only [ord_one] using htwoδPos
    simpa only [ord_one] using (ord K).map_sub_eq_of_lt_right hlt
  have hwOrder : ord K (w : K) = 2 * ordUnit K δu := by
    have hwFinite : ord K (w : K) = ((ordUnit K (Units.mk0 (w : K) hwNe) : Int) : WithTop Int) := by
      exact (coe_ordUnit K (Units.mk0 (w : K) hwNe)).symm
    let wu : Kˣ := Units.mk0 (w : K) hwNe
    have hwuPos : 0 < ordUnit K wu := by
      rw [← show (wu : K) = (w : K) by rfl, ← coe_ordUnit] at hwPos
      exact_mod_cast hwPos
    have hleftOrder :
        ord K ((w : K) ^ 2 +
          ((2 : K) * (δu : K) - 1) * (w : K)) =
          ((ordUnit K wu : Int) : WithTop Int) := by
      have hlinear :
          ord K (((2 : K) * (δu : K) - 1) * (w : K)) =
            ((ordUnit K wu : Int) : WithTop Int) := by
        rw [ord_mul, hcoefOrder, zero_add]
        exact hwFinite
      have hquad : ord K ((w : K) ^ 2) =
          ((2 * ordUnit K wu : Int) : WithTop Int) := by
        calc
          ord K ((w : K) ^ 2) = 2 • ord K (w : K) := ord_pow K _ 2
          _ = 2 • ((ordUnit K wu : Int) : WithTop Int) :=
            congrArg (fun z : WithTop Int => 2 • z) hwFinite
          _ = ((2 * ordUnit K wu : Int) : WithTop Int) := by
            norm_cast
      have hlt :
          ord K (((2 : K) * (δu : K) - 1) * (w : K)) <
            ord K ((w : K) ^ 2) := by
        rw [hlinear, hquad]
        exact_mod_cast (show ordUnit K wu < 2 * ordUnit K wu by omega)
      rw [(ord K).map_add_eq_of_lt_right hlt, hlinear]
    have heq :
        (w : K) ^ 2 + ((2 : K) * (δu : K) - 1) * (w : K) =
          -((δu : K) ^ 2) := by
      exact eq_neg_of_add_eq_zero_left hwEquation
    rw [heq, ord_neg, ord_pow, ← coe_ordUnit] at hleftOrder
    have hwuOrder : ordUnit K wu = 2 * ordUnit K δu := by
      exact_mod_cast hleftOrder.symm
    rw [hwFinite, hwuOrder]
    norm_cast
  let b : K := (t : K) / (d : K) +
    (d : K) / (D : K) * (w : K)
  have hbIntegral : 0 ≤ ord K b := by
    have hfirst : 0 ≤ ord K ((t : K) / (d : K)) := by
      rw [div_eq_mul_inv, ord_mul, AddValuation.map_inv,
        ← coe_ordUnit, ← coe_ordUnit]
      exact_mod_cast (show 0 ≤ ordUnit K t - ordUnit K d by omega)
    have hsecond : 0 ≤
        ord K ((d : K) / (D : K) * (w : K)) := by
      have hsecondInt : 0 ≤
          ordUnit K d - ordUnit K D + 2 * ordUnit K δu := by
        rw [hδOrder]
        omega
      have hdOrder : ord K (d : K) =
          ((ordUnit K d : Int) : WithTop Int) := (coe_ordUnit K d).symm
      have hDOrder : ord K (D : K) =
          ((ordUnit K D : Int) : WithTop Int) := (coe_ordUnit K D).symm
      rw [div_eq_mul_inv, ord_mul, ord_mul, AddValuation.map_inv,
        hdOrder, hDOrder, hwOrder]
      have hcast :
          (0 : WithTop Int) ≤
            ((ordUnit K d - ordUnit K D +
              2 * ordUnit K δu : Int) : WithTop Int) := by
        exact_mod_cast hsecondInt
      convert hcast using 1 <;> norm_cast <;> omega
    exact (le_min hfirst hsecond).trans
      (min_ord_le_ord_add K ((t : K) / (d : K))
        ((d : K) / (D : K) * (w : K)))
  refine ⟨b, hbIntegral, ?_⟩
  have hδValue : (δu : K) = (D : K) * (t : K) / (d : K) ^ 2 := by
    simp [δu]
  have hidentity :
      (D : K) * b ^ 2 - (d : K) * b + (t : K) =
        ((d : K) ^ 2 / (D : K)) *
          ((w : K) ^ 2 +
            ((2 : K) * (δu : K) - 1) * (w : K) +
              (δu : K) ^ 2) := by
    dsimp [b]
    rw [hδValue]
    field_simp [Units.ne_zero D, Units.ne_zero d]
    ring
  rw [hidentity, hwEquation, mul_zero]

end Bong.Dyadic
