/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryEndpointClass
import Bong.Bong.DefectArithmetic
import Bong.Dyadic.QuadraticDefectHensel
import Bong.Dyadic.ResidueArtinSchreier

/-!
# The unique square class of maximal finite quadratic defect

This is O'Meara 63:4 in the form used throughout Beli's papers.  The proof
normalizes a depth-`2e` approximation to `1 - 4r`.  The residue of `r` is in
the unique nontrivial coset of the Artin--Schreier image; two such endpoint
forms therefore multiply to a square.
-/

namespace Bong

open Dyadic

universe u

namespace Dyadic

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

private theorem ord_four :
    ord K (4 : K) =
      (((2 * ramificationIndex K : Nat) : Int) : WithTop Int) := by
  rw [show (4 : K) = 2 * 2 by norm_num, ord_mul,
    ← ramificationIndex_spec]
  norm_cast
  ring

/-- If the endpoint coefficient is Artin--Schreier in the residue field,
the corresponding principal unit is a square. -/
theorem isSquare_of_eq_one_sub_four_mul_of_isArtinSchreierResidue
    (p : Kˣ) (hpUnit : IsValuationUnit K (p : K))
    (r : K) (hrIntegral : IsIntegral K r)
    (hp : (p : K) = 1 - 4 * r)
    (hAS : IsArtinSchreierResidue K r) :
    IsSquare p := by
  rcases hAS with ⟨z, hzIntegral, hzAS⟩
  have htwoR : IsInMaximalIdeal K (2 * r) :=
    isInMaximalIdeal_mul_isIntegral K (two_isInMaximalIdeal K) hrIntegral
  have hQ : IsInMaximalIdeal K (r + z + z ^ 2) := by
    have hsum := isInMaximalIdeal_add K hzAS htwoR
    have heq : (z ^ 2 + z - r) + 2 * r = r + z + z ^ 2 := by ring
    rwa [heq] at hsum
  let t : K := 1 + 2 * z
  have hnumerator : (p : K) - t ^ 2 = -(4 * (r + z + z ^ 2)) := by
    dsimp [t]
    rw [hp]
    ring
  have hnumOrder :
      ord K ((p : K) - t ^ 2) =
        (((2 * ramificationIndex K : Nat) : Int) : WithTop Int) +
          ord K (r + z + z ^ 2) := by
    rw [hnumerator, ord_neg, ord_mul, ord_four]
  have herror :
      1 - t ^ 2 / (p : K) = ((p : K) - t ^ 2) / (p : K) := by
    field_simp [Units.ne_zero p]
  have hdeep :
      (((2 * ramificationIndex K : Nat) : Int) : WithTop Int) <
        ord K (1 - t ^ 2 / (p : K)) := by
    rw [herror, div_eq_mul_inv, ord_mul, AddValuation.map_inv,
      hpUnit, hnumOrder]
    simp only [neg_zero, add_zero]
    change 0 < ord K (r + z + z ^ 2) at hQ
    generalize hq : ord K (r + z + z ^ 2) = d at hQ ⊢
    cases d with
    | top => exact WithTop.coe_lt_top _
    | coe n =>
        norm_cast at hQ ⊢
        omega
  let depth : Nat := 2 * ramificationIndex K + 1
  have hdepth : (depth : WithTop Int) ≤
      ord K (1 - t ^ 2 / (p : K)) := by
    generalize hvalue : ord K (1 - t ^ 2 / (p : K)) = d at hdeep
    cases d with
    | top => simp
    | coe n =>
        norm_cast at hdeep ⊢
  have happ : IsQuadraticApproximation K p depth := ⟨t, hdepth⟩
  have hdefect := natCast_le_quadraticDefect K happ
  apply isSquare_of_quadraticDefect_gt_two_mul_e K p
  have hstep :
      ((2 * ramificationIndex K : Nat) : ℕ∞) < (depth : ℕ∞) := by
    exact_mod_cast Nat.lt_succ_self (2 * ramificationIndex K)
  exact hstep.trans_le hdefect

/-- Two nonsquare endpoint principal units multiply to a square. -/
theorem isSquare_mul_of_endpoint_principal_units
    (p q : Kˣ)
    (hpUnit : IsValuationUnit K (p : K))
    (hqUnit : IsValuationUnit K (q : K))
    (r s : K) (hrIntegral : IsIntegral K r)
    (hsIntegral : IsIntegral K s)
    (hp : (p : K) = 1 - 4 * r)
    (hq : (q : K) = 1 - 4 * s)
    (hpNotSquare : ¬IsSquare p) (hqNotSquare : ¬IsSquare q) :
    IsSquare (p * q) := by
  have hrNotAS : ¬IsArtinSchreierResidue K r := by
    intro hAS
    exact hpNotSquare
      (isSquare_of_eq_one_sub_four_mul_of_isArtinSchreierResidue
        p hpUnit r hrIntegral hp hAS)
  have hsNotAS : ¬IsArtinSchreierResidue K s := by
    intro hAS
    exact hqNotSquare
      (isSquare_of_eq_one_sub_four_mul_of_isArtinSchreierResidue
        q hqUnit s hsIntegral hq hAS)
  rcases isArtinSchreierResidue_add_of_not K hrIntegral hsIntegral
      hrNotAS hsNotAS with ⟨z, hzIntegral, hzAS⟩
  let c : K := r + s - 4 * (r * s)
  have hrsIntegral : IsIntegral K (r * s) :=
    isIntegral_mul K hrIntegral hsIntegral
  have hfourIntegral : IsIntegral K (4 : K) := by
    have hzero : (0 : WithTop Int) ≤
        (((2 * ramificationIndex K : Nat) : Int) : WithTop Int) := by
      exact_mod_cast Nat.zero_le (2 * ramificationIndex K)
    simpa [IsIntegral, ord_four] using hzero
  have hcIntegral : IsIntegral K c := by
    exact isIntegral_sub K (isIntegral_add K hrIntegral hsIntegral)
      (isIntegral_mul K hfourIntegral hrsIntegral)
  have hfourRS : IsInMaximalIdeal K (4 * (r * s)) := by
    have hfourMax : IsInMaximalIdeal K (4 : K) := by
      rw [show (4 : K) = 2 * 2 by norm_num]
      exact isInMaximalIdeal_mul_isIntegral K (two_isInMaximalIdeal K)
        (ord_two_pos K).le
    exact isInMaximalIdeal_mul_isIntegral K hfourMax hrsIntegral
  have hcAS : IsArtinSchreierResidue K c := by
    refine ⟨z, hzIntegral, ?_⟩
    have hsum := isInMaximalIdeal_add K hzAS hfourRS
    have heq :
        (z ^ 2 + z - (r + s)) + 4 * (r * s) =
          z ^ 2 + z - c := by
      dsimp [c]
      ring
    rwa [heq] at hsum
  have hpqUnit : IsValuationUnit K ((p * q : Kˣ) : K) := by
    rw [Units.val_mul, IsValuationUnit, ord_mul, hpUnit, hqUnit]
    simp
  have hpq : ((p * q : Kˣ) : K) = 1 - 4 * c := by
    simp only [Units.val_mul]
    rw [hp, hq]
    dsimp [c]
    ring
  exact isSquare_of_eq_one_sub_four_mul_of_isArtinSchreierResidue
    (p * q) hpqUnit c hcIntegral hpq hcAS

end Dyadic

section Instance

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [laws : DyadicDiscriminantClassLaws K]

local instance defect : QuadraticDefectLaws K :=
  quadraticDefectLawsOfHensel K

private theorem discriminant_not_isSquare :
    ¬IsSquare laws.discriminantUnit := by
  intro hsquare
  have htop := quadraticDefect_eq_top_of_isSquare K hsquare
  rw [laws.discriminant_defect] at htop
  exact ENat.coe_ne_top _ htop

private theorem endpoint_unit_dichotomy
    (u : Kˣ) (huUnit : IsValuationUnit K (u : K))
    (hdefect : ((2 * ramificationIndex K : Nat) : ℕ∞) ≤
      quadraticDefect K u) :
    IsSquare u ∨ IsSquare (u / laws.discriminantUnit) := by
  by_cases huSquare : IsSquare u
  · exact Or.inl huSquare
  right
  rcases (isQuadraticApproximation_iff_le_defect K).2 hdefect with
    ⟨x, hx⟩
  let err : K := 1 - x ^ 2 / (u : K)
  have hendpointPos :
      (0 : WithTop Int) <
        ((2 * (ramificationIndex K : Int) : Int) : WithTop Int) := by
    exact_mod_cast Nat.mul_pos (by norm_num) (ramificationIndex_pos K)
  have herrPos : 0 < ord K err := by
    have hx' :
        ((2 * (ramificationIndex K : Int) : Int) : WithTop Int) ≤
          ord K (1 - x ^ 2 / (u : K)) := by
      convert hx using 1 <;> norm_cast
    exact hendpointPos.trans_le (by simpa [err] using hx')
  have hquotOrder : ord K (x ^ 2 / (u : K)) = 0 := by
    have hlt : ord K (1 : K) < ord K err := by
      simpa only [ord_one] using herrPos
    have hsub := (ord K).map_sub_eq_of_lt_left hlt
    have heq : 1 - err = x ^ 2 / (u : K) := by
      dsimp [err]
      ring
    rw [heq] at hsub
    simpa using hsub
  have hxNe : x ≠ 0 := by
    intro hzero
    rw [hzero] at hquotOrder
    simp at hquotOrder
  let xu : Kˣ := Units.mk0 x hxNe
  let p : Kˣ := xu ^ 2 / u
  have hpVal : (p : K) = x ^ 2 / (u : K) := by
    simp [p, xu]
  have hpUnit : IsValuationUnit K (p : K) := by
    rw [IsValuationUnit, hpVal]
    exact hquotOrder
  let r : K := (1 - (p : K)) / 4
  have hfourOrder :
      ord K (4 : K) =
        (((2 * ramificationIndex K : Nat) : Int) : WithTop Int) := by
    rw [show (4 : K) = 2 * 2 by norm_num, ord_mul,
      ← ramificationIndex_spec]
    norm_cast
    ring
  have hrIntegral : Dyadic.IsIntegral K r := by
    rw [Dyadic.IsIntegral]
    dsimp [r]
    rw [div_eq_mul_inv, ord_mul, AddValuation.map_inv, hfourOrder]
    have herrorOrder :
        (((2 * ramificationIndex K : Nat) : Int) : WithTop Int) ≤
          ord K (1 - (p : K)) := by
      have hx' :
          (((2 * ramificationIndex K : Nat) : Int) : WithTop Int) ≤
            ord K (1 - x ^ 2 / (u : K)) := by
        convert hx using 1 <;> norm_cast
      simpa [hpVal] using hx'
    generalize hv : ord K (1 - (p : K)) = d at herrorOrder
    cases d with
    | top => simp
    | coe n =>
        norm_cast at herrorOrder ⊢
        omega
  have hp : (p : K) = 1 - 4 * r := by
    dsimp [r]
    field_simp
    ring
  have hpNotSquare : ¬IsSquare p := by
    intro hpSquare
    have hxuSquare : IsSquare (xu ^ 2) := ⟨xu, by simp [pow_two]⟩
    have huIdentity : u = p⁻¹ * xu ^ 2 := by
      dsimp [p]
      simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
      group
    apply huSquare
    rw [huIdentity]
    exact hpSquare.inv.mul hxuSquare
  have hdiscNotSquare : ¬IsSquare laws.discriminantUnit :=
    discriminant_not_isSquare (K := K)
  have hrhoIntegral : Dyadic.IsIntegral K laws.rho := by
    rw [Dyadic.IsIntegral, laws.rho_isValuationUnit]
  have hproduct : IsSquare (p * laws.discriminantUnit) :=
    isSquare_mul_of_endpoint_principal_units
      p laws.discriminantUnit hpUnit laws.discriminant_isValuationUnit
      r laws.rho hrIntegral hrhoIntegral
      hp laws.discriminant_eq_one_sub_four_mul_rho
      hpNotSquare hdiscNotSquare
  have hxuSquare : IsSquare (xu ^ 2) := ⟨xu, by simp [pow_two]⟩
  have hpu : p * u = xu ^ 2 := by
    dsimp [p]
    simp
  have hmul :
      (p * laws.discriminantUnit) *
          (u / laws.discriminantUnit) = xu ^ 2 := by
    rw [div_eq_mul_inv]
    calc
      (p * laws.discriminantUnit) *
          (u * laws.discriminantUnit⁻¹) =
            (p * u) *
              (laws.discriminantUnit * laws.discriminantUnit⁻¹) := by
                ac_rfl
      _ = p * u := by simp
      _ = xu ^ 2 := hpu
  have heq : u / laws.discriminantUnit =
      (p * laws.discriminantUnit)⁻¹ * xu ^ 2 := by
    rw [← hmul]
    group
  rw [heq]
  exact hproduct.inv.mul hxuSquare

/-- O'Meara 63:4 supplies the maximal-defect square-class law for every
dyadic local field once a distinguished discriminant unit has been chosen. -/
noncomputable instance dyadicMaximalDefectClassLawsProved :
    DyadicMaximalDefectClassLaws K where
  square_or_discriminantSquare_of_defect_ge_twoE x hdefect := by
    have hnotOdd : ¬Odd (ordUnit K x) := by
      intro hodd
      have hzero := quadraticDefect_eq_zero_of_odd_ordUnit x hodd
      rw [hzero] at hdefect
      have hpos : 0 < 2 * ramificationIndex K :=
        Nat.mul_pos (by norm_num) (ramificationIndex_pos K)
      exact (not_le_of_gt (by exact_mod_cast hpos)) hdefect
    have heven : Even (ordUnit K x) := Int.not_odd_iff_even.mp hnotOdd
    rcases heven with ⟨k, hk⟩
    let s : Kˣ := uniformizerPowerUnit K k
    let u : Kˣ := x / s ^ 2
    have hsOrder : ordUnit K s = k :=
      ordUnit_uniformizerPowerUnit (K := K) k
    have huOrder : ordUnit K u = 0 := by
      dsimp [u]
      rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv, ordUnit_pow,
        hsOrder]
      omega
    have huUnit : IsValuationUnit K (u : K) :=
      (isValuationUnit_iff_ordUnit_eq_zero K u).2 huOrder
    have hfactor : u * s ^ 2 = x := by
      dsimp [u]
      simp
    have huDefect : quadraticDefect K u = quadraticDefect K x := by
      rw [← hfactor, quadraticDefect_mul_square]
    have huEndpoint :
        ((2 * ramificationIndex K : Nat) : ℕ∞) ≤
          quadraticDefect K u := by
      rwa [huDefect]
    rcases endpoint_unit_dichotomy (K := K) u huUnit huEndpoint with
      huSquare | huDiscSquare
    · left
      rw [← hfactor]
      exact huSquare.mul ⟨s, by simp [pow_two]⟩
    · right
      have hquotient : x / laws.discriminantUnit =
          (u / laws.discriminantUnit) * s ^ 2 := by
        rw [← hfactor]
        simp only [div_eq_mul_inv]
        ac_rfl
      rw [hquotient]
      exact huDiscSquare.mul ⟨s, by simp [pow_two]⟩

end Instance

end Bong
