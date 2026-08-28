/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.MaximalDefectClassProof

/-!
# Construction of the dyadic discriminant class

This file constructs the distinguished nonsquare unit `Δ = 1 - 4ρ` from a
nontrivial Artin--Schreier cokernel class in the finite residue field.  It
proves `d(Δ) = 2e` and the endpoint binary-parameter square-class dichotomy,
thereby discharging `DyadicDiscriminantClassLaws` for every dyadic local field.
-/

namespace Bong

open Dyadic

universe u


namespace Dyadic

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

private theorem exists_not_mem_artinSchreierHom_range
    (k : Type*) [Field k] [Finite k] [CharP k 2] :
    ∃ a : k, a ∉ (artinSchreierHom k).range := by
  by_contra h
  push Not at h
  have htop : (artinSchreierHom k).range = ⊤ := by
    refine eq_top_iff.mpr ?_
    intro x _hx
    exact h x
  have hindex := artinSchreierHom_range_index k
  rw [htop] at hindex
  simp at hindex

private theorem exists_valuationUnit_not_isArtinSchreierResidue :
    ∃ rho : K,
      IsValuationUnit K rho ∧
        ¬IsArtinSchreierResidue K rho := by
  let A := normalizedValuationRing K
  let k := normalizedResidueField K
  obtain ⟨rhoBar, hrhoBar⟩ := exists_not_mem_artinSchreierHom_range k
  obtain ⟨rhoA, hrhoA⟩ := IsLocalRing.residue_surjective rhoBar
  have hrhoIntegral : IsIntegral K (rhoA : K) :=
    (mem_normalizedValuationRing_iff K).1 rhoA.property
  have hrhoNotAS : ¬IsArtinSchreierResidue K (rhoA : K) := by
    rw [isArtinSchreierResidue_iff_mem_range K hrhoIntegral]
    simpa only [hrhoA] using hrhoBar
  have hrhoNotMax : ¬IsInMaximalIdeal K (rhoA : K) := by
    intro hrhoMax
    have hrhoMem : rhoA ∈ IsLocalRing.maximalIdeal A :=
      (mem_normalizedMaximalIdeal_iff K rhoA).2 hrhoMax
    have hrhoZero := (IsLocalRing.residue_eq_zero_iff rhoA).2 hrhoMem
    have hzeroRange : (0 : k) ∈ (artinSchreierHom k).range := by
      exact ⟨0, by simp [artinSchreierHom]⟩
    apply hrhoBar
    rwa [← hrhoA, hrhoZero]
  have hrhoUnit : IsValuationUnit K (rhoA : K) := by
    exact le_antisymm (not_lt.mp hrhoNotMax) hrhoIntegral
  exact ⟨rhoA, hrhoUnit, hrhoNotAS⟩

private theorem ord_four :
    ord K (4 : K) =
      (((2 * ramificationIndex K : Nat) : Int) : WithTop Int) := by
  rw [show (4 : K) = 2 * 2 by norm_num, ord_mul,
    ← ramificationIndex_spec]
  norm_cast
  ring

private theorem isArtinSchreierResidue_of_endpoint_square
    (delta : Kˣ) (hdeltaUnit : IsValuationUnit K (delta : K))
    (rho : K) (hrhoUnit : IsValuationUnit K rho)
    (hdelta : (delta : K) = 1 - 4 * rho)
    (hsquare : IsSquare delta) :
    IsArtinSchreierResidue K rho := by
  rcases hsquare with ⟨y, hy⟩
  have hyField : (y : K) ^ 2 = (delta : K) := by
    rw [hy]
    simp [pow_two]
  have hyOrder : ordUnit K y = 0 := by
    have h := congrArg (ordUnit K) hy
    rw [ordUnit_mul,
      (isValuationUnit_iff_ordUnit_eq_zero K delta).1 hdeltaUnit] at h
    omega
  have hyUnit : IsValuationUnit K (y : K) :=
    (isValuationUnit_iff_ordUnit_eq_zero K y).2 hyOrder
  have hproduct : ((y : K) - 1) * ((y : K) + 1) = -(4 * rho) := by
    rw [show ((y : K) - 1) * ((y : K) + 1) = (y : K) ^ 2 - 1 by ring,
      hyField, hdelta]
    ring
  have hrhoNe : rho ≠ 0 := by
    intro hzero
    subst rho
    simp [IsValuationUnit] at hrhoUnit
  have hleftNe : (y : K) - 1 ≠ 0 := by
    intro hzero
    have : -(4 * rho) = 0 := by rw [← hproduct, hzero, zero_mul]
    exact (mul_ne_zero (by norm_num) hrhoNe) (neg_eq_zero.mp this)
  have hrightNe : (y : K) + 1 ≠ 0 := by
    intro hzero
    have : -(4 * rho) = 0 := by rw [← hproduct, hzero, mul_zero]
    exact (mul_ne_zero (by norm_num) hrhoNe) (neg_eq_zero.mp this)
  let left : Kˣ := Units.mk0 ((y : K) - 1) hleftNe
  let right : Kˣ := Units.mk0 ((y : K) + 1) hrightNe
  have hsum : ordUnit K left + ordUnit K right =
      2 * (ramificationIndex K : Int) := by
    apply WithTop.coe_injective
    rw [WithTop.coe_add, coe_ordUnit, coe_ordUnit]
    change ord K ((y : K) - 1) + ord K ((y : K) + 1) =
      ((2 * (ramificationIndex K : Int) : Int) : WithTop Int)
    rw [← ord_mul, hproduct, ord_neg, ord_mul, ord_four, hrhoUnit]
    simp
  have hleftEq : ordUnit K left = (ramificationIndex K : Int) := by
    rcases lt_trichotomy (ordUnit K left) (ordUnit K right) with
      hlt | heq | hgt
    · have hval : ord K ((right : K) - (left : K)) =
          ord K (left : K) :=
        (ord K).map_sub_eq_of_lt_right (by
          rw [← coe_ordUnit, ← coe_ordUnit]
          exact_mod_cast hlt)
      have hfield : (right : K) - (left : K) = 2 := by
        change ((y : K) + 1) - ((y : K) - 1) = 2
        ring
      have hord : ordUnit K left = (ramificationIndex K : Int) := by
        apply WithTop.coe_injective
        rw [coe_ordUnit, ramificationIndex_spec]
        rw [hfield] at hval
        exact hval.symm
      omega
    · omega
    · have hval : ord K ((right : K) - (left : K)) =
          ord K (right : K) :=
        (ord K).map_sub_eq_of_lt_left (by
          rw [← coe_ordUnit, ← coe_ordUnit]
          exact_mod_cast hgt)
      have hfield : (right : K) - (left : K) = 2 := by
        change ((y : K) + 1) - ((y : K) - 1) = 2
        ring
      have hord : ordUnit K right = (ramificationIndex K : Int) := by
        apply WithTop.coe_injective
        rw [coe_ordUnit, ramificationIndex_spec]
        rw [hfield] at hval
        exact hval.symm
      omega
  let z : K := ((y : K) - 1) / 2
  have hzOrder : ord K z = 0 := by
    dsimp only [z]
    rw [div_eq_mul_inv, ord_mul, AddValuation.map_inv]
    change ord K (left : K) + -ord K (2 : K) = 0
    rw [← coe_ordUnit, hleftEq, ← ramificationIndex_spec]
    simp
  have hzIntegral : IsIntegral K z := hzOrder.ge
  have hyz : (y : K) = 1 + 2 * z := by
    dsimp only [z]
    field_simp
    ring
  have hASzero : z ^ 2 + z + rho = 0 := by
    have hmul : (4 : K) * (z ^ 2 + z + rho) = 0 := by
      calc
        (4 : K) * (z ^ 2 + z + rho) = (y : K) ^ 2 - (delta : K) := by
          rw [hyz, hdelta]
          ring
        _ = 0 := sub_eq_zero.mpr hyField
    exact (mul_eq_zero.mp hmul).resolve_left (by norm_num)
  refine ⟨z, hzIntegral, ?_⟩
  have hfield : z ^ 2 + z - rho = 2 * (z ^ 2 + z) := by
    have hrho : rho = -(z ^ 2 + z) := by linear_combination hASzero
    rw [hrho]
    ring
  rw [hfield]
  apply isInMaximalIdeal_mul_isIntegral K (two_isInMaximalIdeal K)
  exact isIntegral_add K
    (by simpa only [pow_two] using isIntegral_mul K hzIntegral hzIntegral)
    hzIntegral

private theorem exists_discriminant_data :
    ∃ delta : Kˣ, ∃ rho : K,
      IsValuationUnit K (delta : K) ∧
        IsValuationUnit K rho ∧
        (delta : K) = 1 - 4 * rho ∧
        quadraticDefect K delta =
          ((2 * ramificationIndex K : Nat) : ℕ∞) := by
  letI : QuadraticDefectLaws K := quadraticDefectLawsOfHensel K
  obtain ⟨rho, hrhoUnit, hrhoNotAS⟩ :=
    exists_valuationUnit_not_isArtinSchreierResidue (K := K)
  have hfourRhoOrder : ord K (4 * rho) =
      (((2 * ramificationIndex K : Nat) : Int) : WithTop Int) := by
    rw [ord_mul, ord_four, hrhoUnit]
    simp
  have hfourRhoPos : (0 : WithTop Int) < ord K (4 * rho) := by
    rw [hfourRhoOrder]
    exact_mod_cast Nat.mul_pos (by norm_num) (ramificationIndex_pos K)
  have hdeltaOrder : ord K (1 - 4 * rho) = 0 := by
    have hlt : ord K (1 : K) < ord K (4 * rho) := by
      simpa only [ord_one] using hfourRhoPos
    simpa only [ord_one] using (ord K).map_sub_eq_of_lt_left hlt
  have hdeltaNe : 1 - 4 * rho ≠ 0 := by
    apply (ord_eq_top_iff K).not.mp
    rw [hdeltaOrder]
    exact WithTop.coe_ne_top
  let delta : Kˣ := Units.mk0 (1 - 4 * rho) hdeltaNe
  have hdeltaField : (delta : K) = 1 - 4 * rho := rfl
  have hdeltaUnit : IsValuationUnit K (delta : K) := by
    exact hdeltaOrder
  have hdeltaNotSquare : ¬IsSquare delta := by
    intro hsquare
    exact hrhoNotAS
      (isArtinSchreierResidue_of_endpoint_square delta hdeltaUnit rho
        hrhoUnit hdeltaField hsquare)
  have hlower : ((2 * ramificationIndex K : Nat) : ℕ∞) ≤
      quadraticDefect K delta := by
    apply natCast_le_quadraticDefect K
    refine ⟨1, ?_⟩
    have hfield : 1 - (1 : K) ^ 2 / (delta : K) =
        -(4 * rho) / (delta : K) := by
      calc
        1 - (1 : K) ^ 2 / (delta : K) =
            ((delta : K) - 1) / (delta : K) := by
              field_simp [Units.ne_zero delta]
        _ = -(4 * rho) / (delta : K) := by rw [hdeltaField]; ring
    rw [hfield, div_eq_mul_inv, ord_mul, ord_neg, hfourRhoOrder,
      AddValuation.map_inv, hdeltaUnit]
    simp
    norm_cast
  have hupper : quadraticDefect K delta ≤
      ((2 * ramificationIndex K : Nat) : ℕ∞) :=
    quadraticDefect_le_two_mul_e_of_not_isSquare (K := K)
      hdeltaNotSquare
  exact ⟨delta, rho, hdeltaUnit, hrhoUnit, hdeltaField,
    le_antisymm hupper hlower⟩

private theorem endpoint_unit_dichotomy_explicit
    (delta : Kˣ) (hdeltaUnit : IsValuationUnit K (delta : K))
    (rho : K) (hrhoUnit : IsValuationUnit K rho)
    (hdelta : (delta : K) = 1 - 4 * rho)
    (hdeltaNotSquare : ¬IsSquare delta)
    (v : Kˣ) (_hvUnit : IsValuationUnit K (v : K))
    (hdefect : ((2 * ramificationIndex K : Nat) : ℕ∞) ≤
      quadraticDefect K v) :
    IsSquare v ∨ IsSquare (v / delta) := by
  by_cases hvSquare : IsSquare v
  · exact Or.inl hvSquare
  right
  rcases (isQuadraticApproximation_iff_le_defect K).2 hdefect with
    ⟨x, hx⟩
  let err : K := 1 - x ^ 2 / (v : K)
  have hendpointPos :
      (0 : WithTop Int) <
        ((2 * (ramificationIndex K : Int) : Int) : WithTop Int) := by
    exact_mod_cast Nat.mul_pos (by norm_num) (ramificationIndex_pos K)
  have herrPos : 0 < ord K err := by
    have hx' :
        ((2 * (ramificationIndex K : Int) : Int) : WithTop Int) ≤
          ord K (1 - x ^ 2 / (v : K)) := by
      convert hx using 1 <;> norm_cast
    exact hendpointPos.trans_le (by simpa [err] using hx')
  have hquotOrder : ord K (x ^ 2 / (v : K)) = 0 := by
    have hlt : ord K (1 : K) < ord K err := by
      simpa only [ord_one] using herrPos
    have hsub := (ord K).map_sub_eq_of_lt_left hlt
    have heq : 1 - err = x ^ 2 / (v : K) := by
      dsimp [err]
      ring
    rw [heq] at hsub
    simpa using hsub
  have hxNe : x ≠ 0 := by
    intro hzero
    rw [hzero] at hquotOrder
    simp at hquotOrder
  let xu : Kˣ := Units.mk0 x hxNe
  let p : Kˣ := xu ^ 2 / v
  have hpVal : (p : K) = x ^ 2 / (v : K) := by
    simp [p, xu]
  have hpUnit : IsValuationUnit K (p : K) := by
    rw [IsValuationUnit, hpVal]
    exact hquotOrder
  let r : K := (1 - (p : K)) / 4
  have hrIntegral : IsIntegral K r := by
    rw [IsIntegral]
    dsimp [r]
    rw [div_eq_mul_inv, ord_mul, AddValuation.map_inv, ord_four]
    have herrorOrder :
        (((2 * ramificationIndex K : Nat) : Int) : WithTop Int) ≤
          ord K (1 - (p : K)) := by
      have hx' :
          (((2 * ramificationIndex K : Nat) : Int) : WithTop Int) ≤
            ord K (1 - x ^ 2 / (v : K)) := by
        convert hx using 1 <;> norm_cast
      simpa [hpVal] using hx'
    generalize hvError : ord K (1 - (p : K)) = d at herrorOrder
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
    have hvIdentity : v = p⁻¹ * xu ^ 2 := by
      dsimp [p]
      simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
      group
    apply hvSquare
    rw [hvIdentity]
    exact hpSquare.inv.mul hxuSquare
  have hrhoIntegral : IsIntegral K rho := by
    rw [IsIntegral, hrhoUnit]
  have hproduct : IsSquare (p * delta) :=
    isSquare_mul_of_endpoint_principal_units
      p delta hpUnit hdeltaUnit r rho hrIntegral hrhoIntegral
      hp hdelta hpNotSquare hdeltaNotSquare
  have hxuSquare : IsSquare (xu ^ 2) := ⟨xu, by simp [pow_two]⟩
  have hpv : p * v = xu ^ 2 := by
    dsimp [p]
    simp
  have hmul : (p * delta) * (v / delta) = xu ^ 2 := by
    rw [div_eq_mul_inv]
    calc
      (p * delta) * (v * delta⁻¹) =
          (p * v) * (delta * delta⁻¹) := by ac_rfl
      _ = p * v := by simp
      _ = xu ^ 2 := hpv
  have heq : v / delta = (p * delta)⁻¹ * xu ^ 2 := by
    rw [← hmul]
    group
  rw [heq]
  exact hproduct.inv.mul hxuSquare

private theorem unitSquareClass_mul_eq_of_isSquare_unit
    (q x : Kˣ) (hxUnit : IsValuationUnit K (x : K))
    (hxSquare : IsSquare x) :
    unitSquareClass K (q * x) = unitSquareClass K q := by
  rcases hxSquare with ⟨s, hs⟩
  have hsOrder : ordUnit K s = 0 := by
    have h := congrArg (ordUnit K) hs
    rw [ordUnit_mul,
      (isValuationUnit_iff_ordUnit_eq_zero K x).1 hxUnit] at h
    omega
  have hsUnit : IsValuationUnit K (s : K) :=
    (isValuationUnit_iff_ordUnit_eq_zero K s).2 hsOrder
  have hxPow : x = s ^ 2 := by simpa only [pow_two] using hs
  rw [hxPow]
  exact unitSquareClass_mul_unit_square K q s hsUnit

private theorem endpoint_parameter_class_explicit
    (delta : Kˣ) (hdeltaUnit : IsValuationUnit K (delta : K))
    (rho : K) (hrhoUnit : IsValuationUnit K rho)
    (hdelta : (delta : K) = 1 - 4 * rho)
    (hdeltaNotSquare : ¬IsSquare delta)
    (a : Kˣ) (hadmissible : BONG.IsBinaryParameterAdmissible a)
    (horder : ordUnit K a =
      -(2 * (ramificationIndex K : Int))) :
    unitSquareClass K a = unitSquareClass K (negativeQuarterUnit K) ∨
      unitSquareClass K a =
        unitSquareClass K (negativeQuarterUnit K * delta) := by
  let quarter : Kˣ := negativeQuarterUnit K
  let x : Kˣ := a / quarter
  have hquarterOrder : ordUnit K quarter =
      -(2 * (ramificationIndex K : Int)) := by
    exact ordUnit_negativeQuarterUnit (K := K)
  have hxOrder : ordUnit K x = 0 := by
    dsimp only [x]
    rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv, horder,
      hquarterOrder]
    omega
  have hxUnit : IsValuationUnit K (x : K) :=
    (isValuationUnit_iff_ordUnit_eq_zero K x).2 hxOrder
  rcases hadmissible with ⟨c, _htwoC, hdiag⟩
  have hdiagOrder : 0 ≤ ord K (c ^ 2 + (a : K)) := by
    exact (mem_integerRing_iff K).1 hdiag
  have haFieldOrder : ord K (a : K) =
      ((-(2 * (ramificationIndex K : Int)) : Int) : WithTop Int) := by
    rw [← coe_ordUnit, horder]
  have hnormalized :
      1 - ((2 : K) * c) ^ 2 / (x : K) =
        (c ^ 2 + (a : K)) / (a : K) := by
    have hxVal : (x : K) = -(4 * (a : K)) := by
      simp [x, quarter, negativeQuarterUnit, div_eq_mul_inv]
      ring
    rw [hxVal]
    field_simp [Units.ne_zero a]
    ring
  have happrox : IsQuadraticApproximation K x
      (2 * ramificationIndex K) := by
    refine ⟨(2 : K) * c, ?_⟩
    rw [hnormalized, div_eq_mul_inv, ord_mul, AddValuation.map_inv,
      haFieldOrder]
    let endpoint : WithTop Int :=
      ((2 * (ramificationIndex K : Int) : Int) : WithTop Int)
    have hbound : endpoint ≤
        ord K (c ^ 2 + (a : K)) + endpoint := by
      have := add_le_add_left hdiagOrder endpoint
      simpa only [zero_add, add_zero, add_comm] using this
    have hnatCast :
        ((2 * ramificationIndex K : Nat) : WithTop Int) =
          2 * ((ramificationIndex K : Nat) : WithTop Int) := by
      norm_cast
    rw [hnatCast]
    simpa [endpoint] using hbound
  have hxDefect : ((2 * ramificationIndex K : Nat) : ℕ∞) ≤
      quadraticDefect K x :=
    natCast_le_quadraticDefect K happrox
  rcases endpoint_unit_dichotomy_explicit delta hdeltaUnit rho
      hrhoUnit hdelta hdeltaNotSquare x hxUnit hxDefect with
    hxSquare | hxDeltaSquare
  · left
    have haFactor : a = quarter * x := by
      dsimp only [x]
      simp [quarter]
    calc
      unitSquareClass K a = unitSquareClass K (quarter * x) :=
        congrArg (unitSquareClass K) haFactor
      _ = unitSquareClass K quarter :=
        unitSquareClass_mul_eq_of_isSquare_unit quarter x hxUnit hxSquare
      _ = unitSquareClass K (negativeQuarterUnit K) := rfl
  · right
    let z : Kˣ := x / delta
    have hzUnit : IsValuationUnit K (z : K) := by
      rw [isValuationUnit_iff_ordUnit_eq_zero]
      dsimp only [z]
      rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv, hxOrder,
        (isValuationUnit_iff_ordUnit_eq_zero K delta).1 hdeltaUnit]
      simp
    have haFactor : a = (quarter * delta) * z := by
      dsimp only [z, x]
      symm
      rw [div_eq_mul_inv, div_eq_mul_inv]
      calc
        (quarter * delta : Kˣ) * ((a * quarter⁻¹) * delta⁻¹) =
            a * (quarter * quarter⁻¹) * (delta * delta⁻¹) := by
          ac_rfl
        _ = a := by simp
    calc
      unitSquareClass K a = unitSquareClass K ((quarter * delta) * z) :=
        congrArg (unitSquareClass K) haFactor
      _ = unitSquareClass K (quarter * delta) :=
        unitSquareClass_mul_eq_of_isSquare_unit
          (quarter * delta) z hzUnit hxDeltaSquare
      _ = unitSquareClass K (negativeQuarterUnit K * delta) := rfl

/-- The discriminant unit and its endpoint square-class dichotomy are
constructed from the nontrivial Artin--Schreier cokernel of the finite
residue field.  This is the dyadic local-field input customarily cited as
O'Meara 63:4. -/
noncomputable instance dyadicDiscriminantClassLawsProved :
    DyadicDiscriminantClassLaws K := by
  let hdata := exists_discriminant_data (K := K)
  let delta : Kˣ := Classical.choose hdata
  have hdeltaData := Classical.choose_spec hdata
  let rho : K := Classical.choose hdeltaData
  have hspec := Classical.choose_spec hdeltaData
  have hdeltaUnit : IsValuationUnit K (delta : K) := hspec.1
  have hrhoUnit : IsValuationUnit K rho := hspec.2.1
  have hdelta : (delta : K) = 1 - 4 * rho := hspec.2.2.1
  have hdefect : quadraticDefect K delta =
      ((2 * ramificationIndex K : Nat) : ℕ∞) := hspec.2.2.2
  have hdeltaNotSquare : ¬IsSquare delta := by
    intro hsquare
    have htop := quadraticDefect_eq_top_of_isSquare K hsquare
    rw [hdefect] at htop
    exact ENat.coe_ne_top _ htop
  exact
    { discriminantUnit := delta
      discriminant_isValuationUnit := hdeltaUnit
      rho := rho
      rho_isValuationUnit := hrhoUnit
      discriminant_eq_one_sub_four_mul_rho := hdelta
      discriminant_defect := hdefect
      endpoint_parameter_class := fun a hadmissible horder =>
        endpoint_parameter_class_explicit delta hdeltaUnit rho hrhoUnit
          hdelta hdeltaNotSquare a hadmissible horder }

end Dyadic

end Bong
