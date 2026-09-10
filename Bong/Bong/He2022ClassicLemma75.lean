/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2022ClassicPProfiles
import Bong.Bong.DiagonalCodimensionTwoRepresentationProof
import Bong.Bong.He2022ClassicLemma43

/-!
# He (2024), Lemma 7.5

The first part of Lemma 7.5 is the uniform ambient-space calculation for the
two literal `P` columns.  The signed determinant obstruction reduces exactly
to the parameter `c` of the small `C` row; the published assumption
`d(c) in {0,1}` therefore makes codimension-two representation automatic.
-/

namespace Bong

open Dyadic BONG.GoodBONG AlternatingEndpointTower

universe u


variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K]
    [DyadicContext K] in
private theorem heClassic_neg_sign_pair_mul_squares
    (pairs : Nat) (c s t : Kˣ) :
    -(((-1 : Kˣ) ^ pairs * t ^ 2)) *
        ((-1 : Kˣ) ^ (pairs + 1) * (s ^ 2 * c)) =
      c * (t * s) ^ 2 := by
  have hsign : (-1 : Kˣ) ^ pairs * (-1 : Kˣ) ^ pairs = 1 := by
    rw [← pow_add]
    exact (show Even (pairs + pairs) from ⟨pairs, by omega⟩).neg_one_pow
  have hpow : (-1 : Kˣ) ^ (pairs + 1) =
      (-1 : Kˣ) ^ pairs * -1 := by
    rw [pow_succ]
  rw [hpow]
  calc
    -(((-1 : Kˣ) ^ pairs * t ^ 2)) *
        (((-1 : Kˣ) ^ pairs * -1) * (s ^ 2 * c)) =
        (((-1 : Kˣ) ^ pairs * (-1 : Kˣ) ^ pairs) *
          (t ^ 2 * s ^ 2 * c)) := by
            apply Units.ext
            simp only [Units.val_neg, Units.val_mul,
              Units.val_pow_eq_pow_val, Units.val_one]
            ring
    _ = c * (t * s) ^ 2 := by
      rw [hsign, one_mul]
      simp only [mul_pow]
      ac_rfl

/-- A defect-zero or defect-one parameter is not a square. -/
theorem heClassic_not_isSquare_of_defect_zero_or_one
    (c : Kˣ)
    (hc : BONG.GoodBONG.defectOrder (K := K) c = 0 ∨
      BONG.GoodBONG.defectOrder (K := K) c = 1) :
    ¬ IsSquare c := by
  intro hsquare
  have htop := BONG.GoodBONG.defectOrder_eq_top_of_isSquare
    (K := K) hsquare
  rcases hc with hc | hc <;> rw [hc] at htop <;> norm_num at htop

private theorem he2022ClassicLemma75i_of_determinants
    (pairs : Nat) (c s t : Kˣ)
    (source : Fin (2 * pairs + 2) → Kˣ)
    (target : Fin (2 * pairs + 4) → Kˣ)
    (hsource : diagonalUnitDeterminant source =
      (-1 : Kˣ) ^ (pairs + 1) * (s ^ 2 * c))
    (htarget : diagonalUnitDeterminant target =
      (-1 : Kˣ) ^ pairs * t ^ 2)
    (hc : BONG.GoodBONG.defectOrder (K := K) c = 0 ∨
      BONG.GoodBONG.defectOrder (K := K) c = 1) :
    DiagonalRepresents
      (diagonalUnitCoefficients source)
      (diagonalUnitCoefficients target) := by
  apply diagonalRepresents_of_not_negative_determinant_square
    source target rfl
  rw [hsource, htarget,
    heClassic_neg_sign_pair_mul_squares pairs c s t]
  intro hsquare
  have hsquareFactor : IsSquare ((t * s) ^ 2) :=
    ⟨t * s, pow_two (t * s)⟩
  have hquotient := hsquare.div hsquareFactor
  have hcancel : (c * (t * s) ^ 2) / (t * s) ^ 2 = c := by
    apply Units.ext
    simp only [Units.val_div_eq_div_val, Units.val_mul,
      Units.val_pow_eq_pow_val]
    field_simp [Units.ne_zero t, Units.ne_zero s]
  rw [hcancel] at hquotient
  exact heClassic_not_isSquare_of_defect_zero_or_one c hc hquotient

/-! ## Literal four-column forms of Lemma 7.5(i) -/

/-- Lemma 7.5(i), `C₁` into `P₁`. -/
theorem he2022ClassicLemma75i_C1_represents_P1
    (pairs : Nat) (a c : Kˣ)
    (hc : BONG.GoodBONG.defectOrder (K := K) c = 0 ∨
      BONG.GoodBONG.defectOrder (K := K) c = 1) :
    DiagonalRepresents
      (diagonalUnitCoefficients (heClassicEvenC1 (K := K) pairs c))
      (diagonalUnitCoefficients (heClassicEvenP1 (K := K) pairs a)) := by
  apply he2022ClassicLemma75i_of_determinants pairs c 1 a
  · rw [diagonalUnitDeterminant_heClassicEvenC1]
    simp
  · exact diagonalUnitDeterminant_heClassicEvenP1 pairs a
  · exact hc

/-- Lemma 7.5(i), `C₂` into `P₁`. -/
theorem he2022ClassicLemma75i_C2_represents_P1
    (pairs : Nat) (a c cSharp : Kˣ)
    (hc : BONG.GoodBONG.defectOrder (K := K) c = 0 ∨
      BONG.GoodBONG.defectOrder (K := K) c = 1) :
    DiagonalRepresents
      (diagonalUnitCoefficients
        (heClassicEvenC2 (K := K) pairs c cSharp))
      (diagonalUnitCoefficients (heClassicEvenP1 (K := K) pairs a)) := by
  apply he2022ClassicLemma75i_of_determinants pairs c cSharp a
  · exact diagonalUnitDeterminant_heClassicEvenC2 pairs c cSharp
  · exact diagonalUnitDeterminant_heClassicEvenP1 pairs a
  · exact hc

/-- Lemma 7.5(i), `C₁` into `P₂`. -/
theorem he2022ClassicLemma75i_C1_represents_P2
    (pairs : Nat) (a aSharp c : Kˣ)
    (hc : BONG.GoodBONG.defectOrder (K := K) c = 0 ∨
      BONG.GoodBONG.defectOrder (K := K) c = 1) :
    DiagonalRepresents
      (diagonalUnitCoefficients (heClassicEvenC1 (K := K) pairs c))
      (diagonalUnitCoefficients
        (heClassicEvenP2 (K := K) pairs a aSharp)) := by
  apply he2022ClassicLemma75i_of_determinants pairs c 1 (a * aSharp)
  · rw [diagonalUnitDeterminant_heClassicEvenC1]
    simp
  · exact diagonalUnitDeterminant_heClassicEvenP2 pairs a aSharp
  · exact hc

/-- Lemma 7.5(i), `C₂` into `P₂`. -/
theorem he2022ClassicLemma75i_C2_represents_P2
    (pairs : Nat) (a aSharp c cSharp : Kˣ)
    (hc : BONG.GoodBONG.defectOrder (K := K) c = 0 ∨
      BONG.GoodBONG.defectOrder (K := K) c = 1) :
    DiagonalRepresents
      (diagonalUnitCoefficients
        (heClassicEvenC2 (K := K) pairs c cSharp))
      (diagonalUnitCoefficients
        (heClassicEvenP2 (K := K) pairs a aSharp)) := by
  apply he2022ClassicLemma75i_of_determinants
    pairs c cSharp (a * aSharp)
  · exact diagonalUnitDeterminant_heClassicEvenC2 pairs c cSharp
  · exact diagonalUnitDeterminant_heClassicEvenP2 pairs a aSharp
  · exact hc

/-! ## The exceptional quaternary block in Lemma 7.5(ii) -/

/-- The displayed residual block
`[1,-Delta,-pi,Delta*pi]` in `P₂⁴(Delta)`. -/
noncomputable def heClassicP2DiscriminantTail : Fin 4 → Kˣ :=
  let delta :=
    (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
  let pi := uniformizerPowerUnit K (1 : Int)
  Fin.append ![(1 : Kˣ), -delta] ![-pi, delta * pi]

/-- The displayed block is the quaternion norm form `(Delta,pi)`. -/
theorem heClassicP2DiscriminantTail_coefficients :
    diagonalUnitCoefficients (heClassicP2DiscriminantTail (K := K)) =
      quaternionNormCoefficients
        (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
        (uniformizerPowerUnit K (1 : Int)) := by
  have htail : heClassicP2DiscriminantTail (K := K) =
      ![(1 : Kˣ),
        -(inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit,
        -(uniformizerPowerUnit K (1 : Int)),
        (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit *
          uniformizerPowerUnit K (1 : Int)] := by
    funext i
    fin_cases i <;> rfl
  rw [htail]
  funext i
  fin_cases i <;>
    simp [diagonalUnitCoefficients, quaternionNormCoefficients]

/-- The residual block in `P₂⁴(Delta)` is anisotropic. -/
theorem heClassicP2DiscriminantTail_anisotropic :
    DiagonalAnisotropic
      (diagonalUnitCoefficients
        (heClassicP2DiscriminantTail (K := K))) := by
  let delta :=
    (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
  let pi := uniformizerPowerUnit K (1 : Int)
  have hpiOdd : Odd (ordUnit K pi) := by
    rw [ordUnit_uniformizerPowerUnit]
    exact odd_one
  have hpiNotNorm : ¬ IsQuadraticNorm K delta pi := by
    intro hnorm
    have heven := (isQuadraticNorm_discriminant_iff_even_order pi).1 hnorm
    exact Int.not_even_iff_odd.mpr hpiOdd heven
  rw [heClassicP2DiscriminantTail_coefficients]
  exact (quaternionNorm_anisotropic_iff_nonnorm delta pi).2 hpiNotNorm

/-- The literal `P₂(Delta)` row is a hyperbolic head followed by the
anisotropic quaternary block displayed in the proof of Lemma 7.5(ii). -/
theorem heClassicEvenP2_discriminant_eq_tower_tail (pairs : Nat) :
    let delta :=
      (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
    let pi := uniformizerPowerUnit K (1 : Int)
    heClassicEvenP2 (K := K) pairs delta pi =
      Fin.append (standardHyperbolicEndpointTower (K := K) pairs)
        (heClassicP2DiscriminantTail (K := K)) := by
  dsimp only
  let delta :=
    (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
  let pi := uniformizerPowerUnit K (1 : Int)
  have htail : heClassicP2DiscriminantTail (K := K) =
      ![(1 : Kˣ), -delta, -pi, delta * pi] := by
    funext i
    fin_cases i <;> rfl
  funext i
  by_cases hhead : i.val < 2 * pairs
  · let j : Fin (2 * pairs) := ⟨i.val, hhead⟩
    let k : Fin (2 * pairs + 2) := ⟨i.val, by omega⟩
    have hiP : i = Fin.castAdd 2 k := Fin.ext rfl
    have hk : k = Fin.castAdd 2 j := Fin.ext rfl
    have hiTarget : i = Fin.castAdd 4 j := Fin.ext rfl
    calc
      heClassicEvenP2 (K := K) pairs delta pi i =
          standardHyperbolicEndpointTower (K := K) pairs j := by
            rw [hiP, heClassicEvenP2_prefix, hk, heClassicEvenC1,
              Fin.append_left, heClassicScaledHyperbolicTower_zero]
      _ = Fin.append
          (standardHyperbolicEndpointTower (K := K) pairs)
          (heClassicP2DiscriminantTail (K := K)) i := by
            rw [hiTarget, Fin.append_left]
  · have hlast : i.val = 2 * pairs ∨ i.val = 2 * pairs + 1 ∨
        i.val = 2 * pairs + 2 ∨ i.val = 2 * pairs + 3 := by
      omega
    rcases hlast with hzero | hone | htwo | hthree
    · have hiP : i = Fin.castAdd 2
          (Fin.natAdd (2 * pairs) (0 : Fin 2)) := Fin.ext hzero
      have hiTarget : i = Fin.natAdd (2 * pairs) (0 : Fin 4) :=
        Fin.ext hzero
      calc
        heClassicEvenP2 (K := K) pairs delta pi i = 1 := by
          rw [hiP, heClassicEvenP2_prefix, heClassicEvenC1_tail]
          rfl
        _ = Fin.append
            (standardHyperbolicEndpointTower (K := K) pairs)
            (heClassicP2DiscriminantTail (K := K)) i := by
          rw [hiTarget, Fin.append_right, htail]
          rfl
    · have hiP : i = Fin.castAdd 2
          (Fin.natAdd (2 * pairs) (1 : Fin 2)) := Fin.ext hone
      have hiTarget : i = Fin.natAdd (2 * pairs) (1 : Fin 4) :=
        Fin.ext hone
      calc
        heClassicEvenP2 (K := K) pairs delta pi i = -delta := by
          rw [hiP, heClassicEvenP2_prefix, heClassicEvenC1_tail]
          rfl
        _ = Fin.append
            (standardHyperbolicEndpointTower (K := K) pairs)
            (heClassicP2DiscriminantTail (K := K)) i := by
          rw [hiTarget, Fin.append_right, htail]
          rfl
    · have hiP : i =
          Fin.natAdd (2 * pairs + 2) (0 : Fin 2) := Fin.ext htwo
      have hiTarget : i = Fin.natAdd (2 * pairs) (2 : Fin 4) :=
        Fin.ext htwo
      calc
        heClassicEvenP2 (K := K) pairs delta pi i = -pi := by
          rw [hiP, heClassicEvenP2_tail_zero_value]
        _ = Fin.append
            (standardHyperbolicEndpointTower (K := K) pairs)
            (heClassicP2DiscriminantTail (K := K)) i := by
          rw [hiTarget, Fin.append_right, htail]
          rfl
    · have hiP : i =
          Fin.natAdd (2 * pairs + 2) (1 : Fin 2) := Fin.ext hthree
      have hiTarget : i = Fin.natAdd (2 * pairs) (3 : Fin 4) :=
        Fin.ext hthree
      calc
        heClassicEvenP2 (K := K) pairs delta pi i = delta * pi := by
          rw [hiP, heClassicEvenP2_tail_one_value]
        _ = Fin.append
            (standardHyperbolicEndpointTower (K := K) pairs)
            (heClassicP2DiscriminantTail (K := K)) i := by
          rw [hiTarget, Fin.append_right, htail]
          rfl

/-- Lemma 7.5(ii): the exceptional hyperbolic row does not embed in
`P₂^(n+2)(Delta)`. -/
theorem he2022ClassicLemma75ii_evenHOne_not_represents_P2Discriminant
    (pairs : Nat) :
    let delta :=
      (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
    let pi := uniformizerPowerUnit K (1 : Int)
    ¬ DiagonalRepresents
      (diagonalUnitCoefficients (heClassicEvenH (K := K) pairs 1))
      (diagonalUnitCoefficients
        (heClassicEvenP2 (K := K) pairs delta pi)) := by
  dsimp only
  intro hrep
  have honeOrder : ordUnit K (1 : Kˣ) = 0 := by
    have h := ordUnit_mul K (1 : Kˣ) 1
    simp only [mul_one] at h
    omega
  have hnormal :=
    heClassicLemma211First_represents_evenHOne
      (K := K) pairs honeOrder
  have hfull := hnormal.trans hrep
  rw [heClassicLemma211First,
    heClassicEvenP2_discriminant_eq_tower_tail] at hfull
  have hfull' : DiagonalRepresents
      (Fin.append
        (diagonalUnitCoefficients
          (standardHyperbolicEndpointTower (K := K) pairs))
        (diagonalUnitCoefficients (heHuHyperbolicPair (K := K))))
      (Fin.append
        (diagonalUnitCoefficients
          (standardHyperbolicEndpointTower (K := K) pairs))
        (diagonalUnitCoefficients
          (heClassicP2DiscriminantTail (K := K)))) := by
    simpa only [diagonalUnitCoefficients_append] using hfull
  have htail := DiagonalRepresents.cancel_common_prefix
    (diagonalUnitCoefficients
      (standardHyperbolicEndpointTower (K := K) pairs))
    (diagonalUnitCoefficients (heHuHyperbolicPair (K := K)))
    (diagonalUnitCoefficients
      (heClassicP2DiscriminantTail (K := K)))
    (fun i ↦ Units.ne_zero
      (standardHyperbolicEndpointTower (K := K) pairs i))
    (fun i ↦ Units.ne_zero (heHuHyperbolicPair (K := K) i))
    (fun i ↦ Units.ne_zero
      (heClassicP2DiscriminantTail (K := K) i)) hfull'
  have hhyperbolic : DiagonalIsotropic
      (diagonalUnitCoefficients (heHuHyperbolicPair (K := K))) := by
    let x : Fin 2 → K := ![1, 1]
    refine ⟨x, ?_, ?_⟩
    · intro hx
      have hzero := congrFun hx (0 : Fin 2)
      norm_num [x] at hzero
    · simp [heHuHyperbolicPair, diagonalUnitCoefficients,
        diagonalQuadratic, Fin.sum_univ_two, x]
  have hisotropic := htail.isotropic_of hhyperbolic
  exact ((not_diagonalIsotropic_iff_diagonalAnisotropic _).2
    (heClassicP2DiscriminantTail_anisotropic (K := K))) hisotropic

/-! ## The two `(n+1)`-ary prefixes used in Lemmas 7.5(iii) and 7.9 -/

/-- The residual ternary row `[1,-c,-1]` of the first `P` prefix. -/
noncomputable def heClassicEvenP1Ternary (c : Kˣ) : Fin 3 → Kˣ :=
  ![1, -c, -1]

/-- The residual ternary row `[1,-c,-c#]` of the second `P` prefix. -/
noncomputable def heClassicEvenP2Ternary
    (c cSharp : Kˣ) : Fin 3 → Kˣ :=
  ![1, -c, -cSharp]

/-- The first `2*pairs+3` coefficients of `P₁^(2*pairs+4)(c)`. -/
noncomputable def heClassicEvenP1Prefix (pairs : Nat) (c : Kˣ) :
    Fin (2 * pairs + 3) → Kˣ :=
  Fin.append (standardHyperbolicEndpointTower (K := K) pairs)
    (heClassicEvenP1Ternary c)

/-- The first `2*pairs+3` coefficients of `P₂^(2*pairs+4)(c)`. -/
noncomputable def heClassicEvenP2Prefix
    (pairs : Nat) (c cSharp : Kˣ) : Fin (2 * pairs + 3) → Kˣ :=
  Fin.append (standardHyperbolicEndpointTower (K := K) pairs)
    (heClassicEvenP2Ternary c cSharp)

/-- The displayed first `P` prefix is literally the initial coefficient
segment of the full row. -/
theorem heClassicEvenP1Prefix_eq_initial
    (pairs : Nat) (c : Kˣ) :
    (fun i : Fin (2 * pairs + 3) ↦
      heClassicEvenP1 (K := K) pairs c i.castSucc) =
      heClassicEvenP1Prefix (K := K) pairs c := by
  funext i
  by_cases hhead : i.val < 2 * pairs
  · let j : Fin (2 * pairs) := ⟨i.val, hhead⟩
    let k : Fin (2 * pairs + 2) := ⟨i.val, by omega⟩
    have hiP : i.castSucc = Fin.castAdd 2 k := Fin.ext rfl
    have hk : k = Fin.castAdd 2 j := Fin.ext rfl
    have hiPrefix : i = Fin.castAdd 3 j := Fin.ext rfl
    calc
      heClassicEvenP1 (K := K) pairs c i.castSucc =
          standardHyperbolicEndpointTower (K := K) pairs j := by
            rw [hiP, heClassicEvenP1_prefix, hk, heClassicEvenC1,
              Fin.append_left, heClassicScaledHyperbolicTower_zero]
      _ = heClassicEvenP1Prefix (K := K) pairs c i := by
        rw [heClassicEvenP1Prefix, hiPrefix, Fin.append_left]
  · have hlast : i.val = 2 * pairs ∨ i.val = 2 * pairs + 1 ∨
        i.val = 2 * pairs + 2 := by
      omega
    rcases hlast with hzero | hone | htwo
    · have hiP : i.castSucc = Fin.castAdd 2
          (Fin.natAdd (2 * pairs) (0 : Fin 2)) := Fin.ext hzero
      have hiPrefix : i = Fin.natAdd (2 * pairs) (0 : Fin 3) :=
        Fin.ext hzero
      calc
        heClassicEvenP1 (K := K) pairs c i.castSucc = 1 := by
          rw [hiP, heClassicEvenP1_prefix, heClassicEvenC1_tail]
          rfl
        _ = heClassicEvenP1Prefix (K := K) pairs c i := by
          rw [heClassicEvenP1Prefix, hiPrefix, Fin.append_right]
          rfl
    · have hiP : i.castSucc = Fin.castAdd 2
          (Fin.natAdd (2 * pairs) (1 : Fin 2)) := Fin.ext hone
      have hiPrefix : i = Fin.natAdd (2 * pairs) (1 : Fin 3) :=
        Fin.ext hone
      calc
        heClassicEvenP1 (K := K) pairs c i.castSucc = -c := by
          rw [hiP, heClassicEvenP1_prefix, heClassicEvenC1_tail]
          rfl
        _ = heClassicEvenP1Prefix (K := K) pairs c i := by
          rw [heClassicEvenP1Prefix, hiPrefix, Fin.append_right]
          rfl
    · have hiP : i.castSucc =
          Fin.natAdd (2 * pairs + 2) (0 : Fin 2) := Fin.ext htwo
      have hiPrefix : i = Fin.natAdd (2 * pairs) (2 : Fin 3) :=
        Fin.ext htwo
      calc
        heClassicEvenP1 (K := K) pairs c i.castSucc = -1 := by
          rw [hiP, heClassicEvenP1_tail_zero_value]
        _ = heClassicEvenP1Prefix (K := K) pairs c i := by
          rw [heClassicEvenP1Prefix, hiPrefix, Fin.append_right]
          rfl

/-- The displayed second `P` prefix is literally the initial coefficient
segment of the full row. -/
theorem heClassicEvenP2Prefix_eq_initial
    (pairs : Nat) (c cSharp : Kˣ) :
    (fun i : Fin (2 * pairs + 3) ↦
      heClassicEvenP2 (K := K) pairs c cSharp i.castSucc) =
      heClassicEvenP2Prefix (K := K) pairs c cSharp := by
  funext i
  by_cases hhead : i.val < 2 * pairs
  · let j : Fin (2 * pairs) := ⟨i.val, hhead⟩
    let k : Fin (2 * pairs + 2) := ⟨i.val, by omega⟩
    have hiP : i.castSucc = Fin.castAdd 2 k := Fin.ext rfl
    have hk : k = Fin.castAdd 2 j := Fin.ext rfl
    have hiPrefix : i = Fin.castAdd 3 j := Fin.ext rfl
    calc
      heClassicEvenP2 (K := K) pairs c cSharp i.castSucc =
          standardHyperbolicEndpointTower (K := K) pairs j := by
            rw [hiP, heClassicEvenP2_prefix, hk, heClassicEvenC1,
              Fin.append_left, heClassicScaledHyperbolicTower_zero]
      _ = heClassicEvenP2Prefix (K := K) pairs c cSharp i := by
        rw [heClassicEvenP2Prefix, hiPrefix, Fin.append_left]
  · have hlast : i.val = 2 * pairs ∨ i.val = 2 * pairs + 1 ∨
        i.val = 2 * pairs + 2 := by
      omega
    rcases hlast with hzero | hone | htwo
    · have hiP : i.castSucc = Fin.castAdd 2
          (Fin.natAdd (2 * pairs) (0 : Fin 2)) := Fin.ext hzero
      have hiPrefix : i = Fin.natAdd (2 * pairs) (0 : Fin 3) :=
        Fin.ext hzero
      calc
        heClassicEvenP2 (K := K) pairs c cSharp i.castSucc = 1 := by
          rw [hiP, heClassicEvenP2_prefix, heClassicEvenC1_tail]
          rfl
        _ = heClassicEvenP2Prefix (K := K) pairs c cSharp i := by
          rw [heClassicEvenP2Prefix, hiPrefix, Fin.append_right]
          rfl
    · have hiP : i.castSucc = Fin.castAdd 2
          (Fin.natAdd (2 * pairs) (1 : Fin 2)) := Fin.ext hone
      have hiPrefix : i = Fin.natAdd (2 * pairs) (1 : Fin 3) :=
        Fin.ext hone
      calc
        heClassicEvenP2 (K := K) pairs c cSharp i.castSucc = -c := by
          rw [hiP, heClassicEvenP2_prefix, heClassicEvenC1_tail]
          rfl
        _ = heClassicEvenP2Prefix (K := K) pairs c cSharp i := by
          rw [heClassicEvenP2Prefix, hiPrefix, Fin.append_right]
          rfl
    · have hiP : i.castSucc =
          Fin.natAdd (2 * pairs + 2) (0 : Fin 2) := Fin.ext htwo
      have hiPrefix : i = Fin.natAdd (2 * pairs) (2 : Fin 3) :=
        Fin.ext htwo
      calc
        heClassicEvenP2 (K := K) pairs c cSharp i.castSucc =
            -cSharp := by
          rw [hiP, heClassicEvenP2_tail_zero_value]
        _ = heClassicEvenP2Prefix (K := K) pairs c cSharp i := by
          rw [heClassicEvenP2Prefix, hiPrefix, Fin.append_right]
          rfl

/-- Every first `P` prefix embeds in its full coefficient space. -/
theorem heClassicEvenP1Prefix_represents_full
    (pairs : Nat) (c : Kˣ) :
    DiagonalRepresents
      (diagonalUnitCoefficients
        (heClassicEvenP1Prefix (K := K) pairs c))
      (diagonalUnitCoefficients
        (heClassicEvenP1 (K := K) pairs c)) := by
  have h := DiagonalRepresents.prefixSucc
    (diagonalUnitCoefficients (heClassicEvenP1 (K := K) pairs c))
  convert h using 1
  funext i
  exact congrArg Units.val
    (congrFun (heClassicEvenP1Prefix_eq_initial
      (K := K) pairs c) i).symm

/-- Every second `P` prefix embeds in its full coefficient space. -/
theorem heClassicEvenP2Prefix_represents_full
    (pairs : Nat) (c cSharp : Kˣ) :
    DiagonalRepresents
      (diagonalUnitCoefficients
        (heClassicEvenP2Prefix (K := K) pairs c cSharp))
      (diagonalUnitCoefficients
        (heClassicEvenP2 (K := K) pairs c cSharp)) := by
  have h := DiagonalRepresents.prefixSucc
    (diagonalUnitCoefficients
      (heClassicEvenP2 (K := K) pairs c cSharp))
  convert h using 1
  funext i
  exact congrArg Units.val
    (congrFun (heClassicEvenP2Prefix_eq_initial
      (K := K) pairs c cSharp) i).symm

/-! ## The exact isotropic/anisotropic prefix dichotomy -/

/-- The residual ternary in `P₁(omega)` is isotropic. -/
theorem heClassicEvenP1OmegaTernary_isotropic :
    DiagonalIsotropic
      (diagonalUnitCoefficients
        (heClassicEvenP1Ternary (K := K)
          (heClassicOmega (K := K)))) := by
  rw [he2022ClassicProposition210]
  simp [heClassicEvenP1Ternary]

/-- The residual ternary in `P₂(omega)` is anisotropic. -/
theorem heClassicEvenP2OmegaTernary_anisotropic :
    DiagonalAnisotropic
      (diagonalUnitCoefficients
        (heClassicEvenP2Ternary (K := K)
          (heClassicOmega (K := K))
          (heClassicOmegaSharp (K := K)))) := by
  rw [he2022ClassicProposition210_anisotropic]
  simpa [heClassicEvenP2Ternary, hilbertSymbol_comm] using
    (heClassicOmegaSharp_hilbert_neg (K := K))

/-- The first residual ternary has determinant order zero. -/
theorem heClassicEvenP1OmegaTernary_determinantOrder :
    ordUnit K (diagonalUnitDeterminant
      (heClassicEvenP1Ternary (K := K)
        (heClassicOmega (K := K)))) = 0 := by
  simp [heClassicEvenP1Ternary, diagonalUnitDeterminant,
    Fin.prod_univ_three, heClassicOmega_order]

/-- The second residual ternary has determinant order zero. -/
theorem heClassicEvenP2OmegaTernary_determinantOrder :
    ordUnit K (diagonalUnitDeterminant
      (heClassicEvenP2Ternary (K := K)
        (heClassicOmega (K := K))
        (heClassicOmegaSharp (K := K)))) = 0 := by
  simp [heClassicEvenP2Ternary, diagonalUnitDeterminant,
    Fin.prod_univ_three, ordUnit_mul, heClassicOmega_order,
    heClassicOmegaSharp_order]

/-- Lemma 7.9(ii), matching branch: `H₁ⁿ(1)` embeds in the first
`(n+1)`-ary prefix. -/
theorem he2022ClassicLemma79ii_evenHOne_represents_P1Prefix
    (pairs : Nat) :
    DiagonalRepresents
      (diagonalUnitCoefficients (heClassicEvenH (K := K) pairs 1))
      (diagonalUnitCoefficients
        (heClassicEvenP1Prefix (K := K) pairs
          (heClassicOmega (K := K)))) := by
  have honeOrder : ordUnit K (1 : Kˣ) = 0 := by
    have h := ordUnit_mul K (1 : Kˣ) 1
    simp only [mul_one] at h
    omega
  have hnormal := (heClassicLemma211First_represents_evenHOne
    (K := K) pairs honeOrder).symm_of_sameRank
  have hselection := (he2022ClassicLemma211ii (K := K) pairs
    (heClassicEvenP1Ternary (K := K) (heClassicOmega (K := K)))
    (heClassicEvenP1OmegaTernary_determinantOrder (K := K))
    (heClassicEvenP1OmegaTernary_isotropic (K := K))).1
  exact hnormal.trans (by
    simpa only [heClassicEvenP1Prefix,
      diagonalUnitCoefficients_append] using hselection)

/-- Lemma 7.9(ii), mismatching branch: `H₁ⁿ(Delta)` does not embed
in the first `(n+1)`-ary prefix. -/
theorem he2022ClassicLemma79ii_evenHDiscriminant_not_represents_P1Prefix
    (pairs : Nat) (heOne : ramificationIndex K = 1) :
    let delta :=
      (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
    ¬ DiagonalRepresents
      (diagonalUnitCoefficients
        (heClassicEvenH (K := K) pairs delta))
      (diagonalUnitCoefficients
        (heClassicEvenP1Prefix (K := K) pairs
          (heClassicOmega (K := K)))) := by
  dsimp only
  intro hrep
  have hnormal :=
    heClassicLemma211Second_represents_evenHDiscriminant
      (K := K) pairs heOne
  have hbad := hnormal.trans hrep
  have hselection := (he2022ClassicLemma211ii (K := K) pairs
    (heClassicEvenP1Ternary (K := K) (heClassicOmega (K := K)))
    (heClassicEvenP1OmegaTernary_determinantOrder (K := K))
    (heClassicEvenP1OmegaTernary_isotropic (K := K))).2
  apply hselection
  simpa only [heClassicEvenP1Prefix,
    diagonalUnitCoefficients_append] using hbad

/-- Lemma 7.9(ii), matching branch: `H₁ⁿ(Delta)` embeds in the
second `(n+1)`-ary prefix. -/
theorem he2022ClassicLemma79ii_evenHDiscriminant_represents_P2Prefix
    (pairs : Nat) (heOne : ramificationIndex K = 1) :
    let delta :=
      (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
    DiagonalRepresents
      (diagonalUnitCoefficients
        (heClassicEvenH (K := K) pairs delta))
      (diagonalUnitCoefficients
        (heClassicEvenP2Prefix (K := K) pairs
          (heClassicOmega (K := K))
          (heClassicOmegaSharp (K := K)))) := by
  dsimp only
  have hnormal :=
    (heClassicLemma211Second_represents_evenHDiscriminant
      (K := K) pairs heOne).symm_of_sameRank
  have hselection := (he2022ClassicLemma211iii (K := K) pairs
    (heClassicEvenP2Ternary (K := K) (heClassicOmega (K := K))
      (heClassicOmegaSharp (K := K)))
    (heClassicEvenP2OmegaTernary_determinantOrder (K := K))
    (heClassicEvenP2OmegaTernary_anisotropic (K := K))).1
  exact hnormal.trans (by
    simpa only [heClassicEvenP2Prefix,
      diagonalUnitCoefficients_append] using hselection)

/-- Lemma 7.9(ii), mismatching branch: `H₁ⁿ(1)` does not embed in
the second `(n+1)`-ary prefix. -/
theorem he2022ClassicLemma79ii_evenHOne_not_represents_P2Prefix
    (pairs : Nat) :
    ¬ DiagonalRepresents
      (diagonalUnitCoefficients (heClassicEvenH (K := K) pairs 1))
      (diagonalUnitCoefficients
        (heClassicEvenP2Prefix (K := K) pairs
          (heClassicOmega (K := K))
          (heClassicOmegaSharp (K := K)))) := by
  intro hrep
  have honeOrder : ordUnit K (1 : Kˣ) = 0 := by
    have h := ordUnit_mul K (1 : Kˣ) 1
    simp only [mul_one] at h
    omega
  have hnormal := heClassicLemma211First_represents_evenHOne
    (K := K) pairs honeOrder
  have hbad := hnormal.trans hrep
  have hselection := (he2022ClassicLemma211iii (K := K) pairs
    (heClassicEvenP2Ternary (K := K) (heClassicOmega (K := K))
      (heClassicOmegaSharp (K := K)))
    (heClassicEvenP2OmegaTernary_determinantOrder (K := K))
    (heClassicEvenP2OmegaTernary_anisotropic (K := K))).2
  apply hselection
  simpa only [heClassicEvenP2Prefix,
    diagonalUnitCoefficients_append] using hbad

/-! ## Lemma 7.5(iii) -/

/-- Lemma 7.5(iii), first representation. -/
theorem he2022ClassicLemma75iii_evenHOne_represents_P1Omega
    (pairs : Nat) :
    DiagonalRepresents
      (diagonalUnitCoefficients (heClassicEvenH (K := K) pairs 1))
      (diagonalUnitCoefficients
        (heClassicEvenP1 (K := K) pairs
          (heClassicOmega (K := K)))) :=
  (he2022ClassicLemma79ii_evenHOne_represents_P1Prefix
    (K := K) pairs).trans
      (heClassicEvenP1Prefix_represents_full
        (K := K) pairs (heClassicOmega (K := K)))

/-- Lemma 7.5(iii), second representation. -/
theorem he2022ClassicLemma75iii_evenHDiscriminant_represents_P2Omega
    (pairs : Nat) (heOne : ramificationIndex K = 1) :
    let delta :=
      (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
    DiagonalRepresents
      (diagonalUnitCoefficients
        (heClassicEvenH (K := K) pairs delta))
      (diagonalUnitCoefficients
        (heClassicEvenP2 (K := K) pairs
          (heClassicOmega (K := K))
          (heClassicOmegaSharp (K := K)))) := by
  dsimp only
  exact (he2022ClassicLemma79ii_evenHDiscriminant_represents_P2Prefix
    (K := K) pairs heOne).trans
      (heClassicEvenP2Prefix_represents_full
        (K := K) pairs (heClassicOmega (K := K))
          (heClassicOmegaSharp (K := K)))

end Bong
