/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.HilbertDefectChoice
import Bong.Bong.ResidueDefectProductProof
import Bong.Dyadic.HilbertSymbolProof

/-!
# Hilbert partners of prescribed dyadic quadratic defect

This file proves Hsia's duality lemma (Hsia 1975, Lemma 3) from the explicit
prime-discriminant binary theorem in O'Meara 63:11.  It then derives all three
local choices used in Beli (2019), Lemma 8.2 and installs the corresponding
concrete law instance.
-/

namespace Bong

open Dyadic

universe u

namespace BONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

private theorem isSquare_mul_discriminant_of_isSquare_div_discriminant
    (a : Kˣ)
    (h : IsSquare
      (a / (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit)) :
    IsSquare
      (a * (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit) := by
  let delta : Kˣ :=
    (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
  rcases h with ⟨s, hs⟩
  refine ⟨s * delta, ?_⟩
  change a * delta = (s * delta) * (s * delta)
  have ha : a = s * s * delta := by
    calc
      a = (a / delta) * delta := by simp
      _ = (s * s) * delta := by rw [hs]
  rw [ha]
  ac_rfl

/-- The endpoint Hilbert pairing: defect zero pairs negatively with the
unique nonsquare unit class of defect `2e`. -/
theorem hilbert_eq_neg_one_of_defect_zero_twoE_proved
    (a b : Kˣ)
    (ha : quadraticDefect K a = 0)
    (hb : quadraticDefect K b =
      ((2 * ramificationIndex K : Nat) : ℕ∞)) :
    hilbertSymbol K a b = -1 := by
  let delta : Kˣ :=
    (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
  have hodd : Odd (ordUnit K a) :=
    odd_ordUnit_of_quadraticDefect_eq_zero a ha
  have hbGe : ((2 * ramificationIndex K : Nat) : ℕ∞) ≤
      quadraticDefect K b := hb.ge
  rcases isSquare_or_isSquare_div_discriminant_of_defect_ge_twoE
      b hbGe with hbSquare | hbDiv
  · have htop := quadraticDefect_eq_top_of_isSquare K hbSquare
    rw [hb] at htop
    exact (ENat.coe_ne_top _ htop).elim
  · have hbDelta : IsSquare (b * delta) := by
      exact isSquare_mul_discriminant_of_isSquare_div_discriminant b hbDiv
    have hne : hilbertSymbol K b a ≠ 1 :=
      hilbertSymbol_ne_one_of_isSquare_mul_discriminant_of_odd_order
        hbDelta hodd
    have hneg : hilbertSymbol K b a = -1 :=
      (Int.units_eq_one_or (hilbertSymbol K b a)).resolve_left hne
    exact (hilbertSymbol_comm K a b).trans hneg

/-- Hsia's duality lemma in the interior range, stated in the form needed
for the boundary case of Beli (2019), Lemma 8.2(i). -/
theorem exists_negative_same_defect_of_sum_eq_twoE_interior
    (a reference : Kˣ)
    (haZero : quadraticDefect K a ≠ 0)
    (hrefZero : quadraticDefect K reference ≠ 0)
    (hsum : quadraticDefect K a + quadraticDefect K reference =
      ((2 * ramificationIndex K : Nat) : ℕ∞)) :
    ∃ b : Kˣ,
      quadraticDefect K b = quadraticDefect K reference ∧
        hilbertSymbol K a b = -1 := by
  have haFinite : quadraticDefect K a ≠ ⊤ := by
    intro haTop
    rw [haTop] at hsum
    exact WithTop.top_ne_coe hsum
  have hrefFinite : quadraticDefect K reference ≠ ⊤ := by
    intro hrefTop
    rw [hrefTop, add_top] at hsum
    exact WithTop.top_ne_coe hsum
  let d : Nat := (quadraticDefect K a).toNat
  let d' : Nat := (quadraticDefect K reference).toNat
  have haCoe : quadraticDefect K a = (d : ℕ∞) := by
    simpa only [d] using (ENat.coe_toNat haFinite).symm
  have hrefCoe : quadraticDefect K reference = (d' : ℕ∞) := by
    simpa only [d'] using (ENat.coe_toNat hrefFinite).symm
  have hsumNat : d + d' = 2 * ramificationIndex K := by
    rw [haCoe, hrefCoe] at hsum
    exact_mod_cast hsum
  have hdPos : 0 < d := by
    have hdNe : d ≠ 0 := by
      intro hd
      apply haZero
      rw [haCoe, hd]
      rfl
    omega
  have hd'Pos : 0 < d' := by
    have hd'Ne : d' ≠ 0 := by
      intro hd'
      apply hrefZero
      rw [hrefCoe, hd']
      rfl
    omega
  have hdLt : d < 2 * ramificationIndex K := by omega
  have hd'Lt : d' < 2 * ramificationIndex K := by omega
  obtain ⟨v, r, t, hvUnit, hvDefect, hfactor, hvField, htOrder⟩ :=
    exists_exact_principal_representation a haFinite haZero
  have htOrderD : ord K t = ((d : Int) : WithTop Int) := by
    simpa only [d] using htOrder
  have hvLt : quadraticDefect K v <
      ((2 * ramificationIndex K : Nat) : ℕ∞) := by
    rw [hvDefect, haCoe]
    exact_mod_cast hdLt
  have hdOdd : Odd d := by
    have h := quadraticDefect_toNat_odd_of_unit_of_lt_two_mul_e
      (K := K) v hvUnit hvLt
    simpa only [hvDefect, d] using h
  let laws : DyadicDiscriminantClassLaws K := inferInstance
  let delta : Kˣ := laws.discriminantUnit
  let rho : K := laws.rho
  have hfourRhoOrder : ord K ((4 : K) * rho) =
      (((2 * ramificationIndex K : Nat) : Int) : WithTop Int) := by
    rw [show (4 : K) = 2 * 2 by norm_num, ord_mul, ord_mul,
      laws.rho_isValuationUnit, add_zero, ← ramificationIndex_spec]
    norm_cast
    ring
  have htLtFourRho : ord K t < ord K ((4 : K) * rho) := by
    rw [htOrderD, hfourRhoOrder]
    exact_mod_cast hdLt
  have htNe : t ≠ 0 := by
    apply (ord_eq_top_iff K).not.mp
    rw [htOrderD]
    exact WithTop.coe_ne_top
  let complement : Nat := 2 * ramificationIndex K - d
  have hcomplementEq : complement = d' := by
    dsimp only [complement]
    omega
  have hcomplementPos : 0 < complement := by
    rw [hcomplementEq]
    exact hd'Pos
  have hcomplementLt : complement < 2 * ramificationIndex K := by
    dsimp only [complement]
    omega
  have hcomplementOdd : Odd complement := by
    rcases hdOdd with ⟨k, hk⟩
    refine ⟨ramificationIndex K - k - 1, ?_⟩
    dsimp only [complement]
    omega
  let q : K := (4 : K) * rho / t
  have hqOrder : ord K q =
      ((complement : Int) : WithTop Int) := by
    dsimp only [q]
    rw [div_eq_mul_inv, ord_mul, AddValuation.map_inv,
      hfourRhoOrder, htOrderD]
    norm_cast
    dsimp only [complement]
    omega
  have hqPos : (0 : WithTop Int) < ord K q := by
    rw [hqOrder]
    exact_mod_cast hcomplementPos
  have hfOrder : ord K (1 + q) = 0 := by
    have hlt : ord K (1 : K) < ord K q := by
      simpa only [ord_one] using hqPos
    simpa only [ord_one] using (ord K).map_add_eq_of_lt_left hlt
  have hfNe : 1 + q ≠ 0 := by
    apply (ord_eq_top_iff K).not.mp
    rw [hfOrder]
    exact WithTop.coe_ne_top
  let f : Kˣ := Units.mk0 (1 + q) hfNe
  have hfField : (f : K) = 1 + q := rfl
  have hfDefect : quadraticDefect K f = (complement : ℕ∞) :=
    quadraticDefect_eq_of_principal_exact_odd f q complement hfField
      hqOrder hcomplementPos hcomplementOdd hcomplementLt
  have hfDefectReference :
      quadraticDefect K f = quadraticDefect K reference := by
    rw [hfDefect, hrefCoe, hcomplementEq]
  let w : K := (delta : K) - (v : K)
  have hwField : w = -((4 : K) * rho + t) := by
    dsimp only [w, delta, rho]
    rw [laws.discriminant_eq_one_sub_four_mul_rho, hvField]
    ring
  have hsumOrder : ord K (t + (4 : K) * rho) = ord K t :=
    (ord K).map_add_eq_of_lt_left htLtFourRho
  have hwOrder : ord K w = ((d : Int) : WithTop Int) := by
    rw [hwField, ord_neg, add_comm, hsumOrder, htOrderD]
  have hwNe : w ≠ 0 := by
    apply (ord_eq_top_iff K).not.mp
    rw [hwOrder]
    exact WithTop.coe_ne_top
  let wu : Kˣ := Units.mk0 w hwNe
  have hwuOrder : ordUnit K wu = (d : Int) := by
    apply WithTop.coe_injective
    rw [coe_ordUnit]
    exact hwOrder
  have hwuOdd : Odd (ordUnit K wu) := by
    rw [hwuOrder]
    exact_mod_cast hdOdd
  have hrepDelta : BinaryRepresentsValue v wu delta := by
    refine ⟨1, 1, ?_⟩
    change (v : K) * 1 ^ 2 + w * 1 ^ 2 = (delta : K)
    dsimp only [w]
    ring
  have hnotOne : ¬BinaryRepresentsValue v wu (1 : Kˣ) := by
    intro hone
    exact primeBinary_not_represents_one_and_discriminant v wu hvUnit hwuOdd
      ⟨hone, hrepDelta⟩
  have hwuNonNorm : ¬IsQuadraticNorm K v wu := by
    intro hnorm
    exact hnotOne (binaryRepresents_one_of_isQuadraticNorm v wu hnorm)
  have hhilbertW : hilbertSymbol K v wu = -1 :=
    (hilbertSymbol_eq_neg_one_iff K v wu).2 hwuNonNorm
  let negT : Kˣ := Units.mk0 (-t) (neg_ne_zero.mpr htNe)
  have hrepOne : BinaryRepresentsValue v negT (1 : Kˣ) := by
    refine ⟨1, 1, ?_⟩
    change (v : K) * 1 ^ 2 + (-t) * 1 ^ 2 = (1 : K)
    rw [hvField]
    ring
  have hhilbertNegT : hilbertSymbol K v negT = 1 :=
    (hilbertSymbol_eq_one_iff K v negT).2
      (isQuadraticNorm_of_binaryRepresents_one v negT hrepOne)
  have hproduct : f * negT = wu := by
    apply Units.ext
    change (1 + q) * (-t) = w
    dsimp only [q]
    rw [hwField]
    field_simp [htNe]
    ring
  have hhilbertF : hilbertSymbol K v f = -1 := by
    have hmul := hilbertSymbol_mul_right K v f negT
    rw [hproduct, hhilbertW, hhilbertNegT, mul_one] at hmul
    exact hmul.symm
  have hhilbertA : hilbertSymbol K a f = -1 := by
    rw [hfactor, hilbertSymbol_mul_square_left]
    exact hhilbertF
  exact ⟨f, hfDefectReference, hhilbertA⟩

/-- Boundary form of Hsia's duality lemma, including the two endpoints. -/
theorem exists_negative_same_defect_of_sum_eq_twoE_proved
    (a reference : Kˣ)
    (hsum : quadraticDefect K a + quadraticDefect K reference =
      ((2 * ramificationIndex K : Nat) : ℕ∞)) :
    ∃ b : Kˣ,
      quadraticDefect K b = quadraticDefect K reference ∧
        hilbertSymbol K a b = -1 := by
  by_cases haZero : quadraticDefect K a = 0
  · have hrefTwoE : quadraticDefect K reference =
        ((2 * ramificationIndex K : Nat) : ℕ∞) := by
      simpa only [haZero, zero_add] using hsum
    let delta : Kˣ :=
      (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
    have hdeltaDefect : quadraticDefect K delta =
        ((2 * ramificationIndex K : Nat) : ℕ∞) := by
      exact (inferInstance : DyadicDiscriminantClassLaws K).discriminant_defect
    refine ⟨delta, hdeltaDefect.trans hrefTwoE.symm, ?_⟩
    exact hilbert_eq_neg_one_of_defect_zero_twoE_proved
      a delta haZero hdeltaDefect
  · by_cases hrefZero : quadraticDefect K reference = 0
    · have haTwoE : quadraticDefect K a =
          ((2 * ramificationIndex K : Nat) : ℕ∞) := by
        simpa only [hrefZero, add_zero] using hsum
      refine ⟨reference, rfl, ?_⟩
      rw [hilbertSymbol_comm K a reference]
      exact hilbert_eq_neg_one_of_defect_zero_twoE_proved
        reference a hrefZero haTwoE
    · exact exists_negative_same_defect_of_sum_eq_twoE_interior
        a reference haZero hrefZero hsum

/-- Every nonsquare has a negative Hilbert partner at the complementary
quadratic defect. -/
theorem exists_complementary_defect_hilbert_neg_proved
    (a : Kˣ) (haNotSquare : ¬IsSquare a) :
    ∃ c : Kˣ,
      quadraticDefect K a + quadraticDefect K c =
          ((2 * ramificationIndex K : Nat) : ℕ∞) ∧
        hilbertSymbol K a c = -1 := by
  by_cases haZero : quadraticDefect K a = 0
  · let delta : Kˣ :=
      (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
    have hdeltaDefect : quadraticDefect K delta =
        ((2 * ramificationIndex K : Nat) : ℕ∞) := by
      exact (inferInstance : DyadicDiscriminantClassLaws K).discriminant_defect
    refine ⟨delta, ?_,
      hilbert_eq_neg_one_of_defect_zero_twoE_proved
        a delta haZero hdeltaDefect⟩
    rw [haZero, zero_add, hdeltaDefect]
  · have haFinite : quadraticDefect K a ≠ ⊤ := by
      intro haTop
      exact haNotSquare
        ((quadraticDefect_eq_top_iff_isSquare (K := K) a).mp haTop)
    have haLe : quadraticDefect K a ≤
        ((2 * ramificationIndex K : Nat) : ℕ∞) :=
      quadraticDefect_le_two_mul_e_of_not_isSquare (K := K) haNotSquare
    by_cases haTwoE : quadraticDefect K a =
        ((2 * ramificationIndex K : Nat) : ℕ∞)
    · let p : Kˣ := uniformizerPowerUnit K 1
      have hpOrder : ordUnit K p = 1 :=
        ordUnit_uniformizerPowerUnit (K := K) 1
      have hpOdd : Odd (ordUnit K p) := by
        rw [hpOrder]
        exact odd_one
      have hpDefect : quadraticDefect K p = 0 :=
        quadraticDefect_eq_zero_of_odd_ordUnit p hpOdd
      refine ⟨p, ?_, ?_⟩
      · rw [haTwoE, hpDefect, add_zero]
      · rw [hilbertSymbol_comm K a p]
        exact hilbert_eq_neg_one_of_defect_zero_twoE_proved
          p a hpDefect haTwoE
    · have haLt : quadraticDefect K a <
          ((2 * ramificationIndex K : Nat) : ℕ∞) :=
        lt_of_le_of_ne haLe haTwoE
      let d : Nat := (quadraticDefect K a).toNat
      have haCoe : quadraticDefect K a = (d : ℕ∞) := by
        simpa only [d] using (ENat.coe_toNat haFinite).symm
      have hdPos : 0 < d := by
        have hdNe : d ≠ 0 := by
          intro hd
          apply haZero
          rw [haCoe, hd]
          rfl
        omega
      have hdLt : d < 2 * ramificationIndex K := by
        rw [haCoe] at haLt
        exact_mod_cast haLt
      obtain ⟨v, _r, _t, hvUnit, hvDefect, _hfactor, _hvField, _htOrder⟩ :=
        exists_exact_principal_representation a haFinite haZero
      have hvLt : quadraticDefect K v <
          ((2 * ramificationIndex K : Nat) : ℕ∞) := by
        rwa [hvDefect]
      have hdOdd : Odd d := by
        have h := quadraticDefect_toNat_odd_of_unit_of_lt_two_mul_e
          (K := K) v hvUnit hvLt
        simpa only [hvDefect, d] using h
      let complement : Nat := 2 * ramificationIndex K - d
      have hcomplementPos : 0 < complement := by
        dsimp only [complement]
        omega
      have hcomplementLt : complement < 2 * ramificationIndex K := by
        dsimp only [complement]
        omega
      have hcomplementOdd : Odd complement := by
        rcases hdOdd with ⟨k, hk⟩
        refine ⟨ramificationIndex K - k - 1, ?_⟩
        dsimp only [complement]
        omega
      rcases exists_unit_quadraticDefect_eq_odd
          (K := K) complement hcomplementPos hcomplementOdd hcomplementLt with
        ⟨reference, _hrefUnit, hrefDefect⟩
      have hsum : quadraticDefect K a + quadraticDefect K reference =
          ((2 * ramificationIndex K : Nat) : ℕ∞) := by
        rw [haCoe, hrefDefect]
        norm_cast
        dsimp only [complement]
        omega
      rcases exists_negative_same_defect_of_sum_eq_twoE_interior
          a reference haZero (by rw [hrefDefect]; exact_mod_cast hcomplementPos.ne')
          hsum with
        ⟨c, hcDefect, hcHilbert⟩
      exact ⟨c, by rwa [hcDefect], hcHilbert⟩

/-- The first choice field in Beli (2019), Lemma 8.2 follows from the
boundary duality class by multiplying with the prescribed reference class. -/
theorem exists_negative_same_defect_of_sum_le_proved
    (a reference : Kˣ)
    (h : quadraticDefect K a + quadraticDefect K reference ≤
      ((2 * ramificationIndex K : Nat) : ℕ∞)) :
    ∃ b : Kˣ,
      quadraticDefect K b = quadraticDefect K reference ∧
        hilbertSymbol K a b = -1 := by
  rcases h.eq_or_lt with heq | hlt
  · exact exists_negative_same_defect_of_sum_eq_twoE_proved
      a reference heq
  · have haNotSquare : ¬IsSquare a := by
      intro haSquare
      have haTop := quadraticDefect_eq_top_of_isSquare K haSquare
      rw [haTop] at hlt
      exact (not_lt_of_ge le_top hlt)
    rcases exists_complementary_defect_hilbert_neg_proved a haNotSquare with
      ⟨c, hcSum, hcNeg⟩
    have haFinite : quadraticDefect K a ≠ ⊤ := by
      intro haTop
      exact haNotSquare
        ((quadraticDefect_eq_top_iff_isSquare (K := K) a).mp haTop)
    have hrefLt : quadraticDefect K reference < quadraticDefect K c := by
      apply (ENat.add_lt_add_iff_left haFinite).mp
      rw [hcSum]
      exact hlt
    by_cases hrefNeg : hilbertSymbol K a reference = -1
    · exact ⟨reference, rfl, hrefNeg⟩
    · have hrefOne : hilbertSymbol K a reference = 1 :=
        (Int.units_eq_one_or (hilbertSymbol K a reference)).resolve_right
          hrefNeg
      refine ⟨reference * c, ?_, ?_⟩
      · exact quadraticDefect_mul_eq_left_of_lt_right (K := K) hrefLt
      · rw [hilbertSymbol_mul_right, hrefOne, hcNeg]
        norm_num

/-- Under a strict defect-sum inequality the complementary negative partner
has strictly larger defect than the prescribed reference. -/
theorem exists_higher_defect_negative_of_sum_lt_proved
    (a reference : Kˣ)
    (h : quadraticDefect K a + quadraticDefect K reference <
      ((2 * ramificationIndex K : Nat) : ℕ∞)) :
    ∃ c : Kˣ,
      quadraticDefect K reference < quadraticDefect K c ∧
        hilbertSymbol K a c = -1 := by
  have haNotSquare : ¬IsSquare a := by
    intro haSquare
    have haTop := quadraticDefect_eq_top_of_isSquare K haSquare
    rw [haTop] at h
    exact (not_lt_of_ge le_top h)
  rcases exists_complementary_defect_hilbert_neg_proved a haNotSquare with
    ⟨c, hcSum, hcNeg⟩
  have haFinite : quadraticDefect K a ≠ ⊤ := by
    intro haTop
    exact haNotSquare
      ((quadraticDefect_eq_top_iff_isSquare (K := K) a).mp haTop)
  refine ⟨c, ?_, hcNeg⟩
  apply (ENat.add_lt_add_iff_left haFinite).mp
  rw [hcSum]
  exact h

/-- Concrete local-field implementation of all three choice fields in
Beli (2019), Lemma 8.2. -/
noncomputable instance dyadicHilbertDefectChoiceLawsProved :
    DyadicHilbertDefectChoiceLaws K where
  exists_negative_same_defect_of_sum_le :=
    exists_negative_same_defect_of_sum_le_proved
  exists_higher_defect_negative_of_sum_lt :=
    exists_higher_defect_negative_of_sum_lt_proved
  hilbert_eq_neg_one_of_zero_twoE a b h := by
    rcases h with h | h
    · exact hilbert_eq_neg_one_of_defect_zero_twoE_proved
        a b h.1 h.2
    · rw [hilbertSymbol_comm K a b]
      exact hilbert_eq_neg_one_of_defect_zero_twoE_proved
        b a h.2 h.1

end BONG

end Bong
