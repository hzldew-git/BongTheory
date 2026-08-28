/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.DiscriminantClassProof
import Bong.Bong.MaximalDefectClassProof
import Bong.Bong.ResidueDefectProductProof
import Bong.Dyadic.UnramifiedNormDirectProof

/-!
# Nondegeneracy of the dyadic Hilbert symbol

This file proves O'Meara 63:13 directly for the project's norm-equation
definition of the Hilbert symbol.  An odd-order square class is detected by
the distinguished unramified discriminant class, the discriminant class is
detected by a uniformizer, and a unit class of intermediate defect is given
the explicit negative partner `alpha = Delta - beta`.

The last case uses O'Meara's chain construction: a hypothetical positive
pairing would make `-alpha * beta`, whose valuation is odd, a norm from the
unramified discriminant extension.  This contradicts the direct norm
classification.  No Hilbert-symbol multiplicativity is assumed.
-/

namespace Bong.Dyadic

universe u

variable {K : Type u} [Field K] [CharZero K]

private theorem diagonal_representation_of_quadraticNorm
    (a b : Kˣ) (h : IsQuadraticNorm K a b) :
    ∃ ξ η : K, (a : K) * ξ ^ 2 + (b : K) * η ^ 2 = 1 := by
  rcases h with ⟨x, y, hxy⟩
  by_cases hx : x = 0
  · subst x
    have hy : y ≠ 0 := by
      intro hy
      subst y
      norm_num at hxy
      exact Units.ne_zero b hxy.symm
    refine ⟨((a : K) + 1) / (2 * (a : K)),
      ((a : K) - 1) / (2 * (a : K) * y), ?_⟩
    have hb : (b : K) = -(a : K) * y ^ 2 := by
      simpa using hxy.symm
    rw [hb]
    field_simp [Units.ne_zero a, hy]
    ring
  · refine ⟨y / x, 1 / x, ?_⟩
    field_simp [hx]
    rw [← hxy]
    ring

omit [CharZero K] in
private theorem norm_identity_of_diagonal_identity
    (delta a b t s : K) (hdelta : delta ≠ 0) (hs : s ≠ 0)
    (hdiag : delta * t ^ 2 + a * b * delta * s ^ 2 = 1) :
    (t / s) ^ 2 - delta * (1 / (delta * s)) ^ 2 = -a * b := by
  field_simp [hdelta, hs]
  linear_combination hdiag

private theorem isQuadraticNorm_neg_mul_of_add
    (delta a b : Kˣ)
    (hdelta : ¬ IsSquare delta)
    (hsum : (delta : K) = (a : K) + (b : K))
    (h : IsQuadraticNorm K a b) :
    IsQuadraticNorm K delta (-a * b) := by
  rcases diagonal_representation_of_quadraticNorm a b h with
    ⟨ξ, η, hrep⟩
  let t : K := ((a : K) * ξ + (b : K) * η) / (delta : K)
  let s : K := (ξ - η) / (delta : K)
  have hdiag :
      (delta : K) * t ^ 2 +
          (a : K) * (b : K) * (delta : K) * s ^ 2 = 1 := by
    calc
      (delta : K) * t ^ 2 +
            (a : K) * (b : K) * (delta : K) * s ^ 2 =
          (a : K) * ξ ^ 2 + (b : K) * η ^ 2 := by
            dsimp only [t, s]
            have habNe : (a : K) + (b : K) ≠ 0 := by
              rw [← hsum]
              exact Units.ne_zero delta
            rw [hsum]
            field_simp [habNe]
            ring
      _ = 1 := hrep
  have hs : s ≠ 0 := by
    intro hs
    have hdeltaSq : IsSquare delta := by
      have htNe : t ≠ 0 := by
        intro ht
        rw [ht, hs] at hdiag
        norm_num at hdiag
      let r : Kˣ := Units.mk0 t⁻¹ (inv_ne_zero htNe)
      refine ⟨r, ?_⟩
      apply Units.ext
      change (delta : K) = t⁻¹ * t⁻¹
      rw [hs, zero_pow (by omega : 2 ≠ 0), mul_zero, add_zero] at hdiag
      field_simp [htNe]
      simpa [pow_two] using hdiag
    exact hdelta hdeltaSq
  refine ⟨t / s, 1 / ((delta : K) * s), ?_⟩
  simp only [Units.val_mul, Units.val_neg]
  exact norm_identity_of_diagonal_identity
    (delta : K) (a : K) (b : K) t s (Units.ne_zero delta) hs hdiag

section Dyadic

variable [ValuativeRel K] [TopologicalSpace K] [DyadicContext K]
  [discriminant : DyadicDiscriminantClassLaws K]
  [DyadicUnramifiedNormLaws K]

omit [DyadicUnramifiedNormLaws K] in
private theorem discriminant_not_square :
    ¬ IsSquare discriminant.discriminantUnit := by
  intro hsquare
  have htop := quadraticDefect_eq_top_of_isSquare K hsquare
  rw [discriminant.discriminant_defect] at htop
  exact ENat.coe_ne_top _ htop

/-- O'Meara's chain construction: if `delta = a + b` and `-a*b` has
odd valuation, then `(a,b) = -1`, because a positive pairing would make
the odd-order element `-a*b` a norm from the unramified discriminant
extension. -/
theorem hilbertSymbol_eq_neg_one_of_add_eq_discriminant_of_product_odd
    (a b : Kˣ)
    (hsum : (discriminant.discriminantUnit : K) = (a : K) + (b : K))
    (hodd : Odd (ordUnit K (-a * b))) :
    hilbertSymbol K a b = -1 := by
  rw [hilbertSymbol_eq_neg_one_iff]
  intro hnorm
  have hdiscNorm : IsQuadraticNorm K discriminant.discriminantUnit (-a * b) :=
    isQuadraticNorm_neg_mul_of_add discriminant.discriminantUnit a b
      (discriminant_not_square (K := K)) hsum hnorm
  have heven : Even (ordUnit K (-a * b)) :=
    (isQuadraticNorm_discriminant_iff_even_order (-a * b)).mp hdiscNorm
  exact Int.not_even_iff_odd.mpr hodd heven

end Dyadic

section ConcreteNondegeneracy

variable [ValuativeRel K] [TopologicalSpace K] [DyadicContext K]

noncomputable local instance concreteDiscriminant :
    DyadicDiscriminantClassLaws K :=
  dyadicDiscriminantClassLawsProved

noncomputable local instance concreteMaximalDefect :
    DyadicMaximalDefectClassLaws K :=
  dyadicMaximalDefectClassLawsProved

noncomputable local instance concreteUnramifiedNorm :
    DyadicUnramifiedNormLaws K :=
  dyadicUnramifiedNormLawsProvedDirect

local instance concreteDefect : QuadraticDefectLaws K :=
  quadraticDefectLawsOfHensel K

private theorem ordUnit_neg_local (x : Kˣ) :
    ordUnit K (-x) = ordUnit K x := by
  apply WithTop.coe_injective
  simp only [coe_ordUnit, Units.val_neg, ord_neg]

omit [ValuativeRel K] [TopologicalSpace K] [DyadicContext K] in
private theorem hilbertSymbol_eq_of_isSquare_div_left
    {a b c : Kˣ} (h : IsSquare (a / b)) :
    hilbertSymbol K a c = hilbertSymbol K b c := by
  rcases h with ⟨s, hs⟩
  have hab : a = b * s ^ 2 := by
    calc
      a = (a / b) * b := by simp
      _ = (s * s) * b := by rw [hs]
      _ = b * s ^ 2 := by simp [pow_two, mul_comm]
  rw [hab, hilbertSymbol_mul_square_left]

/-- Concrete O'Meara 63:13 for the norm-equation definition of the Hilbert
symbol: every nonsquare has an explicitly constructed negative partner. -/
theorem exists_hilbertSymbol_eq_neg_one_of_not_isSquare_proved
    (a : Kˣ) (ha : ¬ IsSquare a) :
    ∃ b : Kˣ, hilbertSymbol K a b = -1 := by
  rcases Int.even_or_odd (ordUnit K a) with haEven | haOdd
  · have haFinite : quadraticDefect K a ≠ ⊤ := by
      intro htop
      exact ha ((quadraticDefect_eq_top_iff_isSquare (K := K) a).mp htop)
    have haNonzero : quadraticDefect K a ≠ 0 := by
      intro hzero
      have hodd := odd_ordUnit_of_quadraticDefect_eq_zero a hzero
      exact Int.not_odd_iff_even.mpr haEven hodd
    obtain ⟨v, r, t, hvUnit, hvDefect, hfactor, hvField, htOrder⟩ :=
      Bong.BONG.exists_exact_principal_representation a haFinite haNonzero
    have hvNotSquare : ¬ IsSquare v := by
      intro hvSquare
      apply ha
      rw [hfactor]
      exact hvSquare.mul ⟨r, by simp [pow_two]⟩
    have hvUpper : quadraticDefect K v ≤
        ((2 * ramificationIndex K : Nat) : ℕ∞) :=
      quadraticDefect_le_two_mul_e_of_not_isSquare (K := K) hvNotSquare
    rcases lt_or_eq_of_le hvUpper with hvLt | hvEndpoint
    · let d := (quadraticDefect K a).toNat
      have haCoe : quadraticDefect K a = (d : ℕ∞) := by
        simpa only [d] using (ENat.coe_toNat haFinite).symm
      have hdLt : d < 2 * ramificationIndex K := by
        rw [hvDefect, haCoe] at hvLt
        exact_mod_cast hvLt
      have hdOdd : Odd d := by
        have hvOdd := quadraticDefect_toNat_odd_of_unit_of_lt_two_mul_e
          (K := K) v hvUnit hvLt
        simpa only [hvDefect, d] using hvOdd
      have hfourRho :
          ord K (4 * concreteDiscriminant.rho) =
            (((2 * ramificationIndex K : Nat) : Int) : WithTop Int) := by
        rw [show (4 : K) = 2 * 2 by norm_num, mul_assoc, ord_mul,
          ord_mul, ← ramificationIndex_spec,
          concreteDiscriminant.rho_isValuationUnit]
        norm_cast
        ring
      have htOrderD : ord K t = ((d : Int) : WithTop Int) := by
        simpa only [d] using htOrder
      have htLtFour : ord K t < ord K (4 * concreteDiscriminant.rho) := by
        rw [htOrderD, hfourRho]
        exact_mod_cast hdLt
      have halphaOrder :
          ord K (((concreteDiscriminant.discriminantUnit : Kˣ) : K) - (v : K)) =
            ((d : Int) : WithTop Int) := by
        have hadd := (ord K).map_add_eq_of_lt_right htLtFour
        have hfield :
            ((concreteDiscriminant.discriminantUnit : Kˣ) : K) - (v : K) =
              -(4 * concreteDiscriminant.rho + t) := by
          rw [concreteDiscriminant.discriminant_eq_one_sub_four_mul_rho,
            hvField]
          ring
        rw [hfield, ord_neg]
        simpa only [htOrderD] using hadd
      have halphaNe :
          ((concreteDiscriminant.discriminantUnit : Kˣ) : K) - (v : K) ≠ 0 := by
        apply (ord_eq_top_iff K).not.mp
        rw [halphaOrder]
        exact WithTop.coe_ne_top
      let alpha : Kˣ := Units.mk0
        (((concreteDiscriminant.discriminantUnit : Kˣ) : K) - (v : K)) halphaNe
      have halphaOrd : ordUnit K alpha = (d : Int) := by
        apply WithTop.coe_injective
        rw [coe_ordUnit]
        exact halphaOrder
      have hproductOdd : Odd (ordUnit K (-alpha * v)) := by
        rw [ordUnit_mul, ordUnit_neg_local, halphaOrd,
          (isValuationUnit_iff_ordUnit_eq_zero K v).mp hvUnit, add_zero]
        exact_mod_cast hdOdd
      have hsum :
          ((concreteDiscriminant.discriminantUnit : Kˣ) : K) =
            (alpha : K) + (v : K) := by
        dsimp only [alpha]
        simp only [Units.val_mk0]
        ring
      have hnegative : hilbertSymbol K alpha v = -1 :=
        hilbertSymbol_eq_neg_one_of_add_eq_discriminant_of_product_odd
          alpha v hsum hproductOdd
      refine ⟨alpha, ?_⟩
      rw [hilbertSymbol_comm, hfactor, hilbertSymbol_mul_square_right]
      exact hnegative
    · have hvLarge :
          ((2 * ramificationIndex K : Nat) : ℕ∞) ≤
            quadraticDefect K v := hvEndpoint.ge
      rcases isSquare_or_isSquare_div_discriminant_of_defect_ge_twoE
          v hvLarge with hvSquare | hvDiscSquare
      · exact (hvNotSquare hvSquare).elim
      · let p : Kˣ := uniformizerPowerUnit K (1 : Int)
        have hpOdd : Odd (ordUnit K p) := by
          rw [ordUnit_uniformizerPowerUnit]
          exact odd_one
        have hdiscNe :
            hilbertSymbol K concreteDiscriminant.discriminantUnit p ≠ 1 :=
          hilbertSymbol_discriminant_ne_one_of_odd_order p hpOdd
        have hdiscNeg :
            hilbertSymbol K concreteDiscriminant.discriminantUnit p = -1 :=
          (Int.units_eq_one_or
            (hilbertSymbol K concreteDiscriminant.discriminantUnit p)).resolve_left
              hdiscNe
        have hvNeg : hilbertSymbol K v p = -1 := by
          rw [hilbertSymbol_eq_of_isSquare_div_left hvDiscSquare]
          exact hdiscNeg
        refine ⟨p, ?_⟩
        rw [hfactor, hilbertSymbol_mul_square_left]
        exact hvNeg
  · have hne :
        hilbertSymbol K concreteDiscriminant.discriminantUnit a ≠ 1 :=
      hilbertSymbol_discriminant_ne_one_of_odd_order a haOdd
    have hneg :
        hilbertSymbol K concreteDiscriminant.discriminantUnit a = -1 :=
      (Int.units_eq_one_or
        (hilbertSymbol K concreteDiscriminant.discriminantUnit a)).resolve_left hne
    exact ⟨concreteDiscriminant.discriminantUnit,
      (hilbertSymbol_comm K a concreteDiscriminant.discriminantUnit).trans hneg⟩

/-- The nondegeneracy field of `HilbertSymbolLaws`, proved without assuming
Hilbert-symbol multiplicativity. -/
theorem hilbertSymbol_nondegenerate_proved (a : Kˣ) :
    (∀ b : Kˣ, hilbertSymbol K a b = 1) → IsSquare a := by
  intro htrivial
  by_contra ha
  rcases exists_hilbertSymbol_eq_neg_one_of_not_isSquare_proved a ha with
    ⟨b, hb⟩
  have hone := htrivial b
  exact (by norm_num : (1 : ℤˣ) ≠ -1) (hone.symm.trans hb)

end ConcreteNondegeneracy

end Bong.Dyadic
