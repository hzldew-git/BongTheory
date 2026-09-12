/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.HeHu2022ExactModels
import Bong.Dyadic.NumberFieldCompletion
import Bong.Lattice.He2022ClassicNumberFieldLocalExtension
import Mathlib.NumberTheory.RamificationInertia.Valuation

/-!
# Concrete finite-completion BONG bridge for He (2024)

This file identifies the valuation and relative quadratic defect used in the
finite-completion proof of Lemma 8.1 with the corresponding concrete BONG
notions.  It then turns the numerical He--Hu coefficient criterion into an
actual integral lattice carrying the displayed good BONG.
-/

open scoped NumberField

namespace Bong.HeClassic2024NumberFieldBONGBridge

open Dyadic

universe u v

variable {K : Type u} [Field K] [NumberField K]

private abbrev Completion
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :=
  p.adicCompletion K

/-- The height-one prime `(2)` of the rational integers. -/
private def rationalTwoPrime :
    IsDedekindDomain.HeightOneSpectrum ℤ where
  asIdeal := Ideal.span {(2 : ℤ)}
  isPrime :=
    (Ideal.span_singleton_prime (by norm_num : (2 : ℤ) ≠ 0)).2
      Int.prime_two
  ne_bot := Ideal.span_singleton_eq_bot.not.mpr (by norm_num)

/- A height-one prime containing `2` lies over the rational prime `(2)`. -/
omit [NumberField K] in
private theorem dyadic_liesOver_rationalTwoPrime
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hp : NumberFieldCompletion.IsDyadic p) :
    p.asIdeal.LiesOver (rationalTwoPrime.asIdeal) := by
  constructor
  apply rationalTwoPrime.isMaximal.eq_of_le
  · exact Ideal.comap_ne_top (algebraMap ℤ (𝓞 K)) p.isPrime.ne_top
  · change Ideal.span {(2 : ℤ)} ≤ Ideal.under ℤ p.asIdeal
    rw [Ideal.span_singleton_le_iff_mem]
    change algebraMap ℤ (𝓞 K) (2 : ℤ) ∈ p.asIdeal
    rw [show algebraMap ℤ (𝓞 K) (2 : ℤ) = (2 : 𝓞 K) by
      exact map_ofNat (algebraMap ℤ (𝓞 K)) 2]
    exact hp

/-- The multiplicative valuation of `2` records the absolute ramification
index of the selected dyadic prime. -/
private theorem intValuation_two_eq_exp_neg_ramificationIdx
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hp : NumberFieldCompletion.IsDyadic p) :
    p.intValuation (2 : 𝓞 K) =
      WithZero.exp (-(p.asIdeal.ramificationIdx ℤ : Int)) := by
  letI : p.asIdeal.LiesOver rationalTwoPrime.asIdeal :=
    dyadic_liesOver_rationalTwoPrime p hp
  have hrel :
      rationalTwoPrime.asIdeal.ramificationIdx' p.asIdeal =
        p.asIdeal.ramificationIdx ℤ :=
    Ideal.ramificationIdx'_eq_ramificationIdx
      rationalTwoPrime.asIdeal p.asIdeal rationalTwoPrime.ne_bot
  have h := rationalTwoPrime.intValuation_liesOver p (2 : ℤ)
  calc
    p.intValuation (2 : 𝓞 K) =
        rationalTwoPrime.intValuation (2 : ℤ) ^
          rationalTwoPrime.asIdeal.ramificationIdx' p.asIdeal := by
      rw [h]
      congr 1
      exact (map_ofNat (algebraMap ℤ (𝓞 K)) 2).symm
    _ = (WithZero.exp (-1 : Int)) ^
          p.asIdeal.ramificationIdx ℤ := by
      rw [rationalTwoPrime.intValuation_singleton (by norm_num) rfl, hrel]
    _ = WithZero.exp (-(p.asIdeal.ramificationIdx ℤ : Int)) := by
      rw [← WithZero.exp_nsmul]
      congr 1
      simp

/-- The BONG ramification index of the concrete completion is the standard
absolute ramification index of the defining number-field prime. -/
theorem ramificationIndex_eq_idealRamificationIdx
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hp : NumberFieldCompletion.IsDyadic p) :
    letI := NumberFieldCompletion.dyadicContext p hp
    ramificationIndex (Completion p) = p.asIdeal.ramificationIdx ℤ := by
  letI := NumberFieldCompletion.dyadicContext p hp
  have htwo : (2 : Completion p) ≠ 0 := by norm_num
  have hvTwo : Valued.v (2 : Completion p) =
      p.intValuation (2 : 𝓞 K) := by
    calc
      Valued.v (2 : Completion p) = p.valuation K (2 : K) := by
        rw [show (2 : Completion p) = ((2 : K) : Completion p) by
          symm
          simpa [NumberField.FinitePlace.embedding_apply] using
            (map_ofNat (NumberField.FinitePlace.embedding (K := K) p) 2)]
        exact
          IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_coe
            K p (2 : K)
      _ = p.intValuation (2 : 𝓞 K) := by
        rw [show (2 : K) = algebraMap (𝓞 K) K (2 : 𝓞 K) by
          symm
          simpa using (map_ofNat (algebraMap (𝓞 K) K) 2)]
        exact p.valuation_of_algebraMap (2 : 𝓞 K)
  have horder : NumberFieldCompletion.adicOrder p (2 : Completion p) =
      ((p.asIdeal.ramificationIdx ℤ : Int) : WithTop Int) := by
    rw [NumberFieldCompletion.adicOrder_apply_of_ne_zero p htwo, hvTwo,
      intValuation_two_eq_exp_neg_ramificationIdx p hp]
    norm_num
  have hspec := ramificationIndex_spec (Completion p)
  change (((ramificationIndex (Completion p) : Nat) : Int) : WithTop Int) =
    NumberFieldCompletion.adicOrder p (2 : Completion p) at hspec
  rw [horder] at hspec
  exact_mod_cast WithTop.coe_injective hspec

/-- On a nonzero completed element, the BONG order is the logarithmic order
used in the direct finite-completion proof of Lemma 8.1. -/
theorem ordUnit_eq_completionAdicOrder
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hp : NumberFieldCompletion.IsDyadic p)
    (a : (Completion p)ˣ) :
    letI := NumberFieldCompletion.dyadicContext p hp
    ordUnit (Completion p) a =
      HeClassic2024NumberFieldLocalExtension.completionAdicOrder p a := by
  letI := NumberFieldCompletion.dyadicContext p hp
  apply WithTop.coe_injective
  rw [coe_ordUnit]
  change NumberFieldCompletion.adicOrder p (a : Completion p) = _
  rw [NumberFieldCompletion.adicOrder_apply_of_ne_zero p (Units.ne_zero a)]
  rfl

/-- The valuation-ball and additive-order formulations of a relative square
approximation agree on a finite completion. -/
theorem isQuadraticApproximation_iff_completion
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hp : NumberFieldCompletion.IsDyadic p)
    (a : (Completion p)ˣ) (n : Nat) :
    letI := NumberFieldCompletion.dyadicContext p hp
    IsQuadraticApproximation (Completion p) a n ↔
      HeClassic2024NumberFieldLocalExtension.CompletionIsQuadraticApproximation
        p a n := by
  letI := NumberFieldCompletion.dyadicContext p hp
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    let error : Completion p := 1 - x ^ 2 / (a : Completion p)
    change Valued.v error ≤ WithZero.exp (-(n : Int))
    by_cases herror : error = 0
    · simp [error, herror]
    · change (n : WithTop Int) ≤
        NumberFieldCompletion.adicOrder p error at hx
      rw [NumberFieldCompletion.adicOrder_apply_of_ne_zero p herror] at hx
      norm_cast at hx
      apply (WithZero.log_le_iff_le_exp (by
        exact ((Valued.v : Valuation (Completion p) _).map_eq_zero_iff).not.mpr
          herror)).1
      omega
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    let error : Completion p := 1 - x ^ 2 / (a : Completion p)
    change Valued.v error ≤ WithZero.exp (-(n : Int)) at hx
    by_cases herror : error = 0
    · change (n : WithTop Int) ≤
        NumberFieldCompletion.adicOrder p error
      simp [herror]
    · have hvError : Valued.v error ≠ 0 :=
        ((Valued.v : Valuation (Completion p) _).map_eq_zero_iff).not.mpr
          herror
      have hlog : (Valued.v error).log ≤ -(n : Int) :=
        (WithZero.log_le_iff_le_exp hvError).2 hx
      change (n : WithTop Int) ≤
        NumberFieldCompletion.adicOrder p error
      rw [NumberFieldCompletion.adicOrder_apply_of_ne_zero p herror]
      norm_cast
      omega

/-- The relative quadratic defect used by the BONG library is exactly the
valuation-ball defect used in the finite-completion proof. -/
theorem quadraticDefect_eq_completionQuadraticDefect
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hp : NumberFieldCompletion.IsDyadic p)
    (a : (Completion p)ˣ) :
    letI := NumberFieldCompletion.dyadicContext p hp
    quadraticDefect (Completion p) a =
      HeClassic2024NumberFieldLocalExtension.completionQuadraticDefect p a := by
  letI := NumberFieldCompletion.dyadicContext p hp
  unfold quadraticDefect
    HeClassic2024NumberFieldLocalExtension.completionQuadraticDefect
  apply le_antisymm
  · apply iSup_le
    rintro ⟨n, hn⟩
    exact le_iSup
      (fun m : {m : Nat //
        HeClassic2024NumberFieldLocalExtension.CompletionIsQuadraticApproximation
          p a m} => (m.1 : ℕ∞))
      ⟨n, (isQuadraticApproximation_iff_completion p hp a n).1 hn⟩
  · apply iSup_le
    rintro ⟨n, hn⟩
    exact le_iSup
      (fun m : {m : Nat // IsQuadraticApproximation (Completion p) a m} =>
        (m.1 : ℕ∞))
      ⟨n, (isQuadraticApproximation_iff_completion p hp a n).2 hn⟩

/-- The rationally embedded defect order used in BONG formulas is the direct
finite-completion defect on the same coefficient. -/
theorem defectOrder_eq_completionQuadraticDefectQ
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hp : NumberFieldCompletion.IsDyadic p)
    (a : (Completion p)ˣ) :
    letI := NumberFieldCompletion.dyadicContext p hp
    BONG.GoodBONG.defectOrder (K := Completion p) a =
      HeClassic2024NumberFieldLocalExtension.completionQuadraticDefectQ p a := by
  letI := NumberFieldCompletion.dyadicContext p hp
  unfold BONG.GoodBONG.defectOrder
    HeClassic2024NumberFieldLocalExtension.completionQuadraticDefectQ
  rw [quadraticDefect_eq_completionQuadraticDefect p hp a]
  rfl

/-- The two-step part of the finite-completion coefficient criterion is the
literal two-step order condition used by the exact BONG constructor. -/
theorem completionGoodBONGCoefficients_weakTwoStep
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hp : NumberFieldCompletion.IsDyadic p)
    {m : Nat} (a : Fin m → (Completion p)ˣ)
    (h : HeClassic2024NumberFieldLocalExtension.CompletionGoodBONGCoefficients
      p a) :
    letI := NumberFieldCompletion.dyadicContext p hp
    BONG.CoefficientWeakTwoStep (K := Completion p) a := by
  letI := NumberFieldCompletion.dyadicContext p hp
  intro i hi
  rw [ordUnit_eq_completionAdicOrder p hp,
    ordUnit_eq_completionAdicOrder p hp]
  exact h.2 i hi

/-- Every adjacent ratio satisfying the finite-completion criterion is a
genuine admissible binary BONG parameter. -/
theorem completionGoodBONGCoefficients_adjacentAdmissible
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hp : NumberFieldCompletion.IsDyadic p)
    {m : Nat} (a : Fin m → (Completion p)ˣ)
    (h : HeClassic2024NumberFieldLocalExtension.CompletionGoodBONGCoefficients
      p a) :
    letI := NumberFieldCompletion.dyadicContext p hp
    BONG.CoefficientAdjacentAdmissible a := by
  letI := NumberFieldCompletion.dyadicContext p hp
  letI : QuadraticDefectLaws (Completion p) :=
    quadraticDefectLawsOfHensel (Completion p)
  intro i hi
  let next : Fin m := ⟨i.val + 1, hi⟩
  let q : (Completion p)ˣ := a next / a i
  have hbase := h.1 i hi
  have hqOrder : ordUnit (Completion p) q =
      HeClassic2024NumberFieldLocalExtension.completionAdicOrder p (a next) -
        HeClassic2024NumberFieldLocalExtension.completionAdicOrder p (a i) := by
    dsimp [q]
    rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv,
      ordUnit_eq_completionAdicOrder p hp,
      ordUnit_eq_completionAdicOrder p hp]
    simp [sub_eq_add_neg]
  apply (BONG.isBinaryParameterAdmissible_iff_order_add_two_e_and_defect q).2
  constructor
  · have hlower :
        -(2 * (p.asIdeal.ramificationIdx ℤ : Int)) ≤
          HeClassic2024NumberFieldLocalExtension.completionAdicOrder p
              (a next) -
            HeClassic2024NumberFieldLocalExtension.completionAdicOrder p
              (a i) := by
      simpa [next] using hbase.2
    rw [hqOrder,
      ramificationIndex_eq_idealRamificationIdx p hp]
    omega
  · apply hasNonnegativeAbsoluteQuadraticDefect_of_nonneg_add_defectOrder
    have hfactorPos : q * (a i) ^ 2 = a i * a next := by
      dsimp [q]
      rw [pow_two, ← mul_assoc, div_mul_cancel, mul_comm]
    have hfactor : (-q) * (a i) ^ 2 = -(a i * a next) := by
      calc
        (-q) * (a i) ^ 2 = -(q * (a i) ^ 2) := by rw [neg_mul]
        _ = -(a i * a next) := congrArg Neg.neg hfactorPos
    have hdefect :
        HeClassic2024NumberFieldLocalExtension.completionQuadraticDefectQ p
            (-(a i * a next)) =
          BONG.GoodBONG.defectOrder (K := Completion p) (-q) := by
      calc
        HeClassic2024NumberFieldLocalExtension.completionQuadraticDefectQ p
            (-(a i * a next)) =
            BONG.GoodBONG.defectOrder (K := Completion p)
              (-(a i * a next)) :=
          (defectOrder_eq_completionQuadraticDefectQ p hp _).symm
        _ = BONG.GoodBONG.defectOrder (K := Completion p)
              ((-q) * (a i) ^ 2) := by rw [hfactor]
        _ = BONG.GoodBONG.defectOrder (K := Completion p) (-q) := by
          unfold BONG.GoodBONG.defectOrder
          rw [quadraticDefect_mul_square]
    rw [ordUnit_neg, hqOrder, ← hdefect]
    simpa [next] using hbase.1

/-- The coefficient row of an actual good BONG satisfies the concrete
finite-completion version of the He--Hu numerical criterion.  Together with
`completionGoodBONGCoefficients_hasGoodBONG`, this proves that the criterion
is neither merely necessary nor merely a detached numerical surrogate. -/
theorem goodBONG_completionGoodBONGCoefficients
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hp : NumberFieldCompletion.IsDyadic p) :
    letI := NumberFieldCompletion.dyadicContext p hp
    ∀ {V : Type v} [AddCommGroup V] [Module (Completion p) V]
      {q : QuadraticSpace (Completion p) V}
      {M : Lattice (Completion p) V} {m : Nat},
      ∀ b : BONG.GoodBONG q M m,
        HeClassic2024NumberFieldLocalExtension.CompletionGoodBONGCoefficients
          p b.valueUnit := by
  letI := NumberFieldCompletion.dyadicContext p hp
  intro V _ _ q M m b
  constructor
  · intro i hi
    let next : Fin m := ⟨i.val + 1, hi⟩
    let parameter : (Completion p)ˣ :=
      b.valueUnit next / b.valueUnit i
    have hadmissible : BONG.IsBinaryParameterAdmissible parameter := by
      dsimp only [parameter]
      exact b.toBONG.adjacentParameter_isBinaryParameterAdmissible i hi
    have hcriterion :=
      (BONG.isBinaryParameterAdmissible_iff_order_add_two_e_and_defect
        parameter).1 hadmissible
    have hparameterOrder : ordUnit (Completion p) parameter =
        HeClassic2024NumberFieldLocalExtension.completionAdicOrder p
            (b.valueUnit next) -
          HeClassic2024NumberFieldLocalExtension.completionAdicOrder p
            (b.valueUnit i) := by
      dsimp [parameter]
      rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv,
        ordUnit_eq_completionAdicOrder p hp,
        ordUnit_eq_completionAdicOrder p hp]
      simp [sub_eq_add_neg]
    have hfactorPos : parameter * (b.valueUnit i) ^ 2 =
        b.valueUnit i * b.valueUnit next := by
      dsimp [parameter]
      rw [pow_two, ← mul_assoc, div_mul_cancel, mul_comm]
    have hfactor : (-parameter) * (b.valueUnit i) ^ 2 =
        -(b.valueUnit i * b.valueUnit next) := by
      calc
        (-parameter) * (b.valueUnit i) ^ 2 =
            -(parameter * (b.valueUnit i) ^ 2) := by rw [neg_mul]
        _ = -(b.valueUnit i * b.valueUnit next) :=
          congrArg Neg.neg hfactorPos
    have hdefect :
        BONG.GoodBONG.defectOrder (K := Completion p) (-parameter) =
          HeClassic2024NumberFieldLocalExtension.completionQuadraticDefectQ p
            (-(b.valueUnit i * b.valueUnit next)) := by
      calc
        BONG.GoodBONG.defectOrder (K := Completion p) (-parameter) =
            BONG.GoodBONG.defectOrder (K := Completion p)
              ((-parameter) * (b.valueUnit i) ^ 2) := by
          unfold BONG.GoodBONG.defectOrder
          rw [quadraticDefect_mul_square]
        _ = BONG.GoodBONG.defectOrder (K := Completion p)
              (-(b.valueUnit i * b.valueUnit next)) := by rw [hfactor]
        _ =
            HeClassic2024NumberFieldLocalExtension.completionQuadraticDefectQ
              p (-(b.valueUnit i * b.valueUnit next)) :=
          defectOrder_eq_completionQuadraticDefectQ p hp _
    constructor
    · have hsum :=
        BONG.GoodBONG.nonneg_ordUnit_add_defectOrder_of_absolute
          (-parameter) hcriterion.2
      rw [ordUnit_neg, hparameterOrder, hdefect] at hsum
      simpa [next] using hsum
    · rw [← hparameterOrder]
      have hlower := hcriterion.1
      rw [ramificationIndex_eq_idealRamificationIdx p hp] at hlower
      omega
  · intro i hi
    rw [← ordUnit_eq_completionAdicOrder p hp,
      ← ordUnit_eq_completionAdicOrder p hp]
    exact b.good i hi

/-- The completed coefficient criterion constructs an actual integral lattice
with a good BONG having exactly the prescribed values. -/
theorem completionGoodBONGCoefficients_hasGoodBONG
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hp : NumberFieldCompletion.IsDyadic p)
    {m : Nat} (a : Fin m → (Completion p)ˣ)
    (h : HeClassic2024NumberFieldLocalExtension.CompletionGoodBONGCoefficients
      p a) :
    letI := NumberFieldCompletion.dyadicContext p hp
    ∃ R : BONG.DiagonalBONGRealization a,
      R.bong.IsGood ∧ ∀ i, R.bong.valueUnit i = a i := by
  letI := NumberFieldCompletion.dyadicContext p hp
  let hadj := completionGoodBONGCoefficients_adjacentAdmissible p hp a h
  let hweak := completionGoodBONGCoefficients_weakTwoStep p hp a h
  let R := heHuExactRealization a hadj hweak
  exact ⟨R, R.isGood hweak, R.valueUnit_eq⟩

/- Dyadicity ascends from a finite number-field prime to every prime lying
above it. -/
omit [NumberField K] in
theorem isDyadic_of_liesOver
    {L : Type*} [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    [P.asIdeal.LiesOver p.asIdeal]
    (hp : NumberFieldCompletion.IsDyadic p) :
    NumberFieldCompletion.IsDyadic P := by
  have hp' : (2 : 𝓞 K) ∈ p.asIdeal := hp
  have hmem : algebraMap (𝓞 K) (𝓞 L) (2 : 𝓞 K) ∈ P.asIdeal :=
    (Ideal.mem_of_liesOver (P := P.asIdeal) (p := p.asIdeal) (2 : 𝓞 K)).1 hp'
  change (2 : 𝓞 L) ∈ P.asIdeal
  rw [← show algebraMap (𝓞 K) (𝓞 L) (2 : 𝓞 K) =
      (2 : 𝓞 L) by
    simpa using (map_ofNat (algebraMap (𝓞 K) (𝓞 L)) 2)]
  exact hmem

/-- After extension to a dyadic prime above `p`, the mapped coefficient row
is realized by an actual integral lattice and an actual good BONG. -/
theorem completionGoodBONGCoefficients_map_hasGoodBONG
    {L : Type*} [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    [P.asIdeal.LiesOver p.asIdeal]
    (hp : NumberFieldCompletion.IsDyadic p)
    {m : Nat} (a : Fin m → (Completion p)ˣ)
    (h : HeClassic2024NumberFieldLocalExtension.CompletionGoodBONGCoefficients
      p a) :
    let hpP := isDyadic_of_liesOver p P hp
    letI := NumberFieldCompletion.dyadicContext P hpP
    ∃ R : BONG.DiagonalBONGRealization (K := P.adicCompletion L)
        (fun i => Units.map
          (HeClassic2024NumberFieldLocalExtension.completionMap p P) (a i)),
      R.bong.IsGood ∧
        ∀ i, R.bong.valueUnit i =
          Units.map
            (HeClassic2024NumberFieldLocalExtension.completionMap p P) (a i) := by
  let hpP := isDyadic_of_liesOver p P hp
  letI := NumberFieldCompletion.dyadicContext P hpP
  exact completionGoodBONGCoefficients_hasGoodBONG P hpP _
    (HeClassic2024NumberFieldLocalExtension.completionGoodBONGCoefficients_map
      p P a h)

/-- Every actual good BONG over the lower dyadic completion has an actual
good-BONG realization over the upper completion whose values are the mapped
lower values.  The output lattice is constructed by the exact He--Hu/Beli
criterion.  No identification with a separately supplied scalar-extension
lattice is asserted here. -/
theorem goodBONG_mappedValues_haveRealization
    {L : Type*} [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    [P.asIdeal.LiesOver p.asIdeal]
    (hp : NumberFieldCompletion.IsDyadic p) :
    letI := NumberFieldCompletion.dyadicContext p hp
    let hpP := isDyadic_of_liesOver p P hp
    letI := NumberFieldCompletion.dyadicContext P hpP
    ∀ {V : Type v} [AddCommGroup V] [Module (Completion p) V]
      {q : QuadraticSpace (Completion p) V}
      {M : Lattice (Completion p) V} {m : Nat}
      (b : BONG.GoodBONG q M m),
      ∃ R : BONG.DiagonalBONGRealization (K := P.adicCompletion L)
          (fun i ↦ Units.map
            (HeClassic2024NumberFieldLocalExtension.completionMap p P)
              (b.valueUnit i)),
        R.bong.IsGood ∧
          ∀ i, R.bong.valueUnit i =
            Units.map
              (HeClassic2024NumberFieldLocalExtension.completionMap p P)
                (b.valueUnit i) := by
  letI := NumberFieldCompletion.dyadicContext p hp
  let hpP := isDyadic_of_liesOver p P hp
  letI := NumberFieldCompletion.dyadicContext P hpP
  intro _ V _ _ q M m b
  exact completionGoodBONGCoefficients_map_hasGoodBONG p P hp b.valueUnit
    (goodBONG_completionGoodBONGCoefficients p hp b)

end Bong.HeClassic2024NumberFieldBONGBridge
