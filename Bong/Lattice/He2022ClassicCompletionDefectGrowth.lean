/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Lattice.He2022ClassicLemma83ObstructionCore
import Bong.Lattice.He2022ClassicCompletionScalarExtensionGoodBONG
import Bong.Dyadic.ValuationUnitDefect

/-!
# Strict quadratic-defect growth under ramified finite completion

A zero-order coefficient over the lower dyadic completion has quadratic
defect at least one. Its image at relative ramification index greater than
one has defect strictly greater than one. This is the arithmetic ingredient
used for the prefix and adjacent defects in v6 Lemma 8.3.
-/

open scoped NumberField

namespace Bong.HeClassic2024NumberFieldScalarExtension

open Dyadic

universe u v w z

variable {K : Type u} {E : Type v} [Field K] [Field E]
  [NumberField K] [NumberField E]
  [Algebra K E] [FiniteDimensional K E]

/-- A lower unit-order square class acquires defect strictly above one at a
ramified upper dyadic completion. No lattice-universality assumption is used. -/
theorem completionDefectOrder_gt_one_of_zero_order
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 E))
    [P.asIdeal.LiesOver p.asIdeal]
    (hp : NumberFieldCompletion.IsDyadic p)
    (x : (p.adicCompletion K)ˣ)
    (he : 1 < P.asIdeal.ramificationIdx (𝓞 K)) :
    letI := NumberFieldCompletion.dyadicContext p hp
    let hpP := HeClassic2024NumberFieldBONGBridge.isDyadic_of_liesOver p P hp
    letI := NumberFieldCompletion.dyadicContext P hpP
    ordUnit (p.adicCompletion K) x = 0 →
      (1 : WithTop ℚ) < BONG.GoodBONG.defectOrder
        (K := P.adicCompletion E)
        (Units.map
          (HeClassic2024NumberFieldLocalExtension.completionMap p P) x) := by
  letI := NumberFieldCompletion.dyadicContext p hp
  let hpP := HeClassic2024NumberFieldBONGBridge.isDyadic_of_liesOver p P hp
  letI := NumberFieldCompletion.dyadicContext P hpP
  dsimp only
  intro hx
  have hEven : Even (ordUnit (p.adicCompletion K) x) := by
    rw [hx]
    exact ⟨0, by norm_num⟩
  have hLower : (1 : WithTop ℚ) ≤
      BONG.GoodBONG.defectOrder (K := p.adicCompletion K) x :=
    BONG.GoodBONG.defectOrder_one_le_of_even x hEven
  have hScale :
      (((P.asIdeal.ramificationIdx (𝓞 K) : Nat) : ℚ) : WithTop ℚ) *
        BONG.GoodBONG.defectOrder (K := p.adicCompletion K) x ≤
      BONG.GoodBONG.defectOrder (K := P.adicCompletion E)
        (Units.map
          (HeClassic2024NumberFieldLocalExtension.completionMap p P) x) := by
    rw [HeClassic2024NumberFieldBONGBridge.defectOrder_eq_completionQuadraticDefectQ
        p hp x,
      HeClassic2024NumberFieldBONGBridge.defectOrder_eq_completionQuadraticDefectQ
        P hpP]
    exact HeClassic2024NumberFieldLocalExtension.completionQuadraticDefectQ_scale
      p P x
  have hMon :
      (((P.asIdeal.ramificationIdx (𝓞 K) : Nat) : ℚ) : WithTop ℚ) * 1 ≤
      (((P.asIdeal.ramificationIdx (𝓞 K) : Nat) : ℚ) : WithTop ℚ) *
        BONG.GoodBONG.defectOrder (K := p.adicCompletion K) x := by
    have hPos : (0 : WithTop ℚ) <
        (((P.asIdeal.ramificationIdx (𝓞 K) : Nat) : ℚ) : WithTop ℚ) := by
      exact_mod_cast (Nat.zero_lt_of_lt he)
    exact (WithTop.mul_right_strictMono hPos (by simp)).monotone hLower
  have hOneLt : (1 : WithTop ℚ) <
      (((P.asIdeal.ramificationIdx (𝓞 K) : Nat) : ℚ) : WithTop ℚ) * 1 := by
    simp only [mul_one]
    exact_mod_cast he
  exact hOneLt.trans_le (hMon.trans hScale)

/-- Once the lower coefficient orders all vanish, every unsigned adjacent
defect of a mapped upper BONG is strictly greater than one. This is the
actual finite-completion arithmetic, not a numerical assumption. -/
theorem completionMappedUnsignedAdjacent_gt_one_of_lowerOrders_zero
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 E))
    [P.asIdeal.LiesOver p.asIdeal]
    (hp : NumberFieldCompletion.IsDyadic p) :
    letI := NumberFieldCompletion.dyadicContext p hp
    let hpP := HeClassic2024NumberFieldBONGBridge.isDyadic_of_liesOver p P hp
    letI := NumberFieldCompletion.dyadicContext P hpP
    ∀ {V : Type w} [AddCommGroup V] [Module (p.adicCompletion K) V]
      {W : Type z} [AddCommGroup W] [Module (P.adicCompletion E) W]
      {q : QuadraticSpace (p.adicCompletion K) V}
      {L : Lattice (p.adicCompletion K) V}
      {r : QuadraticSpace (P.adicCompletion E) W}
      {M : Lattice (P.adicCompletion E) W} {n : Nat}
      (lower : BONG.GoodBONG q L (n + 3))
      (upper : BONG.GoodBONG r M (n + 3)),
      (∀ i, upper.valueUnit i =
        Units.map (HeClassic2024NumberFieldLocalExtension.completionMap p P)
          (lower.valueUnit i)) →
      (∀ i, lower.order i = 0) →
      1 < P.asIdeal.ramificationIdx (𝓞 K) →
      ∀ j : Fin (n + 2),
        (1 : WithTop ℚ) < upper.heClassicUnsignedAdjacentDefect j := by
  letI := NumberFieldCompletion.dyadicContext p hp
  let hpP := HeClassic2024NumberFieldBONGBridge.isDyadic_of_liesOver p P hp
  letI := NumberFieldCompletion.dyadicContext P hpP
  dsimp only
  intro V _ _ W _ _ q L r M n lower upper hValues hZeros he j
  have hBaseOrder : ordUnit (p.adicCompletion K)
      (lower.valueUnit j.castSucc * lower.valueUnit j.succ) = 0 := by
    rw [ordUnit_mul]
    change lower.order j.castSucc + lower.order j.succ = 0
    rw [hZeros j.castSucc, hZeros j.succ]
    omega
  have hGrowth := completionDefectOrder_gt_one_of_zero_order
    p P hp (lower.valueUnit j.castSucc * lower.valueUnit j.succ) he hBaseOrder
  unfold BONG.GoodBONG.heClassicUnsignedAdjacentDefect
  rw [hValues j.castSucc, hValues j.succ, ← map_mul]
  exact hGrowth

/-- If the first `n+2` lower coefficients have order zero, the alternating
prefix used in the even branch of Theorem 1.1 has upper defect greater than
one. This is the other arithmetic input to the ramified obstruction. -/
theorem completionMappedSignedPrefix_gt_one_of_initialOrders_zero
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 E))
    [P.asIdeal.LiesOver p.asIdeal]
    (hp : NumberFieldCompletion.IsDyadic p) :
    letI := NumberFieldCompletion.dyadicContext p hp
    let hpP := HeClassic2024NumberFieldBONGBridge.isDyadic_of_liesOver p P hp
    letI := NumberFieldCompletion.dyadicContext P hpP
    ∀ {V : Type w} [AddCommGroup V] [Module (p.adicCompletion K) V]
      {W : Type z} [AddCommGroup W] [Module (P.adicCompletion E) W]
      {q : QuadraticSpace (p.adicCompletion K) V}
      {L : Lattice (p.adicCompletion K) V}
      {r : QuadraticSpace (P.adicCompletion E) W}
      {M : Lattice (P.adicCompletion E) W} {n : Nat}
      (lower : BONG.GoodBONG q L (n + 3))
      (upper : BONG.GoodBONG r M (n + 3)),
      (∀ i, upper.valueUnit i =
        Units.map (HeClassic2024NumberFieldLocalExtension.completionMap p P)
          (lower.valueUnit i)) →
      (∀ i : Fin (n + 3), i.1 < n + 2 → lower.order i = 0) →
      1 < P.asIdeal.ramificationIdx (𝓞 K) →
      (1 : WithTop ℚ) <
        upper.heClassicSignedPrefixDefect ((n + 2) / 2) (n + 2) := by
  letI := NumberFieldCompletion.dyadicContext p hp
  let hpP := HeClassic2024NumberFieldBONGBridge.isDyadic_of_liesOver p P hp
  letI := NumberFieldCompletion.dyadicContext P hpP
  dsimp only
  intro V _ _ W _ _ q L r M n lower upper hValues hZeros he
  let f := HeClassic2024NumberFieldLocalExtension.completionMap p P
  have hPrefixOrder : ∀ k : Nat, k ≤ n + 2 →
      ordUnit (p.adicCompletion K) (lower.prefixProduct k) = 0 := by
    intro k hk
    induction k with
    | zero =>
        simp only [BONG.GoodBONG.prefixProduct, BONG.prefixProduct_zero]
        have hOne := ordUnit_mul (p.adicCompletion K)
          (1 : (p.adicCompletion K)ˣ) 1
        simp only [mul_one] at hOne
        omega
    | succ k ih =>
        change ordUnit (p.adicCompletion K)
          (lower.toBONG.prefixProduct (k + 1)) = 0
        rw [lower.toBONG.prefixProduct_succ k (by omega), ordUnit_mul]
        have hklt : k < n + 3 := by omega
        have hkInitial : k < n + 2 := by omega
        have hkOrder : ordUnit (p.adicCompletion K)
            (lower.toBONG.valueUnit ⟨k, hklt⟩) = 0 :=
          hZeros ⟨k, hklt⟩ hkInitial
        have ih' : ordUnit (p.adicCompletion K)
            (lower.toBONG.prefixProduct k) = 0 := ih (by omega)
        rw [ih', hkOrder]
        omega
  have hPrefixMap : ∀ k : Nat, k ≤ n + 2 →
      upper.prefixProduct k = Units.map f (lower.prefixProduct k) := by
    intro k hk
    induction k with
    | zero =>
        simp [BONG.GoodBONG.prefixProduct, BONG.prefixProduct_zero]
    | succ k ih =>
        change upper.toBONG.prefixProduct (k + 1) =
          Units.map f (lower.toBONG.prefixProduct (k + 1))
        rw [upper.toBONG.prefixProduct_succ k (by omega),
          lower.toBONG.prefixProduct_succ k (by omega), map_mul]
        rw [show upper.toBONG.prefixProduct k =
          Units.map f (lower.toBONG.prefixProduct k) from ih (by omega)]
        have hValueK : upper.toBONG.valueUnit ⟨k, by omega⟩ =
            Units.map f (lower.toBONG.valueUnit ⟨k, by omega⟩) :=
          hValues ⟨k, by omega⟩
        rw [hValueK]
  have hNegOrder : ordUnit (p.adicCompletion K) (-1 : (p.adicCompletion K)ˣ) = 0 :=
    AlternatingEndpointTower.ordUnit_neg_one_eq_zero
  let signed : (p.adicCompletion K)ˣ :=
    (-1) ^ ((n + 2) / 2) * lower.prefixProduct (n + 2)
  have hSignedOrder : ordUnit (p.adicCompletion K) signed = 0 := by
    dsimp [signed]
    rw [ordUnit_mul, ordUnit_pow, hNegOrder, hPrefixOrder (n + 2) (by omega)]
    omega
  have hNegMap : Units.map f (-1 : (p.adicCompletion K)ˣ) =
      (-1 : (P.adicCompletion E)ˣ) := by
    apply Units.ext
    norm_num [f, Units.map]
  have hSignedMap :
      (-1 : (P.adicCompletion E)ˣ) ^ ((n + 2) / 2) *
          upper.prefixProduct (n + 2) = Units.map f signed := by
    dsimp [signed]
    rw [map_mul, map_pow, hNegMap, hPrefixMap (n + 2) (by omega)]
  have hGrowth := completionDefectOrder_gt_one_of_zero_order
    p P hp signed he hSignedOrder
  unfold BONG.GoodBONG.heClassicSignedPrefixDefect
  rw [hSignedMap]
  exact hGrowth

/-- The actual completed-field coefficient obstruction: two good BONGs
whose exact values are related by the completion map cannot have the upper
lattice classic `n`-universal when the relative extension is ramified.
Unlike the numerical core, no defect bound is a premise here. -/
theorem completionMappedGoodBONG_evenUniversal_contradiction_of_ramified
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 E))
    [P.asIdeal.LiesOver p.asIdeal]
    (hp : NumberFieldCompletion.IsDyadic p) :
    letI := NumberFieldCompletion.dyadicContext p hp
    let hpP := HeClassic2024NumberFieldBONGBridge.isDyadic_of_liesOver p P hp
    letI := NumberFieldCompletion.dyadicContext P hpP
    ∀ {V : Type w} [AddCommGroup V] [Module (p.adicCompletion K) V]
      {W : Type z} [AddCommGroup W] [Module (P.adicCompletion E) W]
      {q : QuadraticSpace (p.adicCompletion K) V}
      {L : Lattice (p.adicCompletion K) V}
      {r : QuadraticSpace (P.adicCompletion E) W}
      {M : Lattice (P.adicCompletion E) W} {n : Nat}
      (lower : BONG.GoodBONG q L (n + 3))
      (upper : BONG.GoodBONG r M (n + 3)),
      (∀ i, upper.valueUnit i =
        Units.map (HeClassic2024NumberFieldLocalExtension.completionMap p P)
          (lower.valueUnit i)) →
      2 ≤ n → Even n →
      1 < P.asIdeal.ramificationIdx (𝓞 K) →
      Lattice.IsClassicNUniversal.{v, z, v} r M n → False := by
  letI := NumberFieldCompletion.dyadicContext p hp
  let hpP := HeClassic2024NumberFieldBONGBridge.isDyadic_of_liesOver p P hp
  letI := NumberFieldCompletion.dyadicContext P hpP
  letI : QuadraticDefectLaws (P.adicCompletion E) :=
    quadraticDefectLawsOfHensel (P.adicCompletion E)
  letI : HilbertSymbolLaws (P.adicCompletion E) :=
    Dyadic.hilbertSymbolLawsProved
  letI : DyadicDiscriminantClassLaws (P.adicCompletion E) :=
    Dyadic.dyadicDiscriminantClassLawsProved
  dsimp only
  intro V _ _ W _ _ q L r M n lower upper hValues hn hnEven he hUniversal
  have hScale (i : Fin (n + 3)) :
      upper.order i =
        lower.order i * (P.asIdeal.ramificationIdx (𝓞 K) : Int) := by
    change ordUnit (P.adicCompletion E) (upper.valueUnit i) =
      ordUnit (p.adicCompletion K) (lower.valueUnit i) *
        (P.asIdeal.ramificationIdx (𝓞 K) : Int)
    rw [hValues i,
      HeClassic2024NumberFieldBONGBridge.ordUnit_eq_completionAdicOrder P hpP,
      HeClassic2024NumberFieldLocalExtension.completionAdicOrder_liesOver p P,
      HeClassic2024NumberFieldBONGBridge.ordUnit_eq_completionAdicOrder p hp]
  have hClassic : Lattice.IsClassicIntegral r M :=
    hUniversal.isClassicIntegral
  have hInitial :=
    lower.he2022ClassicLemma83_initialOrders_zero_of_scaled_evenUniversal
      upper hn hnEven he hScale hClassic hUniversal
  have hPrefix :=
    completionMappedSignedPrefix_gt_one_of_initialOrders_zero
      p P hp lower upper hValues hInitial he
  have hUnsigned (hZeros : ∀ i : Fin (n + 3), lower.order i = 0) :
      ∀ j : Fin (n + 2),
        (1 : WithTop ℚ) < upper.heClassicUnsignedAdjacentDefect j :=
    completionMappedUnsignedAdjacent_gt_one_of_lowerOrders_zero
      p P hp lower upper hValues hZeros he
  have hBasePos : 0 < p.asIdeal.ramificationIdx ℤ := by
    rw [← HeClassic2024NumberFieldBONGBridge.ramificationIndex_eq_idealRamificationIdx
      p hp]
    exact ramificationIndex_pos (K := p.adicCompletion K)
  have hAbsolute : 1 < ramificationIndex (P.adicCompletion E) := by
    rw [HeClassic2024NumberFieldBONGBridge.ramificationIndex_eq_idealRamificationIdx
      P hpP,
      HeClassic2024NumberFieldLocalExtension.absoluteRamificationIndex_tower p P]
    nlinarith
  exact lower.he2022ClassicLemma83_contradiction_of_scaled_defects
    upper hn hnEven he hScale hClassic hUniversal hPrefix hUnsigned hAbsolute

/-- He Classic v6, Lemma 8.3 in the corrected even `n ≥ 2` scope, for the
literal integral scalar extension at actual dyadic number-field completions.
The upper good BONG is constructed on that very lattice; its exact values
are the images of the lower values. The conclusion is non-universality of the
specified scalar-extension lattice, hence is invariant under integral
quadratic-lattice isometry. -/
theorem completionScalarExtension_not_evenUniversal_of_ramified
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 E))
    [P.asIdeal.LiesOver p.asIdeal]
    (hp : NumberFieldCompletion.IsDyadic p) :
    letI := NumberFieldCompletion.dyadicContext p hp
    let hpP := HeClassic2024NumberFieldBONGBridge.isDyadic_of_liesOver p P hp
    letI := NumberFieldCompletion.dyadicContext P hpP
    letI := HeClassic2024NumberFieldLocalExtension.CompletionLiesOver.instAlgebra
      (p := p) (P := P)
    ∀ {V : Type w} [AddCommGroup V] [Module (p.adicCompletion K) V]
      [FiniteDimensional (p.adicCompletion K) V]
      {q : QuadraticSpace (p.adicCompletion K) V}
      {L : Lattice (p.adicCompletion K) V} {n : Nat}
      (_lower : BONG.GoodBONG q L (n + 3))
      (_ : 2 ≤ n) (_ : Even n)
      (_ : Lattice.IsClassicNUniversal.{u, w, u} q L n)
      (_ : 1 < P.asIdeal.ramificationIdx (𝓞 K)),
      ¬ Lattice.IsClassicNUniversal.{v, max v w, v}
        (q.scalarExtension (E := P.adicCompletion E))
        (Lattice.scalarExtension (E := P.adicCompletion E) L) n := by
  letI := NumberFieldCompletion.dyadicContext p hp
  let hpP := HeClassic2024NumberFieldBONGBridge.isDyadic_of_liesOver p P hp
  letI := NumberFieldCompletion.dyadicContext P hpP
  letI := HeClassic2024NumberFieldLocalExtension.CompletionLiesOver.instAlgebra
    (p := p) (P := P)
  dsimp only
  intro V _ _ _ q L n lower hn hnEven hUniversal he hUpperUniversal
  have hClassic : Lattice.IsClassicIntegral q L :=
    hUniversal.isClassicIntegral
  obtain ⟨upper, hValues⟩ :=
    completionScalarExtension_hasGoodBONG_of_evenUniversal
      p P hp lower hn hnEven hClassic hUniversal
  exact completionMappedGoodBONG_evenUniversal_contradiction_of_ramified
    p P hp lower upper hValues hn hnEven he hUpperUniversal

end Bong.HeClassic2024NumberFieldScalarExtension
