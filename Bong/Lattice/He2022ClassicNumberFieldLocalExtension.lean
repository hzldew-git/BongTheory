/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.He2022ClassicSectionEight
import Mathlib.Data.ENat.Lattice
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.RamificationInertia.Valuation
import Mathlib.Topology.Algebra.UniformRing

/-!
# Number-field coefficient extension for He (2024), Lemma 8.1

This file proves the order-scaling and ramification-tower statements for a
nonzero coefficient in a number field and two height-one primes in a finite
extension. It then constructs the induced map of finite completions and uses
continuity and density to prove Lemma 8.1(i) for every nonzero element of the
completed base field.

The completed-field adapter derives the order, ramification, quadratic-defect,
and good-BONG coefficient-criterion fields of
`HeClassic2024LocalExtensionData.Lemma81Laws` without caller-supplied
arithmetic assumptions.
-/

open scoped NumberField
open WithZeroTopology

namespace Bong.HeClassic2024NumberFieldLocalExtension

/-- The additive order of a nonzero number-field element at a height-one
prime, obtained from mathlib's multiplicative adic valuation. -/
noncomputable def adicOrder {K : Type*} [Field K] [NumberField K]
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (x : Kˣ) : Int :=
  -(p.valuation K (x : K)).log

/-- The order-scaling part of He (2024), Lemma 8.1(i), for a nonzero
coefficient in the underlying number field. -/
theorem adicOrder_liesOver
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    [P.asIdeal.LiesOver p.asIdeal] (x : Kˣ) :
    adicOrder P (Units.map (algebraMap K L) x) =
      adicOrder p x *
        (P.asIdeal.ramificationIdx (𝓞 K) : Int) := by
  have hrel :
      p.asIdeal.ramificationIdx' P.asIdeal =
        P.asIdeal.ramificationIdx (𝓞 K) :=
    Ideal.ramificationIdx'_eq_ramificationIdx
      p.asIdeal P.asIdeal p.ne_bot
  unfold adicOrder
  change
    -((P.valuation L) ((algebraMap K L) (x : K))).log =
      -(p.valuation K (x : K)).log *
        (P.asIdeal.ramificationIdx (𝓞 K) : Int)
  rw [← p.valuation_liesOver L P (x : K), WithZero.log_pow, hrel]
  simp only [nsmul_eq_mul]
  ring

/-- Positivity of the relative ramification index at a prime lying over the
chosen base prime. -/
theorem relativeRamificationIndex_pos
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    [P.asIdeal.LiesOver p.asIdeal] :
    0 < P.asIdeal.ramificationIdx (𝓞 K) := by
  exact Ideal.ramificationIdx_pos P.asIdeal (𝓞 K)

/-- The absolute ramification indices satisfy
`e(P / 2) = e(p / 2) * e(P / p)`. -/
theorem absoluteRamificationIndex_tower
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    [P.asIdeal.LiesOver p.asIdeal] :
    P.asIdeal.ramificationIdx ℤ =
      p.asIdeal.ramificationIdx ℤ *
        P.asIdeal.ramificationIdx (𝓞 K) := by
  exact Ideal.ramificationIdx_tower p.asIdeal P.asIdeal

/-- The still-unformalized parts of Lemma 8.1 after specializing its
coefficients to `Kˣ` and deriving order and ramification from prime ideals. -/
structure RemainingCoefficientInputs
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) where
  baseDefect : Kˣ → WithTop ℚ
  extensionDefect : Kˣ → WithTop ℚ
  BaseGoodBONG : {m : Nat} → (Fin m → Kˣ) → Prop
  ExtensionGoodBONG : {m : Nat} → (Fin m → Kˣ) → Prop
  defect_scale (x : Kˣ) :
    (((P.asIdeal.ramificationIdx (𝓞 K) : Nat) : ℚ) : WithTop ℚ) *
        baseDefect x ≤ extensionDefect x
  goodBONG_transfer {m : Nat} (a : Fin m → Kˣ) :
    BaseGoodBONG a → ExtensionGoodBONG a

/-- Interpret the number-field coefficient specialization in the abstract
local-extension interface used by Section 8. -/
noncomputable def RemainingCoefficientInputs.toLocalExtensionData
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)}
    {P : IsDedekindDomain.HeightOneSpectrum (𝓞 L)}
    [P.asIdeal.LiesOver p.asIdeal]
    (D : RemainingCoefficientInputs p P) :
    HeClassic2024LocalExtensionData where
  Element := Kˣ
  baseOrder := adicOrder p
  extensionOrder x := adicOrder P (Units.map (algebraMap K L) x)
  baseDefect := D.baseDefect
  extensionDefect := D.extensionDefect
  baseRamificationIndex := p.asIdeal.ramificationIdx ℤ
  extensionRamificationIndex := P.asIdeal.ramificationIdx ℤ
  relativeRamificationIndex := P.asIdeal.ramificationIdx (𝓞 K)
  BaseGoodBONG := D.BaseGoodBONG
  ExtensionGoodBONG := D.ExtensionGoodBONG

/-- Derive the order, positivity, and ramification-tower fields of Lemma 8.1;
only defect scaling and good-BONG transfer are supplied by the caller. -/
theorem RemainingCoefficientInputs.lemma81Laws
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)}
    {P : IsDedekindDomain.HeightOneSpectrum (𝓞 L)}
    [P.asIdeal.LiesOver p.asIdeal]
    (D : RemainingCoefficientInputs p P) :
    D.toLocalExtensionData.Lemma81Laws where
  relativeRamificationIndex_pos := relativeRamificationIndex_pos p P
  ramificationIndex_tower := absoluteRamificationIndex_tower p P
  order_scale := adicOrder_liesOver p P
  defect_scale := D.defect_scale
  goodBONG_transfer := D.goodBONG_transfer

/-! ## The induced map of finite completions -/

/-- The continuous ring homomorphism from the `p`-adic completion of `K` to
the `P`-adic completion of `L`, induced by `K → L` when `P` lies over `p`. -/
noncomputable def completionMap
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    [P.asIdeal.LiesOver p.asIdeal] :
    p.adicCompletion K →+* P.adicCompletion L :=
  (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv L P).symm.toRingHom.comp
    ((UniformSpace.Completion.mapRingHom
      (algebraMap (WithVal (p.valuation K)) (WithVal (P.valuation L)))
      (p.uniformContinuous_algebraMap_liesOver K L P).continuous).comp
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv K p).toRingHom)

/-- The completion map agrees with the original number-field embedding on
the dense subfield `K`. -/
theorem completionMap_coe
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    [P.asIdeal.LiesOver p.asIdeal] (x : K) :
    completionMap p P (x : p.adicCompletion K) =
      ((algebraMap K L) x : P.adicCompletion L) := by
  apply IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext
  change UniformSpace.Completion.map
      (algebraMap (WithVal (p.valuation K)) (WithVal (P.valuation L)))
      (x : (p.valuation K).Completion) =
    ((algebraMap K L) x : (P.valuation L).Completion)
  rw [UniformSpace.Completion.map_coe
    (p.uniformContinuous_algebraMap_liesOver K L P)]
  congr 1

/-- Continuity of the induced map of completions. -/
theorem continuous_completionMap
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    [P.asIdeal.LiesOver p.asIdeal] :
    Continuous (completionMap p P) := by
  exact
    (IsDedekindDomain.HeightOneSpectrum.adicCompletion.continuous_ofCompletion L P).comp
      (UniformSpace.Completion.continuous_map.comp
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion.continuous_toCompletion K p))

/-- The valuation on the upper completion restricts to the ramification-index
power of the valuation on the lower completion. The equality is first known
on the dense number-field subfield and is extended by continuity. -/
theorem completionMap_valuation
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    [P.asIdeal.LiesOver p.asIdeal]
    (x : p.adicCompletion K) :
    Valued.v (completionMap p P x) =
      Valued.v x ^ P.asIdeal.ramificationIdx (𝓞 K) := by
  have hleft :
      Continuous (fun y : p.adicCompletion K =>
        Valued.v (completionMap p P y)) :=
    (Valued.continuous_valuation_of_surjective
      (P.valuedAdicCompletion_surjective L)).comp
        (continuous_completionMap p P)
  have hright :
      Continuous (fun y : p.adicCompletion K =>
        Valued.v y ^ P.asIdeal.ramificationIdx (𝓞 K)) :=
    (Valued.continuous_valuation_of_surjective
      (p.valuedAdicCompletion_surjective K)).pow _
  have heq :
      (fun y : p.adicCompletion K => Valued.v (completionMap p P y)) =
        (fun y : p.adicCompletion K =>
          Valued.v y ^ P.asIdeal.ramificationIdx (𝓞 K)) := by
    apply Continuous.ext_on (p.denseRange_algebraMap K) hleft hright
    rintro _ ⟨y, rfl⟩
    change Valued.v (completionMap p P (y : p.adicCompletion K)) =
      Valued.v (y : p.adicCompletion K) ^
        P.asIdeal.ramificationIdx (𝓞 K)
    rw [completionMap_coe]
    simp only [IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_coe]
    simpa [Ideal.ramificationIdx'_eq_ramificationIdx
      p.asIdeal P.asIdeal p.ne_bot] using
        (p.valuation_liesOver L P y).symm
  exact congrFun heq x

/-- The additive order of a nonzero element of a number-field finite
completion. -/
noncomputable def completionAdicOrder
    {K : Type*} [Field K] [NumberField K]
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (x : (p.adicCompletion K)ˣ) : Int :=
  -(Valued.v (x : p.adicCompletion K)).log

/-- The full order-scaling part of He (2024), Lemma 8.1(i), for every nonzero
element of the completed base field. -/
theorem completionAdicOrder_liesOver
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    [P.asIdeal.LiesOver p.asIdeal]
    (x : (p.adicCompletion K)ˣ) :
    completionAdicOrder P (Units.map (completionMap p P) x) =
      completionAdicOrder p x *
        (P.asIdeal.ramificationIdx (𝓞 K) : Int) := by
  unfold completionAdicOrder
  change
    -(Valued.v (completionMap p P (x : p.adicCompletion K))).log =
      -(Valued.v (x : p.adicCompletion K)).log *
        (P.asIdeal.ramificationIdx (𝓞 K) : Int)
  rw [completionMap_valuation, WithZero.log_pow]
  simp only [nsmul_eq_mul]
  ring

/-! ## Quadratic defect under finite extension -/

/-- A square approximation in a finite completion, expressed directly in
mathlib's multiplicative adic valuation. This is the completed-field version
of the paper's relative condition
`n ≤ ord (1 - x² / a)`, including exact square approximations because the
multiplicative valuation sends zero to zero. -/
def CompletionIsQuadraticApproximation
    {K : Type*} [Field K] [NumberField K]
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (a : (p.adicCompletion K)ˣ) (n : Nat) : Prop :=
  ∃ x : p.adicCompletion K,
    Valued.v (1 - x ^ 2 / (a : p.adicCompletion K)) ≤
      WithZero.exp (-(n : Int))

/-- The order of the relative quadratic defect in a finite completion, valued
in `ℕ ∪ {∞}` as in the paper. -/
noncomputable def completionQuadraticDefect
    {K : Type*} [Field K] [NumberField K]
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (a : (p.adicCompletion K)ˣ) : ℕ∞ :=
  ⨆ n : {n : Nat // CompletionIsQuadraticApproximation p a n}, (n.1 : ℕ∞)

/-- Every attained finite approximation depth lies below the completed
quadratic defect. -/
theorem natCast_le_completionQuadraticDefect
    {K : Type*} [Field K] [NumberField K]
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    {a : (p.adicCompletion K)ˣ} {n : Nat}
    (h : CompletionIsQuadraticApproximation p a n) :
    (n : ℕ∞) ≤ completionQuadraticDefect p a := by
  exact le_iSup
    (fun m : {m : Nat // CompletionIsQuadraticApproximation p a m} =>
      (m.1 : ℕ∞)) ⟨n, h⟩

/-- The normalized square-approximation error is preserved by the completed
field embedding. -/
private theorem completionMap_normalizedError
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    [P.asIdeal.LiesOver p.asIdeal]
    (a : (p.adicCompletion K)ˣ) (x : p.adicCompletion K) :
    completionMap p P (1 - x ^ 2 / (a : p.adicCompletion K)) =
      1 - (completionMap p P x) ^ 2 /
        ((Units.map (completionMap p P) a : (P.adicCompletion L)ˣ) :
          P.adicCompletion L) := by
  simp

/-- A base-field square approximation of depth `n` maps to an extension-field
approximation of depth `e(P/p) * n`. -/
theorem completionIsQuadraticApproximation_map
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    [P.asIdeal.LiesOver p.asIdeal]
    {a : (p.adicCompletion K)ˣ} {n : Nat}
    (h : CompletionIsQuadraticApproximation p a n) :
    CompletionIsQuadraticApproximation P
      (Units.map (completionMap p P) a)
      (P.asIdeal.ramificationIdx (𝓞 K) * n) := by
  rcases h with ⟨x, hx⟩
  refine ⟨completionMap p P x, ?_⟩
  rw [← completionMap_normalizedError p P a x,
    completionMap_valuation]
  calc
    Valued.v (1 - x ^ 2 / (a : p.adicCompletion K)) ^
        P.asIdeal.ramificationIdx (𝓞 K) ≤
      (WithZero.exp (-(n : Int))) ^
        P.asIdeal.ramificationIdx (𝓞 K) := by
          exact pow_le_pow_left' hx _
    _ = WithZero.exp
        (-((P.asIdeal.ramificationIdx (𝓞 K) * n : Nat) : Int)) := by
      rw [← WithZero.exp_nsmul]
      congr 1
      push_cast
      ring

/-- He (2024), Lemma 8.1(ii), for every nonzero element of the completed base
field: relative quadratic defect grows by at least the relative ramification
index. -/
theorem completionQuadraticDefect_scale
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    [P.asIdeal.LiesOver p.asIdeal]
    (a : (p.adicCompletion K)ˣ) :
    (P.asIdeal.ramificationIdx (𝓞 K) : ℕ∞) *
        completionQuadraticDefect p a ≤
      completionQuadraticDefect P (Units.map (completionMap p P) a) := by
  rw [completionQuadraticDefect, ENat.mul_iSup]
  apply iSup_le
  rintro ⟨n, hn⟩
  rw [← ENat.coe_mul]
  exact natCast_le_completionQuadraticDefect P
    (completionIsQuadraticApproximation_map p P hn)

/-- The natural-valued defect scale embedded into the rational scale required
by the abstract Section 8 arithmetic adapter. -/
noncomputable def completionQuadraticDefectQ
    {K : Type*} [Field K] [NumberField K]
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (a : (p.adicCompletion K)ˣ) : WithTop Rat :=
  ENat.map Nat.cast (completionQuadraticDefect p a)

/-- Rational-scale form of completed quadratic-defect scaling. -/
theorem completionQuadraticDefectQ_scale
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    [P.asIdeal.LiesOver p.asIdeal]
    (a : (p.adicCompletion K)ˣ) :
    (((P.asIdeal.ramificationIdx (𝓞 K) : Nat) : Rat) : WithTop Rat) *
        completionQuadraticDefectQ p a ≤
      completionQuadraticDefectQ P (Units.map (completionMap p P) a) := by
  have h := completionQuadraticDefect_scale p P a
  have hmap :=
    (ENat.map_natCast_strictMono (α := Rat)).monotone h
  simpa [completionQuadraticDefectQ, ENat.map_natCast_mul] using hmap

/-- The two adjacent conditions in the coefficient criterion for a BONG:
`Rᵢ₊₁ - Rᵢ + d(-aᵢaᵢ₊₁) ≥ 0` and
`Rᵢ₊₁ - Rᵢ ≥ -2e`. -/
def CompletionBONGConditions
    {K : Type*} [Field K] [NumberField K]
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    {m : Nat} (a : Fin m → (p.adicCompletion K)ˣ) : Prop :=
  ∀ (i : Fin m) (hi : i.1 + 1 < m),
    (0 : WithTop Rat) ≤
        (((completionAdicOrder p (a ⟨i.1 + 1, hi⟩) -
          completionAdicOrder p (a i) : Int) : Rat) : WithTop Rat) +
          completionQuadraticDefectQ p
            (-(a i * a ⟨i.1 + 1, hi⟩)) ∧
      -(2 * (p.asIdeal.ramificationIdx Int : Int)) ≤
        completionAdicOrder p (a ⟨i.1 + 1, hi⟩) -
          completionAdicOrder p (a i)

/-- The exact numerical coefficient criterion from He--Hu, Lemma 2.2:
the adjacent BONG conditions together with `Rᵢ ≤ Rᵢ₊₂`. -/
def CompletionGoodBONGCoefficients
    {K : Type*} [Field K] [NumberField K]
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    {m : Nat} (a : Fin m → (p.adicCompletion K)ˣ) : Prop :=
  CompletionBONGConditions p a ∧
    ∀ (i : Fin m) (hi : i.1 + 2 < m),
      completionAdicOrder p (a i) ≤
        completionAdicOrder p (a ⟨i.1 + 2, hi⟩)

/-- He (2024), Lemma 8.1(iii), at its exact coefficient-criterion level:
the image of a coefficient sequence satisfying the good-BONG criterion again
satisfies that criterion over the upper completion. -/
theorem completionGoodBONGCoefficients_map
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    [P.asIdeal.LiesOver p.asIdeal]
    {m : Nat} (a : Fin m → (p.adicCompletion K)ˣ)
    (h : CompletionGoodBONGCoefficients p a) :
    CompletionGoodBONGCoefficients P
      (fun i => Units.map (completionMap p P) (a i)) := by
  let e : Nat := P.asIdeal.ramificationIdx (𝓞 K)
  have he : 0 ≤ (e : Int) := by positivity
  constructor
  · intro i hi
    let next : Fin m := ⟨i.1 + 1, hi⟩
    have hbase := h.1 i hi
    have hdefect := completionQuadraticDefect_scale p P
      (-(a i * a next))
    have hdefectMap :=
      (ENat.map_natCast_strictMono (α := Rat)).monotone hdefect
    have hmapNsmul (d : ℕ∞) :
        ENat.map (Nat.cast : Nat → Rat) (e • d) =
          e • ENat.map (Nat.cast : Nat → Rat) d := by
      change ((Nat.castAddMonoidHom Rat).ENatMap) (e • d) =
        e • ((Nat.castAddMonoidHom Rat).ENatMap) d
      exact map_nsmul (Nat.castAddMonoidHom Rat).ENatMap e d
    have hdefect' :
        e • completionQuadraticDefectQ p (-(a i * a next)) ≤
          completionQuadraticDefectQ P
            (-(Units.map (completionMap p P) (a i) *
              Units.map (completionMap p P) (a next))) := by
      rw [← nsmul_eq_mul] at hdefectMap
      rw [hmapNsmul] at hdefectMap
      simpa [completionQuadraticDefectQ, e] using hdefectMap
    constructor
    · have hscaled :
          (0 : WithTop Rat) ≤
            e •
              (((((completionAdicOrder p (a next) -
                completionAdicOrder p (a i) : Int) : Rat) : WithTop Rat)) +
                completionQuadraticDefectQ p (-(a i * a next))) :=
        nsmul_nonneg hbase.1 e
      calc
        (0 : WithTop Rat) ≤
            e •
              (((((completionAdicOrder p (a next) -
                completionAdicOrder p (a i) : Int) : Rat) : WithTop Rat)) +
                completionQuadraticDefectQ p (-(a i * a next))) := hscaled
        _ =
            (((((completionAdicOrder p (a next) -
              completionAdicOrder p (a i)) * (e : Int) : Int) : Rat) :
                WithTop Rat)) +
              e • completionQuadraticDefectQ p (-(a i * a next)) := by
                rw [nsmul_add]
                congr 1
                norm_cast
                push_cast
                ring
        _ ≤
            (((((completionAdicOrder p (a next) -
              completionAdicOrder p (a i)) * (e : Int) : Int) : Rat) :
                WithTop Rat)) +
              completionQuadraticDefectQ P
                (-(Units.map (completionMap p P) (a i) *
                  Units.map (completionMap p P) (a next))) := by
            simpa [add_comm] using
              add_le_add_right hdefect'
                (((((completionAdicOrder p (a next) -
                  completionAdicOrder p (a i)) * (e : Int) : Int) : Rat) :
                    WithTop Rat))
        _ =
            (((completionAdicOrder P
                (Units.map (completionMap p P) (a next)) -
              completionAdicOrder P
                (Units.map (completionMap p P) (a i)) : Int) : Rat) :
                WithTop Rat) +
              completionQuadraticDefectQ P
                (-(Units.map (completionMap p P) (a i) *
                  Units.map (completionMap p P) (a next))) := by
            rw [completionAdicOrder_liesOver,
              completionAdicOrder_liesOver]
            congr 2
            dsimp [e]
            ring
    · rw [completionAdicOrder_liesOver,
        completionAdicOrder_liesOver,
        absoluteRamificationIndex_tower p P]
      dsimp [e] at he ⊢
      nlinarith [hbase.2]
  · intro i hi
    have hbase := h.2 i hi
    rw [completionAdicOrder_liesOver,
      completionAdicOrder_liesOver]
    exact mul_le_mul_of_nonneg_right hbase he

/-- The actual finite-completion extension, with good-BONG predicates defined
by the exact coefficient criterion used in the paper. -/
noncomputable def completionLocalExtensionData
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    [P.asIdeal.LiesOver p.asIdeal] : HeClassic2024LocalExtensionData where
  Element := (p.adicCompletion K)ˣ
  baseOrder := completionAdicOrder p
  extensionOrder x :=
    completionAdicOrder P (Units.map (completionMap p P) x)
  baseDefect := completionQuadraticDefectQ p
  extensionDefect x :=
    completionQuadraticDefectQ P (Units.map (completionMap p P) x)
  baseRamificationIndex := p.asIdeal.ramificationIdx ℤ
  extensionRamificationIndex := P.asIdeal.ramificationIdx ℤ
  relativeRamificationIndex := P.asIdeal.ramificationIdx (𝓞 K)
  BaseGoodBONG := CompletionGoodBONGCoefficients p
  ExtensionGoodBONG a :=
    CompletionGoodBONGCoefficients P
      (fun i => Units.map (completionMap p P) (a i))

/-- All arithmetic fields used in the written proof of He (2024), Lemma 8.1,
on the actual finite completions and the exact coefficient criterion used to
recognize good BONGs.  This adapter does not assert that the lattice supplied
by that criterion is a preassigned scalar-extension lattice. -/
theorem completionLemma81Laws
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    [P.asIdeal.LiesOver p.asIdeal] :
    (completionLocalExtensionData p P).Lemma81Laws where
  relativeRamificationIndex_pos := relativeRamificationIndex_pos p P
  ramificationIndex_tower := absoluteRamificationIndex_tower p P
  order_scale := completionAdicOrder_liesOver p P
  defect_scale := completionQuadraticDefectQ_scale p P
  goodBONG_transfer := completionGoodBONGCoefficients_map p P

/-! The instances are scoped to avoid creating an unconditional global
instance diamond if mathlib later supplies the same finite-completion map. -/

namespace CompletionLiesOver

/-- The algebra structure on the upper completion induced by
`completionMap`. -/
noncomputable scoped instance instAlgebra
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)}
    {P : IsDedekindDomain.HeightOneSpectrum (𝓞 L)}
    [P.asIdeal.LiesOver p.asIdeal] :
    Algebra (p.adicCompletion K) (P.adicCompletion L) :=
  (completionMap p P).toAlgebra

/-- The number-field and completed-field embeddings form a scalar tower. -/
scoped instance instIsScalarTower
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)}
    {P : IsDedekindDomain.HeightOneSpectrum (𝓞 L)}
    [P.asIdeal.LiesOver p.asIdeal] :
    IsScalarTower K (p.adicCompletion K) (P.adicCompletion L) :=
  .of_algebraMap_eq fun x => by
    rw [RingHom.algebraMap_toAlgebra]
    exact (completionMap_coe p P x).symm

/-- Scalar multiplication through the completed embedding is continuous. -/
scoped instance instContinuousSMul
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)}
    {P : IsDedekindDomain.HeightOneSpectrum (𝓞 L)}
    [P.asIdeal.LiesOver p.asIdeal] :
    ContinuousSMul (p.adicCompletion K) (P.adicCompletion L) where
  continuous_smul :=
    ((continuous_completionMap p P).comp continuous_fst).mul continuous_snd

end CompletionLiesOver

end Bong.HeClassic2024NumberFieldLocalExtension
