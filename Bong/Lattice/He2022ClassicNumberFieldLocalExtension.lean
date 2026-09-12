/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.He2022ClassicSectionEight
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

The completed-field adapter derives the three arithmetic fields of
`HeClassic2024LocalExtensionData.Lemma81Laws`. Quadratic-defect scaling and
good-BONG scalar extension remain explicit inputs.
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

/-- The remaining parts of Lemma 8.1 after the completed-field order and
ramification formulas have been proved. The extension-side data are evaluated
on the images of the base coefficients under `completionMap`. -/
structure RemainingCompletionInputs
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    [P.asIdeal.LiesOver p.asIdeal] where
  baseDefect : (p.adicCompletion K)ˣ → WithTop ℚ
  extensionDefect : (P.adicCompletion L)ˣ → WithTop ℚ
  BaseGoodBONG : {m : Nat} → (Fin m → (p.adicCompletion K)ˣ) → Prop
  ExtensionGoodBONG : {m : Nat} → (Fin m → (P.adicCompletion L)ˣ) → Prop
  defect_scale (x : (p.adicCompletion K)ˣ) :
    (((P.asIdeal.ramificationIdx (𝓞 K) : Nat) : ℚ) : WithTop ℚ) *
        baseDefect x ≤
      extensionDefect (Units.map (completionMap p P) x)
  goodBONG_transfer {m : Nat} (a : Fin m → (p.adicCompletion K)ˣ) :
    BaseGoodBONG a →
      ExtensionGoodBONG (fun i => Units.map (completionMap p P) (a i))

/-- Interpret the actual finite-completion extension in the abstract
local-extension interface used by Section 8. -/
noncomputable def RemainingCompletionInputs.toLocalExtensionData
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)}
    {P : IsDedekindDomain.HeightOneSpectrum (𝓞 L)}
    [P.asIdeal.LiesOver p.asIdeal]
    (D : RemainingCompletionInputs p P) :
    HeClassic2024LocalExtensionData where
  Element := (p.adicCompletion K)ˣ
  baseOrder := completionAdicOrder p
  extensionOrder x :=
    completionAdicOrder P (Units.map (completionMap p P) x)
  baseDefect := D.baseDefect
  extensionDefect x :=
    D.extensionDefect (Units.map (completionMap p P) x)
  baseRamificationIndex := p.asIdeal.ramificationIdx ℤ
  extensionRamificationIndex := P.asIdeal.ramificationIdx ℤ
  relativeRamificationIndex := P.asIdeal.ramificationIdx (𝓞 K)
  BaseGoodBONG := D.BaseGoodBONG
  ExtensionGoodBONG a :=
    D.ExtensionGoodBONG (fun i => Units.map (completionMap p P) (a i))

/-- Derive the completed-field order, positivity, and ramification-tower fields
of Lemma 8.1; only defect scaling and good-BONG transfer remain supplied by
the caller. -/
theorem RemainingCompletionInputs.lemma81Laws
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    {p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)}
    {P : IsDedekindDomain.HeightOneSpectrum (𝓞 L)}
    [P.asIdeal.LiesOver p.asIdeal]
    (D : RemainingCompletionInputs p P) :
    D.toLocalExtensionData.Lemma81Laws where
  relativeRamificationIndex_pos := relativeRamificationIndex_pos p P
  ramificationIndex_tower := absoluteRamificationIndex_tower p P
  order_scale := completionAdicOrder_liesOver p P
  defect_scale := D.defect_scale
  goodBONG_transfer := D.goodBONG_transfer

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
