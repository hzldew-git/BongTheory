/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.HeHu2022Lemma44

/-!
# He--Hu 2022, Lemma 4.5

This file proves the equivalence between condition (iv) of Theorem 2.8
for every integral even-rank target and the final large-gap condition
`I3^E`.  The first lemma below is the cross-space endpoint-tower
representation used in the terminal branch of the published proof.
-/

namespace Bong

open Dyadic AlternatingEndpointTower

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

/-- The literal diagonal values of the `k` half-hyperbolic BONG blocks
prepended in Lemma 3.10.  This is deliberately kept separate from the
standard hyperbolic-space model `[1,-1]`: the odd coordinates carry the
square factor `pi^(-2e)` used by the integral BONG. -/
noncomputable def heHuLemma45HyperbolicBONGValues (k : Nat) :
    Fin (2 * k) → Kˣ := fun i ↦
  if Even i.val then 1
  else -(uniformizerPowerUnit K
    (-(2 * (ramificationIndex K : Int))))

/-- Coordinate squares which identify the literal half-hyperbolic BONG
head from Lemma 3.10 with the conventional diagonal hyperbolic tower. -/
noncomputable def heHuLemma45HyperbolicBONGFactors (k : Nat) :
    Fin (2 * k) → Kˣ := fun i ↦
  if Odd i.val then
    uniformizerPowerUnit K (-(ramificationIndex K : Int))
  else 1

/-- The Lemma 3.10 head and the standard hyperbolic tower differ
coordinatewise by the displayed nonzero squares. -/
theorem heHuLemma45HyperbolicBONGValues_eq_standard_mul_square
    (k : Nat) (i : Fin (2 * k)) :
    heHuLemma45HyperbolicBONGValues (K := K) k i =
      standardHyperbolicEndpointTower (K := K) k i *
        heHuLemma45HyperbolicBONGFactors (K := K) k i ^ 2 := by
  rcases Nat.even_or_odd i.val with hiEven | hiOdd
  · rcases hiEven with ⟨t, ht⟩
    have htSmall : t < k := by omega
    let j : Fin k := ⟨t, htSmall⟩
    have hiEq : i = ⟨2 * j.val, by omega⟩ := by
      apply Fin.ext
      simpa only [j, two_mul] using ht
    rw [hiEq, standardHyperbolicEndpointTower_even (K := K) j]
    have hnotOdd : ¬ Odd (2 * j.val) :=
      Nat.not_odd_iff_even.mpr ⟨j.val, by omega⟩
    simp [heHuLemma45HyperbolicBONGValues,
      heHuLemma45HyperbolicBONGFactors, hnotOdd]
  · rcases hiOdd with ⟨t, ht⟩
    have htSmall : t < k := by omega
    let j : Fin k := ⟨t, htSmall⟩
    have hiEq : i = ⟨2 * j.val + 1, by omega⟩ := by
      apply Fin.ext
      omega
    rw [hiEq, standardHyperbolicEndpointTower_odd (K := K) j]
    have hnotEven : ¬ Even (2 * j.val + 1) :=
      Nat.not_even_two_mul_add_one j.val
    have hodd : Odd (2 * j.val + 1) := ⟨j.val, by omega⟩
    rw [heHuLemma45HyperbolicBONGValues,
      heHuLemma45HyperbolicBONGFactors, if_neg hnotEven, if_pos hodd]
    simp only [neg_mul, one_mul]
    unfold uniformizerPowerUnit
    rw [pow_two, ← zpow_add]
    congr 2
    ring

/-- Equal-rank isometry between the literal Lemma 3.10 head and the
standard diagonal hyperbolic tower. -/
theorem heHuLemma45HyperbolicBONGValues_represents_standard (k : Nat) :
    DiagonalRepresents
      (diagonalUnitCoefficients
        (heHuLemma45HyperbolicBONGValues (K := K) k))
      (diagonalUnitCoefficients
        (standardHyperbolicEndpointTower (K := K) k)) :=
  Beli2009FinalRemarksProof.diagonalRepresents_of_pointwise_mul_square
    (heHuLemma45HyperbolicBONGValues (K := K) k)
    (standardHyperbolicEndpointTower (K := K) k)
    (heHuLemma45HyperbolicBONGFactors (K := K) k)
    (heHuLemma45HyperbolicBONGValues_eq_standard_mul_square
      (K := K) k)

/-- A square class whose finite defect is strictly below the
discriminant endpoint is in the domain of He--Hu's sharp operation. -/
theorem heHuLemma45_sharpDomain_of_defect_lt_twoE
    (x : Kˣ) (d : Int)
    (hdefect : defectOrder (K := K) x =
      (((d : Int) : ℚ) : WithTop ℚ))
    (hdLt : d < 2 * (ramificationIndex K : Int)) :
    HeHuSharpDomain x := by
  constructor
  · intro hsquare
    have htop := defectOrder_eq_top_of_isSquare (K := K) hsquare
    rw [hdefect] at htop
    exact WithTop.coe_ne_top htop
  · intro hdiscriminant
    have htwisted :=
      isSquare_mul_discriminant_of_div_discriminant_square x hdiscriminant
    have hendpoint :=
      defectOrder_eq_twoE_of_mul_discriminant_isSquare x htwisted
    rw [hdefect] at hendpoint
    have hcoe := WithTop.coe_eq_coe.mp hendpoint
    have hdEq : d = 2 * (ramificationIndex K : Int) := by
      exact_mod_cast hcoe
    omega

/-- Replacing a field element by its normalized unit part times a
uniformizer power of the same parity does not change its square class. -/
theorem heHuLemma45_normalizedUniformizer_sameSquareClass
    (x : Kˣ) (R : Int) (hparity : Even (ordUnit K x - R)) :
    IsSquare
      (x * (normalizedUnitPart K x * uniformizerPowerUnit K R)) := by
  have hsumEven : Even (ordUnit K x + R) := by
    simpa only [add_comm] using
      (even_add_of_even_sub (a := R) (b := ordUnit K x) hparity)
  rcases isSquare_uniformizerPowerUnit_of_even
      (K := K) (ordUnit K x + R) hsumEven with ⟨s, hs⟩
  let δ := normalizedUnitPart K x
  have hx : uniformizerPowerUnit K (ordUnit K x) * δ = x := by
    simpa only [δ] using uniformizerPower_mul_normalizedUnitPart K x
  refine ⟨δ * s, ?_⟩
  calc
    x * (normalizedUnitPart K x * uniformizerPowerUnit K R) =
        (uniformizerPowerUnit K (ordUnit K x) * δ) *
          (δ * uniformizerPowerUnit K R) := by rw [hx]
    _ = δ * δ *
          (uniformizerPowerUnit K (ordUnit K x) *
            uniformizerPowerUnit K R) := by ac_rfl
    _ = δ * δ *
          uniformizerPowerUnit K (ordUnit K x + R) := by
        unfold uniformizerPowerUnit
        rw [← zpow_add]
    _ = δ * δ * (s * s) := by
        rw [hs]
    _ = (δ * s) * (δ * s) := by ac_rfl

/-- Two elements whose product is a square have the same quadratic-defect
order. -/
theorem heHuLemma45_defectOrder_eq_of_mul_isSquare
    (x y : Kˣ) (h : IsSquare (x * y)) :
    defectOrder (K := K) x = defectOrder (K := K) y := by
  rcases h with ⟨s, hs⟩
  have hy : y = x * (s * x⁻¹) ^ 2 := by
    calc
      y = (x * y) * x⁻¹ := by
        calc
          y = y * (x * x⁻¹) := by simp
          _ = (x * y) * x⁻¹ := by ac_rfl
      _ = (s * s) * x⁻¹ := by rw [hs]
      _ = x * (s * x⁻¹) ^ 2 := by
        simp only [pow_two]
        calc
          s * s * x⁻¹ = (x * x⁻¹) * (s * s) * x⁻¹ := by simp
          _ = x * (s * x⁻¹ * (s * x⁻¹)) := by ac_rfl
  rw [hy, defectOrder_mul_square]

/-- For an even-valuation class, removing the uniformizer power preserves
the defect order. -/
theorem heHuLemma45_normalizedUnitPart_defectOrder
    (x : Kˣ) (heven : Even (ordUnit K x)) :
    defectOrder (K := K) (normalizedUnitPart K x) =
      defectOrder (K := K) x := by
  rcases isSquare_uniformizerPowerUnit_of_even
      (K := K) (ordUnit K x) heven with ⟨s, hs⟩
  have hx : x = normalizedUnitPart K x * s ^ 2 := by
    calc
      x = uniformizerPowerUnit K (ordUnit K x) *
          normalizedUnitPart K x :=
        (uniformizerPower_mul_normalizedUnitPart K x).symm
      _ = (s * s) * normalizedUnitPart K x := by rw [hs]
      _ = normalizedUnitPart K x * s ^ 2 := by
        simp only [pow_two]
        ac_rfl
  calc
    defectOrder (K := K) (normalizedUnitPart K x) =
        defectOrder (K := K) (normalizedUnitPart K x * s ^ 2) :=
      (defectOrder_mul_square _ _).symm
    _ = defectOrder (K := K) x :=
      congrArg (fun z : Kˣ ↦ defectOrder (K := K) z) hx.symm

/-- The generic Table 2 tail exposes exactly the two coefficients used in
its definition. -/
@[simp]
theorem heHuLemma45_unitDefectTailGoodBONG_valueUnit
    [QuadraticDefectLaws K]
    (a c : Kˣ) (d : Int)
    (ha : IsValuationUnit K (a : K))
    (hc : IsValuationUnit K (c : K))
    (hdOdd : Odd d) (hdNonneg : 0 ≤ d)
    (hdLt : d < 2 * (ramificationIndex K : Int))
    (hcDefect : defectOrder (K := K) c =
      (((d : Int) : ℚ) : WithTop ℚ)) (i : Fin 2) :
    (heHuUnitDefectTailGoodBONG a c d ha hc hdOdd hdNonneg hdLt
      hcDefect).valueUnit i = heHuUnitDefectTailValues (K := K) a c d i := by
  unfold heHuUnitDefectTailGoodBONG
  rw [binaryDiagonalExactGoodBONG_valueUnit]
  fin_cases i <;> rfl

/-- The Lemma 3.10 extension remains integral; the first order is inherited
from the tail when no pair is added and is zero otherwise. -/
theorem heHuLemma45_lemma310_isIntegral {n : Nat}
    {X : Type u} [AddCommGroup X] [Module K X]
    {s : QuadraticSpace K X} {N : Lattice K X}
    (b : GoodBONG s N (n + 1))
    (hBIntegral : Lattice.IsIntegral s N) (k : Nat)
    (_hfirst : 0 ≤ b.order 0) :
    Lattice.IsIntegral
      (Lattice.halfHyperbolicExtensionForm s k)
      (N.halfHyperbolicExtensionLattice k) := by
  exact heHuHalfHyperbolicExtension_isIntegral hBIntegral k

/-- The coefficient family produced by Lemma 3.10 is literally a common
half-hyperbolic head followed by the original tail, up to the harmless
arithmetic cast between `tailRank + 2*k` and `2*k + tailRank`. -/
theorem heHuLemma45Lemma310_valueUnit_eq_append {n : Nat}
    {V' : Type u} [AddCommGroup V'] [Module K V']
    {q' : QuadraticSpace K V'} {L' : Lattice K V'}
    (b : GoodBONG q' L' (n + 1))
    (hIntegral : Lattice.IsIntegral q' L') (k : Nat) :
    (heHu2022Lemma310BONG b hIntegral k).valueUnit =
      heHuFinFamilyCast (by omega :
          2 * k + (n + 1) = (n + 1) + 2 * k)
        (Fin.append (heHuLemma45HyperbolicBONGValues (K := K) k)
          b.valueUnit) := by
  funext i
  unfold heHuFinFamilyCast
  by_cases hi : i.val < 2 * k
  · have hiEvenOrOdd := Nat.even_or_odd i.val
    rcases hiEvenOrOdd with hiEven | hiOdd
    · rcases hiEven with ⟨t, ht⟩
      have htSmall : t < k := by omega
      let j : Fin k := ⟨t, htSmall⟩
      have hindex : i = ⟨2 * j.val, by omega⟩ := by
        apply Fin.ext
        simpa only [j, two_mul] using ht
      rw [hindex, (heHu2022Lemma310HyperbolicValues
        b hIntegral k j).1]
      have hcast :
          Fin.cast (by omega : (n + 1) + 2 * k = 2 * k + (n + 1))
              ⟨2 * j.val, by omega⟩ =
            Fin.castAdd (n + 1) ⟨2 * j.val, by omega⟩ := by
        apply Fin.ext
        rfl
      rw [hcast, Fin.append_left]
      have hjEven : Even (2 * j.val) := ⟨j.val, by omega⟩
      simp [heHuLemma45HyperbolicBONGValues, hjEven]
    · rcases hiOdd with ⟨t, ht⟩
      have htSmall : t < k := by omega
      let j : Fin k := ⟨t, htSmall⟩
      have hindex : i = ⟨2 * j.val + 1, by omega⟩ := by
        apply Fin.ext
        omega
      rw [hindex, (heHu2022Lemma310HyperbolicValues
        b hIntegral k j).2]
      have hcast :
          Fin.cast (by omega : (n + 1) + 2 * k = 2 * k + (n + 1))
              ⟨2 * j.val + 1, by omega⟩ =
            Fin.castAdd (n + 1) ⟨2 * j.val + 1, by omega⟩ := by
        apply Fin.ext
        rfl
      rw [hcast, Fin.append_left]
      have hnotEven : ¬ Even (2 * j.val + 1) :=
        Nat.not_even_two_mul_add_one j.val
      simp [heHuLemma45HyperbolicBONGValues, hnotEven]
  · have hjBound : i.val - 2 * k < n + 1 := by omega
    let j : Fin (n + 1) := ⟨i.val - 2 * k, hjBound⟩
    have hindex : i = ⟨2 * k + j.val, by omega⟩ := by
      apply Fin.ext
      simp only [j]
      omega
    rw [hindex, heHu2022Lemma310TailValues]
    have hcast :
        Fin.cast (by omega : (n + 1) + 2 * k = 2 * k + (n + 1))
            ⟨2 * k + j.val, by omega⟩ =
          Fin.natAdd (2 * k) j := by
      apply Fin.ext
      rfl
    rw [hcast, Fin.append_right]

/-- Lemma 3.10 transports any equal-rank identification of its tail to
the standard hyperbolic extension of that tail.  The proof retains the
literal BONG coefficients on the source side and removes their square
factors only through an explicit diagonal isometry. -/
theorem heHuLemma45Lemma310_represents_tower {n : Nat}
    {V' : Type u} [AddCommGroup V'] [Module K V']
    {q' : QuadraticSpace K V'} {L' : Lattice K V'}
    (b : GoodBONG q' L' (n + 1))
    (hIntegral : Lattice.IsIntegral q' L') (k : Nat)
    (tail : Fin (n + 1) → Kˣ)
    (hTail : DiagonalRepresents
      (diagonalUnitCoefficients b.valueUnit)
      (diagonalUnitCoefficients tail)) :
    DiagonalRepresents
      (diagonalUnitCoefficients
        (heHu2022Lemma310BONG b hIntegral k).valueUnit)
      (diagonalUnitCoefficients
        (heHuFinFamilyCast (by omega :
            2 * k + (n + 1) = (n + 1) + 2 * k)
          (Fin.append
            (standardHyperbolicEndpointTower (K := K) k) tail))) := by
  have hhead := heHuLemma45HyperbolicBONGValues_represents_standard
    (K := K) k
  have happend := DiagonalRepresents.appendBoth hhead hTail
  have hcast := diagonalRepresents_heHuFinFamilyCast_both
    (K := K)
    (by omega : 2 * k + (n + 1) = (n + 1) + 2 * k)
    (by omega : 2 * k + (n + 1) = (n + 1) + 2 * k)
    (Fin.append (heHuLemma45HyperbolicBONGValues (K := K) k)
      b.valueUnit)
    (Fin.append (standardHyperbolicEndpointTower (K := K) k) tail)
    (by simpa only [diagonalUnitCoefficients_append] using happend)
  rw [heHuLemma45Lemma310_valueUnit_eq_append b hIntegral k]
  exact hcast

/-- The square-row Table 2 target in every admissible even rank.  The
parameter `p` gives the rank `2*(p+1)+2`; thus the undefined binary case
`W_2^2(1)` is excluded by construction, exactly as in the paper. -/
noncomputable def heHuLemma45EvenSecondOneTarget (p : Nat) :=
  let b := heHuLemma311EvenSecondOneTail (K := K)
  let hIntegral := heHuIntegral_of_firstOrder_nonneg b (by
    rw [heHuLemma311EvenSecondOneTail_order]
    norm_num)
  (heHu2022Lemma310BONG b hIntegral p).castLength
    (by omega : 4 + 2 * p = 2 * (p + 1) + 2)

/-- The square-row target is integral. -/
theorem heHuLemma45EvenSecondOneTarget_isIntegral (p : Nat) :
    UnderlyingLatticeIsIntegral
      (heHuLemma45EvenSecondOneTarget (K := K) p) := by
  unfold heHuLemma45EvenSecondOneTarget
  exact heHuHalfHyperbolicExtension_isIntegral
    (heHuIntegral_of_firstOrder_nonneg
      (heHuLemma311EvenSecondOneTail (K := K)) (by
        rw [heHuLemma311EvenSecondOneTail_order]
        norm_num)) p

/-- Last order of the square-row target, as printed in Lemma 3.11(i). -/
theorem heHuLemma45EvenSecondOneTarget_lastOrder (p : Nat) :
    (heHuLemma45EvenSecondOneTarget (K := K) p).order
        ⟨2 * (p + 1) + 1, by omega⟩ =
      1 - 2 * (ramificationIndex K : Int) := by
  let b := heHuLemma311EvenSecondOneTail (K := K)
  let hIntegral := heHuIntegral_of_firstOrder_nonneg b (by
    rw [heHuLemma311EvenSecondOneTail_order]
    norm_num)
  have hprofile := (heHu2022Lemma311iSecondOne (K := K) p).2
    (3 : Fin 4)
  unfold heHuLemma45EvenSecondOneTarget
  rw [order_castLength]
  have hindex :
      (⟨2 * (p + 1) + 1, by omega⟩ : Fin (4 + 2 * p)) =
        ⟨2 * p + (3 : Fin 4).val, by omega⟩ := by
    apply Fin.ext
    norm_num
    omega
  rw [hindex]
  norm_num at hprofile ⊢
  exact hprofile

/-- The literal square-row target is isometric to
`W_2^(2*(p+1)+2)(1)`. -/
theorem heHuLemma45EvenSecondOneTarget_represents_evenSecond (p : Nat) :
    DiagonalRepresents
      (diagonalUnitCoefficients
        (heHuLemma45EvenSecondOneTarget (K := K) p).valueUnit)
      (diagonalUnitCoefficients
        (heHuEvenSecond (K := K) (p + 1) 1
          (Or.inl (by omega : 0 < p + 1)))) := by
  let b := heHuLemma311EvenSecondOneTail (K := K)
  let hIntegral := heHuIntegral_of_firstOrder_nonneg b (by
    rw [heHuLemma311EvenSecondOneTail_order]
    norm_num)
  have htail : DiagonalRepresents
      (diagonalUnitCoefficients b.valueUnit)
      (diagonalUnitCoefficients
        (beliAnisotropicQuaternaryUnits (K := K))) := by
    have hraw :=
      Beli2009FinalRemarksProof.diagonalRepresents_of_pointwise_mul_square
        b.valueUnit
        (heHuLemma311EvenSecondOneStandardValues (K := K))
        (heHuLemma311EvenSecondOneFactors (K := K))
        (heHuLemma311EvenSecondOneTail_eq_anisotropic_mul_square
          (K := K))
    rw [heHuLemma311EvenSecondOneStandardValues_eq_anisotropic] at hraw
    exact hraw
  have hlift := heHuLemma45Lemma310_represents_tower
    b hIntegral p (beliAnisotropicQuaternaryUnits (K := K)) htail
  let raw := heHu2022Lemma310BONG b hIntegral p
  let model := heHuFinFamilyCast (by omega :
      2 * p + 4 = 4 + 2 * p)
    (Fin.append (standardHyperbolicEndpointTower (K := K) p)
      (beliAnisotropicQuaternaryUnits (K := K)))
  let hdim : 4 + 2 * p = 2 * (p + 1) + 2 := by omega
  have hliftCast := diagonalRepresents_heHuFinFamilyCast_both
    (K := K) hdim hdim raw.valueUnit model hlift
  have hsquare : IsSquare (1 : Kˣ) := ⟨1, by simp⟩
  rw [heHuEvenSecond_succ_of_square p 1
    (Or.inl (by omega : 0 < p + 1)) hsquare]
  have hsource :
      (heHuLemma45EvenSecondOneTarget (K := K) p).valueUnit =
        heHuFinFamilyCast hdim raw.valueUnit := by
    funext i
    simp only [heHuLemma45EvenSecondOneTarget, raw,
      heHuFinFamilyCast, valueUnit_castLength_heHu]
    congr 2
  have htarget :
      heHuFinFamilyCast hdim model =
        heHuFinFamilyCast (by omega :
            2 * p + 4 = 2 * (p + 1) + 2)
          (Fin.append (standardHyperbolicEndpointTower (K := K) p)
            (beliAnisotropicQuaternaryUnits (K := K))) := by
    simp only [model, heHuFinFamilyCast_trans]
  rw [hsource]
  rw [htarget] at hliftCast
  exact hliftCast

/-- The first-column even space with parameter `1` or `Delta` is itself
an alternating endpoint tower. -/
theorem heHuLemma45_evenFirst_pairClasses
    [laws : DyadicDiscriminantClassLaws K] (p : Nat) (mu : Kˣ)
    (hmu : mu = 1 ∨
      mu = (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit) :
    AlternatingEndpointPairClasses (pairs := p + 1)
      (heHuEvenFirst (K := K) p mu) := by
  rw [heHuEvenFirst_eq_towerModel]
  intro t
  by_cases ht : t.val < p
  · let j : Fin p := ⟨t.val, ht⟩
    have hevenIndex :
        (⟨2 * t.val, by omega⟩ : Fin (2 * (p + 1))) =
          Fin.castAdd 2 (⟨2 * j.val, by omega⟩ : Fin (2 * p)) := by
      apply Fin.ext
      rfl
    have hoddIndex :
        (⟨2 * t.val + 1, by omega⟩ : Fin (2 * (p + 1))) =
          Fin.castAdd 2 (⟨2 * j.val + 1, by omega⟩ : Fin (2 * p)) := by
      apply Fin.ext
      rfl
    rw [hevenIndex, hoddIndex, Fin.append_left, Fin.append_left]
    exact standardHyperbolicEndpointTower_pairClasses (K := K) p j
  · have htEq : t.val = p := by omega
    have hevenIndex :
        (⟨2 * t.val, by omega⟩ : Fin (2 * (p + 1))) =
          Fin.natAdd (2 * p) (0 : Fin 2) := by
      apply Fin.ext
      simp [htEq]
    have hoddIndex :
        (⟨2 * t.val + 1, by omega⟩ : Fin (2 * (p + 1))) =
          Fin.natAdd (2 * p) (1 : Fin 2) := by
      apply Fin.ext
      simp [htEq]
    rw [hevenIndex, hoddIndex, Fin.append_right, Fin.append_right]
    rcases hmu with rfl | rfl
    · left
      refine ⟨1, ?_⟩
      simp [heHuBinaryFirst]
    · right
      refine ⟨(inferInstance :
        DyadicDiscriminantClassLaws K).discriminantUnit, ?_⟩
      simp [heHuBinaryFirst, pow_two]

/-- All leading lines of the first-column even endpoint model have unit
order. -/
theorem heHuLemma45_evenFirst_leadingOrders (p : Nat) (mu : Kˣ) :
    AlternatingEndpointLeadingOrdersAt (pairs := p + 1)
      (heHuEvenFirst (K := K) p mu) 1 := by
  rw [heHuEvenFirst_eq_towerModel]
  intro t
  by_cases ht : t.val < p
  · let j : Fin p := ⟨t.val, ht⟩
    have hevenIndex :
        (⟨2 * t.val, by omega⟩ : Fin (2 * (p + 1))) =
          Fin.castAdd 2 (⟨2 * j.val, by omega⟩ : Fin (2 * p)) := by
      apply Fin.ext
      rfl
    rw [hevenIndex, Fin.append_left]
    exact standardHyperbolicEndpointTower_leadingOrders (K := K) p j
  · have htEq : t.val = p := by omega
    have hevenIndex :
        (⟨2 * t.val, by omega⟩ : Fin (2 * (p + 1))) =
          Fin.natAdd (2 * p) (0 : Fin 2) := by
      apply Fin.ext
      simp [htEq]
    rw [hevenIndex, Fin.append_right]
    simp [heHuBinaryFirst]

/-- Proposition 2.7(iv) in the exact normal form needed in Lemma 4.5:
an alternating source prefix ending at order `-2e` is one of
`W_1^(2k+4)(1)` and `W_1^(2k+4)(Delta)`. -/
theorem heHuLemma45_sourcePrefix_evenFirst
    (sourceLaws : Beli2006AlphaLaws.{u, v} K)
    [DyadicDiscriminantClassLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    {m k : Nat} (a : GoodBONG q L ((m + 1) + 2))
    (hmStable : 2 * k + 2 ≤ m)
    (hSourceFirst : a.order 0 = 0)
    (hSourceBoundary : a.order ⟨2 * k + 3, by omega⟩ =
      -(2 * (ramificationIndex K : Int))) :
    ∃ mu : Kˣ,
      (mu = 1 ∨
        mu = (inferInstance :
          DyadicDiscriminantClassLaws K).discriminantUnit) ∧
      DiagonalRepresents
        (diagonalUnitCoefficients (heHuEvenFirst (K := K) (k + 1) mu))
        (a.prefixValues (2 * (k + 2)) (by omega)) := by
  let source : Fin (2 * (k + 2)) → Kˣ :=
    a.prefixValueUnits (2 * (k + 2)) (by omega)
  have hlast : a.order ⟨2 * (k + 2) - 1, by omega⟩ =
      0 - 2 * (ramificationIndex K : Int) := by
    convert hSourceBoundary using 1 <;> congr 1 <;> omega
  have hsourceClasses : AlternatingEndpointPairClasses source := by
    letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
    simpa only [source] using
      a.lemma79_endpointTower_pairClasses 0 (k + 2) (by omega)
        (by omega) hSourceFirst hlast
  have hsourceOrders :
      AlternatingEndpointLeadingOrdersAt source (1 : Kˣ) := by
    letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
    have hone : ordUnit K (1 : Kˣ) = 0 := by
      have h := ordUnit_mul K (1 : Kˣ) 1
      simp only [mul_one] at h
      omega
    intro t
    rw [hone]
    simpa only [source] using
      a.lemma79_endpointTower_leadingOrders 0 (k + 2) (by omega)
        (by omega) hSourceFirst hlast t
  rcases AlternatingEndpointTower.signedDeterminant_cases source
      hsourceClasses with hsquare | hdelta
  · refine ⟨1, Or.inl rfl, ?_⟩
    have htargetClasses := heHuLemma45_evenFirst_pairClasses
      (K := K) (k + 1) 1 (Or.inl rfl)
    have htargetOrders := heHuLemma45_evenFirst_leadingOrders
      (K := K) (k + 1) 1
    have hdet : IsSquare
        (diagonalUnitDeterminant source *
          diagonalUnitDeterminant (heHuEvenFirst (K := K) (k + 1) 1)) := by
      rw [diagonalUnitDeterminant_heHuEvenFirst]
      simpa [AlternatingEndpointTower.signedDeterminant,
        mul_comm, mul_left_comm, mul_assoc] using hsquare
    have hrep := alternatingEndpointTower_equalDeterminantRepresentation
      (pairs := k + 2) source (heHuEvenFirst (K := K) (k + 1) 1)
        (1 : Kˣ) hsourceClasses htargetClasses hsourceOrders
          htargetOrders hdet
    simpa only [source, diagonalUnitCoefficients_prefixValueUnits] using hrep
  · let delta :=
      (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
    refine ⟨delta, Or.inr (by rfl), ?_⟩
    have htargetClasses := heHuLemma45_evenFirst_pairClasses
      (K := K) (k + 1) delta (Or.inr (by rfl))
    have htargetOrders := heHuLemma45_evenFirst_leadingOrders
      (K := K) (k + 1) delta
    have hdet : IsSquare
        (diagonalUnitDeterminant source *
          diagonalUnitDeterminant
            (heHuEvenFirst (K := K) (k + 1) delta)) := by
      rw [diagonalUnitDeterminant_heHuEvenFirst]
      simpa [AlternatingEndpointTower.signedDeterminant, delta,
        mul_comm, mul_left_comm, mul_assoc] using hdelta
    have hrep := alternatingEndpointTower_equalDeterminantRepresentation
      (pairs := k + 2) source
        (heHuEvenFirst (K := K) (k + 1) delta) (1 : Kˣ)
          hsourceClasses htargetClasses hsourceOrders htargetOrders hdet
    simpa only [source, diagonalUnitCoefficients_prefixValueUnits] using hrep

/-- The common coefficient head used by Lemma 3.10 is exactly the first
`2*k` entries of the already-constructed second discriminant test. -/
theorem heHuLemma45HyperbolicBONGValues_eq_targetPrefix
    [DyadicDiscriminantClassLaws K] (k : Nat) :
    heHuLemma45HyperbolicBONGValues (K := K) k =
      (heHuLemma43Target (K := K) k).prefixValueUnits (2 * k) (by omega) := by
  funext i
  rcases Nat.even_or_odd i.val with hiEven | hiOdd
  · rcases hiEven with ⟨t, ht⟩
    have htSmall : t < k := by omega
    let j : Fin k := ⟨t, htSmall⟩
    have hindex : i = ⟨2 * j.val, by omega⟩ := by
      apply Fin.ext
      simpa only [j, two_mul] using ht
    rw [hindex]
    change (if Even (2 * j.val) then 1 else
        -(uniformizerPowerUnit K
          (-(2 * (ramificationIndex K : Int))))) =
      (heHuLemma43Target (K := K) k).valueUnit ⟨2 * j.val, by omega⟩
    rw [(heHuLemma43Target_hyperbolicValues (K := K) k j).1]
    simp only [even_two_mul, if_true]
  · rcases hiOdd with ⟨t, ht⟩
    have htSmall : t < k := by omega
    let j : Fin k := ⟨t, htSmall⟩
    have hindex : i = ⟨2 * j.val + 1, by omega⟩ := by
      apply Fin.ext
      omega
    rw [hindex]
    change (if Even (2 * j.val + 1) then 1 else
        -(uniformizerPowerUnit K
          (-(2 * (ramificationIndex K : Int))))) =
      (heHuLemma43Target (K := K) k).valueUnit
        ⟨2 * j.val + 1, by omega⟩
    rw [(heHuLemma43Target_hyperbolicValues (K := K) k j).2]
    simp only [Nat.not_even_two_mul_add_one, if_false]

/-- The signed determinant of the literal Lemma 3.10 head is a square.
This is the determinant factor used in both Table 2 tests. -/
theorem heHuLemma45HyperbolicBONGValues_signedDeterminant_isSquare
    [DyadicDiscriminantClassLaws K] (k : Nat) :
    IsSquare
      ((-1 : Kˣ) ^ k *
        diagonalUnitDeterminant
          (heHuLemma45HyperbolicBONGValues (K := K) k)) := by
  have htarget :=
    heHuLemma43Target_signedHyperbolicPrefix_isSquare (K := K) k
  rw [heHuLemma45HyperbolicBONGValues_eq_targetPrefix (K := K) k,
    (heHuLemma43Target (K := K) k).diagonalUnitDeterminant_prefixValueUnits]
  change IsSquare
    ((-1 : Kˣ) ^ k *
      (heHuLemma43Target (K := K) k).toBONG.prefixProduct (2 * k))
  simpa only [BONG.signedEvenPrefixProduct] using htarget

/-- Determinant calculation common to the two tests built from a binary
`[1,-x]` tail.  The square-class hypothesis is the paper's signed source
prefix parameter. -/
theorem heHuLemma45_firstTest_determinantSquare
    [DyadicDiscriminantClassLaws K]
    {X : Type u} [AddCommGroup X] [Module K X]
    {s : QuadraticSpace K X} {N : Lattice K X}
    (A x : Kˣ) (k : Nat) (b : GoodBONG s N 2)
    (hBIntegral : Lattice.IsIntegral s N)
    (hvalues : b.valueUnit = heHuBinaryFirst x)
    (hclass : IsSquare (((-1 : Kˣ) ^ (k + 2) * A) * x)) :
    IsSquare
      (-A * diagonalUnitDeterminant
        (heHu2022Lemma310BONG b hBIntegral k).valueUnit) := by
  have hhead :=
    heHuLemma45HyperbolicBONGValues_signedDeterminant_isSquare
      (K := K) k
  have hproduct := hhead.mul hclass
  rw [heHuLemma45Lemma310_valueUnit_eq_append b hBIntegral k,
    diagonalUnitDeterminant_heHuFinFamilyCast,
    diagonalUnitDeterminant_append, hvalues,
    diagonalUnitDeterminant_heHuBinaryFirst]
  have hsign : (-1 : Kˣ) ^ k * (-1 : Kˣ) ^ (k + 2) = 1 := by
    rw [← pow_add]
    have hsum : k + (k + 2) = 2 * (k + 1) := by omega
    rw [hsum, pow_mul]
    norm_num
  have heq :
      -A *
          (diagonalUnitDeterminant
              (heHuLemma45HyperbolicBONGValues (K := K) k) * -x) =
        (((-1 : Kˣ) ^ k *
            diagonalUnitDeterminant
              (heHuLemma45HyperbolicBONGValues (K := K) k)) *
          (((-1 : Kˣ) ^ (k + 2) * A) * x)) := by
    calc
      -A *
          (diagonalUnitDeterminant
              (heHuLemma45HyperbolicBONGValues (K := K) k) * -x) =
        A * diagonalUnitDeterminant
            (heHuLemma45HyperbolicBONGValues (K := K) k) * x := by
        simp only [neg_mul, mul_neg, neg_neg, mul_assoc]
      _ = ((-1 : Kˣ) ^ k * (-1 : Kˣ) ^ (k + 2)) *
          (A * diagonalUnitDeterminant
            (heHuLemma45HyperbolicBONGValues (K := K) k) * x) := by
        rw [hsign]
        simp only [one_mul]
      _ = (((-1 : Kˣ) ^ k *
            diagonalUnitDeterminant
              (heHuLemma45HyperbolicBONGValues (K := K) k)) *
          (((-1 : Kˣ) ^ (k + 2) * A) * x)) := by ac_rfl
  rw [heq]
  exact hproduct

/-- Equal-rank isometries on the two entries transport the complete
two-class package of Definition 3.4. -/
theorem HeHuSpacePairProperties.transport {n : Nat}
    {first second first' second' : Fin n → Kˣ}
    (P : HeHuSpacePairProperties first second)
    (hfirst : DiagonalRepresents
      (diagonalUnitCoefficients first')
      (diagonalUnitCoefficients first))
    (hsecond : DiagonalRepresents
      (diagonalUnitCoefficients second')
      (diagonalUnitCoefficients second)) :
    HeHuSpacePairProperties first' second' := by
  apply HeHuSpacePairProperties.of_det_not
  · have hf := DiagonalIsometryInvariantLaws.determinant_square
      first' first hfirst
    have hs := DiagonalIsometryInvariantLaws.determinant_square
      second' second hsecond
    have hsP := isSquare_mul_trans
      (diagonalUnitDeterminant second')
      (diagonalUnitDeterminant second)
      (diagonalUnitDeterminant first) hs P.determinantSquare
    exact isSquare_mul_trans
      (diagonalUnitDeterminant second')
      (diagonalUnitDeterminant first)
      (diagonalUnitDeterminant first') hsP (by
        simpa only [mul_comm] using hf)
  · intro hrep
    exact P.nonisometric
      (hsecond.symm_of_sameRank.trans hrep |>.trans hfirst)

/-- Lemma 3.10 preserves a Table-1 pair: both coefficient lists acquire
the same half-hyperbolic head. -/
theorem heHuLemma45Lemma310_pair {n : Nat}
    {V' V'' : Type u}
    [AddCommGroup V'] [Module K V'] [AddCommGroup V''] [Module K V'']
    {q' : QuadraticSpace K V'} {L' : Lattice K V'}
    {q'' : QuadraticSpace K V''} {L'' : Lattice K V''}
    (b : GoodBONG q' L' (n + 1)) (c : GoodBONG q'' L'' (n + 1))
    (hBIntegral : Lattice.IsIntegral q' L')
    (hCIntegral : Lattice.IsIntegral q'' L'')
    (P : HeHuSpacePairProperties b.valueUnit c.valueUnit) (k : Nat) :
    HeHuSpacePairProperties
      (heHu2022Lemma310BONG b hBIntegral k).valueUnit
      (heHu2022Lemma310BONG c hCIntegral k).valueUnit := by
  let head := heHuLemma45HyperbolicBONGValues (K := K) k
  have Pappend : HeHuSpacePairProperties
      (Fin.append head b.valueUnit) (Fin.append head c.valueUnit) :=
    P.append head
  have Pcast := Pappend.cast (by omega :
    2 * k + (n + 1) = (n + 1) + 2 * k)
  rw [heHuLemma45Lemma310_valueUnit_eq_append b hBIntegral k,
    heHuLemma45Lemma310_valueUnit_eq_append c hCIntegral k]
  exact Pcast

/-- In the hypothetical nonzero boundary-alpha branch, Lemma 2.10(ii)
removes both alpha caps from the signed prefix defect.  The strict final
jump makes the right cap larger than the resulting threshold. -/
theorem heHuLemma45_rawPrefixDefect_of_alpha_one
    [QuadraticDefectLaws K]
    {m k : Nat} (a : GoodBONG q L ((m + 1) + 2))
    (hmStable : 2 * k + 2 ≤ m)
    (hAIntegral : Lattice.IsIntegral q L)
    (hI1 : a.HeHuI1E (2 * k + 2) (by omega))
    (hI2 : a.HeHuI2E (2 * k + 2) (by omega))
    (halpha : a.alphaValue ⟨2 * k + 2, by omega⟩ = 1)
    (hlargeGap : 2 * (ramificationIndex K : Int) <
      a.order ⟨2 * k + 4, by omega⟩ -
        a.order ⟨2 * k + 3, by omega⟩) :
    let R := a.order ⟨2 * k + 3, by omega⟩
    let d := 1 - R
    defectOrder (K := K)
        ((-1 : Kˣ) ^ (k + 2) * a.prefixProduct (2 * k + 4)) =
        (((d : Int) : ℚ) : WithTop ℚ) ∧
      0 ≤ d ∧ d < 2 * (ramificationIndex K : Int) := by
  dsimp only
  let n := 2 * k + 2
  let idx : LongRepresentationIndex ((m + 1) + 2) (n + 1) :=
    { val := n
      one_lt := by simp only [n]; omega
      succ_lt_large := by simp only [n]; omega
      le_small_succ := by omega }
  let boundary : Fin (m + 2) := ⟨n, by simp only [n]; omega⟩
  let nextBoundary : Fin (m + 2) :=
    ⟨n + 1, by simp only [n]; omega⟩
  have hnEven : Even n := ⟨k + 1, by simp only [n]; omega⟩
  have hprevious : a.order ⟨idx.val - 1, by
      have := idx.succ_lt_large
      omega⟩ = -(2 * (ramificationIndex K : Int)) := by
    have hindexEven : Even ((n - 1) + 1) :=
      ⟨k + 1, by simp only [n]; omega⟩
    have h := hI1.evenOrder ⟨n - 1, by omega⟩ hindexEven
    simpa only [idx, n] using h
  have hcurrent : a.order ⟨idx.val, by
      have := idx.succ_lt_large
      omega⟩ = 0 := by
    have h := hI1.oddOrder ⟨n, by omega⟩ (Even.add_one hnEven)
    simpa only [idx] using h
  have hboundaryGap : a.orderGap boundary =
      a.order ⟨2 * k + 3, by omega⟩ := by
    unfold orderGap
    rw [show boundary.castSucc =
        (⟨2 * k + 2, by omega⟩ : Fin ((m + 1) + 2)) by
          apply Fin.ext
          rfl]
    rw [show boundary.succ =
        (⟨2 * k + 3, by omega⟩ : Fin ((m + 1) + 2)) by
          apply Fin.ext
          rfl]
    have hzero : a.order ⟨2 * k + 2, by omega⟩ = 0 := by
      simpa only [idx, n] using hcurrent
    rw [hzero]
    omega
  have hRcases :=
    ((a.heHu2022Proposition26 boundary).alphaOne (by
      simpa only [boundary, n] using halpha)).1
  rw [hboundaryGap] at hRcases
  have hRLower : 2 - 2 * (ramificationIndex K : Int) ≤
      a.order ⟨2 * k + 3, by omega⟩ := by
    rcases hRcases with hRone | hReven
    · rw [hRone]
      have he := ramificationIndex_pos (K := K)
      omega
    · exact hReven.2.1
  have hRUpper : a.order ⟨2 * k + 3, by omega⟩ ≤ 1 := by
    rcases hRcases with hRone | hReven
    · rw [hRone]
    · omega
  have hdNonneg : 0 ≤ 1 - a.order ⟨2 * k + 3, by omega⟩ := by
    omega
  have hdLt : 1 - a.order ⟨2 * k + 3, by omega⟩ <
      2 * (ramificationIndex K : Int) := by
    omega
  have hnextGap : a.orderGap nextBoundary =
      a.order ⟨2 * k + 4, by omega⟩ -
        a.order ⟨2 * k + 3, by omega⟩ := by
    unfold orderGap
    rw [show nextBoundary.castSucc =
        (⟨2 * k + 3, by omega⟩ : Fin ((m + 1) + 2)) by
          apply Fin.ext
          rfl]
    rw [show nextBoundary.succ =
        (⟨2 * k + 4, by omega⟩ : Fin ((m + 1) + 2)) by
          apply Fin.ext
          rfl]
  have hnextAlpha : 2 * (ramificationIndex K : ℚ) <
      a.alphaValue nextBoundary := by
    exact ((a.heHu2022Proposition26 nextBoundary).compareTwoE.2.2).2 (by
      rw [hnextGap]
      exact hlargeGap)
  have hrightCap : a.prefixAlphaCap (2 * k + 4) =
      (a.alphaValue nextBoundary : WithTop ℚ) := by
    rw [a.prefixAlphaCap_of_internal (by omega) (by omega)]
    congr 2
  have hthresholdLtCap :
      ((((1 - a.order ⟨2 * k + 3, by omega⟩ : Int) : ℚ) :
          WithTop ℚ)) < a.prefixAlphaCap (2 * k + 4) := by
    rw [hrightCap]
    apply WithTop.coe_lt_coe.mpr
    have hdLtQ :
        ((1 - a.order ⟨2 * k + 3, by omega⟩ : Int) : ℚ) <
          2 * (ramificationIndex K : ℚ) := by
      exact_mod_cast hdLt
    exact hdLtQ.trans hnextAlpha
  have hlocalRaw :=
    ((a.heHuI2E_iff_alpha_le_one_and_capped_boundary
      (n := 2 * k + 2) (by omega)).mp hI2).2 halpha
  have hlocal :
      a.truncatedPrefixDefect a (-1) idx.val (idx.val + 2) =
        ((((1 - a.order ⟨idx.val + 1, idx.succ_lt_large⟩ : Int) : ℚ) :
          WithTop ℚ)) := by
    simpa only [heHuAdjacentCappedDefect, idx, n, Int.cast_sub,
      Int.cast_one] using hlocalRaw
  have hnextOrderLower : -(2 * (ramificationIndex K : Int)) <
      a.order ⟨idx.val + 1, idx.succ_lt_large⟩ := by
    simpa only [idx, n] using lt_of_lt_of_le (by omega :
      -(2 * (ramificationIndex K : Int)) <
        2 - 2 * (ramificationIndex K : Int)) hRLower
  have hfullRaw :=
    (a.heHu2022Lemma210ii hAIntegral idx hnEven hprevious hcurrent
      hnextOrderLower).mp hlocal
  have hhalf : (2 * k + 2 + 2) / 2 = k + 2 := by omega
  have hlength : 2 * k + 2 + 2 = 2 * k + 4 := by omega
  have hnextIndex : 2 * k + 2 + 1 = 2 * k + 3 := by omega
  have hfull :
      a.truncatedPrefixDefect a ((-1 : Kˣ) ^ (k + 2)) 0
          (2 * k + 4) =
        ((((1 - a.order ⟨2 * k + 3, by omega⟩ : Int) : ℚ) :
          WithTop ℚ)) := by
    simpa only [idx, n, hhalf, hlength, hnextIndex] using hfullRaw
  have hminimum :
      ((((1 - a.order ⟨2 * k + 3, by omega⟩ : Int) : ℚ) :
          WithTop ℚ)) =
        min (defectOrder (K := K)
          ((-1 : Kˣ) ^ (k + 2) * a.prefixProduct (2 * k + 4)))
          (a.prefixAlphaCap (2 * k + 4)) := by
    rw [← hfull]
    unfold truncatedPrefixDefect
    rw [a.prefixAlphaCap_zero]
    simp only [min_top_left, BONG.GoodBONG.prefixProduct,
      BONG.prefixProduct_zero, mul_one]
  have hraw := eq_left_of_eq_min_lt_right hminimum hthresholdLtCap
  exact ⟨hraw.symm, hdNonneg, hdLt⟩

/-- The contradiction common to the two Table-2 tests in the necessity
half of Lemma 4.5.  The order hypotheses are exactly condition (iv)'s
terminal trigger, while `hdet` is the determinant identity printed in the
paper immediately before the appeal to Lemma 3.13. -/
theorem heHuLemma45_twoTestContradiction
    [DyadicDiagonalCodimensionTwoLaws K]
    {X Y : Type u}
    [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
    {s : QuadraticSpace K X} {t : QuadraticSpace K Y}
    {N : Lattice K X} {P : Lattice K Y}
    {m k : Nat} (a : GoodBONG q L ((m + 1) + 2))
    (b₁ : GoodBONG s N (2 * k + 2))
    (b₂ : GoodBONG t P (2 * k + 2))
    (hmStable : 2 * k + 2 ≤ m)
    (hB₁Integral : Lattice.IsIntegral s N)
    (hB₂Integral : Lattice.IsIntegral t P)
    (hAll : HeHuAllLongRepresentationConditions.{u, v, u}
      (n := 2 * k + 1) a)
    (S : Int)
    (hB₁Last : b₁.order ⟨2 * k + 1, by omega⟩ = S)
    (hB₂Last : b₂.order ⟨2 * k + 1, by omega⟩ = S)
    (hBoundary : a.order ⟨2 * k + 3, by omega⟩ ≤ S)
    (hNext : S + 2 * (ramificationIndex K : Int) <
      a.order ⟨2 * k + 4, by omega⟩)
    (pair : HeHuSpacePairProperties b₁.valueUnit b₂.valueUnit)
    (hdet : IsSquare
      (-diagonalUnitDeterminant
          (a.prefixValueUnits (2 * k + 4) (by omega)) *
        diagonalUnitDeterminant b₁.valueUnit)) : False := by
  let i : LongRepresentationIndex ((m + 1) + 2) (2 * k + 2) :=
    { val := 2 * k + 3
      one_lt := by omega
      succ_lt_large := by omega
      le_small_succ := by omega }
  have htrigger₁ :
      ((if hiTarget : i.val ≤ 2 * k + 2 then
          a.order ⟨i.val + 1, i.succ_lt_large⟩ ≤
            b₁.order ⟨i.val - 1, by
              have := i.one_lt
              omega⟩
        else True) ∧
        b₁.order ⟨i.val - 2, by
            have := i.one_lt
            have := i.le_small_succ
            omega⟩ + 2 * (ramificationIndex K : Int) <
          a.order ⟨i.val + 1, i.succ_lt_large⟩ ∧
        a.order ⟨i.val, by
            have := i.succ_lt_large
            omega⟩ + 2 * (ramificationIndex K : Int) ≤
          b₁.order ⟨i.val - 2, by
            have := i.one_lt
            have := i.le_small_succ
            omega⟩ + 2 * (ramificationIndex K : Int)) := by
    have hlastIndex :
        (⟨i.val - 2, by
          have := i.one_lt
          have := i.le_small_succ
          omega⟩ : Fin (2 * k + 2)) = ⟨2 * k + 1, by omega⟩ := by
      apply Fin.ext
      dsimp only [i]
      omega
    have hboundaryIndex :
        (⟨i.val, by have := i.succ_lt_large; omega⟩ :
          Fin ((m + 1) + 2)) = ⟨2 * k + 3, by omega⟩ := by
      apply Fin.ext
      rfl
    have hnextIndex :
        (⟨i.val + 1, i.succ_lt_large⟩ : Fin ((m + 1) + 2)) =
          ⟨2 * k + 4, by omega⟩ := by
      apply Fin.ext
      rfl
    constructor
    · simp [i]
    constructor
    · rw [hlastIndex, hnextIndex, hB₁Last]
      exact hNext
    · rw [hboundaryIndex, hlastIndex, hB₁Last]
      omega
  have htrigger₂ :
      ((if hiTarget : i.val ≤ 2 * k + 2 then
          a.order ⟨i.val + 1, i.succ_lt_large⟩ ≤
            b₂.order ⟨i.val - 1, by
              have := i.one_lt
              omega⟩
        else True) ∧
        b₂.order ⟨i.val - 2, by
            have := i.one_lt
            have := i.le_small_succ
            omega⟩ + 2 * (ramificationIndex K : Int) <
          a.order ⟨i.val + 1, i.succ_lt_large⟩ ∧
        a.order ⟨i.val, by
            have := i.succ_lt_large
            omega⟩ + 2 * (ramificationIndex K : Int) ≤
          b₂.order ⟨i.val - 2, by
            have := i.one_lt
            have := i.le_small_succ
            omega⟩ + 2 * (ramificationIndex K : Int)) := by
    have hlastIndex :
        (⟨i.val - 2, by
          have := i.one_lt
          have := i.le_small_succ
          omega⟩ : Fin (2 * k + 2)) = ⟨2 * k + 1, by omega⟩ := by
      apply Fin.ext
      dsimp only [i]
      omega
    have hboundaryIndex :
        (⟨i.val, by have := i.succ_lt_large; omega⟩ :
          Fin ((m + 1) + 2)) = ⟨2 * k + 3, by omega⟩ := by
      apply Fin.ext
      rfl
    have hnextIndex :
        (⟨i.val + 1, i.succ_lt_large⟩ : Fin ((m + 1) + 2)) =
          ⟨2 * k + 4, by omega⟩ := by
      apply Fin.ext
      rfl
    constructor
    · simp [i]
    constructor
    · rw [hlastIndex, hnextIndex, hB₂Last]
      exact hNext
    · rw [hboundaryIndex, hlastIndex, hB₂Last]
      omega
  have hrep₁Raw := (hAll b₁ hB₁Integral) i htrigger₁
  have hrep₂Raw := (hAll b₂ hB₂Integral) i htrigger₂
  have hrep₁ : DiagonalRepresents
      (diagonalUnitCoefficients b₁.valueUnit)
      (diagonalUnitCoefficients
        (a.prefixValueUnits (2 * k + 4) (by omega))) := by
    have hs : i.val - 1 = 2 * k + 2 := by
      dsimp only [i]
      omega
    have ht : i.val + 1 = 2 * k + 4 := by
      dsimp only [i]
    have hcast := heHuLemma43_diagonalRepresents_castLengths
      (K := K) hs ht hrep₁Raw
    convert hcast using 1
    · funext j
      rfl
    · funext j
      rfl
  have hrep₂ : DiagonalRepresents
      (diagonalUnitCoefficients b₂.valueUnit)
      (diagonalUnitCoefficients
        (a.prefixValueUnits (2 * k + 4) (by omega))) := by
    have hs : i.val - 1 = 2 * k + 2 := by
      dsimp only [i]
      omega
    have ht : i.val + 1 = 2 * k + 4 := by
      dsimp only [i]
    have hcast := heHuLemma43_diagonalRepresents_castLengths
      (K := K) hs ht hrep₂Raw
    convert hcast using 1
    · funext j
      rfl
    · funext j
      rfl
  have hexact := heHu2022Lemma313CodimensionTwo
    b₁.valueUnit b₂.valueUnit pair
      (a.prefixValueUnits (2 * k + 4) (by omega)) hdet
  rcases hexact with hfirst | hsecond
  · exact hfirst.2 hrep₂
  · exact hsecond.1 hrep₁

/-- Lift a pair of integral binary Table 2 tails through Lemma 3.10 and
apply the common Lemma 3.13 contradiction. -/
theorem heHuLemma45_binaryTailTestsContradiction
    [DyadicDiscriminantClassLaws K]
    [DyadicDiagonalCodimensionTwoLaws K]
    {X Y : Type u}
    [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
    {s : QuadraticSpace K X} {t : QuadraticSpace K Y}
    {N : Lattice K X} {P : Lattice K Y}
    {m k : Nat} (a : GoodBONG q L ((m + 1) + 2))
    (b₁ : GoodBONG s N 2) (b₂ : GoodBONG t P 2)
    (hB₁Integral : Lattice.IsIntegral s N)
    (hB₂Integral : Lattice.IsIntegral t P)
    (hAll : HeHuAllLongRepresentationConditions.{u, v, u}
      (n := 2 * k + 1) a)
    (hmStable : 2 * k + 2 ≤ m)
    (R x : Kˣ)
    (hR₁ : b₁.order 1 = ordUnit K R)
    (hR₂ : b₂.order 1 = ordUnit K R)
    (hpair : HeHuSpacePairProperties b₁.valueUnit b₂.valueUnit)
    (hfirstValues : b₁.valueUnit = heHuBinaryFirst x)
    (hclass : IsSquare
      (((-1 : Kˣ) ^ (k + 2) * a.prefixProduct (2 * k + 4)) * x))
    (hBoundary : a.order ⟨2 * k + 3, by omega⟩ ≤ ordUnit K R)
    (hNext : ordUnit K R + 2 * (ramificationIndex K : Int) <
      a.order ⟨2 * k + 4, by omega⟩) : False := by
  let raw₁ := heHu2022Lemma310BONG b₁ hB₁Integral k
  let raw₂ := heHu2022Lemma310BONG b₂ hB₂Integral k
  let hdim : 2 + 2 * k = 2 * k + 2 := by omega
  let B₁ := raw₁.castLength hdim
  let B₂ := raw₂.castLength hdim
  have hB₁Integral' : Lattice.IsIntegral
      (Lattice.halfHyperbolicExtensionForm s k)
      (N.halfHyperbolicExtensionLattice k) :=
    heHuHalfHyperbolicExtension_isIntegral hB₁Integral k
  have hB₂Integral' : Lattice.IsIntegral
      (Lattice.halfHyperbolicExtensionForm t k)
      (P.halfHyperbolicExtensionLattice k) :=
    heHuHalfHyperbolicExtension_isIntegral hB₂Integral k
  have hB₁Values : B₁.valueUnit =
      heHuFinFamilyCast hdim raw₁.valueUnit := by
    funext i
    simp only [B₁, heHuFinFamilyCast, valueUnit_castLength_heHu]
    congr 1
  have hB₂Values : B₂.valueUnit =
      heHuFinFamilyCast hdim raw₂.valueUnit := by
    funext i
    simp only [B₂, heHuFinFamilyCast, valueUnit_castLength_heHu]
    congr 1
  have hpairRaw := heHuLemma45Lemma310_pair b₁ b₂
    hB₁Integral hB₂Integral hpair k
  have hpairFull : HeHuSpacePairProperties B₁.valueUnit B₂.valueUnit := by
    rw [hB₁Values, hB₂Values]
    exact hpairRaw.cast hdim
  have hlastRaw₁ := heHu2022Lemma310TailOrders
    b₁ hB₁Integral k (1 : Fin 2)
  have hlastRaw₂ := heHu2022Lemma310TailOrders
    b₂ hB₂Integral k (1 : Fin 2)
  have hlast₁ : B₁.order ⟨2 * k + 1, by omega⟩ = ordUnit K R := by
    dsimp only [B₁]
    rw [order_castLength]
    exact hlastRaw₁.trans hR₁
  have hlast₂ : B₂.order ⟨2 * k + 1, by omega⟩ = ordUnit K R := by
    dsimp only [B₂]
    rw [order_castLength]
    exact hlastRaw₂.trans hR₂
  have hdetRaw := heHuLemma45_firstTest_determinantSquare
    (K := K) (a.prefixProduct (2 * k + 4)) x k b₁ hB₁Integral
      hfirstValues hclass
  have hdet : IsSquare
      (-diagonalUnitDeterminant
          (a.prefixValueUnits (2 * k + 4) (by omega)) *
        diagonalUnitDeterminant B₁.valueUnit) := by
    rw [a.diagonalUnitDeterminant_prefixValueUnits]
    rw [hB₁Values, diagonalUnitDeterminant_heHuFinFamilyCast]
    exact hdetRaw
  exact heHuLemma45_twoTestContradiction a B₁ B₂ hmStable
    hB₁Integral' hB₂Integral' hAll (ordUnit K R) hlast₁ hlast₂
      hBoundary hNext hpairFull hdet

/-- The first conclusion in the large-gap clause of Lemma 4.5.  If the
boundary alpha were one, the two Table 2 lattices determined by the signed
source prefix would both be represented, contrary to Lemma 3.13. -/
theorem heHu2022Lemma45_boundaryAlpha_zero
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicDiagonalCodimensionTwoLaws K]
    {m k : Nat} (a : GoodBONG q L ((m + 1) + 2))
    (hmStable : 2 * k + 2 ≤ m)
    (hAIntegral : Lattice.IsIntegral q L)
    (hI1 : a.HeHuI1E (2 * k + 2) (by omega))
    (hI2 : a.HeHuI2E (2 * k + 2) (by omega))
    (hAll : HeHuAllLongRepresentationConditions.{u, v, u}
      (n := 2 * k + 1) a)
    (hlargeGap : 2 * (ramificationIndex K : Int) <
      a.order ⟨2 * k + 4, by omega⟩ -
        a.order ⟨2 * k + 3, by omega⟩) :
    a.alphaValue ⟨2 * k + 2, by omega⟩ = 0 := by
  by_contra halphaNe
  have halphaLe := hI2.alphaBoundary_le_one
  have halphaOne : a.alphaValue ⟨2 * k + 2, by omega⟩ = 1 :=
    le_antisymm (by simpa using halphaLe)
      (a.heHuOne_le_alphaValue_of_ne_zero ⟨2 * k + 2, by omega⟩
        halphaNe)
  have hrawData := a.heHuLemma45_rawPrefixDefect_of_alpha_one hmStable
    hAIntegral hI1 hI2 halphaOne hlargeGap
  let R : Int := a.order ⟨2 * k + 3, by omega⟩
  let d : Int := 1 - R
  let cRaw : Kˣ :=
    (-1 : Kˣ) ^ (k + 2) * a.prefixProduct (2 * k + 4)
  have hraw : defectOrder (K := K) cRaw =
      (((d : Int) : ℚ) : WithTop ℚ) := by
    simpa only [R, d, cRaw] using hrawData.1
  have hdNonneg : 0 ≤ d := by
    simpa only [R, d] using hrawData.2.1
  have hdLt : d < 2 * (ramificationIndex K : Int) := by
    simpa only [R, d] using hrawData.2.2
  have hNext : R + 2 * (ramificationIndex K : Int) <
      a.order ⟨2 * k + 4, by omega⟩ := by
    dsimp only [R]
    omega
  rcases Int.even_or_odd (ordUnit K cRaw) with hcEven | hcOdd
  · have hdOddRational :=
      isOddRationalInteger_of_even_ordUnit_of_defectOrder_eq
        cRaw (d : ℚ) hcEven hraw (by exact_mod_cast hdLt)
    rcases hdOddRational with ⟨z, hzOdd, hdz⟩
    have hdzInt : d = z := by exact_mod_cast hdz
    have hdOdd : Odd d := by simpa only [hdzInt] using hzOdd
    have hREven : Even R := by
      rcases hdOdd with ⟨z, hz⟩
      refine ⟨-z, ?_⟩
      dsimp only [d] at hz
      omega
    let δ : Kˣ := normalizedUnitPart K cRaw
    have hδUnit : IsValuationUnit K (δ : K) := by
      simpa only [δ] using normalizedUnitPart_isValuationUnit K cRaw
    have hδDefect : defectOrder (K := K) δ =
        (((d : Int) : ℚ) : WithTop ℚ) :=
      (heHuLemma45_normalizedUnitPart_defectOrder cRaw hcEven).trans hraw
    let x : Kˣ := δ * uniformizerPowerUnit K R
    have hparity : Even (ordUnit K cRaw - R) := hcEven.sub hREven
    have hclass : IsSquare (cRaw * x) := by
      simpa only [x, δ] using
        heHuLemma45_normalizedUniformizer_sameSquareClass cRaw R hparity
    have hxDefect : defectOrder (K := K) x =
        (((d : Int) : ℚ) : WithTop ℚ) :=
      (heHuLemma45_defectOrder_eq_of_mul_isSquare cRaw x hclass).symm.trans
        hraw
    have hxSharp : HeHuSharpDomain x :=
      heHuLemma45_sharpDomain_of_defect_lt_twoE x d hxDefect hdLt
    let eta : Kˣ := heHuSharp x hxSharp
    have hetaUnit : IsValuationUnit K (eta : K) := by
      simpa only [eta] using (heHu2022Proposition32 x hxSharp).1
    have honeUnit : IsValuationUnit K ((1 : Kˣ) : K) := by
      simp [IsValuationUnit]
    let b₁ := heHuUnitDefectTailGoodBONG (K := K)
      (1 : Kˣ) δ d honeUnit hδUnit hdOdd hdNonneg hdLt hδDefect
    let b₂ := heHuUnitDefectTailGoodBONG (K := K)
      eta δ d hetaUnit hδUnit hdOdd hdNonneg hdLt hδDefect
    have hB₁Integral : Lattice.IsIntegral
        (binaryDiagonalModelSpace
          (heHuUnitDefectTailValues (K := K) (1 : Kˣ) δ d 0)
          (heHuUnitDefectTailValues (K := K) (1 : Kˣ) δ d 1)
          (heHuUnitDefectTail_admissible (1 : Kˣ) δ d honeUnit
            hδUnit hdOdd hdNonneg hdLt hδDefect))
        (binaryDiagonalModelLattice (K := K)) := by
      apply heHuIntegral_of_firstOrder_nonneg b₁
      rw [heHuUnitDefectTailGoodBONG_order]
      norm_num
    have hB₂Integral : Lattice.IsIntegral
        (binaryDiagonalModelSpace
          (heHuUnitDefectTailValues (K := K) eta δ d 0)
          (heHuUnitDefectTailValues (K := K) eta δ d 1)
          (heHuUnitDefectTail_admissible eta δ d hetaUnit hδUnit hdOdd
            hdNonneg hdLt hδDefect))
        (binaryDiagonalModelLattice (K := K)) := by
      apply heHuIntegral_of_firstOrder_nonneg b₂
      rw [heHuUnitDefectTailGoodBONG_order]
      norm_num
    have hRFormula : 1 - d = R := by
      dsimp only [d]
      omega
    have hB₁Values : b₁.valueUnit = heHuBinaryFirst x := by
      funext i
      rw [heHuLemma45_unitDefectTailGoodBONG_valueUnit]
      fin_cases i
      · rfl
      · change -(1 * δ * uniformizerPowerUnit K (1 - d)) = -x
        rw [hRFormula]
        simp only [one_mul, x]
    have hB₂Values : b₂.valueUnit = heHuBinaryTwist x eta := by
      funext i
      rw [heHuLemma45_unitDefectTailGoodBONG_valueUnit]
      fin_cases i
      · rfl
      · change -(eta * δ * uniformizerPowerUnit K (1 - d)) =
          -(eta * x)
        rw [hRFormula]
        simp only [x, mul_assoc]
    have hclassification := heHuBinaryTwist_classification x eta
      (by simpa only [eta] using (heHu2022Proposition32 x hxSharp).2.2)
    have hpair : HeHuSpacePairProperties b₁.valueUnit b₂.valueUnit := by
      rw [hB₁Values, hB₂Values]
      exact HeHuSpacePairProperties.of_det_not _ _
        hclassification.1 hclassification.2.1
    have hB₁Last : b₁.order 1 = R := by
      rw [heHuUnitDefectTailGoodBONG_order]
      change 1 - d = R
      exact hRFormula
    have hB₂Last : b₂.order 1 = R := by
      rw [heHuUnitDefectTailGoodBONG_order]
      change 1 - d = R
      exact hRFormula
    have hclassSource : IsSquare
        (((-1 : Kˣ) ^ (k + 2) * a.prefixProduct (2 * k + 4)) * x) :=
      hclass
    exact a.heHuLemma45_binaryTailTestsContradiction b₁ b₂
      hB₁Integral hB₂Integral hAll hmStable
      (uniformizerPowerUnit K R) x
      (by rw [ordUnit_uniformizerPowerUnit]; exact hB₁Last)
      (by rw [ordUnit_uniformizerPowerUnit]; exact hB₂Last)
      hpair hB₁Values hclassSource
      (by rw [ordUnit_uniformizerPowerUnit])
      (by rw [ordUnit_uniformizerPowerUnit]; exact hNext)
  · have hcZero : defectOrder (K := K) cRaw = 0 := by
      unfold defectOrder
      rw [quadraticDefect_eq_zero_of_odd_ordUnit cRaw hcOdd]
      rfl
    have hdZero : d = 0 := by
      have hcoe : (((d : Int) : ℚ) : WithTop ℚ) = (0 : WithTop ℚ) :=
        hraw.symm.trans hcZero
      have hq : (d : ℚ) = 0 := WithTop.coe_eq_coe.mp hcoe
      exact_mod_cast hq
    have hROne : R = 1 := by
      dsimp only [d] at hdZero
      omega
    let δ : Kˣ := normalizedUnitPart K cRaw
    have hδUnit : IsValuationUnit K (δ : K) := by
      simpa only [δ] using normalizedUnitPart_isValuationUnit K cRaw
    let x : Kˣ := δ * uniformizerPowerUnit K 1
    have hparity : Even (ordUnit K cRaw - (1 : Int)) := by
      rcases hcOdd with ⟨z, hz⟩
      exact ⟨z, by omega⟩
    have hclass : IsSquare (cRaw * x) := by
      simpa only [x, δ] using
        heHuLemma45_normalizedUniformizer_sameSquareClass cRaw 1 hparity
    have hxOrder : ordUnit K x = 1 := by
      dsimp only [x]
      rw [ordUnit_mul, ordUnit_uniformizerPowerUnit,
        (isValuationUnit_iff_ordUnit_eq_zero K δ).1 hδUnit]
      omega
    have hxOdd : Odd (ordUnit K x) := by
      rw [hxOrder]
      exact odd_one
    let delta :=
      (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
    have hnegativeNe : hilbertSymbol K delta x ≠ 1 := by
      simpa only [delta] using
        hilbertSymbol_discriminant_ne_one_of_odd_order x hxOdd
    have hnegative : hilbertSymbol K delta x = -1 :=
      (Int.units_eq_one_or (hilbertSymbol K delta x)).resolve_left hnegativeNe
    have honeUnit : IsValuationUnit K ((1 : Kˣ) : K) := by
      simp [IsValuationUnit]
    have hdeltaUnit : IsValuationUnit K (delta : K) := by
      simpa only [delta] using
        (inferInstance : DyadicDiscriminantClassLaws K).discriminant_isValuationUnit
    let b₁ := heHuUnitUniformizerPairGoodBONG (K := K)
      (1 : Kˣ) δ honeUnit hδUnit
    let b₂ := heHuUnitUniformizerPairGoodBONG (K := K)
      delta δ hdeltaUnit hδUnit
    have hB₁Integral : Lattice.IsIntegral
        (binaryDiagonalModelSpace
          (heHuUnitUniformizerPairValues (K := K) (1 : Kˣ) δ 0)
          (heHuUnitUniformizerPairValues (K := K) (1 : Kˣ) δ 1)
          (heHuUnitUniformizerPair_admissible (1 : Kˣ) δ honeUnit
            hδUnit))
        (binaryDiagonalModelLattice (K := K)) := by
      apply heHuIntegral_of_firstOrder_nonneg b₁
      rw [heHuUnitUniformizerPairGoodBONG_orders]
      norm_num
    have hB₂Integral : Lattice.IsIntegral
        (binaryDiagonalModelSpace
          (heHuUnitUniformizerPairValues (K := K) delta δ 0)
          (heHuUnitUniformizerPairValues (K := K) delta δ 1)
          (heHuUnitUniformizerPair_admissible delta δ hdeltaUnit hδUnit))
        (binaryDiagonalModelLattice (K := K)) := by
      apply heHuIntegral_of_firstOrder_nonneg b₂
      rw [heHuUnitUniformizerPairGoodBONG_orders]
      norm_num
    have hB₁Values : b₁.valueUnit = heHuBinaryFirst x := by
      funext i
      rw [heHuUnitUniformizerPairGoodBONG_valueUnit]
      fin_cases i
      · rfl
      · change -(1 * δ * uniformizerPowerUnit K 1) = -x
        simp only [one_mul, x]
    have hB₂Values : b₂.valueUnit = heHuBinaryTwist x delta := by
      funext i
      rw [heHuUnitUniformizerPairGoodBONG_valueUnit]
      fin_cases i
      · rfl
      · change -(delta * δ * uniformizerPowerUnit K 1) =
          -(delta * x)
        simp only [x, mul_assoc]
    have hclassification :=
      heHuBinaryTwist_classification x delta hnegative
    have hpair : HeHuSpacePairProperties b₁.valueUnit b₂.valueUnit := by
      rw [hB₁Values, hB₂Values]
      exact HeHuSpacePairProperties.of_det_not _ _
        hclassification.1 hclassification.2.1
    have hB₁Last : b₁.order 1 = R := by
      rw [heHuUnitUniformizerPairGoodBONG_orders]
      exact hROne.symm
    have hB₂Last : b₂.order 1 = R := by
      rw [heHuUnitUniformizerPairGoodBONG_orders]
      exact hROne.symm
    have hclassSource : IsSquare
        (((-1 : Kˣ) ^ (k + 2) * a.prefixProduct (2 * k + 4)) * x) :=
      hclass
    exact a.heHuLemma45_binaryTailTestsContradiction b₁ b₂
      hB₁Integral hB₂Integral hAll hmStable
      (uniformizerPowerUnit K R) x
      (by rw [ordUnit_uniformizerPowerUnit]; exact hB₁Last)
      (by rw [ordUnit_uniformizerPowerUnit]; exact hB₂Last)
      hpair hB₁Values hclassSource
      (by rw [ordUnit_uniformizerPowerUnit])
      (by rw [ordUnit_uniformizerPowerUnit]; exact hNext)

/-- Once the boundary alpha vanishes, Proposition 2.6(i) and `I1^E`
identify the last line of the alternating source prefix.  This is the
displayed equality `R_(n+2)=-2e` immediately after the first paragraph of
the published proof of Lemma 4.5. -/
theorem heHu2022Lemma45_boundaryOrder
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicDiagonalCodimensionTwoLaws K]
    {m k : Nat} (a : GoodBONG q L ((m + 1) + 2))
    (hmStable : 2 * k + 2 ≤ m)
    (hAIntegral : Lattice.IsIntegral q L)
    (hI1 : a.HeHuI1E (2 * k + 2) (by omega))
    (hI2 : a.HeHuI2E (2 * k + 2) (by omega))
    (hAll : HeHuAllLongRepresentationConditions.{u, v, u}
      (n := 2 * k + 1) a)
    (hlargeGap : 2 * (ramificationIndex K : Int) <
      a.order ⟨2 * k + 4, by omega⟩ -
        a.order ⟨2 * k + 3, by omega⟩) :
    a.order ⟨2 * k + 3, by omega⟩ =
      -(2 * (ramificationIndex K : Int)) := by
  let boundary : Fin (m + 2) := ⟨2 * k + 2, by omega⟩
  have halpha : a.alphaValue boundary = 0 := by
    simpa only [boundary] using
      a.heHu2022Lemma45_boundaryAlpha_zero hmStable hAIntegral hI1 hI2
        hAll hlargeGap
  have hgap := ((a.heHu2022Proposition26 boundary).alphaZero).1 halpha
  have hcurrentIndex : boundary.castSucc =
      (⟨2 * k + 2, by omega⟩ : Fin ((m + 1) + 2)) := by
    apply Fin.ext
    rfl
  have hcurrent : a.order boundary.castSucc = 0 := by
    rw [hcurrentIndex]
    exact hI1.oddOrder
      (⟨2 * k + 2, by omega⟩ : Fin (2 * k + 3))
      (⟨k + 1, by omega⟩ : Odd (2 * k + 2 + 1))
  have hnextIndex : boundary.succ =
      (⟨2 * k + 3, by omega⟩ : Fin ((m + 1) + 2)) := by
    apply Fin.ext
    rfl
  unfold orderGap at hgap
  rw [hcurrent, hnextIndex] at hgap
  omega

/-- The terminal condition-(iv) index for an even target.  Its existence
is precisely the stable-rank inequality occurring in `I3^E`. -/
def heHuLemma45TerminalIndex {m : Nat} (k : Nat)
    (hmStable : 2 * k + 2 <= m) :
    LongRepresentationIndex ((m + 1) + 2) (2 * k + 2) where
  val := 2 * k + 3
  one_lt := by omega
  succ_lt_large := by omega
  le_small_succ := by omega

/-- At the terminal index, the inequalities occurring in condition (iv)
reduce exactly to the last target order `1-2e`, the source endpoint
`-2e`, and the strict bound `1<R_(n+3)`. -/
theorem heHuLemma45_terminalRepresentation
    {X : Type u} [AddCommGroup X] [Module K X]
    {s : QuadraticSpace K X} {N : Lattice K X}
    {m k : Nat} (a : GoodBONG q L ((m + 1) + 2))
    (b : GoodBONG s N (2 * k + 2))
    (hmStable : 2 * k + 2 ≤ m)
    (hAll : HeHuAllLongRepresentationConditions.{u, v, u}
      (n := 2 * k + 1) a)
    (hBIntegral : Lattice.IsIntegral s N)
    (hTargetLast : b.order ⟨2 * k + 1, by omega⟩ =
      1 - 2 * (ramificationIndex K : Int))
    (hSourceBoundary : a.order ⟨2 * k + 3, by omega⟩ =
      -(2 * (ramificationIndex K : Int)))
    (hSourceNext : 1 < a.order ⟨2 * k + 4, by omega⟩) :
    DiagonalRepresents
      (b.prefixValues (2 * k + 2) (by omega))
      (a.prefixValues (2 * k + 4) (by omega)) := by
  let i := heHuLemma45TerminalIndex (m := m) k hmStable
  have hconditions := hAll b hBIntegral
  have htrigger :
      ((if hi : i.val ≤ 2 * k + 2 then
          a.order ⟨i.val + 1, i.succ_lt_large⟩ ≤
            b.order ⟨i.val - 1, by
              have := i.one_lt
              have := hi
              omega⟩
        else True) ∧
        b.order ⟨i.val - 2, by
            have := i.one_lt
            have := i.le_small_succ
            omega⟩ + 2 * (ramificationIndex K : Int) <
          a.order ⟨i.val + 1, i.succ_lt_large⟩ ∧
        a.order ⟨i.val, by
            have := i.succ_lt_large
            omega⟩ + 2 * (ramificationIndex K : Int) ≤
          b.order ⟨i.val - 2, by
            have := i.one_lt
            have := i.le_small_succ
            omega⟩ + 2 * (ramificationIndex K : Int)) := by
    have hiFalse : ¬ i.val ≤ 2 * k + 2 := by
      dsimp only [i, heHuLemma45TerminalIndex]
      omega
    rw [dif_neg hiFalse]
    constructor
    · trivial
    constructor
    · have hlastIndex :
          (⟨i.val - 2, by
            have := i.one_lt
            have := i.le_small_succ
            omega⟩ : Fin (2 * k + 2)) =
            ⟨2 * k + 1, by omega⟩ := by
          apply Fin.ext
          dsimp only [i, heHuLemma45TerminalIndex]
          omega
      have hnextIndex :
          (⟨i.val + 1, i.succ_lt_large⟩ : Fin ((m + 1) + 2)) =
            ⟨2 * k + 4, by omega⟩ := by
          apply Fin.ext
          dsimp only [i, heHuLemma45TerminalIndex]
      rw [hlastIndex, hnextIndex, hTargetLast]
      omega
    · have hcurrentIndex :
          (⟨i.val, by
            have := i.succ_lt_large
            omega⟩ : Fin ((m + 1) + 2)) =
            ⟨2 * k + 3, by omega⟩ := by
          apply Fin.ext
          dsimp only [i, heHuLemma45TerminalIndex]
      have hlastIndex :
          (⟨i.val - 2, by
            have := i.one_lt
            have := i.le_small_succ
            omega⟩ : Fin (2 * k + 2)) =
            ⟨2 * k + 1, by omega⟩ := by
          apply Fin.ext
          dsimp only [i, heHuLemma45TerminalIndex]
          omega
      rw [hcurrentIndex, hlastIndex, hSourceBoundary, hTargetLast]
      omega
  have hrep := hconditions i htrigger
  exact prefixRepresents_cast b a (by
      dsimp only [i, heHuLemma45TerminalIndex]
      omega) (by
      dsimp only [i, heHuLemma45TerminalIndex]) hrep

/-- Common Proposition 3.5(iii) contradiction used for both possible
endpoint classes.  A literal integral Table 2 target is forced by
condition (iv) into the source prefix, while that prefix has already been
identified with the unique first-column space which does not represent
the second-column target. -/
theorem heHuLemma45_evenSecondContradiction
    [DyadicDiscriminantClassLaws K]
    {X : Type u} [AddCommGroup X] [Module K X]
    {s : QuadraticSpace K X} {N : Lattice K X}
    {m k : Nat} (a : GoodBONG q L ((m + 1) + 2))
    (b : GoodBONG s N (2 * k + 2))
    (hmStable : 2 * k + 2 ≤ m)
    (hAll : HeHuAllLongRepresentationConditions.{u, v, u}
      (n := 2 * k + 1) a)
    (mu : Kˣ) (hdefined : HeHuEvenSecondDefined (K := K) k mu)
    (hBIntegral : Lattice.IsIntegral s N)
    (hTargetLast : b.order ⟨2 * k + 1, by omega⟩ =
      1 - 2 * (ramificationIndex K : Int))
    (hSourceBoundary : a.order ⟨2 * k + 3, by omega⟩ =
      -(2 * (ramificationIndex K : Int)))
    (hSourceNext : 1 < a.order ⟨2 * k + 4, by omega⟩)
    (hTargetModel : DiagonalRepresents
      (diagonalUnitCoefficients b.valueUnit)
      (diagonalUnitCoefficients (heHuEvenSecond (K := K) k mu hdefined)))
    (hSourceModel : DiagonalRepresents
      (diagonalUnitCoefficients (heHuEvenFirst (K := K) (k + 1) mu))
      (a.prefixValues (2 * (k + 2)) (by omega))) : False := by
  have hterminal := a.heHuLemma45_terminalRepresentation b hmStable hAll
    hBIntegral hTargetLast hSourceBoundary hSourceNext
  have hterminalUnits : DiagonalRepresents
      (diagonalUnitCoefficients b.valueUnit)
      (a.prefixValues (2 * k + 4) (by omega)) := by
    convert hterminal using 1
    funext i
    rfl
  have hterminalNormalized : DiagonalRepresents
      (diagonalUnitCoefficients b.valueUnit)
      (a.prefixValues (2 * (k + 2)) (by omega)) :=
    targetPrefixRepresents_cast
      (diagonalUnitCoefficients b.valueUnit) a (by omega)
        hterminalUnits
  have hbad : DiagonalRepresents
      (diagonalUnitCoefficients (heHuEvenSecond (K := K) k mu hdefined))
      (diagonalUnitCoefficients (heHuEvenFirst (K := K) (k + 1) mu)) :=
    hTargetModel.symm_of_sameRank.trans hterminalNormalized |>.trans
      hSourceModel.symm_of_sameRank
  have hbadCast := diagonalRepresents_heHuFinFamilyCast_both
    (K := K) (rfl : 2 * k + 2 = 2 * k + 2)
      (by omega : 2 * (k + 1) + 2 = (2 * k + 2) + 2)
      (heHuEvenSecond (K := K) k mu hdefined)
      (heHuEvenFirst (K := K) (k + 1) mu) hbad
  have hforbidden : DiagonalRepresents
      (diagonalUnitCoefficients (heHuEvenSecond (K := K) k mu hdefined))
      (diagonalUnitCoefficients
        (heHuFinFamilyCast (by omega :
            2 * (k + 1) + 2 = (2 * k + 2) + 2)
          (heHuEvenFirst (K := K) (k + 1) mu))) := by
    simpa only [heHuFinFamilyCast_self] using hbadCast
  exact (heHu2022Proposition35iiiEvenSecond (K := K) k mu hdefined)
    |>.exactness.misses hforbidden

/-- The second conclusion in the large-gap clause of Lemma 4.5.  Under
the published dimension/defect premise, the next order is exactly one.
The two endpoint classes use the literal square and discriminant rows of
Table 2, including the exceptional binary argument which forces
`mu=Delta`. -/
theorem heHu2022Lemma45_nextOrder_one
    (sourceLaws : Beli2006AlphaLaws.{u, v} K)
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicDiagonalCodimensionTwoLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    {m k : Nat} (a : GoodBONG q L ((m + 1) + 2))
    (hmStable : 2 * k + 2 ≤ m)
    (hAIntegral : Lattice.IsIntegral q L)
    (hI1 : a.HeHuI1E (2 * k + 2) (by omega))
    (hI2 : a.HeHuI2E (2 * k + 2) (by omega))
    (hAll : HeHuAllLongRepresentationConditions.{u, v, u}
      (n := 2 * k + 1) a)
    (hlargeGap : 2 * (ramificationIndex K : Int) <
      a.order ⟨2 * k + 4, by omega⟩ -
        a.order ⟨2 * k + 3, by omega⟩)
    (hPremise : 4 ≤ 2 * k + 2 ∨
      (2 * k + 2 = 2 ∧
        a.heHuPrefixDefect 4 =
          (((2 * (ramificationIndex K : Int) : Int) : ℚ) :
            WithTop ℚ))) :
    a.order ⟨2 * k + 4, by omega⟩ = 1 := by
  have hSourceBoundary := a.heHu2022Lemma45_boundaryOrder hmStable
    hAIntegral hI1 hI2 hAll hlargeGap
  have hSourceNextLower :
      1 ≤ a.order ⟨2 * k + 4, by omega⟩ := by
    omega
  by_contra hnextNe
  have hSourceNext : 1 < a.order ⟨2 * k + 4, by omega⟩ := by
    omega
  have hSourceFirst : a.order 0 = 0 := by
    have h := hI1.oddOrder (0 : Fin (2 * k + 3))
      (⟨0, rfl⟩ : Odd (0 + 1))
    convert h using 1
    congr 1
  rcases a.heHuLemma45_sourcePrefix_evenFirst sourceLaws hmStable
      hSourceFirst hSourceBoundary with ⟨mu, hmu, hSourceModel⟩
  rcases hmu with hmuOne | hmuDelta
  · subst mu
    have hkPos : 0 < k := by
      by_contra hkNot
      have hkZero : k = 0 := Nat.eq_zero_of_not_pos hkNot
      subst k
      have hdefect : a.heHuPrefixDefect 4 =
          (((2 * (ramificationIndex K : Int) : Int) : ℚ) :
            WithTop ℚ) := by
        rcases hPremise with hfour | hbinary
        · omega
        · exact hbinary.2
      let source : Fin 4 → Kˣ := a.prefixValueUnits 4 (by omega)
      have hSourceUnits : DiagonalRepresents
          (diagonalUnitCoefficients (heHuEvenFirst (K := K) 1 1))
          (diagonalUnitCoefficients source) := by
        simpa only [source, diagonalUnitCoefficients_prefixValueUnits]
          using hSourceModel
      have hdet := DiagonalIsometryInvariantLaws.determinant_square
        (heHuEvenFirst (K := K) 1 1) source hSourceUnits
      have hsourceDet : diagonalUnitDeterminant source =
          a.prefixProduct 4 := by
        simpa only [source] using
          a.diagonalUnitDeterminant_prefixValueUnits 4 (by omega)
      rw [hsourceDet, diagonalUnitDeterminant_heHuEvenFirst] at hdet
      have hprefixSquare : IsSquare (a.prefixProduct 4) := by
        simpa using hdet
      have htop := defectOrder_eq_top_of_isSquare
        (K := K) hprefixSquare
      unfold heHuPrefixDefect at hdefect
      rw [hdefect] at htop
      exact WithTop.coe_ne_top htop
    obtain ⟨p, hp⟩ := Nat.exists_eq_succ_of_ne_zero
      (Nat.ne_of_gt hkPos)
    subst k
    let b := heHuLemma45EvenSecondOneTarget (K := K) p
    have hBIntegral : UnderlyingLatticeIsIntegral b := by
      simpa only [b] using
        heHuLemma45EvenSecondOneTarget_isIntegral (K := K) p
    have hTargetLast : b.order ⟨2 * (p + 1) + 1, by omega⟩ =
        1 - 2 * (ramificationIndex K : Int) := by
      simpa only [b] using
        heHuLemma45EvenSecondOneTarget_lastOrder (K := K) p
    have hTargetModel : DiagonalRepresents
        (diagonalUnitCoefficients b.valueUnit)
        (diagonalUnitCoefficients
          (heHuEvenSecond (K := K) (p + 1) 1
            (Or.inl (by omega : 0 < p + 1)))) := by
      simpa only [b] using
        heHuLemma45EvenSecondOneTarget_represents_evenSecond
          (K := K) p
    exact a.heHuLemma45_evenSecondContradiction b (by omega) hAll 1
      (Or.inl (by omega)) hBIntegral hTargetLast hSourceBoundary
        hSourceNext hTargetModel hSourceModel
  · subst mu
    let delta :=
      (Dyadic.dyadicDiscriminantClassLawsProved
        (K := K)).discriminantUnit
    let b := heHuLemma43Target (K := K) k
    have hdefined : HeHuEvenSecondDefined (K := K) k delta := by
      exact heHuLemma43_evenSecondDefined (K := K) k
    have hBIntegral : UnderlyingLatticeIsIntegral b := by
      exact heHuLemma43Target_isIntegral (K := K) k
    have hTargetLast : b.order ⟨2 * k + 1, by omega⟩ =
        1 - 2 * (ramificationIndex K : Int) := by
      exact (heHuLemma43Target_lastOrders (K := K) k).2
    have hTargetModel : DiagonalRepresents
        (diagonalUnitCoefficients b.valueUnit)
        (diagonalUnitCoefficients
          (heHuEvenSecond (K := K) k delta hdefined)) := by
      exact heHuLemma43Target_represents_evenSecond (K := K) k
    exact a.heHuLemma45_evenSecondContradiction b hmStable hAll delta
      hdefined hBIntegral hTargetLast hSourceBoundary hSourceNext
        hTargetModel hSourceModel

/-- Lemma 4.5, implication `(i) -> (iii)`: the universal condition-(iv)
assumption forces both conclusions in `I3^E`. -/
theorem heHu2022Lemma45Necessity
    (sourceLaws : Beli2006AlphaLaws.{u, v} K)
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicDiagonalCodimensionTwoLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    {m k : Nat} (a : GoodBONG q L ((m + 1) + 2))
    (hm : 2 * k + 2 ≤ m + 1)
    (hAIntegral : Lattice.IsIntegral q L)
    (hI1 : a.HeHuI1E (2 * k + 2) (by omega))
    (hI2 : a.HeHuI2E (2 * k + 2) (by omega))
    (hAll : HeHuAllLongRepresentationConditions.{u, v, u}
      (n := 2 * k + 1) a) :
    a.HeHuI3E (2 * k + 2) (by omega) := by
  intro hmStableRaw hlargeGap
  have hmStable : 2 * k + 2 ≤ m := by omega
  constructor
  · exact a.heHu2022Lemma45_boundaryOrder hmStable hAIntegral hI1 hI2
      hAll hlargeGap
  · intro hPremise
    exact a.heHu2022Lemma45_nextOrder_one sourceLaws hmStable hAIntegral
      hI1 hI2 hAll hlargeGap hPremise

/-- Cross-space form of the endpoint-tower one-pair extension theorem.
An endpoint tower with `pairs + 1` hyperbolic-type pairs represents every
endpoint tower with `pairs` pairs at the same scale.  The two good BONGs
may live in unrelated quadratic spaces. -/
theorem endpointTowers_onePairExtension_cross
    (sourceLaws : Beli2006AlphaLaws.{u, v} K)
    (targetLaws : Beli2006AlphaLaws.{u, w} K)
    [DyadicDiscriminantClassLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    {ma mb pairs : Nat} (a : GoodBONG q L (ma + 2))
    (b : GoodBONG r M (mb + 2)) (R : Int)
    (hpairs : 0 < pairs)
    (haBound : 2 * (pairs + 1) <= ma + 2)
    (hbBound : 2 * pairs <= mb + 2)
    (haFirst : a.order 0 = R)
    (haLast : a.order ⟨2 * (pairs + 1) - 1, by omega⟩ =
      R - 2 * (ramificationIndex K : Int))
    (hbFirst : b.order 0 = R)
    (hbLast : b.order ⟨2 * pairs - 1, by omega⟩ =
      R - 2 * (ramificationIndex K : Int)) :
    DiagonalRepresents
      (b.prefixValues (2 * pairs) hbBound)
      (a.prefixValues (2 * (pairs + 1)) haBound) := by
  let large : Fin (2 * (pairs + 1)) → Kˣ :=
    a.prefixValueUnits (2 * (pairs + 1)) haBound
  let small : Fin (2 * pairs) → Kˣ :=
    b.prefixValueUnits (2 * pairs) hbBound
  let extra : Kˣ := uniformizerPowerUnit K R
  have hlargeClasses : AlternatingEndpointPairClasses large := by
    letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
    simpa only [large] using
      a.lemma79_endpointTower_pairClasses R (pairs + 1)
        (Nat.succ_pos pairs) haBound haFirst haLast
  have hsmallClasses : AlternatingEndpointPairClasses small := by
    letI : Beli2006AlphaLaws.{u, w} K := targetLaws
    simpa only [small] using
      b.lemma79_endpointTower_pairClasses R pairs hpairs hbBound
        hbFirst hbLast
  have hextra : ordUnit K extra = R := by
    simpa only [extra] using ordUnit_uniformizerPowerUnit (K := K) R
  have hlargeOrders : ∀ t : Fin (pairs + 1),
      ordUnit K (large ⟨2 * t.val, by omega⟩) = ordUnit K extra := by
    intro t
    calc
      ordUnit K (large ⟨2 * t.val, by omega⟩) = R := by
        letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
        simpa only [large] using
          a.lemma79_endpointTower_leadingOrders R (pairs + 1)
            (Nat.succ_pos pairs) haBound haFirst haLast t
      _ = ordUnit K extra := hextra.symm
  have hsmallOrders : ∀ t : Fin pairs,
      ordUnit K (small ⟨2 * t.val, by omega⟩) = ordUnit K extra := by
    intro t
    calc
      ordUnit K (small ⟨2 * t.val, by omega⟩) = R := by
        letI : Beli2006AlphaLaws.{u, w} K := targetLaws
        simpa only [small] using
          b.lemma79_endpointTower_leadingOrders R pairs hpairs hbBound
            hbFirst hbLast t
      _ = ordUnit K extra := hextra.symm
  have hextended := alternatingEndpointTower_onePairExtensionRepresentation
    large small extra hlargeClasses hsmallClasses hlargeOrders hsmallOrders
  have hprefix : DiagonalRepresents
      (diagonalUnitCoefficients small)
      (diagonalUnitCoefficients (Fin.snoc small extra)) := by
    convert DiagonalRepresents.prefixOfLE
      (diagonalUnitCoefficients (Fin.snoc small extra))
      (show 2 * pairs <= 2 * pairs + 1 by omega) using 1
    funext i
    simp [diagonalUnitCoefficients, Fin.snoc, small]
  have hrep := hprefix.trans hextended
  have hsmallCoefficients : diagonalUnitCoefficients small =
      b.prefixValues (2 * pairs) hbBound := by
    simpa only [small, diagonalUnitCoefficients_prefixValueUnits]
  have hlargeCoefficients : diagonalUnitCoefficients large =
      a.prefixValues (2 * (pairs + 1)) haBound := by
    simpa only [large, diagonalUnitCoefficients_prefixValueUnits]
  rwa [hsmallCoefficients, hlargeCoefficients] at hrep

/-- Before the terminal paper index, the strict source jump demanded by
condition (iv) is incompatible with `I1^E` and `I2^E`.  At interior
indices this is the alternating `0,-2e` calculation; at the last initial
boundary, `I2^E` and Proposition 2.6 give the required upper bound. -/
theorem heHuLemma45_nonterminalTrigger_false
    {m k : Nat} (a : GoodBONG q L ((m + 1) + 2))
    (b : GoodBONG r M (2 * k + 2))
    (hm : 2 * k + 2 <= m + 1)
    (hI1 : a.HeHuI1E (2 * k + 2) (by omega))
    (hI2 : a.HeHuI2E (2 * k + 2) (by omega))
    (i : LongRepresentationIndex ((m + 1) + 2) (2 * k + 2))
    (hi : i.val <= 2 * k + 2)
    (htrigger :
      ((if hiTarget : i.val <= 2 * k + 2 then
          a.order ⟨i.val + 1, i.succ_lt_large⟩ <=
            b.order ⟨i.val - 1, by
              have := i.one_lt
              omega⟩
        else True) ∧
        b.order ⟨i.val - 2, by
            have := i.one_lt
            have := i.le_small_succ
            omega⟩ + 2 * (ramificationIndex K : Int) <
          a.order ⟨i.val + 1, i.succ_lt_large⟩ ∧
        a.order ⟨i.val, by
            have := i.succ_lt_large
            omega⟩ + 2 * (ramificationIndex K : Int) <=
          b.order ⟨i.val - 2, by
            have := i.one_lt
            have := i.le_small_succ
            omega⟩ + 2 * (ramificationIndex K : Int))) : False := by
  have hjump :
      a.order ⟨i.val, by
          have := i.succ_lt_large
          omega⟩ + 2 * (ramificationIndex K : Int) <
        a.order ⟨i.val + 1, i.succ_lt_large⟩ :=
    htrigger.2.2.trans_lt htrigger.2.1
  by_cases hboundary : i.val = 2 * k + 2
  · let boundary : Fin (m + 2) := ⟨2 * k + 2, by omega⟩
    have halpha : a.alphaValue boundary <= 1 := by
      simpa only [boundary] using hI2.alphaBoundary_le_one
    have heInt : (1 : Int) <= 2 * (ramificationIndex K : Int) := by
      have he := ramificationIndex_pos (K := K)
      omega
    have heRat : (1 : ℚ) <= 2 * (ramificationIndex K : ℚ) := by
      exact_mod_cast heInt
    have halphaTwo :
        a.alphaValue boundary <= 2 * (ramificationIndex K : ℚ) :=
      halpha.trans heRat
    have hgapLe :
        a.orderGap boundary <= 2 * (ramificationIndex K : Int) := by
      apply le_of_not_gt
      intro hgap
      have halphaGt :=
        ((a.heHu2022Proposition26 boundary).compareTwoE.2.2).2 hgap
      exact (not_lt_of_ge halphaTwo) halphaGt
    have hgapLe' :
        a.order ⟨2 * k + 3, by omega⟩ -
            a.order ⟨2 * k + 2, by omega⟩ <=
          2 * (ramificationIndex K : Int) := by
      unfold orderGap at hgapLe
      have hsucc : boundary.succ =
          (⟨2 * k + 3, by omega⟩ : Fin ((m + 1) + 2)) := by
        apply Fin.ext
        rfl
      have hcast : boundary.castSucc =
          (⟨2 * k + 2, by omega⟩ : Fin ((m + 1) + 2)) := by
        apply Fin.ext
        rfl
      rw [hsucc, hcast] at hgapLe
      exact hgapLe
    have hcurrentIndex :
        (⟨i.val, by
          have := i.succ_lt_large
          omega⟩ : Fin ((m + 1) + 2)) =
          ⟨2 * k + 2, by omega⟩ := by
      apply Fin.ext
      exact hboundary
    have hnextIndex :
        (⟨i.val + 1, i.succ_lt_large⟩ : Fin ((m + 1) + 2)) =
          ⟨2 * k + 3, by omega⟩ := by
      apply Fin.ext
      simp only [Fin.mk.injEq]
      omega
    rw [hcurrentIndex, hnextIndex] at hjump
    omega
  · have hinterior : i.val < 2 * k + 2 := by omega
    rcases Nat.even_or_odd i.val with hiEven | hiOdd
    · rcases hiEven with ⟨d, hd⟩
      have hcurrent :
          a.order ⟨i.val, by
              have := i.succ_lt_large
              omega⟩ = 0 := by
        apply hI1.oddOrder ⟨i.val, by omega⟩
        change Odd (i.val + 1)
        exact Even.add_one ⟨d, hd⟩
      have hnext :
          a.order ⟨i.val + 1, i.succ_lt_large⟩ =
            -(2 * (ramificationIndex K : Int)) := by
        apply hI1.evenOrder ⟨i.val + 1, by omega⟩
        change Even (i.val + 2)
        exact ⟨d + 1, by omega⟩
      have he := ramificationIndex_pos (K := K)
      rw [hcurrent, hnext] at hjump
      omega
    · rcases hiOdd with ⟨d, hd⟩
      have hcurrent :
          a.order ⟨i.val, by
              have := i.succ_lt_large
              omega⟩ =
            -(2 * (ramificationIndex K : Int)) := by
        apply hI1.evenOrder ⟨i.val, by omega⟩
        change Even (i.val + 1)
        exact ⟨d + 1, by omega⟩
      have hnext :
          a.order ⟨i.val + 1, i.succ_lt_large⟩ = 0 := by
        apply hI1.oddOrder ⟨i.val + 1, by omega⟩
        change Odd (i.val + 2)
        exact ⟨d + 1, by omega⟩
      rw [hcurrent, hnext] at hjump
      omega

/-- Proposition 2.7(iii) propagates a terminal order `-2e` backwards
through an integral even-rank target, so its first order is zero. -/
theorem heHuLemma45_targetFirstOrder_zero
    {k : Nat} (b : GoodBONG r M (2 * k + 2))
    (hBIntegral : Lattice.IsIntegral r M)
    (hlast : b.order ⟨2 * k + 1, by omega⟩ =
      -(2 * (ramificationIndex K : Int))) :
    b.order 0 = 0 := by
  let last : Fin (2 * k + 2) := ⟨2 * k + 1, by omega⟩
  have hlastOdd : Odd last.val := by
    exact ⟨k, by dsimp only [last]⟩
  let C := b.heHu2022Proposition27iiiiv hBIntegral last hlastOdd (by
    simpa only [last] using hlast)
  let firstGap : Fin (2 * k + 1) := ⟨0, by omega⟩
  let lastGap : Fin (2 * k + 1) := ⟨last.val - 1, by omega⟩
  have hfirst := C.alternatingDecomposition.arithmetic.even_order
    firstGap (Fin.zero_le firstGap) (Fin.zero_le lastGap) Even.zero
  have hindex : firstGap.castSucc = (0 : Fin (2 * k + 2)) := by
    apply Fin.ext
    rfl
  rw [hindex] at hfirst
  exact hfirst

/-- Two hyperbolic planes represent every binary diagonal space.  The
negative-square determinant class is the hyperbolic binary plane itself;
all other classes follow from the proved codimension-two local theorem. -/
theorem heHuLemma45_binary_represents_twoHyperbolicPlanes
    [DyadicDiagonalCodimensionTwoLaws K]
    (w : Fin 2 → Kˣ) :
    DiagonalRepresents
      (diagonalUnitCoefficients w)
      (diagonalUnitCoefficients
        (standardHyperbolicEndpointTower (K := K) 2)) := by
  by_cases hsigned : IsSquare (-diagonalUnitDeterminant w)
  · have hwRatio : IsSquare (-(w 0 / w 1)) := by
      apply isSquare_neg_div_of_neg_mul_square
      simpa [diagonalUnitDeterminant, Fin.prod_univ_two] using hsigned
    have hstandardRatio : IsSquare (-((1 : Kˣ) / (-1 : Kˣ))) := by
      simp
    have hbinaryRaw :=
      QuadraticSpace.finiteDiagonal_fin_two_diagonalRepresents_of_signedRatioSquares
        (w 0) (w 1) 1 (-1) hwRatio hstandardRatio
    have hbinary : DiagonalRepresents
        (diagonalUnitCoefficients w)
        (diagonalUnitCoefficients
          (standardHyperbolicEndpointTower (K := K) 1)) := by
      convert hbinaryRaw using 1 <;> funext i <;> fin_cases i <;> rfl
    have hprefixRaw := DiagonalRepresents.prefixOfLE
      (diagonalUnitCoefficients
        (standardHyperbolicEndpointTower (K := K) 2))
      (by omega : 2 <= 4)
    have hprefix : DiagonalRepresents
        (diagonalUnitCoefficients
          (standardHyperbolicEndpointTower (K := K) 1))
        (diagonalUnitCoefficients
          (standardHyperbolicEndpointTower (K := K) 2)) := by
      convert hprefixRaw using 1 <;> funext i <;> fin_cases i <;> rfl
    exact hbinary.trans hprefix
  · apply diagonalRepresents_of_not_negative_determinant_square
      w (standardHyperbolicEndpointTower (K := K) 2) rfl
    simpa [diagonalUnitDeterminant_standardHyperbolicEndpointTower]
      using hsigned

/-- A four-entry endpoint prefix with square determinant is the split
quaternary space `H ⊥ H`; consequently it represents every binary
diagonal space.  This packages the exceptional `n=2`, `d(a_1...a_4)=∞`
branch of the published proof. -/
theorem heHuLemma45_exceptionalBinaryRepresentation
    (sourceLaws : Beli2006AlphaLaws.{u, v} K)
    [DyadicDiscriminantClassLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    [DyadicDiagonalCodimensionTwoLaws K]
    {ma mb : Nat} (a : GoodBONG q L (ma + 2))
    (b : GoodBONG r M (mb + 2))
    (haBound : 4 <= ma + 2) (hbBound : 2 <= mb + 2)
    (haFirst : a.order 0 = 0)
    (haLast : a.order ⟨3, by omega⟩ =
      -(2 * (ramificationIndex K : Int)))
    (haDet : IsSquare (a.prefixProduct 4)) :
    DiagonalRepresents
      (b.prefixValues 2 hbBound)
      (a.prefixValues 4 haBound) := by
  let source : Fin 4 → Kˣ := a.prefixValueUnits 4 haBound
  let split : Fin 4 → Kˣ :=
    standardHyperbolicEndpointTower (K := K) 2
  let target : Fin 2 → Kˣ := b.prefixValueUnits 2 hbBound
  have haLast' : a.order ⟨2 * 2 - 1, by omega⟩ =
      0 - 2 * (ramificationIndex K : Int) := by
    convert haLast using 1 <;> norm_num
  have hsourceClasses :
      AlternatingEndpointPairClasses (pairs := 2) source := by
    letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
    simpa only [source] using
      a.lemma79_endpointTower_pairClasses 0 2 (by omega) haBound
        haFirst haLast'
  have hsourceOrders :
      AlternatingEndpointLeadingOrdersAt (pairs := 2) source (1 : Kˣ) := by
    letI : Beli2006AlphaLaws.{u, v} K := sourceLaws
    have hone : ordUnit K (1 : Kˣ) = 0 := by
      have h := ordUnit_mul K (1 : Kˣ) 1
      simp only [mul_one] at h
      omega
    intro t
    have h := a.lemma79_endpointTower_leadingOrders 0 2 (by omega)
      haBound haFirst haLast' t
    rw [hone]
    simpa [source] using h
  have hsplitClasses :
      AlternatingEndpointPairClasses (pairs := 2) split := by
    simpa only [split] using
      standardHyperbolicEndpointTower_pairClasses (K := K) 2
  have hsplitOrders :
      AlternatingEndpointLeadingOrdersAt (pairs := 2) split (1 : Kˣ) := by
    simpa only [split] using
      standardHyperbolicEndpointTower_leadingOrders (K := K) 2
  have hdet : IsSquare
      (diagonalUnitDeterminant source * diagonalUnitDeterminant split) := by
    rw [show diagonalUnitDeterminant source = a.prefixProduct 4 by
      simpa only [source] using
        a.diagonalUnitDeterminant_prefixValueUnits 4 haBound]
    rw [show diagonalUnitDeterminant split = 1 by
      simpa [split] using
        diagonalUnitDeterminant_standardHyperbolicEndpointTower
          (K := K) 2]
    simpa only [mul_one] using haDet
  have hsplitSource :=
    alternatingEndpointTower_equalDeterminantRepresentation (pairs := 2)
      source split (1 : Kˣ) hsourceClasses hsplitClasses hsourceOrders
        hsplitOrders hdet
  have htargetSplit : DiagonalRepresents
      (diagonalUnitCoefficients target)
      (diagonalUnitCoefficients split) := by
    simpa only [target, split] using
      heHuLemma45_binary_represents_twoHyperbolicPlanes (K := K) target
  have hrep := htargetSplit.trans hsplitSource
  have htargetCoefficients : diagonalUnitCoefficients target =
      b.prefixValues 2 hbBound := by
    simpa only [target, diagonalUnitCoefficients_prefixValueUnits]
  have hsourceCoefficients : diagonalUnitCoefficients source =
      a.prefixValues 4 haBound := by
    simpa only [source, diagonalUnitCoefficients_prefixValueUnits]
  rwa [htargetCoefficients, hsourceCoefficients] at hrep

/-- The nonexceptional half of Lemma 4.5, implication `(iii) -> (i)`.
Once the premise in the second clause of `I3^E` holds, its two conclusions
force the source prefix and target prefix to be endpoint towers differing
by one pair. -/
theorem heHu2022Lemma45Sufficiency_of_terminalPremise
    (sourceLaws : Beli2006AlphaLaws.{u, v} K)
    (targetLaws : Beli2006AlphaLaws.{u, w} K)
    [DyadicDiscriminantClassLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    {m k : Nat} (a : GoodBONG q L ((m + 1) + 2))
    (b : GoodBONG r M (2 * k + 2))
    (hm : 2 * k + 2 <= m + 1)
    (hBIntegral : Lattice.IsIntegral r M)
    (hI1 : a.HeHuI1E (2 * k + 2) (by omega))
    (hI2 : a.HeHuI2E (2 * k + 2) (by omega))
    (hI3 : a.HeHuI3E (2 * k + 2) (by omega))
    (hTerminalPremise :
      4 <= 2 * k + 2 ∨
        (2 * k + 2 = 2 ∧
          a.heHuPrefixDefect 4 =
            (((2 * (ramificationIndex K : Int) : Int) : ℚ) :
              WithTop ℚ))) :
    a.LongRepresentationConditions b := by
  unfold LongRepresentationConditions
  intro i htrigger
  by_cases hiNonterminal : i.val <= 2 * k + 2
  · exact False.elim (a.heHuLemma45_nonterminalTrigger_false
      b hm hI1 hI2 i hiNonterminal htrigger)
  · have hiTerminal : i.val = 2 * k + 3 := by
      have := i.le_small_succ
      omega
    have hmStable : 2 * k + 2 <= m := by
      have := i.succ_lt_large
      omega
    have hcurrentIndex :
        (⟨i.val, by
          have := i.succ_lt_large
          omega⟩ : Fin ((m + 1) + 2)) =
          ⟨2 * k + 3, by omega⟩ := by
      apply Fin.ext
      exact hiTerminal
    have hnextIndex :
        (⟨i.val + 1, i.succ_lt_large⟩ : Fin ((m + 1) + 2)) =
          ⟨2 * k + 4, by omega⟩ := by
      apply Fin.ext
      change i.val + 1 = 2 * k + 4
      omega
    have htargetLastIndex :
        (⟨i.val - 2, by
          have := i.one_lt
          have := i.le_small_succ
          omega⟩ : Fin (2 * k + 2)) =
          ⟨2 * k + 1, by omega⟩ := by
      apply Fin.ext
      change i.val - 2 = 2 * k + 1
      omega
    have hlargeGap : 2 * (ramificationIndex K : Int) <
        a.order ⟨2 * k + 4, by omega⟩ -
          a.order ⟨2 * k + 3, by omega⟩ := by
      have hjump := htrigger.2.2.trans_lt htrigger.2.1
      rw [hcurrentIndex, hnextIndex] at hjump
      omega
    have hI3Consequences := hI3 (by omega) hlargeGap
    have hsourceLast : a.order ⟨2 * k + 3, by omega⟩ =
        -(2 * (ramificationIndex K : Int)) := hI3Consequences.1
    have hsourceNext : a.order ⟨2 * k + 4, by omega⟩ = 1 :=
      hI3Consequences.2 hTerminalPremise
    have htargetLast : b.order ⟨2 * k + 1, by omega⟩ =
        -(2 * (ramificationIndex K : Int)) := by
      have hlower := htrigger.2.2
      have hupper := htrigger.2.1
      rw [hcurrentIndex, htargetLastIndex, hsourceLast] at hlower
      rw [htargetLastIndex, hnextIndex, hsourceNext] at hupper
      omega
    have hsourceFirst : a.order 0 = 0 := by
      have h := hI1.oddOrder (⟨0, by omega⟩ : Fin (2 * k + 3))
        (⟨0, rfl⟩ : Odd (0 + 1))
      convert h using 1
      congr 1
    have htargetFirst : b.order 0 = 0 :=
      b.heHuLemma45_targetFirstOrder_zero hBIntegral htargetLast
    have hrep := endpointTowers_onePairExtension_cross (pairs := k + 1)
      sourceLaws targetLaws a b 0 (by omega) (by omega) (by omega)
        hsourceFirst (by
          convert hsourceLast using 1 <;> congr 1 <;> omega)
        htargetFirst (by
          convert htargetLast using 1 <;> congr 1 <;> omega)
    exact prefixRepresents_cast b a (by omega) (by omega) hrep

/-- Lemma 4.5, full implication `(iii) -> (i)`.  If the second premise of
`I3^E` is unavailable, arithmetic forces the binary case; Proposition
2.7 and the defect endpoint theorem then identify the four-dimensional
source prefix with two hyperbolic planes. -/
theorem heHu2022Lemma45Sufficiency
    (sourceLaws : Beli2006AlphaLaws.{u, v} K)
    (targetLaws : Beli2006AlphaLaws.{u, w} K)
    [QuadraticDefectLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    [DyadicDiagonalCodimensionTwoLaws K]
    {m k : Nat} (a : GoodBONG q L ((m + 1) + 2))
    (b : GoodBONG r M (2 * k + 2))
    (hm : 2 * k + 2 <= m + 1)
    (hAIntegral : Lattice.IsIntegral q L)
    (hBIntegral : Lattice.IsIntegral r M)
    (hI1 : a.HeHuI1E (2 * k + 2) (by omega))
    (hI2 : a.HeHuI2E (2 * k + 2) (by omega))
    (hI3 : a.HeHuI3E (2 * k + 2) (by omega)) :
    a.LongRepresentationConditions b := by
  by_cases hTerminalPremise :
      4 <= 2 * k + 2 ∨
        (2 * k + 2 = 2 ∧
          a.heHuPrefixDefect 4 =
            (((2 * (ramificationIndex K : Int) : Int) : ℚ) :
              WithTop ℚ))
  · exact a.heHu2022Lemma45Sufficiency_of_terminalPremise
      sourceLaws targetLaws b hm hBIntegral hI1 hI2 hI3 hTerminalPremise
  · unfold LongRepresentationConditions
    intro i htrigger
    by_cases hiNonterminal : i.val <= 2 * k + 2
    · exact False.elim (a.heHuLemma45_nonterminalTrigger_false
        b hm hI1 hI2 i hiNonterminal htrigger)
    · have hiTerminal : i.val = 2 * k + 3 := by
        have := i.le_small_succ
        omega
      have hmStable : 2 * k + 2 <= m := by
        have := i.succ_lt_large
        omega
      have hcurrentIndex :
          (⟨i.val, by
            have := i.succ_lt_large
            omega⟩ : Fin ((m + 1) + 2)) =
            ⟨2 * k + 3, by omega⟩ := by
        apply Fin.ext
        exact hiTerminal
      have hnextIndex :
          (⟨i.val + 1, i.succ_lt_large⟩ : Fin ((m + 1) + 2)) =
            ⟨2 * k + 4, by omega⟩ := by
        apply Fin.ext
        change i.val + 1 = 2 * k + 4
        omega
      have hlargeGap : 2 * (ramificationIndex K : Int) <
          a.order ⟨2 * k + 4, by omega⟩ -
            a.order ⟨2 * k + 3, by omega⟩ := by
        have hjump := htrigger.2.2.trans_lt htrigger.2.1
        rw [hcurrentIndex, hnextIndex] at hjump
        omega
      have hsourceLast : a.order ⟨2 * k + 3, by omega⟩ =
          -(2 * (ramificationIndex K : Int)) :=
        (hI3 (by omega) hlargeGap).1
      have hkZero : k = 0 := by
        by_contra hk
        apply hTerminalPremise
        left
        omega
      subst k
      have hdefectNe : a.heHuPrefixDefect 4 ≠
          (((2 * (ramificationIndex K : Int) : Int) : ℚ) :
            WithTop ℚ) := by
        intro hdefect
        apply hTerminalPremise
        right
        exact ⟨by omega, hdefect⟩
      let j : Fin ((m + 1) + 2) := ⟨3, by omega⟩
      have hjOdd : Odd j.val := by
        exact ⟨1, by norm_num [j]⟩
      have hjOrder : a.order j =
          -(2 * (ramificationIndex K : Int)) := by
        simpa only [j] using hsourceLast
      let C := a.heHu2022Proposition27iiiiv hAIntegral j hjOdd hjOrder
      have htruncated :
          (((2 * ramificationIndex K : ℚ) : WithTop ℚ)) <=
            a.truncatedPrefixDefect a (1 : Kˣ) 0 4 := by
        simpa [j] using C.alternatingPrefixDefect
      have hraw := htruncated.trans
        (a.truncatedPrefixDefect_le_defect a (1 : Kˣ) 0 4)
      have hprefixLower :
          (((2 * ramificationIndex K : ℚ) : WithTop ℚ)) <=
            a.heHuPrefixDefect 4 := by
        simpa [heHuPrefixDefect, GoodBONG.prefixProduct] using hraw
      have hprefixStrict :
          (((2 * ramificationIndex K : ℚ) : WithTop ℚ)) <
            a.heHuPrefixDefect 4 := by
        have hne : a.heHuPrefixDefect 4 ≠
            (((2 * ramificationIndex K : ℚ) : WithTop ℚ)) := by
          exact_mod_cast hdefectNe
        exact lt_of_le_of_ne hprefixLower hne.symm
      have hprefixSquare : IsSquare (a.prefixProduct 4) := by
        apply isSquare_of_two_mul_e_lt_defectOrder
        have hstrictNat :
            ((((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ)) <
              a.heHuPrefixDefect 4 := by
          convert hprefixStrict using 1 <;> norm_num
        simpa only [heHuPrefixDefect] using hstrictNat
      have hsourceFirst : a.order 0 = 0 := by
        have h := hI1.oddOrder (⟨0, by omega⟩ : Fin 3)
          (⟨0, rfl⟩ : Odd (0 + 1))
        convert h using 1
        congr 1
      have hrep := a.heHuLemma45_exceptionalBinaryRepresentation
        sourceLaws b (by omega) (by omega) hsourceFirst (by
          convert hsourceLast using 1 <;> congr 1 <;> omega)
        hprefixSquare
      exact prefixRepresents_cast b a (by omega) (by omega) hrep

/-- Universal-target form of the sufficiency half of Lemma 4.5. -/
theorem heHu2022Lemma45SufficiencyAll
    (sourceLaws : Beli2006AlphaLaws.{u, v} K)
    [QuadraticDefectLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    [DyadicDiagonalCodimensionTwoLaws K]
    {m k : Nat} (a : GoodBONG q L ((m + 1) + 2))
    (hm : 2 * k + 2 ≤ m + 1)
    (hAIntegral : Lattice.IsIntegral q L)
    (hI1 : a.HeHuI1E (2 * k + 2) (by omega))
    (hI2 : a.HeHuI2E (2 * k + 2) (by omega))
    (hI3 : a.HeHuI3E (2 * k + 2) (by omega)) :
    HeHuAllLongRepresentationConditions.{u, v, u}
      (n := 2 * k + 1) a := by
  intro X _ _ s N b hBIntegral
  let targetLaws : Beli2006AlphaLaws.{u, u} K :=
    beliUniversalAlphaLaws
  exact a.heHu2022Lemma45Sufficiency sourceLaws targetLaws b hm
    hAIntegral hBIntegral hI1 hI2 hI3

/-- He--Hu, Lemma 4.5, complete equivalence between Theorem 2.8(iv)
for every integral even-rank target and `I3^E`. -/
theorem heHu2022Lemma45
    (sourceLaws : Beli2006AlphaLaws.{u, v} K)
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    [DyadicDiagonalCodimensionTwoLaws K]
    {m k : Nat} (a : GoodBONG q L ((m + 1) + 2))
    (hm : 2 * k + 2 ≤ m + 1)
    (hAIntegral : Lattice.IsIntegral q L)
    (hI1 : a.HeHuI1E (2 * k + 2) (by omega))
    (hI2 : a.HeHuI2E (2 * k + 2) (by omega)) :
    Lattice.AmbientlyNUniversal.{u, v, u} q (2 * k + 2) →
      (HeHuAllLongRepresentationConditions.{u, v, u}
          (n := 2 * k + 1) a ↔
        a.HeHuI3E (2 * k + 2) (by omega)) := by
  intro _hAmbient
  constructor
  · exact a.heHu2022Lemma45Necessity sourceLaws hm hAIntegral hI1 hI2
  · exact a.heHu2022Lemma45SufficiencyAll sourceLaws hm hAIntegral hI1 hI2

end BONG.GoodBONG

end Bong
