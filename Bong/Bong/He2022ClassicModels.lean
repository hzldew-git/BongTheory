/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2022ClassicProposition24
import Bong.Bong.HeHu2022ExactModels
import Bong.Bong.HeHu2022SectionThreeSpaces
import Bong.Bong.HeHu2022Proposition35iii

/-!
# He (2024), Section 2: the displayed classic test lattices

This file records the literal good-BONG coefficient rows in Definition 2.6
of Zilong He, *On classic n-universal quadratic forms over dyadic local
fields*, manuscripta math. 174 (2024), 559--595.  The parameter called
`pairs` is the number of displayed `H_t` blocks before the terminal row.

The paper defines `c#` only up to choices made after selecting a square-class
representative.  We therefore keep the selected sharp unit as an explicit
argument in the two `C₂` coefficient constructors.  Later theorems instantiate
it with the paper's discriminant unit or the proved He--Hu sharp choice.
-/

namespace Bong

open Dyadic BONG.GoodBONG AlternatingEndpointTower

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The literal good-BONG row for `H_t^s`:
`pi^t,-pi^(-t),...,pi^t,-pi^(-t)`. -/
noncomputable def heClassicScaledHyperbolicTower
    (t pairs : Nat) : Fin (2 * pairs) → Kˣ := fun i =>
  if Even i.val then
    uniformizerPowerUnit K (t : Int)
  else
    -(uniformizerPowerUnit K (-(t : Int)))

@[simp]
theorem heClassicScaledHyperbolicTower_even
    {t pairs : Nat} (j : Fin pairs) :
    heClassicScaledHyperbolicTower (K := K) t pairs
        ⟨2 * j.val, by omega⟩ =
      uniformizerPowerUnit K (t : Int) := by
  simp [heClassicScaledHyperbolicTower]

@[simp]
theorem heClassicScaledHyperbolicTower_odd
    {t pairs : Nat} (j : Fin pairs) :
    heClassicScaledHyperbolicTower (K := K) t pairs
        ⟨2 * j.val + 1, by omega⟩ =
      -(uniformizerPowerUnit K (-(t : Int))) := by
  have hodd : ¬ Even (2 * j.val + 1) :=
    Nat.not_even_two_mul_add_one j.val
  simp [heClassicScaledHyperbolicTower, hodd]

/-- The orders of the two entries in every `H_t` block are `t,-t`. -/
theorem heClassicScaledHyperbolicTower_orders
    {t pairs : Nat} (j : Fin pairs) :
    ordUnit K (heClassicScaledHyperbolicTower (K := K) t pairs
        ⟨2 * j.val, by omega⟩) = (t : Int) ∧
      ordUnit K (heClassicScaledHyperbolicTower (K := K) t pairs
        ⟨2 * j.val + 1, by omega⟩) = -(t : Int) := by
  rw [heClassicScaledHyperbolicTower_even,
    heClassicScaledHyperbolicTower_odd,
    ordUnit_uniformizerPowerUnit, ordUnit_neg,
    ordUnit_uniformizerPowerUnit]
  exact ⟨rfl, rfl⟩

/-- Definition 2.6, the even-rank row `H_e^n(c)`.  Its rank is
`2*pairs+2`. -/
noncomputable def heClassicEvenH (pairs : Nat) (c : Kˣ) :
    Fin (2 * pairs + 2) → Kˣ :=
  Fin.append
    (heClassicScaledHyperbolicTower (K := K)
      (ramificationIndex K) pairs)
    ![uniformizerPowerUnit K (ramificationIndex K : Int),
      -(c * uniformizerPowerUnit K
        (-(ramificationIndex K : Int)))]

/-- Definition 2.6, the even-rank first classic row
`C₁^n(c)=H_0^((n-2)/2) perp <1,-c>`. -/
noncomputable def heClassicEvenC1 (pairs : Nat) (c : Kˣ) :
    Fin (2 * pairs + 2) → Kˣ :=
  Fin.append (heClassicScaledHyperbolicTower (K := K) 0 pairs)
    ![1, -c]

/-- Definition 2.6, the even-rank second classic row
`C₂^n(c)=H_0^((n-2)/2) perp <c#,-c#c>`. -/
noncomputable def heClassicEvenC2 (pairs : Nat) (c cSharp : Kˣ) :
    Fin (2 * pairs + 2) → Kˣ :=
  Fin.append (heClassicScaledHyperbolicTower (K := K) 0 pairs)
    ![cSharp, -(cSharp * c)]

/-- Definition 2.6, the odd-rank first classic row.  The paper rank is
`2*pairs+3`. -/
noncomputable def heClassicOddC1 (pairs : Nat) (c : Kˣ) :
    Fin (2 * pairs + 3) → Kˣ :=
  Fin.snoc (heClassicScaledHyperbolicTower (K := K) 0 (pairs + 1)) c

/-- Definition 2.6, the odd-order branch of the odd-rank second row:
`H_0^pairs perp <1,-Delta,Delta*c>`. -/
noncomputable def heClassicOddC2Odd (pairs : Nat) (c : Kˣ) :
    Fin (2 * pairs + 3) → Kˣ :=
  let delta :=
    (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
  Fin.append (heClassicScaledHyperbolicTower (K := K) 0 pairs)
    ![1, -delta, c * delta]

/-- Definition 2.6, the even-order branch of the odd-rank second row:
`H_0^pairs perp <c*omega#, -c*omega#*omega, c*omega>`.
The two distinguished units are kept explicit so the coefficient statement
does not hide the source's choice of `omega#`. -/
noncomputable def heClassicOddC2Even (pairs : Nat)
    (c omega omegaSharp : Kˣ) : Fin (2 * pairs + 3) → Kˣ :=
  Fin.append (heClassicScaledHyperbolicTower (K := K) 0 pairs)
    ![c * omegaSharp, -(c * omegaSharp * omega), c * omega]

/-- The `H_0` coefficient tower is literally the standard diagonal
hyperbolic tower `[1,-1]^pairs`. -/
theorem heClassicScaledHyperbolicTower_zero
    (pairs : Nat) :
    heClassicScaledHyperbolicTower (K := K) 0 pairs =
      standardHyperbolicEndpointTower (K := K) pairs := by
  funext i
  simp only [heClassicScaledHyperbolicTower,
    standardHyperbolicEndpointTower, Int.ofNat_zero, neg_zero]
  split <;> simp_all [uniformizerPowerUnit]

/-- The first classic rows agree exactly with the already classified
He--Hu first-column coefficient spaces. -/
theorem heClassicEvenC1_eq_heHuEvenFirst
    (pairs : Nat) (c : Kˣ) :
    heClassicEvenC1 (K := K) pairs c = heHuEvenFirst pairs c := by
  rw [heClassicEvenC1, heClassicScaledHyperbolicTower_zero,
    heHuEvenFirst_eq_towerModel]
  rfl

theorem heClassicOddC1_eq_heHuOddFirst
    (pairs : Nat) (c : Kˣ) :
    heClassicOddC1 (K := K) pairs c = heHuOddFirst pairs c := by
  funext i
  simp only [heClassicOddC1, heClassicScaledHyperbolicTower,
    heHuOddFirst, heHuOddFirstTail, Fin.snoc]
  by_cases hhead : i.val < 2 * pairs
  · let j : Fin (2 * pairs) := ⟨i.val, hhead⟩
    have hi : i = Fin.castAdd 3 j := Fin.ext rfl
    rw [hi, Fin.append_left]
    have hsnoc' : i.val < 2 * pairs + 2 := by omega
    simp [j, standardHyperbolicEndpointTower,
      uniformizerPowerUnit, hsnoc']
  · have hlast : i.val = 2 * pairs ∨
        i.val = 2 * pairs + 1 ∨ i.val = 2 * pairs + 2 := by
      omega
    rcases hlast with hzero | hone | htwo
    · have hi : i = Fin.natAdd (2 * pairs) (0 : Fin 3) := by
        apply Fin.ext
        simpa using hzero
      rw [hi, Fin.append_right]
      simp [uniformizerPowerUnit]
    · have hi : i = Fin.natAdd (2 * pairs) (1 : Fin 3) := by
        apply Fin.ext
        simpa using hone
      rw [hi, Fin.append_right]
      have hodd : ¬ Even (2 * pairs + 1) :=
        Nat.not_even_two_mul_add_one pairs
      simp [hodd, uniformizerPowerUnit]
    · have hi : i = Fin.natAdd (2 * pairs) (2 : Fin 3) := by
        apply Fin.ext
        simpa using htwo
      rw [hi, Fin.append_right]
      simp

/-- Paper-labelled endpoint for Proposition 2.10. -/
theorem he2022ClassicProposition210 (a : Fin 3 → Kˣ) :
    DiagonalIsotropic (diagonalUnitCoefficients a) ↔
      hilbertSymbol K (-(a 0 * a 1)) (-(a 0 * a 2)) = 1 := by
  let x : Kˣ := -(a 0 * a 1)
  let z : Kˣ := -(a 0 * a 2)
  have harg : -(a 1 * a 2) =
      z * ((-x) * (a 0)⁻¹ ^ 2) := by
    apply Units.ext
    simp [x, z]
    field_simp
  have hsymbol :
      hilbertSymbol K x (-(a 1 * a 2)) =
        hilbertSymbol K x z := by
    rw [harg, hilbertSymbol_mul_right,
      hilbertSymbol_neg_self_mul_square_eq_one]
    simp
  rw [diagonalUnitTernary_isotropic_iff_adjacentHilbertOne]
  change hilbertSymbol K x (-(a 1 * a 2)) = 1 ↔
    hilbertSymbol K x z = 1
  rw [hsymbol]

/-- The anisotropic half of Proposition 2.10, with the source's two Hilbert
symbol values made explicit. -/
theorem he2022ClassicProposition210_anisotropic (a : Fin 3 → Kˣ) :
    DiagonalAnisotropic (diagonalUnitCoefficients a) ↔
      hilbertSymbol K (-(a 0 * a 1)) (-(a 0 * a 2)) = -1 := by
  rw [← not_diagonalIsotropic_iff_diagonalAnisotropic,
    he2022ClassicProposition210]
  constructor
  · intro hne
    exact (Int.units_eq_one_or
      (hilbertSymbol K (-(a 0 * a 1)) (-(a 0 * a 2)))).resolve_left hne
  · intro hneg hone
    rw [hone] at hneg
    norm_num at hneg

end Bong
