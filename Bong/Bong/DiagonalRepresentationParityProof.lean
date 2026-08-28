/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.DiagonalRepresentationParity
import Bong.Bong.DiagonalDeterminantExtension
import Bong.Bong.DiagonalLocalClassificationProof

/-!
# Concrete parity laws for codimension-one diagonal representations

The three parity cycles in Beli's Lemma 1.5 follow from local diagonal
classification.  A codimension-one representation is first converted into
one Hasse-sign equation; Hilbert-symbol bilinearity then shows that the four
signs in each cycle have product one.
-/

namespace Bong

open Dyadic BONG.GoodBONG

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

private theorem intUnit_eq_iff_mul_eq_one (x y : ℤˣ) :
    x = y ↔ x * y = 1 := by
  constructor
  · rintro rfl
    exact Int.units_mul_self x
  · intro h
    calc
      x = x * 1 := by simp
      _ = x * (x * y) := by rw [h]
      _ = (x * x) * y := by rw [mul_assoc]
      _ = y := by rw [Int.units_mul_self, one_mul]

/-- The Hasse invariant of the determinant completion of a codimension-one
diagonal form. -/
theorem diagonalHasseSymbol_determinantCompletion
    {n : Nat} (source : Fin n → Kˣ) (target : Fin (n + 1) → Kˣ) :
    diagonalHasseSymbol K
        (Fin.snoc source
          (diagonalUnitDeterminant target * diagonalUnitDeterminant source)) =
      diagonalHasseSymbol K source *
        hilbertSymbol K (diagonalUnitDeterminant source)
          (diagonalUnitDeterminant target) *
        hilbertSymbol K (diagonalUnitDeterminant target) (-1) := by
  rw [diagonalHasseSymbol_snoc, hilbertSymbol_mul_right,
    hilbertSymbol_self_eq_neg_one, hilbertSymbol_self_eq_neg_one,
    hilbertSymbol_mul_left]
  have hself := Int.units_mul_self
    (hilbertSymbol K (diagonalUnitDeterminant source) (-1))
  calc
    diagonalHasseSymbol K source *
          (hilbertSymbol K (diagonalUnitDeterminant source)
              (diagonalUnitDeterminant target) *
            hilbertSymbol K (diagonalUnitDeterminant source)
              (-1)) *
        (hilbertSymbol K (diagonalUnitDeterminant target) (-1) *
          hilbertSymbol K (diagonalUnitDeterminant source) (-1)) =
        diagonalHasseSymbol K source *
          hilbertSymbol K (diagonalUnitDeterminant source)
            (diagonalUnitDeterminant target) *
          hilbertSymbol K (diagonalUnitDeterminant target) (-1) *
          (hilbertSymbol K (diagonalUnitDeterminant source) (-1) *
            hilbertSymbol K (diagonalUnitDeterminant source) (-1)) := by
      ac_rfl
    _ = diagonalHasseSymbol K source *
          hilbertSymbol K (diagonalUnitDeterminant source)
            (diagonalUnitDeterminant target) *
          hilbertSymbol K (diagonalUnitDeterminant target) (-1) := by
      rw [hself, mul_one]

/-- The Hasse-sign criterion for a codimension-one diagonal
representation. -/
theorem diagonalCodimensionOneRepresents_iff_sign_eq_one
    {n : Nat} (source : Fin n → Kˣ) (target : Fin (n + 1) → Kˣ) :
    DiagonalRepresents (diagonalUnitCoefficients source)
        (diagonalUnitCoefficients target) ↔
      diagonalHasseSymbol K target * diagonalHasseSymbol K source *
          hilbertSymbol K (diagonalUnitDeterminant source)
            (diagonalUnitDeterminant target) *
          hilbertSymbol K (diagonalUnitDeterminant target) (-1) = 1 := by
  let d := diagonalUnitDeterminant target * diagonalUnitDeterminant source
  let completed : Fin (n + 1) → Kˣ := Fin.snoc source d
  have hrep_iff :
      DiagonalRepresents (diagonalUnitCoefficients source)
          (diagonalUnitCoefficients target) ↔
        diagonalHasseSymbol K completed = diagonalHasseSymbol K target := by
    constructor
    · intro hrep
      have hcompleted : DiagonalRepresents
          (diagonalUnitCoefficients completed)
          (diagonalUnitCoefficients target) := by
        simpa only [completed, d] using
          determinantCompletion_represents_base_general target source hrep
      exact DiagonalIsometryInvariantLaws.hasse_eq completed target hcompleted
    · intro hhasse
      have hdet : IsSquare
          (diagonalUnitDeterminant completed *
            diagonalUnitDeterminant target) := by
        refine ⟨diagonalUnitDeterminant target *
          diagonalUnitDeterminant source, ?_⟩
        simp only [completed, d, diagonalUnitDeterminant_snoc]
        ac_rfl
      have hcompleted : DiagonalRepresents
          (diagonalUnitCoefficients completed)
          (diagonalUnitCoefficients target) :=
        DyadicDiagonalClassificationLaws.represents_of_invariants
          completed target hdet hhasse
      have hprefix : DiagonalRepresents
          (diagonalUnitCoefficients source)
          (diagonalUnitCoefficients completed) := by
        convert DiagonalRepresents.prefixSucc
          (diagonalUnitCoefficients completed) using 1
        funext i
        simp only [completed, diagonalUnitCoefficients_snoc,
          Fin.snoc_castSucc]
      exact hprefix.trans hcompleted
  rw [hrep_iff]
  have hformula := diagonalHasseSymbol_determinantCompletion source target
  rw [hformula]
  rw [intUnit_eq_iff_mul_eq_one]
  constructor <;> intro h <;>
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h

/-- Four signs with product one have even truth parity. -/
private theorem evenTruthParity_of_units_product_one
    (x y z w : ℤˣ) (hproduct : x * y * z * w = 1) :
    EvenTruthParity (x = 1) (y = 1) (z = 1) (w = 1) := by
  unfold EvenTruthParity
  rcases Int.units_eq_one_or x with hx | hx <;>
    rcases Int.units_eq_one_or y with hy | hy <;>
      rcases Int.units_eq_one_or z with hz | hz <;>
        rcases Int.units_eq_one_or w with hw | hw <;>
          simp [hx, hy, hz, hw] at hproduct ⊢

/-- The first parity cycle in Beli's Lemma 1.5. -/
theorem diagonalRepresentationParity_caseI
    {i j k : Nat} (a : Fin i → Kˣ) (b : Fin j → Kˣ)
    (c : Fin k → Kˣ) (hab : i = j) (hkb : k + 1 = j) :
    EvenTruthParity
      (DiagonalRepresents
        (diagonalUnitCoefficients
          (diagonalUnitTake b k (by omega)))
        (diagonalUnitCoefficients a))
      (DiagonalRepresents
        (diagonalUnitCoefficients c)
        (diagonalUnitCoefficients b))
      (DiagonalRepresents
        (diagonalUnitCoefficients c)
        (diagonalUnitCoefficients a))
      (hilbertSymbol K
        (diagonalUnitDeterminant a * diagonalUnitDeterminant b)
        (diagonalUnitDeterminant (diagonalUnitTake b k (by omega)) *
          diagonalUnitDeterminant c) = 1) := by
  subst i
  subst j
  let p : Fin k → Kˣ := diagonalUnitTake b k (by omega)
  let HA := diagonalHasseSymbol K a
  let HB := diagonalHasseSymbol K b
  let HP := diagonalHasseSymbol K p
  let HC := diagonalHasseSymbol K c
  let DA := diagonalUnitDeterminant a
  let DB := diagonalUnitDeterminant b
  let DP := diagonalUnitDeterminant p
  let DC := diagonalUnitDeterminant c
  let sP := HA * HP * hilbertSymbol K DP DA * hilbertSymbol K DA (-1)
  let sQ := HB * HC * hilbertSymbol K DC DB * hilbertSymbol K DB (-1)
  let sR := HA * HC * hilbertSymbol K DC DA * hilbertSymbol K DA (-1)
  let sS := hilbertSymbol K (DA * DB) (DP * DC)
  have hpiff : DiagonalRepresents (diagonalUnitCoefficients p)
      (diagonalUnitCoefficients a) ↔ sP = 1 := by
    simpa only [sP, HA, HP, DP, DA] using
      diagonalCodimensionOneRepresents_iff_sign_eq_one p a
  have hqiff : DiagonalRepresents (diagonalUnitCoefficients c)
      (diagonalUnitCoefficients b) ↔ sQ = 1 := by
    simpa only [sQ, HB, HC, DC, DB] using
      diagonalCodimensionOneRepresents_iff_sign_eq_one c b
  have hriff : DiagonalRepresents (diagonalUnitCoefficients c)
      (diagonalUnitCoefficients a) ↔ sR = 1 := by
    simpa only [sR, HA, HC, DC, DA] using
      diagonalCodimensionOneRepresents_iff_sign_eq_one c a
  have hprefix : DiagonalRepresents (diagonalUnitCoefficients p)
      (diagonalUnitCoefficients b) := by
    convert DiagonalRepresents.prefixSucc
      (diagonalUnitCoefficients b) using 1
    funext x
    simp only [p, diagonalUnitTake, diagonalUnitCoefficients]
    congr 1
  have hbase :
      HB * HP * hilbertSymbol K DP DB * hilbertSymbol K DB (-1) = 1 := by
    simpa only [HB, HP, DP, DB] using
      (diagonalCodimensionOneRepresents_iff_sign_eq_one p b).mp hprefix
  have hproduct : sP * sQ * sR * sS = 1 := by
    have hreorder : sP * sQ * sR * sS =
        (HA * HA) * (HC * HC) *
          (hilbertSymbol K DP DA * hilbertSymbol K DP DA) *
          (hilbertSymbol K DC DB * hilbertSymbol K DC DB) *
          (hilbertSymbol K DC DA * hilbertSymbol K DC DA) *
          (hilbertSymbol K DA (-1) * hilbertSymbol K DA (-1)) *
          (HB * HP * hilbertSymbol K DP DB *
            hilbertSymbol K DB (-1)) := by
      dsimp only [sP, sQ, sR, sS]
      rw [hilbertSymbol_mul_left, hilbertSymbol_mul_right,
        hilbertSymbol_mul_right,
        hilbertSymbol_comm K DA DP,
        hilbertSymbol_comm K DA DC,
        hilbertSymbol_comm K DB DP,
        hilbertSymbol_comm K DB DC]
      ac_rfl
    rw [hreorder, Int.units_mul_self, Int.units_mul_self,
      Int.units_mul_self, Int.units_mul_self, Int.units_mul_self,
      Int.units_mul_self]
    simpa using hbase
  have hparity := evenTruthParity_of_units_product_one sP sQ sR sS hproduct
  rw [hpiff, hqiff, hriff]
  simpa only [sS, DA, DB, DP, DC, p] using hparity

/-- The second parity cycle in Beli's Lemma 1.5. -/
theorem diagonalRepresentationParity_caseII
    {i j k : Nat} (a : Fin i → Kˣ) (b : Fin j → Kˣ)
    (c : Fin k → Kˣ) (hba : j + 1 = i) (hck : k + 1 = j) :
    EvenTruthParity
      (DiagonalRepresents
        (diagonalUnitCoefficients b)
        (diagonalUnitCoefficients a))
      (DiagonalRepresents
        (diagonalUnitCoefficients c)
        (diagonalUnitCoefficients b))
      (DiagonalRepresents
        (diagonalUnitCoefficients c)
        (diagonalUnitCoefficients
          (diagonalUnitTake a j (by omega))))
      (hilbertSymbol K
        (diagonalUnitDeterminant (diagonalUnitTake a j (by omega)) *
          diagonalUnitDeterminant b)
        (-diagonalUnitDeterminant a * diagonalUnitDeterminant c) = 1) := by
  subst i
  subst j
  let p : Fin (k + 1) → Kˣ :=
    diagonalUnitTake a (k + 1) (by omega)
  let HA := diagonalHasseSymbol K a
  let HB := diagonalHasseSymbol K b
  let HP := diagonalHasseSymbol K p
  let HC := diagonalHasseSymbol K c
  let DA := diagonalUnitDeterminant a
  let DB := diagonalUnitDeterminant b
  let DP := diagonalUnitDeterminant p
  let DC := diagonalUnitDeterminant c
  let sP := HA * HB * hilbertSymbol K DB DA * hilbertSymbol K DA (-1)
  let sQ := HB * HC * hilbertSymbol K DC DB * hilbertSymbol K DB (-1)
  let sR := HP * HC * hilbertSymbol K DC DP * hilbertSymbol K DP (-1)
  let sS := hilbertSymbol K (DP * DB) (-DA * DC)
  have hpiff : DiagonalRepresents (diagonalUnitCoefficients b)
      (diagonalUnitCoefficients a) ↔ sP = 1 := by
    simpa only [sP, HA, HB, DB, DA] using
      diagonalCodimensionOneRepresents_iff_sign_eq_one b a
  have hqiff : DiagonalRepresents (diagonalUnitCoefficients c)
      (diagonalUnitCoefficients b) ↔ sQ = 1 := by
    simpa only [sQ, HB, HC, DC, DB] using
      diagonalCodimensionOneRepresents_iff_sign_eq_one c b
  have hriff : DiagonalRepresents (diagonalUnitCoefficients c)
      (diagonalUnitCoefficients p) ↔ sR = 1 := by
    simpa only [sR, HP, HC, DC, DP] using
      diagonalCodimensionOneRepresents_iff_sign_eq_one c p
  have hprefix : DiagonalRepresents (diagonalUnitCoefficients p)
      (diagonalUnitCoefficients a) := by
    convert DiagonalRepresents.prefixSucc
      (diagonalUnitCoefficients a) using 1
    funext x
    simp only [p, diagonalUnitTake, diagonalUnitCoefficients]
    congr 1
  have hbase :
      HA * HP * hilbertSymbol K DP DA * hilbertSymbol K DA (-1) = 1 := by
    simpa only [HA, HP, DP, DA] using
      (diagonalCodimensionOneRepresents_iff_sign_eq_one p a).mp hprefix
  have hSexpand : sS =
      hilbertSymbol K DP (-1) * hilbertSymbol K DP DA *
          hilbertSymbol K DP DC *
        (hilbertSymbol K DB (-1) * hilbertSymbol K DB DA *
          hilbertSymbol K DB DC) := by
    dsimp only [sS]
    rw [show -DA = (-1) * DA by simp]
    rw [hilbertSymbol_mul_left, hilbertSymbol_mul_right,
      hilbertSymbol_mul_right, hilbertSymbol_mul_right,
      hilbertSymbol_mul_right]
  have hproduct : sP * sQ * sR * sS = 1 := by
    have hreorder : sP * sQ * sR * sS =
        (HB * HB) * (HC * HC) *
          (hilbertSymbol K DB DA * hilbertSymbol K DB DA) *
          (hilbertSymbol K DC DB * hilbertSymbol K DC DB) *
          (hilbertSymbol K DC DP * hilbertSymbol K DC DP) *
          (hilbertSymbol K DB (-1) * hilbertSymbol K DB (-1)) *
          (hilbertSymbol K DP (-1) * hilbertSymbol K DP (-1)) *
          (HA * HP * hilbertSymbol K DP DA *
            hilbertSymbol K DA (-1)) := by
      rw [hSexpand]
      dsimp only [sP, sQ, sR]
      rw [hilbertSymbol_comm K DB DC,
        hilbertSymbol_comm K DP DC]
      ac_rfl
    rw [hreorder, Int.units_mul_self, Int.units_mul_self,
      Int.units_mul_self, Int.units_mul_self, Int.units_mul_self,
      Int.units_mul_self, Int.units_mul_self]
    simpa using hbase
  have hparity := evenTruthParity_of_units_product_one sP sQ sR sS hproduct
  rw [hpiff, hqiff, hriff]
  simpa only [sS, DA, DB, DP, DC, p] using hparity

/-- The third parity cycle in Beli's Lemma 1.5. -/
theorem diagonalRepresentationParity_caseIII
    {i j k l : Nat} (a : Fin i → Kˣ) (b : Fin j → Kˣ)
    (c : Fin k → Kˣ) (hba : j + 1 = i) (hcb : k = j)
    (hlc : l + 1 = k) :
    EvenTruthParity
      (DiagonalRepresents
        (diagonalUnitCoefficients b)
        (diagonalUnitCoefficients a))
      (DiagonalRepresents
        (diagonalUnitCoefficients
          (diagonalUnitTake c l (by omega)))
        (diagonalUnitCoefficients b))
      (DiagonalRepresents
        (diagonalUnitCoefficients c)
        (diagonalUnitCoefficients a))
      (hilbertSymbol K
        (diagonalUnitDeterminant b * diagonalUnitDeterminant c)
        (-diagonalUnitDeterminant a *
          diagonalUnitDeterminant (diagonalUnitTake c l (by omega))) = 1) := by
  subst i
  subst k
  subst j
  let p : Fin l → Kˣ := diagonalUnitTake c l (by omega)
  let HA := diagonalHasseSymbol K a
  let HB := diagonalHasseSymbol K b
  let HC := diagonalHasseSymbol K c
  let HP := diagonalHasseSymbol K p
  let DA := diagonalUnitDeterminant a
  let DB := diagonalUnitDeterminant b
  let DC := diagonalUnitDeterminant c
  let DP := diagonalUnitDeterminant p
  let sP := HA * HB * hilbertSymbol K DB DA * hilbertSymbol K DA (-1)
  let sQ := HB * HP * hilbertSymbol K DP DB * hilbertSymbol K DB (-1)
  let sR := HA * HC * hilbertSymbol K DC DA * hilbertSymbol K DA (-1)
  let sS := hilbertSymbol K (DB * DC) (-DA * DP)
  have hpiff : DiagonalRepresents (diagonalUnitCoefficients b)
      (diagonalUnitCoefficients a) ↔ sP = 1 := by
    simpa only [sP, HA, HB, DB, DA] using
      diagonalCodimensionOneRepresents_iff_sign_eq_one b a
  have hqiff : DiagonalRepresents (diagonalUnitCoefficients p)
      (diagonalUnitCoefficients b) ↔ sQ = 1 := by
    simpa only [sQ, HB, HP, DP, DB] using
      diagonalCodimensionOneRepresents_iff_sign_eq_one p b
  have hriff : DiagonalRepresents (diagonalUnitCoefficients c)
      (diagonalUnitCoefficients a) ↔ sR = 1 := by
    simpa only [sR, HA, HC, DC, DA] using
      diagonalCodimensionOneRepresents_iff_sign_eq_one c a
  have hprefix : DiagonalRepresents (diagonalUnitCoefficients p)
      (diagonalUnitCoefficients c) := by
    convert DiagonalRepresents.prefixSucc
      (diagonalUnitCoefficients c) using 1
    funext x
    simp only [p, diagonalUnitTake, diagonalUnitCoefficients]
    congr 1
  have hbase :
      HC * HP * hilbertSymbol K DP DC * hilbertSymbol K DC (-1) = 1 := by
    simpa only [HC, HP, DP, DC] using
      (diagonalCodimensionOneRepresents_iff_sign_eq_one p c).mp hprefix
  have hSexpand : sS =
      hilbertSymbol K DB (-1) * hilbertSymbol K DB DA *
          hilbertSymbol K DB DP *
        (hilbertSymbol K DC (-1) * hilbertSymbol K DC DA *
          hilbertSymbol K DC DP) := by
    dsimp only [sS]
    rw [show -DA = (-1) * DA by simp]
    rw [hilbertSymbol_mul_left, hilbertSymbol_mul_right,
      hilbertSymbol_mul_right, hilbertSymbol_mul_right,
      hilbertSymbol_mul_right]
  have hproduct : sP * sQ * sR * sS = 1 := by
    have hreorder : sP * sQ * sR * sS =
        (HA * HA) * (HB * HB) *
          (hilbertSymbol K DB DA * hilbertSymbol K DB DA) *
          (hilbertSymbol K DP DB * hilbertSymbol K DP DB) *
          (hilbertSymbol K DC DA * hilbertSymbol K DC DA) *
          (hilbertSymbol K DA (-1) * hilbertSymbol K DA (-1)) *
          (hilbertSymbol K DB (-1) * hilbertSymbol K DB (-1)) *
          (HC * HP * hilbertSymbol K DP DC *
            hilbertSymbol K DC (-1)) := by
      rw [hSexpand]
      dsimp only [sP, sQ, sR]
      rw [hilbertSymbol_comm K DB DP,
        hilbertSymbol_comm K DC DP]
      ac_rfl
    rw [hreorder, Int.units_mul_self, Int.units_mul_self,
      Int.units_mul_self, Int.units_mul_self, Int.units_mul_self,
      Int.units_mul_self, Int.units_mul_self]
    simpa using hbase
  have hparity := evenTruthParity_of_units_product_one sP sQ sR sS hproduct
  rw [hpiff, hqiff, hriff]
  simpa only [sS, DA, DB, DC, DP, p] using hparity

/-- The unconditional parity package for the three codimension-one cycles. -/
noncomputable instance diagonalRepresentationParityLawsProved :
    DiagonalRepresentationParityLaws K where
  caseI := diagonalRepresentationParity_caseI
  caseII := diagonalRepresentationParity_caseII
  caseIII := diagonalRepresentationParity_caseIII

example : DiagonalRepresentationParityLaws K := inferInstance

end Bong
