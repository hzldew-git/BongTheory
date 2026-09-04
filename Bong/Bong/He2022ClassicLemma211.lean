/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2022ClassicModels
import Bong.Bong.Beli2019Lemma88Necessity
import Bong.Bong.BeliUniversalCorollary410
import Bong.Bong.DiagonalCodimensionOneCancellationProof
import Bong.Bong.DiagonalLocalClassificationProof
import Bong.Bong.HeHu2022SectionThreeSpaces

/-!
# He (2024), Lemma 2.11

This file proves the local Witt dichotomy used at the end of Section 2 of
Zilong He, *On classic n-universal quadratic forms over dyadic local fields*.
The paper's two even-dimensional tests are written with a common hyperbolic
head.  Their residual binary spaces are `[1,-1]` and `[pi,-Delta*pi]`.

The proof first establishes the rank-three dichotomy from determinant
completion, the ternary Hilbert criterion, and local diagonal
classification.  It then appends or cancels the common hyperbolic head.
-/

namespace Bong

open Dyadic BONG.GoodBONG
open AlternatingEndpointTower

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The ramified binary space `[pi,-Delta*pi]` in Lemma 2.11. -/
noncomputable def heClassicRamifiedBinary : Fin 2 → Kˣ :=
  heHuDiscriminantBinary
    (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit

@[simp] theorem heClassicRamifiedBinary_zero :
    heClassicRamifiedBinary (K := K) 0 =
      uniformizerPowerUnit K (1 : Int) := rfl

@[simp] theorem heClassicRamifiedBinary_one :
    heClassicRamifiedBinary (K := K) 1 =
      -((uniformizerPowerUnit K (1 : Int)) *
        (inferInstance :
          DyadicDiscriminantClassLaws K).discriminantUnit) := rfl

theorem heClassicRamifiedBinary_determinant_order :
    ordUnit K (diagonalUnitDeterminant
      (heClassicRamifiedBinary (K := K))) = 2 := by
  let delta :=
    (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
  have hdelta : ordUnit K delta = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K delta).1
      (inferInstance : DyadicDiscriminantClassLaws K).discriminant_isValuationUnit
  simp only [heClassicRamifiedBinary, heHuDiscriminantBinary,
    heHuBinaryTwist, diagonalUnitDeterminant, Fin.prod_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue,
    ordUnit_neg, ordUnit_mul, ordUnit_uniformizerPowerUnit]
  change 1 + (1 + ordUnit K delta) = 2
  rw [hdelta]
  norm_num

/-- The determinant completion of `[pi,-Delta*pi]` inside a ternary space. -/
noncomputable def heClassicRamifiedCompletion (u : Fin 3 → Kˣ) :
    Fin 3 → Kˣ :=
  Fin.snoc (heClassicRamifiedBinary (K := K))
    (diagonalUnitDeterminant u *
      diagonalUnitDeterminant (heClassicRamifiedBinary (K := K)))

/-- A unit-determinant completion of `[pi,-Delta*pi]` is anisotropic. -/
theorem heClassicRamifiedSnoc_anisotropic
    (d : Kˣ) (hd : ordUnit K d = 2) :
    DiagonalAnisotropic
      (diagonalUnitCoefficients
        (Fin.snoc (heClassicRamifiedBinary (K := K)) d)) := by
  let delta :=
    (inferInstance : DyadicDiscriminantClassLaws K).discriminantUnit
  let c : Kˣ := delta⁻¹ * d
  have hdelta : ordUnit K delta = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K delta).1
      (inferInstance : DyadicDiscriminantClassLaws K).discriminant_isValuationUnit
  have hc : ordUnit K c = 2 := by
    simp only [c, ordUnit_mul, ordUnit_inv, hdelta, hd]
    omega
  have hcEven : Even (ordUnit K c) := by rw [hc]; exact even_two
  have heq : Fin.snoc (heClassicRamifiedBinary (K := K)) d =
      heHuOddSecondTailEven (K := K) c := by
    funext i
    fin_cases i
    · rfl
    · change -(uniformizerPowerUnit K (1 : Int) * delta) =
        -(delta * uniformizerPowerUnit K (1 : Int))
      rw [mul_comm]
    · change d = delta * (delta⁻¹ * d)
      simp
  rw [heq]
  exact heHuOddSecondTailEven_anisotropic c hcEven

/-- A unit-determinant completion of `[pi,-Delta*pi]` is anisotropic. -/
theorem heClassicRamifiedCompletion_anisotropic
    (u : Fin 3 → Kˣ)
    (hdet : ordUnit K (diagonalUnitDeterminant u) = 0) :
    DiagonalAnisotropic
      (diagonalUnitCoefficients
        (heClassicRamifiedCompletion (K := K) u)) := by
  apply heClassicRamifiedSnoc_anisotropic
  simp only [ordUnit_mul, hdet,
    heClassicRamifiedBinary_determinant_order]
  omega

/-- A ternary diagonal space of unit determinant represents the ramified
binary test exactly in its anisotropic branch. -/
theorem heClassicRamifiedBinary_represents_iff_anisotropic
    (u : Fin 3 → Kˣ)
    (hdet : ordUnit K (diagonalUnitDeterminant u) = 0) :
    DiagonalRepresents
        (diagonalUnitCoefficients (heClassicRamifiedBinary (K := K)))
        (diagonalUnitCoefficients u) ↔
      DiagonalAnisotropic (diagonalUnitCoefficients u) := by
  let completion := heClassicRamifiedCompletion (K := K) u
  have hcompletionAnisotropic :
      DiagonalAnisotropic (diagonalUnitCoefficients completion) :=
    heClassicRamifiedCompletion_anisotropic u hdet
  constructor
  · intro hrep
    have hfull := BONG.GoodBONG.determinantCompletion_represents_base
      u (heClassicRamifiedBinary (K := K)) hrep
    change DiagonalRepresents
      (diagonalUnitCoefficients completion)
      (diagonalUnitCoefficients u) at hfull
    exact hfull.symm_of_sameRank.anisotropic_of hcompletionAnisotropic
  · intro huAnisotropic
    have hisotropy :
        DiagonalIsotropic (diagonalUnitCoefficients completion) ↔
          DiagonalIsotropic (diagonalUnitCoefficients u) := by
      constructor <;> intro h
      · exact False.elim
          (((not_diagonalIsotropic_iff_diagonalAnisotropic _).2
            hcompletionAnisotropic) h)
      · exact False.elim
          (((not_diagonalIsotropic_iff_diagonalAnisotropic _).2
            huAnisotropic) h)
    have hhasse : diagonalHasseSymbol K completion =
        diagonalHasseSymbol K u :=
      diagonalHasseSymbol_fin_three_eq_of_isotropic_iff
        completion u hisotropy
    have hdetSquare : IsSquare
        (diagonalUnitDeterminant completion *
          diagonalUnitDeterminant u) := by
      let DB := diagonalUnitDeterminant
        (heClassicRamifiedBinary (K := K))
      let DU := diagonalUnitDeterminant u
      refine ⟨DB * DU, ?_⟩
      simp only [completion, heClassicRamifiedCompletion,
        diagonalUnitDeterminant_snoc, DB, DU]
      ac_rfl
    have hfull : DiagonalRepresents
        (diagonalUnitCoefficients completion)
        (diagonalUnitCoefficients u) :=
      diagonalUnitTernary_represents_of_invariants
        completion u hdetSquare hhasse
    have hprefix : DiagonalRepresents
        (diagonalUnitCoefficients (heClassicRamifiedBinary (K := K)))
        (diagonalUnitCoefficients completion) := by
      have hp := DiagonalRepresents.prefixOfLE
        (k := 2) (diagonalUnitCoefficients completion) (by omega)
      have hcoeff :
          (fun i : Fin 2 =>
            diagonalUnitCoefficients completion
              ⟨i.val, i.isLt.trans_le (by omega : 2 ≤ 3)⟩) =
            diagonalUnitCoefficients
              (heClassicRamifiedBinary (K := K)) := by
        funext i
        have hi :
            (⟨i.val, i.isLt.trans_le (by omega : 2 ≤ 3)⟩ : Fin 3) =
              i.castSucc := by
          apply Fin.ext
          rfl
        rw [hi]
        simp [completion, heClassicRamifiedCompletion,
          diagonalUnitCoefficients]
      rw [hcoeff] at hp
      exact hp
    exact hprefix.trans hfull

set_option maxHeartbeats 1000000 in
/-- The standard hyperbolic binary test represents a ternary diagonal
space exactly in its isotropic branch. -/
theorem heClassicHyperbolicPair_represents_iff_isotropic
    (u : Fin 3 → Kˣ) :
    DiagonalRepresents
        (diagonalUnitCoefficients (heHuHyperbolicPair (K := K)))
        (diagonalUnitCoefficients u) ↔
      DiagonalIsotropic (diagonalUnitCoefficients u) := by
  constructor
  · intro hrep
    apply hrep.isotropic_of
    let x : Fin 2 → K := ![1, 1]
    refine ⟨x, ?_, ?_⟩
    · intro hx
      have hzero := congrFun hx (0 : Fin 2)
      norm_num [x] at hzero
    · simp [heHuHyperbolicPair, diagonalUnitCoefficients,
        diagonalQuadratic, Fin.sum_univ_two, x]
  · intro hisotropic
    have htarget :=
      QuadraticSpace.finiteDiagonal_represents_hyperbolicPlane_one_of_isotropic
        (diagonalUnitCoefficients u)
        (fun i => Units.ne_zero (u i)) hisotropic
    have hsquare : IsSquare (-((1 : Kˣ) / (-1 : Kˣ))) := by simp
    rcases QuadraticSpace.finiteDiagonal_fin_two_isIsometric_hyperbolicPlane_one
        (K := K) (1 : Kˣ) (-1 : Kˣ) hsquare with ⟨hsource⟩
    rcases htarget with ⟨hinto⟩
    have hsourceRep :
        QuadraticSpace.Representation
          (QuadraticSpace.finiteDiagonal
            (diagonalUnitCoefficients (heHuHyperbolicPair (K := K)))
            (fun i => Units.ne_zero
              (heHuHyperbolicPair (K := K) i)))
          (QuadraticSpace.hyperbolicPlane (K := K) (1 : Kˣ)) := by
      change QuadraticSpace.Representation
        (QuadraticSpace.finiteDiagonal ![(1 : K), (-1 : K)] (by simp))
        (QuadraticSpace.hyperbolicPlane (K := K) (1 : Kˣ))
      exact hsource.toRepresentation
    have hspace :
        (QuadraticSpace.finiteDiagonal (diagonalUnitCoefficients u)
          (fun i => Units.ne_zero (u i))).Represents
        (QuadraticSpace.finiteDiagonal
          (diagonalUnitCoefficients (heHuHyperbolicPair (K := K)))
          (fun i => Units.ne_zero
            (heHuHyperbolicPair (K := K) i))) := by
      exact ⟨hinto.trans hsourceRep⟩
    exact (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
      (heHuHyperbolicPair (K := K)) u).mp hspace

/-- Lemma 2.11(i) in the rank-three residual form. -/
theorem he2022ClassicLemma211i_ternary
    (u : Fin 3 → Kˣ)
    (hdet : ordUnit K (diagonalUnitDeterminant u) = 0) :
    ¬ (DiagonalRepresents
          (diagonalUnitCoefficients (heHuHyperbolicPair (K := K)))
          (diagonalUnitCoefficients u) ∧
        DiagonalRepresents
          (diagonalUnitCoefficients (heClassicRamifiedBinary (K := K)))
          (diagonalUnitCoefficients u)) := by
  rintro ⟨hH, hB⟩
  have hiso :=
    (heClassicHyperbolicPair_represents_iff_isotropic u).1 hH
  have haniso :=
    (heClassicRamifiedBinary_represents_iff_anisotropic u hdet).1 hB
  exact ((not_diagonalIsotropic_iff_diagonalAnisotropic _).2 haniso) hiso

/-- Lemma 2.11(ii) in the rank-three residual form. -/
theorem he2022ClassicLemma211ii_ternary
    (u : Fin 3 → Kˣ)
    (hdet : ordUnit K (diagonalUnitDeterminant u) = 0)
    (hiso : DiagonalIsotropic (diagonalUnitCoefficients u)) :
    DiagonalRepresents
        (diagonalUnitCoefficients (heHuHyperbolicPair (K := K)))
        (diagonalUnitCoefficients u) ∧
      ¬ DiagonalRepresents
        (diagonalUnitCoefficients (heClassicRamifiedBinary (K := K)))
        (diagonalUnitCoefficients u) := by
  constructor
  · exact (heClassicHyperbolicPair_represents_iff_isotropic u).2 hiso
  · intro hrep
    have haniso :=
      (heClassicRamifiedBinary_represents_iff_anisotropic u hdet).1 hrep
    exact ((not_diagonalIsotropic_iff_diagonalAnisotropic _).2 haniso) hiso

/-- Lemma 2.11(iii) in the rank-three residual form. -/
theorem he2022ClassicLemma211iii_ternary
    (u : Fin 3 → Kˣ)
    (hdet : ordUnit K (diagonalUnitDeterminant u) = 0)
    (haniso : DiagonalAnisotropic (diagonalUnitCoefficients u)) :
    DiagonalRepresents
        (diagonalUnitCoefficients (heClassicRamifiedBinary (K := K)))
        (diagonalUnitCoefficients u) ∧
      ¬ DiagonalRepresents
        (diagonalUnitCoefficients (heHuHyperbolicPair (K := K)))
        (diagonalUnitCoefficients u) := by
  constructor
  · exact (heClassicRamifiedBinary_represents_iff_anisotropic u hdet).2
      haniso
  · intro hrep
    have hiso :=
      (heClassicHyperbolicPair_represents_iff_isotropic u).1 hrep
    exact ((not_diagonalIsotropic_iff_diagonalAnisotropic _).2 haniso) hiso

/-! ## Appending the common hyperbolic head -/

/-- The two rank `2*k+2` tests in Lemma 2.11. -/
noncomputable def heClassicLemma211First (k : Nat) :
    Fin (2 * k + 2) → Kˣ :=
  Fin.append (standardHyperbolicEndpointTower (K := K) k)
    (heHuHyperbolicPair (K := K))

noncomputable def heClassicLemma211Second (k : Nat) :
    Fin (2 * k + 2) → Kˣ :=
  Fin.append (standardHyperbolicEndpointTower (K := K) k)
    (heClassicRamifiedBinary (K := K))

/-- Lemma 2.11(i), with `n=2*k+2`, for an arbitrary ambient
`(n+1)`-dimensional diagonal space of unit determinant order.  The two
codimension-one representations are completed by their determinant lines;
after cancelling their common hyperbolic head, the first ternary completion
is isotropic whereas the second one is anisotropic. -/
theorem he2022ClassicLemma211i (k : Nat)
    (v : Fin (2 * k + 3) → Kˣ)
    (hdet : ordUnit K (diagonalUnitDeterminant v) = 0) :
    ¬ (DiagonalRepresents
          (diagonalUnitCoefficients (heClassicLemma211First (K := K) k))
          (diagonalUnitCoefficients v) ∧
        DiagonalRepresents
          (diagonalUnitCoefficients (heClassicLemma211Second (K := K) k))
          (diagonalUnitCoefficients v)) := by
  rintro ⟨hfirst, hsecond⟩
  let common := standardHyperbolicEndpointTower (K := K) k
  let first := heClassicLemma211First (K := K) k
  let second := heClassicLemma211Second (K := K) k
  let dFirst := diagonalUnitDeterminant v *
    diagonalUnitDeterminant first
  let dSecond := diagonalUnitDeterminant v *
    diagonalUnitDeterminant second
  have hfullFirst : DiagonalRepresents
      (diagonalUnitCoefficients (Fin.snoc first dFirst))
      (diagonalUnitCoefficients v) := by
    simpa only [first, dFirst] using
      determinantCompletion_represents_base_general v first hfirst
  have hfullSecond : DiagonalRepresents
      (diagonalUnitCoefficients (Fin.snoc second dSecond))
      (diagonalUnitCoefficients v) := by
    simpa only [second, dSecond] using
      determinantCompletion_represents_base_general v second hsecond
  have hbetween : DiagonalRepresents
      (diagonalUnitCoefficients (Fin.snoc first dFirst))
      (diagonalUnitCoefficients (Fin.snoc second dSecond)) :=
    hfullFirst.trans hfullSecond.symm_of_sameRank
  have hbetween' : DiagonalRepresents
      (Fin.append (diagonalUnitCoefficients common)
        (diagonalUnitCoefficients
          (Fin.snoc (heHuHyperbolicPair (K := K)) dFirst)))
      (Fin.append (diagonalUnitCoefficients common)
        (diagonalUnitCoefficients
          (Fin.snoc (heClassicRamifiedBinary (K := K)) dSecond))) := by
    simpa only [first, second, heClassicLemma211First,
      heClassicLemma211Second, common, diagonalUnitCoefficients_snoc,
      diagonalUnitCoefficients_append, Fin.append_snoc] using hbetween
  have htail : DiagonalRepresents
      (diagonalUnitCoefficients
        (Fin.snoc (heHuHyperbolicPair (K := K)) dFirst))
      (diagonalUnitCoefficients
        (Fin.snoc (heClassicRamifiedBinary (K := K)) dSecond)) :=
    DiagonalRepresents.cancel_common_prefix
      (diagonalUnitCoefficients common)
      (diagonalUnitCoefficients
        (Fin.snoc (heHuHyperbolicPair (K := K)) dFirst))
      (diagonalUnitCoefficients
        (Fin.snoc (heClassicRamifiedBinary (K := K)) dSecond))
      (by intro i; simp [diagonalUnitCoefficients])
      (by intro i; simp [diagonalUnitCoefficients])
      (by intro i; simp [diagonalUnitCoefficients])
      hbetween'
  have hsourceIsotropic : DiagonalIsotropic
      (diagonalUnitCoefficients
        (Fin.snoc (heHuHyperbolicPair (K := K)) dFirst)) := by
    have hprefix : DiagonalRepresents
        (diagonalUnitCoefficients (heHuHyperbolicPair (K := K)))
        (diagonalUnitCoefficients
          (Fin.snoc (heHuHyperbolicPair (K := K)) dFirst)) := by
      convert DiagonalRepresents.prefixSucc
        (diagonalUnitCoefficients
          (Fin.snoc (heHuHyperbolicPair (K := K)) dFirst)) using 1
      funext i
      simp only [diagonalUnitCoefficients_snoc, Fin.snoc_castSucc]
    exact (heClassicHyperbolicPair_represents_iff_isotropic
      (Fin.snoc (heHuHyperbolicPair (K := K)) dFirst)).1 hprefix
  have hsecondDetOrder : ordUnit K
      (diagonalUnitDeterminant second) = 2 := by
    change ordUnit K (diagonalUnitDeterminant
      (heClassicLemma211Second (K := K) k)) = 2
    rw [heClassicLemma211Second,
      diagonalUnitDeterminant_append, ordUnit_mul,
      diagonalUnitDeterminant_standardHyperbolicEndpointTower,
      ordUnit_pow, ordUnit_neg_one_eq_zero,
      heClassicRamifiedBinary_determinant_order]
    omega
  have hdSecond : ordUnit K dSecond = 2 := by
    simp only [dSecond, ordUnit_mul, hdet, hsecondDetOrder]
    omega
  have htargetAnisotropic : DiagonalAnisotropic
      (diagonalUnitCoefficients
        (Fin.snoc (heClassicRamifiedBinary (K := K)) dSecond)) :=
    heClassicRamifiedSnoc_anisotropic dSecond hdSecond
  have htargetIsotropic := htail.isotropic_of hsourceIsotropic
  exact ((not_diagonalIsotropic_iff_diagonalAnisotropic _).2
    htargetAnisotropic) htargetIsotropic

/-- Lemma 2.11(ii), with `n=2*k+2` and the displayed decomposition
`V = H^k perp U`. -/
theorem he2022ClassicLemma211ii (k : Nat) (u : Fin 3 → Kˣ)
    (hdet : ordUnit K (diagonalUnitDeterminant u) = 0)
    (hiso : DiagonalIsotropic (diagonalUnitCoefficients u)) :
    DiagonalRepresents
        (diagonalUnitCoefficients (heClassicLemma211First (K := K) k))
        (diagonalUnitCoefficients
          (Fin.append (standardHyperbolicEndpointTower (K := K) k) u)) ∧
      ¬ DiagonalRepresents
        (diagonalUnitCoefficients (heClassicLemma211Second (K := K) k))
        (diagonalUnitCoefficients
          (Fin.append (standardHyperbolicEndpointTower (K := K) k) u)) := by
  let common := standardHyperbolicEndpointTower (K := K) k
  have hcommon : DiagonalRepresents
      (diagonalUnitCoefficients common)
      (diagonalUnitCoefficients common) := diagonalRepresents_refl _
  obtain ⟨hH, hB⟩ := he2022ClassicLemma211ii_ternary u hdet hiso
  constructor
  · simpa [heClassicLemma211First, common,
      diagonalUnitCoefficients_append] using
      DiagonalRepresents.appendBoth hcommon hH
  · intro hrep
    have htail := DiagonalRepresents.cancel_common_prefix
      (diagonalUnitCoefficients common)
      (diagonalUnitCoefficients (heClassicRamifiedBinary (K := K)))
      (diagonalUnitCoefficients u)
      (fun i => Units.ne_zero (common i))
      (fun i => Units.ne_zero (heClassicRamifiedBinary (K := K) i))
      (fun i => Units.ne_zero (u i)) (by
        simpa [heClassicLemma211Second, common,
          diagonalUnitCoefficients_append] using hrep)
    exact hB htail

/-- Lemma 2.11(iii), with `n=2*k+2` and the displayed decomposition
`V = H^k perp U`. -/
theorem he2022ClassicLemma211iii (k : Nat) (u : Fin 3 → Kˣ)
    (hdet : ordUnit K (diagonalUnitDeterminant u) = 0)
    (haniso : DiagonalAnisotropic (diagonalUnitCoefficients u)) :
    DiagonalRepresents
        (diagonalUnitCoefficients (heClassicLemma211Second (K := K) k))
        (diagonalUnitCoefficients
          (Fin.append (standardHyperbolicEndpointTower (K := K) k) u)) ∧
      ¬ DiagonalRepresents
        (diagonalUnitCoefficients (heClassicLemma211First (K := K) k))
        (diagonalUnitCoefficients
          (Fin.append (standardHyperbolicEndpointTower (K := K) k) u)) := by
  let common := standardHyperbolicEndpointTower (K := K) k
  have hcommon : DiagonalRepresents
      (diagonalUnitCoefficients common)
      (diagonalUnitCoefficients common) := diagonalRepresents_refl _
  obtain ⟨hB, hH⟩ := he2022ClassicLemma211iii_ternary u hdet haniso
  constructor
  · simpa [heClassicLemma211Second, common,
      diagonalUnitCoefficients_append] using
      DiagonalRepresents.appendBoth hcommon hB
  · intro hrep
    have htail := DiagonalRepresents.cancel_common_prefix
      (diagonalUnitCoefficients common)
      (diagonalUnitCoefficients (heHuHyperbolicPair (K := K)))
      (diagonalUnitCoefficients u)
      (fun i => Units.ne_zero (common i))
      (fun i => Units.ne_zero (heHuHyperbolicPair (K := K) i))
      (fun i => Units.ne_zero (u i)) (by
        simpa [heClassicLemma211First, common,
          diagonalUnitCoefficients_append] using hrep)
    exact hH htail

end Bong
