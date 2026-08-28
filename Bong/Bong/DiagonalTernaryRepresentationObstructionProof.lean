/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.DiagonalTernaryRepresentationObstruction
import Bong.Bong.DiagonalLocalClassificationProof

/-!
# Concrete ternary representation obstruction

This file proves the signed-determinant obstruction used in the rank-three
part of Beli's 2019 representation theorem.  Both directions are obtained
from explicit diagonal splitting, binary isotropy, and the already proved
local diagonal classification chain.
-/

namespace Bong

open Dyadic BONG.GoodBONG

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- A represented nonzero scalar gives a unary diagonal representation. -/
theorem diagonalUnaryRepresents_of_exists_value
    (a : Fin 3 → Kˣ) (b : Kˣ)
    (hvalue : ∃ x : Fin 3 → K,
      diagonalQuadratic (diagonalUnitCoefficients a) x = (b : K)) :
    DiagonalRepresents (fun _ : Fin 1 => (b : K))
      (diagonalUnitCoefficients a) := by
  rcases hvalue with ⟨x, hx⟩
  obtain ⟨c, hsplit, _⟩ :=
    exists_diagonal_split_first (K := K) 2 a b x hx
  have hline : DiagonalRepresents
      (fun _ : Fin 1 => (b : K))
      (diagonalUnitCoefficients (Fin.cons b c)) := by
    convert DiagonalRepresents.prefixOfLE
      (k := 1) (diagonalUnitCoefficients (Fin.cons b c)) (by omega)
    simp [diagonalUnitCoefficients]
  exact hline.trans hsplit

/-- A signed-square binary determinant gives an explicit isotropic vector. -/
theorem diagonalUnitBinary_isotropic_of_signedDeterminantSquare
    (c : Fin 2 → Kˣ)
    (hsquare : IsSquare (-diagonalUnitDeterminant c)) :
    DiagonalIsotropic (diagonalUnitCoefficients c) := by
  rcases hsquare with ⟨s, hs⟩
  let x : Fin 2 → K := ![(c 1 : K), (s : K)]
  have hx : x ≠ 0 := by
    intro hzero
    have h := congrFun hzero 0
    exact Units.ne_zero (c 1) (by simpa [x] using h)
  refine ⟨x, hx, ?_⟩
  have hsval := congrArg Units.val hs
  simp only [Units.val_neg, Units.val_mul] at hsval
  have hsval' : (s : K) ^ 2 = -((c 0 : K) * (c 1 : K)) := by
    rw [pow_two]
    simpa [diagonalUnitDeterminant, Fin.prod_univ_two] using hsval.symm
  simp [diagonalQuadratic, diagonalUnitCoefficients, x, hsval']
  ring

/-- Concrete ternary representation obstruction over a dyadic local field. -/
theorem dyadicTernaryRepresentation_obstruction
    (a : Fin 3 → Kˣ) (b : Kˣ)
    (hnot : ¬ DiagonalRepresents
      (fun _ : Fin 1 => (b : K))
      (diagonalUnitCoefficients a)) :
    DiagonalAnisotropic (diagonalUnitCoefficients a) ∧
      IsSquare ((-1 : Kˣ) * diagonalUnitDeterminant a * b) := by
  have hanisotropic : DiagonalAnisotropic
      (diagonalUnitCoefficients a) := by
    by_contra hnotAnisotropic
    have hisotropic : DiagonalIsotropic
        (diagonalUnitCoefficients a) := by
      by_contra hnotIsotropic
      exact hnotAnisotropic
        ((not_diagonalIsotropic_iff_diagonalAnisotropic
          (diagonalUnitCoefficients a)).mp hnotIsotropic)
    have hvalue := diagonal_exists_value_of_isotropic
      (diagonalUnitCoefficients a)
      (fun i => Units.ne_zero (a i)) hisotropic b
    exact hnot (diagonalUnaryRepresents_of_exists_value a b hvalue)
  have hsquare : IsSquare
      ((-1 : Kˣ) * diagonalUnitDeterminant a * b) := by
    by_contra hnotSquare
    have hnotSquare' :
        ¬ IsSquare (-diagonalUnitDeterminant a * b) := by
      simpa [mul_assoc] using hnotSquare
    have hvalue :=
      diagonalUnitTernary_exists_value_of_not_signedDeterminantSquare
        a b hnotSquare'
    exact hnot (diagonalUnaryRepresents_of_exists_value a b hvalue)
  exact ⟨hanisotropic, hsquare⟩

/-- The converse: a represented line with the exceptional signed determinant
class leaves an isotropic binary complement. -/
theorem dyadicTernaryRepresentation_isotropic_of_represents
    (a : Fin 3 → Kˣ) (b : Kˣ)
    (hrep : DiagonalRepresents
      (fun _ : Fin 1 => (b : K))
      (diagonalUnitCoefficients a))
    (hsquare : IsSquare
      ((-1 : Kˣ) * diagonalUnitDeterminant a * b)) :
    DiagonalIsotropic (diagonalUnitCoefficients a) := by
  rcases hrep with ⟨f, hf, hquadratic⟩
  let e : Fin 1 → K := Pi.basisFun K (Fin 1) 0
  have hvalue : diagonalQuadratic (diagonalUnitCoefficients a) (f e) =
      (b : K) := by
    rw [hquadratic]
    exact DiagonalRepresents.diagonalQuadratic_basisFun
      (fun _ : Fin 1 => (b : K)) 0
  obtain ⟨c, hsplit, _⟩ :=
    exists_diagonal_split_first (K := K) 2 a b (f e) hvalue
  have hsplitDet := DiagonalIsometryInvariantLaws.determinant_square
    (Fin.cons b c) a hsplit
  have hsquare' : IsSquare
      (diagonalUnitDeterminant a * (-b)) := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using hsquare
  have hraw : IsSquare
      (diagonalUnitDeterminant (Fin.cons b c) * (-b)) :=
    isSquare_mul_trans _ (diagonalUnitDeterminant a) _
      hsplitDet hsquare'
  have hb2 : IsSquare (b ^ 2) := ⟨b, pow_two b⟩
  have htailQuotient : IsSquare
      ((diagonalUnitDeterminant (Fin.cons b c) * (-b)) / (b ^ 2)) :=
    hraw.div hb2
  have heq :
      (diagonalUnitDeterminant (Fin.cons b c) * (-b)) / (b ^ 2) =
        -diagonalUnitDeterminant c := by
    rw [diagonalUnitDeterminant_cons]
    apply Units.ext
    simp only [Units.val_div_eq_div_val, Units.val_mul, Units.val_neg,
      Units.val_pow_eq_pow_val]
    field_simp [Units.ne_zero b]
  rw [heq] at htailQuotient
  have htailIso :=
    diagonalUnitBinary_isotropic_of_signedDeterminantSquare c htailQuotient
  have hconsIso : DiagonalIsotropic
      (diagonalUnitCoefficients (Fin.cons b c)) := by
    rcases htailIso with ⟨x, hx, hxzero⟩
    let y : Fin 3 → K := Fin.cons 0 x
    refine ⟨y, ?_, ?_⟩
    · intro hy
      apply hx
      funext i
      have hi := congrFun hy i.succ
      simpa [y] using hi
    · rw [diagonalUnitCoefficients_cons,
        DiagonalRepresents.diagonalQuadratic_cons]
      simpa [y] using hxzero
  exact hsplit.isotropic_of hconsIso

noncomputable instance dyadicTernaryRepresentationObstructionLawsProved :
    DyadicTernaryRepresentationObstructionLaws K where
  obstruction := dyadicTernaryRepresentation_obstruction
  isotropic_of_represents_and_signedDeterminantSquare :=
    dyadicTernaryRepresentation_isotropic_of_represents

example : DyadicTernaryRepresentationObstructionLaws K := inferInstance

end Bong
