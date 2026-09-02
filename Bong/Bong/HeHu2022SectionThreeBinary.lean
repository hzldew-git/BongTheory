/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.HeHu2022SectionThreeSharp
import Bong.Bong.DiagonalLocalClassificationProof
import Bong.Bong.DiagonalIsometryInvariantProof

/-! # He--Hu (2024), Proposition 3.3 -/

namespace Bong

open Dyadic
open BONG.GoodBONG

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The paper's binary space `[1,-c]`, represented by its diagonal units. -/
def heHuBinaryFirst (c : Kˣ) : Fin 2 → Kˣ := ![1, -c]

/-- The paper's binary space `[c#, -c# c]`. -/
noncomputable def heHuBinarySecond (c : Kˣ) (hc : HeHuSharpDomain c) :
    Fin 2 → Kˣ :=
  ![heHuSharp c hc, -(heHuSharp c hc * c)]

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K]
  [DyadicContext K] in
@[simp] theorem diagonalUnitDeterminant_heHuBinaryFirst (c : Kˣ) :
    diagonalUnitDeterminant (heHuBinaryFirst c) = -c := by
  simp [heHuBinaryFirst, diagonalUnitDeterminant, Fin.prod_univ_two]

@[simp]
theorem diagonalUnitDeterminant_heHuBinarySecond
    (c : Kˣ) (hc : HeHuSharpDomain c) :
    diagonalUnitDeterminant (heHuBinarySecond c hc) =
      -(heHuSharp c hc * heHuSharp c hc * c) := by
  simp [heHuBinarySecond, diagonalUnitDeterminant, Fin.prod_univ_two]
  group

/-- The two displayed binaries have the same determinant square class. -/
theorem heHuBinarySecond_determinantSquare_first
    (c : Kˣ) (hc : HeHuSharpDomain c) :
    IsSquare
      (diagonalUnitDeterminant (heHuBinarySecond c hc) *
        diagonalUnitDeterminant (heHuBinaryFirst c)) := by
  refine ⟨heHuSharp c hc * c, ?_⟩
  simp only [diagonalUnitDeterminant_heHuBinarySecond,
    diagonalUnitDeterminant_heHuBinaryFirst]
  apply Units.ext
  simp
  ring

/-- The sharp binary is not isometric to `[1,-c]`; equivalently, the latter
does not represent its first line `c#`. -/
theorem heHuBinarySecond_not_represents_first
    (c : Kˣ) (hc : HeHuSharpDomain c) :
    ¬ DiagonalRepresents
      (diagonalUnitCoefficients (heHuBinarySecond c hc))
      (diagonalUnitCoefficients (heHuBinaryFirst c)) := by
  intro hrep
  have hlineOther : DiagonalRepresents
      (fun _ : Fin 1 => (heHuSharp c hc : K))
      (diagonalUnitCoefficients (heHuBinarySecond c hc)) := by
    convert (DiagonalRepresents.prefixSucc
      (diagonalUnitCoefficients (heHuBinarySecond c hc))) using 1
    funext i
    fin_cases i
    rfl
  have hlineFirst := hlineOther.trans hrep
  have hhilbert :=
    (DiagonalRepresents.unary_binary_iff_hilbertSymbol_one
      (K := K) (1 : Kˣ) (-c) (heHuSharp c hc)).mp (by
        convert hlineFirst using 1
        funext i
        fin_cases i <;> rfl)
  have hnegative := (heHu2022Proposition32 c hc).2.2
  have : hilbertSymbol K (heHuSharp c hc) c = 1 := by
    simpa using hhilbert
  rw [hnegative] at this
  norm_num at this

/-- In `ℤˣ`, two elements distinct from the same third element coincide. -/
private theorem intUnit_eq_of_ne_same {x y z : ℤˣ}
    (hx : x ≠ z) (hy : y ≠ z) : x = y := by
  rcases Int.units_eq_one_or z with hz | hz
  · have hxOne : x ≠ 1 := by
      intro h
      exact hx (h.trans hz.symm)
    have hyOne : y ≠ 1 := by
      intro h
      exact hy (h.trans hz.symm)
    have hxNeg := (Int.units_eq_one_or x).resolve_left hxOne
    have hyNeg := (Int.units_eq_one_or y).resolve_left hyOne
    rw [hxNeg, hyNeg]
  · have hxNeg : x ≠ -1 := by
      intro h
      exact hx (h.trans hz.symm)
    have hyNeg : y ≠ -1 := by
      intro h
      exact hy (h.trans hz.symm)
    have hxOne := (Int.units_eq_one_or x).resolve_right hxNeg
    have hyOne := (Int.units_eq_one_or y).resolve_right hyNeg
    rw [hxOne, hyOne]

/-- He--Hu, Proposition 3.3.  Among nondegenerate binary diagonal spaces in
the determinant class of `[1,-c]`, `[c#,-c#c]` is the unique other isometry
class.  Equal-rank diagonal representation is the repository's concrete
isometry relation. -/
theorem heHu2022Proposition33 (c : Kˣ) (hc : HeHuSharpDomain c) :
    ¬ DiagonalRepresents
        (diagonalUnitCoefficients (heHuBinarySecond c hc))
        (diagonalUnitCoefficients (heHuBinaryFirst c)) ∧
      ∀ w : Fin 2 → Kˣ,
        IsSquare
            (diagonalUnitDeterminant w *
              diagonalUnitDeterminant (heHuBinaryFirst c)) →
        ¬ DiagonalRepresents
            (diagonalUnitCoefficients w)
            (diagonalUnitCoefficients (heHuBinaryFirst c)) →
        DiagonalRepresents
            (diagonalUnitCoefficients w)
            (diagonalUnitCoefficients (heHuBinarySecond c hc)) := by
  let first := heHuBinaryFirst c
  let second := heHuBinarySecond c hc
  have hsecondDet : IsSquare
      (diagonalUnitDeterminant second * diagonalUnitDeterminant first) := by
    simpa only [first, second] using
      heHuBinarySecond_determinantSquare_first c hc
  have hsecondNot : ¬ DiagonalRepresents
      (diagonalUnitCoefficients second)
      (diagonalUnitCoefficients first) := by
    simpa only [first, second] using
      heHuBinarySecond_not_represents_first c hc
  refine ⟨hsecondNot, ?_⟩
  intro w hwDet hwNot
  have hsecondHasseNe :
      diagonalHasseSymbol K second ≠ diagonalHasseSymbol K first := by
    intro hhasse
    exact hsecondNot
      (diagonalUnitBinary_represents_of_invariants
        second first hsecondDet hhasse)
  have hwHasseNe :
      diagonalHasseSymbol K w ≠ diagonalHasseSymbol K first := by
    intro hhasse
    exact hwNot
      (diagonalUnitBinary_represents_of_invariants
        w first hwDet hhasse)
  have hwHasse : diagonalHasseSymbol K w =
      diagonalHasseSymbol K second :=
    intUnit_eq_of_ne_same hwHasseNe hsecondHasseNe
  have hfirstSecond : IsSquare
      (diagonalUnitDeterminant first *
        diagonalUnitDeterminant second) := by
    simpa only [mul_comm] using hsecondDet
  have hwSecondDet : IsSquare
      (diagonalUnitDeterminant w *
        diagonalUnitDeterminant second) :=
    isSquare_mul_trans
      (diagonalUnitDeterminant w)
      (diagonalUnitDeterminant first)
      (diagonalUnitDeterminant second) hwDet hfirstSecond
  exact diagonalUnitBinary_represents_of_invariants
    w second hwSecondDet hwHasse

end Bong
