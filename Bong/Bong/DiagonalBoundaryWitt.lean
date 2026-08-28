/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.DiagonalLocalClassificationProof
import Bong.Bong.DiagonalRepresentationParityProof
import Bong.Bong.DiagonalRepresentationCons

/-!
# A five-dimensional diagonal Witt splitting lemma

This file packages the field-theoretic calculation used at a strict
boundary in the necessity direction of O'Meara 93:28.  Three explicit
Hilbert-symbol identities split two successive ternary subspaces and show
that a five-dimensional diagonal space represents two hyperbolic pairs.
-/

namespace Bong

open Dyadic

namespace BONG.GoodBONG

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

private def boundaryFiveCycle : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 4, 2, 3]
  invFun := ![0, 1, 3, 4, 2]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

private theorem hilbertSymbol_self_mul_right_eq_neg_right
    (x y : Kˣ) :
    hilbertSymbol K x (x * y) = hilbertSymbol K x (-y) := by
  rw [hilbertSymbol_mul_right, hilbertSymbol_self_eq_neg_one]
  rw [show -y = (-1 : Kˣ) * y by simp, hilbertSymbol_mul_right]

/-- If the negative discriminants of two binary diagonal blocks are
mutually Hilbert-orthogonal and each is Hilbert-orthogonal to the indicated
quotient of the adjoined line, then the resulting quinary diagonal form
represents two copies of `[1,-1]`.

The proof uses the unconditional dyadic classification theorem for the two
ternary replacements; it carries no project-specific classification-law
parameter. -/
theorem diagonalQuinary_represents_twoHyperbolicPairs_of_hilbert
    (A D Z E a : Kˣ)
    (h1 : hilbertSymbol K (-D) (-(a / A)) = 1)
    (h2 : hilbertSymbol K (-E) (-(a / Z)) = 1)
    (h12 : hilbertSymbol K (-D) (-E) = 1) :
    DiagonalRepresents
      (diagonalUnitCoefficients ![(1 : Kˣ), -1, 1, -1])
      (diagonalUnitCoefficients ![A, D / A, Z, E / Z, a]) := by
  let first : Fin 3 → Kˣ := ![A, D / A, a]
  let firstSplit : Fin 3 → Kˣ := ![(1 : Kˣ), -1, -(D * a)]
  let secondBinary : Fin 2 → Kˣ := ![Z, E / Z]
  let second : Fin 3 → Kˣ := ![Z, E / Z, -(D * a)]
  let secondSplit : Fin 3 → Kˣ := ![(1 : Kˣ), -1, D * E * a]
  let pair : Fin 2 → Kˣ := ![(1 : Kˣ), -1]
  let pairs : Fin 4 → Kˣ := ![(1 : Kˣ), -1, 1, -1]
  let target : Fin 5 → Kˣ := ![A, D / A, Z, E / Z, a]
  have hfirstAdjacent :
      hilbertSymbol K (-(first 0 * first 1))
        (-(first 1 * first 2)) = 1 := by
    have heq : hilbertSymbol K (-D) (-(D / A * a)) =
        hilbertSymbol K (-D) (-(a / A)) := by
      rw [show -(D / A * a) = (-D) * (a / A) by
        apply Units.ext
        simp only [Units.val_neg, Units.val_mul,
          Units.val_div_eq_div_val]
        field_simp [Units.ne_zero A]]
      exact hilbertSymbol_self_mul_right_eq_neg_right (-D) (a / A)
    simpa [first] using heq.trans h1
  have hfirstSplitAdjacent :
      hilbertSymbol K (-(firstSplit 0 * firstSplit 1))
        (-(firstSplit 1 * firstSplit 2)) = 1 := by
    simp [firstSplit, hilbertSymbol_one_left]
  have hfirstDet : IsSquare
      (diagonalUnitDeterminant firstSplit *
        diagonalUnitDeterminant first) := by
    refine ⟨D * a, ?_⟩
    simp [firstSplit, first, diagonalUnitDeterminant,
      Fin.prod_univ_three]
  have hfirstHasse : diagonalHasseSymbol K firstSplit =
      diagonalHasseSymbol K first := by
    rw [diagonalHasseSymbol_fin_three_eq_adjacent,
      diagonalHasseSymbol_fin_three_eq_adjacent,
      hfirstSplitAdjacent, hfirstAdjacent]
  have hfirst : DiagonalRepresents
      (diagonalUnitCoefficients firstSplit)
      (diagonalUnitCoefficients first) :=
    DyadicDiagonalClassificationLaws.represents_of_invariants
      firstSplit first hfirstDet hfirstHasse
  have hsecondAdjacent :
      hilbertSymbol K (-(second 0 * second 1))
        (-(second 1 * second 2)) = 1 := by
    have h12' : hilbertSymbol K (-E) (-D) = 1 := by
      rw [hilbertSymbol_comm]
      exact h12
    have hbase : hilbertSymbol K (-E) (D * a / Z) = 1 := by
      rw [show D * a / Z = (-(a / Z)) * (-D) by
        apply Units.ext
        simp only [Units.val_neg, Units.val_mul,
          Units.val_div_eq_div_val]
        field_simp [Units.ne_zero Z],
        hilbertSymbol_mul_right, h2, h12', one_mul]
    have heq : hilbertSymbol K (-E) (-(second 1 * second 2)) =
        hilbertSymbol K (-E) (D * a / Z) := by
      rw [show -(second 1 * second 2) =
          (-E) * (-(D * a / Z)) by
        change -((E / Z) * (-(D * a))) =
          (-E) * (-(D * a / Z))
        apply Units.ext
        simp only [Units.val_neg, Units.val_mul,
          Units.val_div_eq_div_val]
        field_simp [Units.ne_zero Z]]
      simpa using
        (hilbertSymbol_self_mul_right_eq_neg_right
          (-E) (-(D * a / Z)))
    have hfirstArg : -(second 0 * second 1) = -E := by
      change -(Z * (E / Z)) = -E
      apply Units.ext
      simp only [Units.val_neg, Units.val_mul,
        Units.val_div_eq_div_val]
      field_simp [Units.ne_zero Z]
    rw [hfirstArg, heq]
    exact hbase
  have hsecondSplitAdjacent :
      hilbertSymbol K (-(secondSplit 0 * secondSplit 1))
        (-(secondSplit 1 * secondSplit 2)) = 1 := by
    simp [secondSplit, hilbertSymbol_one_left]
  have hsecondDet : IsSquare
      (diagonalUnitDeterminant secondSplit *
        diagonalUnitDeterminant second) := by
    refine ⟨-(D * E * a), ?_⟩
    simp [secondSplit, second, diagonalUnitDeterminant,
      Fin.prod_univ_three]
    ac_rfl
  have hsecondHasse : diagonalHasseSymbol K secondSplit =
      diagonalHasseSymbol K second := by
    rw [diagonalHasseSymbol_fin_three_eq_adjacent,
      diagonalHasseSymbol_fin_three_eq_adjacent,
      hsecondSplitAdjacent, hsecondAdjacent]
  have hsecond : DiagonalRepresents
      (diagonalUnitCoefficients secondSplit)
      (diagonalUnitCoefficients second) :=
    DyadicDiagonalClassificationLaws.represents_of_invariants
      secondSplit second hsecondDet hsecondHasse
  have hrotateTarget : DiagonalRepresents
      (diagonalUnitCoefficients (Fin.append first secondBinary))
      (diagonalUnitCoefficients target) := by
    have h := diagonalRepresents_reindex
      (diagonalUnitCoefficients target) boundaryFiveCycle
    convert h using 1
    funext i
    fin_cases i <;> rfl
  have hfirstExtended : DiagonalRepresents
      (diagonalUnitCoefficients (Fin.append firstSplit secondBinary))
      (diagonalUnitCoefficients (Fin.append first secondBinary)) := by
    have h := diagonalRepresents_append hfirst
      (diagonalUnitCoefficients secondBinary)
    convert h using 1 <;> funext i <;> fin_cases i <;> rfl
  have hfirstInTarget := hfirstExtended.trans hrotateTarget
  have hrotateMiddle : DiagonalRepresents
      (diagonalUnitCoefficients (Fin.append pair second))
      (diagonalUnitCoefficients (Fin.append firstSplit secondBinary)) := by
    have h := diagonalRepresents_reindex
      (diagonalUnitCoefficients (Fin.append firstSplit secondBinary))
      boundaryFiveCycle.symm
    convert h using 1
    funext i
    fin_cases i <;> rfl
  have hsecondExtended : DiagonalRepresents
      (diagonalUnitCoefficients (Fin.append pair secondSplit))
      (diagonalUnitCoefficients (Fin.append pair second)) := by
    have h := diagonalRepresents_cons
      (diagonalRepresents_cons hsecond (-1 : K)) (1 : K)
    convert h using 1 <;> funext i <;> fin_cases i <;> rfl
  have hpairsInSplit : DiagonalRepresents
      (diagonalUnitCoefficients pairs)
      (diagonalUnitCoefficients (Fin.append pair secondSplit)) := by
    have h := DiagonalRepresents.prefixOfLE
      (diagonalUnitCoefficients (Fin.append pair secondSplit))
      (by omega : 4 ≤ 5)
    convert h using 1
    funext i
    fin_cases i <;> rfl
  exact hpairsInSplit.trans
    (hsecondExtended.trans (hrotateMiddle.trans
      (hfirstExtended.trans hrotateTarget)))

/-! ## Reversing a hyperbolic quaternary boundary representation -/

/-- The fixed diagonal presentation of two hyperbolic planes. -/
def twoHyperbolicPairsUnits : Fin 4 → Kˣ :=
  ![(1 : Kˣ), -1, 1, -1]

/-- The determinant of the fixed two-hyperbolic-pair presentation is one. -/
@[simp]
theorem diagonalUnitDeterminant_twoHyperbolicPairsUnits :
    diagonalUnitDeterminant (twoHyperbolicPairsUnits (K := K)) = 1 := by
  simp [twoHyperbolicPairsUnits, diagonalUnitDeterminant,
    Fin.prod_univ_four]

/-- The modified Hasse symbol of two hyperbolic planes. -/
theorem diagonalHasseSymbol_twoHyperbolicPairsUnits :
    diagonalHasseSymbol K (twoHyperbolicPairsUnits (K := K)) =
      hilbertSymbol K (-1) (-1) := by
  let p0 : Fin 0 → Kˣ := fun i ↦ Fin.elim0 i
  let p1 : Fin 1 → Kˣ := ![(1 : Kˣ)]
  let p2 : Fin 2 → Kˣ := ![(1 : Kˣ), -1]
  let p3 : Fin 3 → Kˣ := ![(1 : Kˣ), -1, 1]
  have hp1 : p1 = Fin.snoc p0 1 := by
    funext i
    fin_cases i <;> rfl
  have hp2 : p2 = Fin.snoc p1 (-1) := by
    funext i
    fin_cases i <;> rfl
  have hp3 : p3 = Fin.snoc p2 1 := by
    funext i
    fin_cases i <;> rfl
  have hp4 : twoHyperbolicPairsUnits (K := K) =
      Fin.snoc p3 (-1) := by
    funext i
    fin_cases i <;> rfl
  have hd1 : diagonalUnitDeterminant p1 = 1 := by
    simp [p1, diagonalUnitDeterminant]
  have hd2 : diagonalUnitDeterminant p2 = -1 := by
    simp [p2, diagonalUnitDeterminant, Fin.prod_univ_two]
  have hd3 : diagonalUnitDeterminant p3 = -1 := by
    simp [p3, diagonalUnitDeterminant, Fin.prod_univ_three]
  have hH1 : diagonalHasseSymbol K p1 = 1 := by
    rw [hp1, diagonalHasseSymbol_snoc, diagonalHasseSymbol_zero]
    simp [p0, diagonalUnitDeterminant]
  have hH2 : diagonalHasseSymbol K p2 =
      hilbertSymbol K (-1) (-1) := by
    rw [hp2, diagonalHasseSymbol_snoc, hH1, hd1]
    simp [hilbertSymbol_one_left]
  have hH3 : diagonalHasseSymbol K p3 =
      hilbertSymbol K (-1) (-1) := by
    rw [hp3, diagonalHasseSymbol_snoc, hH2, hd2]
    simp [hilbertSymbol_one_right]
  rw [hp4, diagonalHasseSymbol_snoc, hH3, hd3]
  rw [Int.units_mul_self, one_mul]

/-- O'Meara 93:28, Step 2, field-theoretic Witt maneuver.

If two hyperbolic planes embed in a quaternary form with the negative line
`[-a]` adjoined, then the quaternary form embeds in the two hyperbolic
planes with `[a]` adjoined.  The signs are essential: this is the exact
conversion used after applying Step 1 to the reverse-dual last component. -/
theorem diagonalRankFour_reverseHyperbolicBoundary
    (t : Fin 4 → Kˣ) (a : Kˣ)
    (h : DiagonalRepresents
      (diagonalUnitCoefficients (twoHyperbolicPairsUnits (K := K)))
      (diagonalUnitCoefficients (Fin.snoc t (-a)))) :
    DiagonalRepresents
      (diagonalUnitCoefficients t)
      (diagonalUnitCoefficients
        (Fin.snoc (twoHyperbolicPairsUnits (K := K)) a)) := by
  have hsign :=
    (diagonalCodimensionOneRepresents_iff_sign_eq_one
      (K := K) (twoHyperbolicPairsUnits (K := K))
        (Fin.snoc t (-a))).mp h
  apply (diagonalCodimensionOneRepresents_iff_sign_eq_one
    (K := K) t
      (Fin.snoc (twoHyperbolicPairsUnits (K := K)) a)).mpr
  simp only [diagonalHasseSymbol_snoc,
    diagonalUnitDeterminant_snoc] at hsign ⊢
  rw [diagonalUnitDeterminant_twoHyperbolicPairsUnits,
    diagonalHasseSymbol_twoHyperbolicPairsUnits] at hsign ⊢
  simp only [one_mul, hilbertSymbol_one_left] at hsign ⊢
  simp only [hilbertSymbol_mul_left] at hsign ⊢
  rw [hilbertSymbol_self_eq_neg_one, hilbertSymbol_self_eq_neg_one,
    hilbertSymbol_self_eq_neg_one, hilbertSymbol_self_eq_neg_one] at hsign ⊢
  have hself (x : ℤˣ) : x * x = 1 := Int.units_mul_self x
  rw [show -a = (-1 : Kˣ) * a by simp] at hsign
  simp only [hilbertSymbol_mul_left, hilbertSymbol_mul_right] at hsign
  have haa : hilbertSymbol K a a = hilbertSymbol K a (-1) :=
    hilbertSymbol_self_eq_neg_one a
  rw [haa]
  let HT := diagonalHasseSymbol K t
  let X := hilbertSymbol K (diagonalUnitDeterminant t) (-1)
  let Y := hilbertSymbol K (diagonalUnitDeterminant t) a
  let H0 := hilbertSymbol K (-1) (-1)
  let A0 := hilbertSymbol K a (-1)
  change HT * (X * Y) * (H0 * A0) * H0 * 1 *
      (X * (H0 * A0)) = 1 at hsign
  change H0 * 1 * A0 * HT * Y * A0 = 1
  have hreorder :
      HT * (X * Y) * (H0 * A0) * H0 * 1 *
          (X * (H0 * A0)) =
        (HT * Y * H0) * (X * X) * (A0 * A0) * (H0 * H0) := by
    ac_rfl
  rw [hreorder, hself X, hself A0, hself H0] at hsign
  simp only [mul_one] at hsign
  have hgoal : H0 * 1 * A0 * HT * Y * A0 =
      (HT * Y * H0) * (A0 * A0) := by
    ac_rfl
  rw [hgoal, hself A0, mul_one]
  exact hsign

end BONG.GoodBONG

end Bong
