/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma83
import Bong.Bong.Beli2019ComplementaryHilbertChoice
import Bong.Bong.Beli2019UnitDefectSpectrumProof
import Bong.Bong.Beli2009AlphaParityProof
import Bong.Bong.Beli2019EvenClassMultiplier
import Bong.Bong.Beli2019OddPrefixDefect
import Bong.Bong.DiagonalLocalClassificationProof
import Bong.Bong.HilbertDefectChoiceProof
import Bong.Bong.ResidueDefectProductProof

/-!
# The quaternary first-scaling law

This file supplies the local quadratic-space construction in Beli (2019),
Lemma 8.3.  The proof follows the two Hasse-invariant branches in the paper.

The first part is a reusable calculation for a quaternary diagonal form whose
four coefficients are multiplied independently by valuation units.  It turns
the multiplier-prefix defects, the determinant square class, the Hasse
invariant, and one alpha calculation into a
`QuaternaryFirstScalingCertificate`.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- Multiply the four diagonal coefficients by independent square classes. -/
noncomputable def quaternaryMultiplierValues
    (a : GoodBONG q L 4) (m : Fin 4 -> Kˣ) : Fin 4 -> Kˣ :=
  fun i => m i * a.valueUnit i

/-- Product of the multipliers before a cut. -/
noncomputable def quaternaryMultiplierPrefix
    (m : Fin 4 -> Kˣ) (k : Nat) : Kˣ :=
  ∏ j : Fin 4 with j.1 < k, m j

theorem quaternaryMultiplierValues_determinant
    (a : GoodBONG q L 4) (m : Fin 4 -> Kˣ) :
    diagonalUnitDeterminant (a.quaternaryMultiplierValues m) =
      quaternaryMultiplierPrefix m 4 *
        diagonalUnitDeterminant a.valueUnit := by
  classical
  unfold quaternaryMultiplierValues quaternaryMultiplierPrefix
    diagonalUnitDeterminant
  rw [show Finset.univ.filter (fun j : Fin 4 => j.1 < 4) =
      Finset.univ by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact iff_true_intro j.isLt]
  rw [Finset.prod_mul_distrib]

/-- A multiplier prefix is exactly the nonsquare factor in the corresponding
mixed comparison product. -/
theorem quaternaryMultiplier_comparisonPrefixUnit
    (a : GoodBONG q L 4) (X : BONG.OrthogonalBasisData q 4)
    (m : Fin 4 -> Kˣ)
    (hvalues : ∀ i, X.valueUnit i = a.quaternaryMultiplierValues m i)
    (k : Nat) :
    X.comparisonPrefixUnit a k =
      quaternaryMultiplierPrefix m k * (a.prefixProduct k) ^ 2 := by
  classical
  unfold BONG.OrthogonalBasisData.comparisonPrefixUnit
    BONG.OrthogonalBasisData.prefixProduct GoodBONG.prefixProduct
    BONG.prefixProduct
    quaternaryMultiplierPrefix
  rw [Finset.prod_congr rfl (fun j hj => hvalues j)]
  simp only [quaternaryMultiplierValues]
  rw [Finset.prod_mul_distrib]
  unfold GoodBONG.valueUnit
  simp only [pow_two]
  ac_rfl

/-- Pointwise valuation-unit multipliers preserve the four orders. -/
theorem quaternaryMultiplier_sameOrders
    (a : GoodBONG q L 4) (X : BONG.OrthogonalBasisData q 4)
    (m : Fin 4 -> Kˣ)
    (hunit : ∀ i, IsValuationUnit K (m i : K))
    (hvalues : ∀ i, X.valueUnit i = a.quaternaryMultiplierValues m i) :
    X.SameOrders a := by
  intro i
  have hmOrder : ordUnit K (m i) = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K (m i)).1 (hunit i)
  change ordUnit K (X.valueUnit i) = a.order i
  rw [hvalues i]
  unfold quaternaryMultiplierValues
  rw [ordUnit_mul, hmOrder, zero_add]
  exact a.toBONG.order_eq_ordUnit i |>.symm.trans rfl

/-- The mixed-prefix defect bounds reduce to the defects of the multiplier
prefixes. -/
theorem quaternaryMultiplier_prefixDefectBounds
    [QuadraticDefectLaws K]
    (a : GoodBONG q L 4) (X : BONG.OrthogonalBasisData q 4)
    (m : Fin 4 -> Kˣ)
    (hvalues : ∀ i, X.valueUnit i = a.quaternaryMultiplierValues m i)
    (hprefix : ∀ i : Fin 3,
      (a.alphaValue i : WithTop ℚ) ≤
        defectOrder (K := K) (quaternaryMultiplierPrefix m (i.1 + 1))) :
    X.PrefixDefectBounds a := by
  intro i
  change (a.alphaValue i : WithTop ℚ) ≤
    X.comparisonPrefixDefect a (i.1 + 1)
  unfold BONG.OrthogonalBasisData.comparisonPrefixDefect
  rw [a.quaternaryMultiplier_comparisonPrefixUnit X m hvalues,
    defectOrder_mul_square]
  exact hprefix i

/-- A square total multiplier gives the endpoint square condition. -/
theorem quaternaryMultiplier_fullComparisonSquare
    (a : GoodBONG q L 4) (X : BONG.OrthogonalBasisData q 4)
    (m : Fin 4 -> Kˣ)
    (hvalues : ∀ i, X.valueUnit i = a.quaternaryMultiplierValues m i)
    (hfull : IsSquare (quaternaryMultiplierPrefix m 4)) :
    IsSquare (X.comparisonPrefixUnit a 4) := by
  rw [a.quaternaryMultiplier_comparisonPrefixUnit X m hvalues]
  rcases hfull with ⟨s, hs⟩
  refine ⟨s * a.prefixProduct 4, ?_⟩
  rw [hs]
  simp only [pow_two]
  ac_rfl

/-- The determinant comparison required by local diagonal classification is
automatic from a square total multiplier. -/
theorem quaternaryMultiplier_determinantSquare
    (a : GoodBONG q L 4) (m : Fin 4 -> Kˣ)
    (hfull : IsSquare (quaternaryMultiplierPrefix m 4)) :
    IsSquare
      (diagonalUnitDeterminant (a.quaternaryMultiplierValues m) *
        diagonalUnitDeterminant a.valueUnit) := by
  rw [a.quaternaryMultiplierValues_determinant m]
  rcases hfull with ⟨s, hs⟩
  refine ⟨s * diagonalUnitDeterminant a.valueUnit, ?_⟩
  rw [hs]
  ac_rfl

/-- Local diagonal classification realizes any multiplier family with the
correct Hasse invariant. -/
theorem exists_quaternaryMultiplierOrthogonalBasis
    [HilbertSymbolLaws K] [DyadicDiagonalClassificationLaws K]
    (a : GoodBONG q L 4) (m : Fin 4 -> Kˣ)
    (hfull : IsSquare (quaternaryMultiplierPrefix m 4))
    (hhasse :
      diagonalHasseSymbol K (a.quaternaryMultiplierValues m) =
        diagonalHasseSymbol K a.valueUnit) :
    ∃ X : BONG.OrthogonalBasisData q 4,
      ∀ i, X.valueUnit i = a.quaternaryMultiplierValues m i := by
  have hrep : DiagonalRepresents
      (diagonalUnitCoefficients (a.quaternaryMultiplierValues m))
      (diagonalUnitCoefficients a.valueUnit) :=
    DyadicDiagonalClassificationLaws.represents_of_invariants
      (a.quaternaryMultiplierValues m) a.valueUnit
      (a.quaternaryMultiplier_determinantSquare m hfull) hhasse
  exact DiagonalRepresents.exists_orthogonalBasisData a
    (a.quaternaryMultiplierValues m) hrep

end BONG.GoodBONG

namespace QuaternaryHasse

open BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

theorem diagonalUnitDeterminant_append_proved
    {m n : Nat} (a : Fin m -> Kˣ) (b : Fin n -> Kˣ) :
    diagonalUnitDeterminant (Fin.append a b) =
      diagonalUnitDeterminant a * diagonalUnitDeterminant b := by
  unfold diagonalUnitDeterminant
  rw [Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right]

/-- Orthogonal-sum formula for two diagonal coefficient families. -/
theorem diagonalHasseSymbol_append_proved
    [HilbertSymbolLaws K]
    {m n : Nat} (a : Fin m -> Kˣ) (b : Fin n -> Kˣ) :
    diagonalHasseSymbol K (Fin.append a b) =
      diagonalHasseSymbol K a *
        hilbertSymbol K (diagonalUnitDeterminant a)
          (diagonalUnitDeterminant b) *
        diagonalHasseSymbol K b := by
  induction n with
  | zero =>
      have happ : Fin.append a b = a := by
        funext i
        simpa using Fin.append_left a b i
      rw [happ]
      simp [diagonalUnitDeterminant]
  | succ n ih =>
      let b0 : Fin n -> Kˣ := Fin.init b
      let d : Kˣ := b (Fin.last n)
      have hb : b = Fin.snoc b0 d := (Fin.snoc_init_self b).symm
      rw [hb, Fin.append_snoc, diagonalHasseSymbol_snoc,
        diagonalHasseSymbol_snoc, ih]
      rw [diagonalUnitDeterminant_append_proved,
        diagonalUnitDeterminant_snoc,
        hilbertSymbol_mul_left, hilbertSymbol_mul_right]
      ac_rfl

/-- Scaling both coefficients of a binary diagonal form changes Beli's
Hasse symbol by `(eta,-det)`. -/
theorem diagonalHasseSymbol_fin_two_scale
    [HilbertSymbolLaws K]
    (c : Fin 2 -> Kˣ) (eta : Kˣ) :
    diagonalHasseSymbol K (fun i => eta * c i) =
      hilbertSymbol K eta (-diagonalUnitDeterminant c) *
        diagonalHasseSymbol K c := by
  rw [diagonalHasseSymbol_fin_two_eq_det_cross,
    diagonalHasseSymbol_fin_two_eq_det_cross]
  have hdet :
      diagonalUnitDeterminant (fun i => eta * c i) =
        diagonalUnitDeterminant c * eta ^ 2 := by
    apply Units.ext
    simp only [diagonalUnitDeterminant, Fin.prod_univ_two,
      Units.val_mul, Units.val_pow_eq_pow_val]
    ring
  rw [hdet, hilbertSymbol_mul_square_left]
  change
    hilbertSymbol K (diagonalUnitDeterminant c) (-1) *
        hilbertSymbol K (eta * c 0) (eta * c 1) = _
  rw [hilbertSymbol_mul_left, hilbertSymbol_mul_right,
    hilbertSymbol_mul_right, hilbertSymbol_comm K (c 0) eta,
    hilbertSymbol_self_eq_neg_one]
  rw [show -diagonalUnitDeterminant c =
      (-1 : Kˣ) * c 0 * c 1 by
    apply Units.ext
    simp [diagonalUnitDeterminant, Fin.prod_univ_two]]
  rw [hilbertSymbol_mul_right, hilbertSymbol_mul_right]
  ac_rfl

/-- The first and last binary halves of a quaternary coefficient family. -/
def head (c : Fin 4 -> Kˣ) : Fin 2 -> Kˣ := ![c 0, c 1]

def tail (c : Fin 4 -> Kˣ) : Fin 2 -> Kˣ := ![c 2, c 3]

theorem append_head_tail (c : Fin 4 -> Kˣ) :
    Fin.append (head c) (tail c) = c := by
  funext i
  fin_cases i <;> rfl

theorem determinant_head_mul_tail (c : Fin 4 -> Kˣ) :
    diagonalUnitDeterminant (head c) *
        diagonalUnitDeterminant (tail c) =
      diagonalUnitDeterminant c := by
  apply Units.ext
  simp only [head, tail, diagonalUnitDeterminant, Fin.prod_univ_two,
    Fin.prod_univ_four, Units.val_mul]
  ac_rfl

/-- O'Meara 58:3 in the rank-four diagonal coordinates used in Lemma 8.3. -/
theorem diagonalHasseSymbol_fin_four_scale
    [HilbertSymbolLaws K]
    (c : Fin 4 -> Kˣ) (epsilon : Kˣ) :
    diagonalHasseSymbol K (fun i => epsilon * c i) =
      hilbertSymbol K epsilon (diagonalUnitDeterminant c) *
        diagonalHasseSymbol K c := by
  let scaled : Fin 4 -> Kˣ := fun i => epsilon * c i
  have hscaledAppend :
      scaled = Fin.append (fun i => epsilon * head c i)
        (fun i => epsilon * tail c i) := by
    funext i
    fin_cases i <;> rfl
  have hcAppend : c = Fin.append (head c) (tail c) :=
    (append_head_tail c).symm
  have hcHasse :
      diagonalHasseSymbol K c =
        diagonalHasseSymbol K (Fin.append (head c) (tail c)) :=
    congrArg (diagonalHasseSymbol K) hcAppend
  rw [show (fun i => epsilon * c i) = scaled by rfl,
    hscaledAppend, hcHasse,
    diagonalHasseSymbol_append_proved,
    diagonalHasseSymbol_append_proved,
    diagonalHasseSymbol_fin_two_scale,
    diagonalHasseSymbol_fin_two_scale]
  have hheadDet :
      diagonalUnitDeterminant (fun i => epsilon * head c i) =
        diagonalUnitDeterminant (head c) * epsilon ^ 2 := by
    apply Units.ext
    simp only [diagonalUnitDeterminant, head, Fin.prod_univ_two,
      Units.val_mul, Units.val_pow_eq_pow_val]
    ring
  have htailDet :
      diagonalUnitDeterminant (fun i => epsilon * tail c i) =
        diagonalUnitDeterminant (tail c) * epsilon ^ 2 := by
    apply Units.ext
    simp only [diagonalUnitDeterminant, tail, Fin.prod_univ_two,
      Units.val_mul, Units.val_pow_eq_pow_val]
    ring
  rw [hheadDet, htailDet, hilbertSymbol_mul_square_left,
    hilbertSymbol_mul_square_right]
  have hnegHead :
      hilbertSymbol K epsilon (-diagonalUnitDeterminant (head c)) =
        hilbertSymbol K epsilon (-1) *
          hilbertSymbol K epsilon (diagonalUnitDeterminant (head c)) := by
    rw [show -diagonalUnitDeterminant (head c) =
        (-1 : Kˣ) * diagonalUnitDeterminant (head c) by simp,
      hilbertSymbol_mul_right]
  have hnegTail :
      hilbertSymbol K epsilon (-diagonalUnitDeterminant (tail c)) =
        hilbertSymbol K epsilon (-1) *
          hilbertSymbol K epsilon (diagonalUnitDeterminant (tail c)) := by
    rw [show -diagonalUnitDeterminant (tail c) =
        (-1 : Kˣ) * diagonalUnitDeterminant (tail c) by simp,
      hilbertSymbol_mul_right]
  have hdetPairing :
      hilbertSymbol K epsilon (diagonalUnitDeterminant c) =
        hilbertSymbol K epsilon (diagonalUnitDeterminant (head c)) *
          hilbertSymbol K epsilon (diagonalUnitDeterminant (tail c)) := by
    rw [← determinant_head_mul_tail c, hilbertSymbol_mul_right]
  rw [hnegHead, hnegTail, hdetPairing]
  rcases Int.units_eq_one_or (hilbertSymbol K epsilon (-1)) with
    hminus | hminus <;> simp [hminus] <;> ac_rfl

/-- Scaling only the final binary pair changes the quaternary Hasse symbol
by the Hilbert symbol of that pair's signed determinant. -/
theorem diagonalHasseSymbol_fin_four_scale_last_pair
    [HilbertSymbolLaws K]
    (c : Fin 4 -> Kˣ) (eta : Kˣ) :
    diagonalHasseSymbol K ![c 0, c 1, eta * c 2, eta * c 3] =
      hilbertSymbol K eta (-(c 2 * c 3)) *
        diagonalHasseSymbol K c := by
  let changed : Fin 4 -> Kˣ := ![c 0, c 1, eta * c 2, eta * c 3]
  have hchangedAppend :
      changed = Fin.append (head c) (fun i => eta * tail c i) := by
    funext i
    fin_cases i <;> rfl
  have hcAppend : c = Fin.append (head c) (tail c) :=
    (append_head_tail c).symm
  have hcHasse :
      diagonalHasseSymbol K c =
        diagonalHasseSymbol K (Fin.append (head c) (tail c)) :=
    congrArg (diagonalHasseSymbol K) hcAppend
  rw [show ![c 0, c 1, eta * c 2, eta * c 3] = changed by rfl,
    hchangedAppend, hcHasse,
    diagonalHasseSymbol_append_proved,
    diagonalHasseSymbol_append_proved,
    diagonalHasseSymbol_fin_two_scale]
  have htailDet :
      diagonalUnitDeterminant (fun i => eta * tail c i) =
        diagonalUnitDeterminant (tail c) * eta ^ 2 := by
    apply Units.ext
    simp only [diagonalUnitDeterminant, tail, Fin.prod_univ_two,
      Units.val_mul, Units.val_pow_eq_pow_val]
    ring
  rw [htailDet, hilbertSymbol_mul_square_right]
  have hsignedTail : -diagonalUnitDeterminant (tail c) =
      -(c 2 * c 3) := by
    simp [tail, diagonalUnitDeterminant, Fin.prod_univ_two]
  rw [hsignedTail]
  ac_rfl

end QuaternaryHasse

namespace BONG.OrthogonalBasisData

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {N : Nat}

/-- Every right-defect candidate bounds the alpha of an orthogonal basis. -/
theorem alpha_le_rightDefectCandidate
    (X : OrthogonalBasisData q (N + 2))
    {i j : Fin (N + 1)} (hij : i ≤ j) :
    X.alpha i ≤ X.rightDefectCandidate i j := by
  apply Finset.min'_le
  unfold alphaCandidates
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image,
    Finset.mem_filter, Finset.mem_univ, true_and]
  exact Or.inr (Or.inr ⟨j, hij, rfl⟩)

/-- Orthogonal-basis version of the left-candidate estimate in Lemma 8.6(ii).
It is useful before the prescribed basis has been realized by a lattice. -/
theorem sourceAlpha_le_leftDefectCandidate
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 2)) (X : OrthogonalBasisData q (N + 2))
    (horders : X.SameOrders a) (hprefix : X.PrefixDefectBounds a)
    (hfull : IsSquare (X.comparisonPrefixUnit a (N + 2)))
    (i j : Fin (N + 1)) (hji : j ≤ i) :
    (a.alphaValue i : WithTop ℚ) ≤ X.leftDefectCandidate i j := by
  let coefficient : ℚ := (a.order i.succ - a.order j.succ : Int)
  have hendpoint := a.alphaRightEndpoint_antitone hji
  have hfirstRat :
      a.alphaValue i ≤ coefficient + a.alphaValue j := by
    unfold GoodBONG.alphaRightEndpoint at hendpoint
    dsimp [coefficient]
    push_cast at hendpoint ⊢
    linarith
  have hfirst :
      (a.alphaValue i : WithTop ℚ) ≤
        (coefficient : WithTop ℚ) + (a.alphaValue j : WithTop ℚ) := by
    exact_mod_cast hfirstRat
  have hlocal := X.alpha_le_orderGap_add_adjacentDefect
    a hprefix hfull j
  have hshift := add_le_add_left hlocal (coefficient : WithTop ℚ)
  have hcombined :
      (a.alphaValue i : WithTop ℚ) ≤
        (coefficient : WithTop ℚ) +
          ((((a.orderGap j : Int) : ℚ) : WithTop ℚ) +
            X.adjacentDefect j) := by
    exact hfirst.trans (by
      calc
        (coefficient : WithTop ℚ) + (a.alphaValue j : WithTop ℚ) =
            (a.alphaValue j : WithTop ℚ) + coefficient := add_comm _ _
        _ ≤ ((((a.orderGap j : Int) : ℚ) : WithTop ℚ) +
              X.adjacentDefect j) + coefficient := hshift
        _ = (coefficient : WithTop ℚ) +
              ((((a.orderGap j : Int) : ℚ) : WithTop ℚ) +
                X.adjacentDefect j) := add_comm _ _)
  calc
    (a.alphaValue i : WithTop ℚ) ≤
        (coefficient : WithTop ℚ) +
          ((((a.orderGap j : Int) : ℚ) : WithTop ℚ) +
            X.adjacentDefect j) := hcombined
    _ = X.leftDefectCandidate i j := by
      unfold coefficient GoodBONG.orderGap leftDefectCandidate
      rw [horders i.succ, horders j.castSucc]
      rw [← add_assoc]
      congr 1
      norm_cast
      ring

/-- Orthogonal-basis version of the right-candidate estimate in
Lemma 8.6(ii). -/
theorem sourceAlpha_le_rightDefectCandidate
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 2)) (X : OrthogonalBasisData q (N + 2))
    (horders : X.SameOrders a) (hprefix : X.PrefixDefectBounds a)
    (hfull : IsSquare (X.comparisonPrefixUnit a (N + 2)))
    (i j : Fin (N + 1)) (hij : i ≤ j) :
    (a.alphaValue i : WithTop ℚ) ≤ X.rightDefectCandidate i j := by
  let coefficient : ℚ :=
    (a.order j.castSucc - a.order i.castSucc : Int)
  have hendpoint := a.alphaLeftEndpoint_monotone hij
  have hfirstRat :
      a.alphaValue i ≤ coefficient + a.alphaValue j := by
    unfold GoodBONG.alphaLeftEndpoint at hendpoint
    dsimp [coefficient]
    push_cast at hendpoint ⊢
    linarith
  have hfirst :
      (a.alphaValue i : WithTop ℚ) ≤
        (coefficient : WithTop ℚ) + (a.alphaValue j : WithTop ℚ) := by
    exact_mod_cast hfirstRat
  have hlocal := X.alpha_le_orderGap_add_adjacentDefect
    a hprefix hfull j
  have hshift := add_le_add_left hlocal (coefficient : WithTop ℚ)
  have hcombined :
      (a.alphaValue i : WithTop ℚ) ≤
        (coefficient : WithTop ℚ) +
          ((((a.orderGap j : Int) : ℚ) : WithTop ℚ) +
            X.adjacentDefect j) := by
    exact hfirst.trans (by
      calc
        (coefficient : WithTop ℚ) + (a.alphaValue j : WithTop ℚ) =
            (a.alphaValue j : WithTop ℚ) + coefficient := add_comm _ _
        _ ≤ ((((a.orderGap j : Int) : ℚ) : WithTop ℚ) +
              X.adjacentDefect j) + coefficient := hshift
        _ = (coefficient : WithTop ℚ) +
              ((((a.orderGap j : Int) : ℚ) : WithTop ℚ) +
                X.adjacentDefect j) := add_comm _ _)
  calc
    (a.alphaValue i : WithTop ℚ) ≤
        (coefficient : WithTop ℚ) +
          ((((a.orderGap j : Int) : ℚ) : WithTop ℚ) +
            X.adjacentDefect j) := hcombined
    _ = X.rightDefectCandidate i j := by
      unfold coefficient GoodBONG.orderGap rightDefectCandidate
      rw [horders j.succ, horders i.castSucc]
      rw [← add_assoc]
      congr 1
      norm_cast
      ring

/-- Lemma 8.6(ii), already at the level of a prescribed orthogonal basis. -/
theorem sourceAlphaValue_le
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (N + 2)) (X : OrthogonalBasisData q (N + 2))
    (horders : X.SameOrders a) (hprefix : X.PrefixDefectBounds a)
    (hfull : IsSquare (X.comparisonPrefixUnit a (N + 2)))
    (i : Fin (N + 1)) :
    a.alphaValue i ≤ X.alphaValue i := by
  have htop :
      (a.alphaValue i : WithTop ℚ) ≤ (X.alphaValue i : WithTop ℚ) := by
    rw [X.coe_alphaValue]
    unfold alpha
    apply Finset.le_min'
    intro y hy
    simp only [alphaCandidates, Finset.mem_insert, Finset.mem_union,
      Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    rcases hy with rfl | (⟨j, ⟨hji, rfl⟩⟩ | ⟨j, ⟨hij, rfl⟩⟩)
    · unfold halfGapCandidate
      rw [horders i.succ, horders i.castSucc]
      rw [a.coe_alphaValue]
      exact a.alpha_le_halfGapCandidate i
    · exact X.sourceAlpha_le_leftDefectCandidate
        a horders hprefix hfull i j hji
    · exact X.sourceAlpha_le_rightDefectCandidate
        a horders hprefix hfull i j hij
  exact_mod_cast htop

/-- In the alternating quaternary case, an exact final adjacent defect gives
the reverse inequality needed to identify the first alpha. -/
theorem firstAlphaValue_eq_of_tailAdjacentDefect
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L 4) (X : OrthogonalBasisData q 4)
    (halternating : a.HasQuaternaryAlternatingOrders)
    (horders : X.SameOrders a) (hprefix : X.PrefixDefectBounds a)
    (hfull : IsSquare (X.comparisonPrefixUnit a 4))
    (htail : X.adjacentDefect (2 : Fin 3) =
      (a.alphaValue (1 : Fin 3) : WithTop ℚ)) :
    X.alphaValue (0 : Fin 3) = a.alphaValue (0 : Fin 3) := by
  have hlower : a.alphaValue (0 : Fin 3) ≤
      X.alphaValue (0 : Fin 3) :=
    X.sourceAlphaValue_le a horders hprefix hfull 0
  have hcandidate := X.alpha_le_rightDefectCandidate
    (i := (0 : Fin 3)) (j := (2 : Fin 3)) (by decide)
  have hendpoint :=
    (a.alphaLeftEndpoints_eq_of_quaternaryAlternating halternating).1
  have hcandidateValue :
      X.rightDefectCandidate (0 : Fin 3) (2 : Fin 3) =
        (a.alphaValue (0 : Fin 3) : WithTop ℚ) := by
    unfold rightDefectCandidate
    rw [horders (2 : Fin 3).succ, horders (0 : Fin 3).castSucc,
      htail]
    change
      (((((a.order (3 : Fin 4) - a.order (0 : Fin 4) : Int) : ℚ) :
          WithTop ℚ) + (a.alphaValue (1 : Fin 3) : WithTop ℚ)) =
        (a.alphaValue (0 : Fin 3) : WithTop ℚ))
    rw [← halternating.2]
    unfold GoodBONG.alphaLeftEndpoint at hendpoint
    change
      (a.order (0 : Fin 4) : ℚ) + a.alphaValue (0 : Fin 3) =
        (a.order (1 : Fin 4) : ℚ) + a.alphaValue (1 : Fin 3)
      at hendpoint
    have hrat :
        ((a.order (1 : Fin 4) - a.order (0 : Fin 4) : Int) : ℚ) +
            a.alphaValue (1 : Fin 3) = a.alphaValue (0 : Fin 3) := by
      push_cast
      linarith
    exact_mod_cast hrat
  rw [hcandidateValue] at hcandidate
  have hupper : X.alphaValue (0 : Fin 3) ≤
      a.alphaValue (0 : Fin 3) := by
    rw [← X.coe_alphaValue] at hcandidate
    exact_mod_cast hcandidate
  exact le_antisymm hupper hlower

end BONG.OrthogonalBasisData

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- The finite list of checks which turns a multiplier family into the
ambient-basis certificate of Lemma 8.3. -/
structure QuaternaryMultiplierCertificateInput
    (a : GoodBONG q L 4) (epsilon : Kˣ) (m : Fin 4 -> Kˣ) : Prop where
  firstMultiplier_eq : m (0 : Fin 4) = epsilon
  multiplier_isValuationUnit : ∀ i, IsValuationUnit K (m i : K)
  prefixDefectBounds : ∀ i : Fin 3,
    (a.alphaValue i : WithTop ℚ) ≤
      defectOrder (K := K) (quaternaryMultiplierPrefix m (i.1 + 1))
  totalMultiplierSquare : IsSquare (quaternaryMultiplierPrefix m 4)
  hasse_eq :
    diagonalHasseSymbol K (a.quaternaryMultiplierValues m) =
      diagonalHasseSymbol K a.valueUnit
  firstAlpha_eq : ∀ (X : BONG.OrthogonalBasisData q 4),
    (∀ i, X.valueUnit i = a.quaternaryMultiplierValues m i) ->
      X.alphaValue (0 : Fin 3) = a.alphaValue (0 : Fin 3)

/-- Package the invariant calculation as the exact certificate requested by
`DyadicQuaternaryFirstScalingLaws`. -/
theorem QuaternaryMultiplierCertificateInput.toCertificate
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [DyadicDiagonalClassificationLaws K]
    {a : GoodBONG q L 4} {epsilon : Kˣ} {m : Fin 4 -> Kˣ}
    (D : QuaternaryMultiplierCertificateInput a epsilon m) :
    Nonempty (QuaternaryFirstScalingCertificate a epsilon) := by
  rcases a.exists_quaternaryMultiplierOrthogonalBasis m
      D.totalMultiplierSquare D.hasse_eq with ⟨X, hvalues⟩
  have horders : X.SameOrders a :=
    a.quaternaryMultiplier_sameOrders X m
      D.multiplier_isValuationUnit hvalues
  have hprefix : X.PrefixDefectBounds a :=
    a.quaternaryMultiplier_prefixDefectBounds X m hvalues
      D.prefixDefectBounds
  have hfull : IsSquare (X.comparisonPrefixUnit a 4) :=
    a.quaternaryMultiplier_fullComparisonSquare X m hvalues
      D.totalMultiplierSquare
  refine ⟨{
    basisData := X
    firstValue_eq := ?_
    sameOrders := horders
    prefixDefectBounds := hprefix
    fullComparisonSquare := hfull
    firstAlpha_eq := D.firstAlpha_eq X hvalues
  }⟩
  rw [hvalues (0 : Fin 4)]
  unfold quaternaryMultiplierValues
  rw [D.firstMultiplier_eq]

/-- Uniformly scale all four coefficients. -/
noncomputable def quaternaryUniformMultipliers (epsilon : Kˣ) :
    Fin 4 -> Kˣ := ![epsilon, epsilon, epsilon, epsilon]

@[simp] theorem quaternaryUniformMultipliers_zero (epsilon : Kˣ) :
    quaternaryUniformMultipliers epsilon (0 : Fin 4) = epsilon := rfl

@[simp] theorem quaternaryUniformMultipliers_apply
    (epsilon : Kˣ) (i : Fin 4) :
    quaternaryUniformMultipliers epsilon i = epsilon := by
  fin_cases i <;> rfl

theorem quaternaryUniformMultiplierPrefix_one (epsilon : Kˣ) :
    quaternaryMultiplierPrefix (quaternaryUniformMultipliers epsilon) 1 =
      epsilon := by
  unfold quaternaryMultiplierPrefix
  rw [show Finset.univ.filter (fun j : Fin 4 => j.1 < 1) = {0} by
    decide]
  simp

theorem quaternaryUniformMultiplierPrefix_two (epsilon : Kˣ) :
    quaternaryMultiplierPrefix (quaternaryUniformMultipliers epsilon) 2 =
      epsilon ^ 2 := by
  unfold quaternaryMultiplierPrefix
  rw [show Finset.univ.filter (fun j : Fin 4 => j.1 < 2) = {0, 1} by
    decide]
  simp [pow_two]

theorem quaternaryUniformMultiplierPrefix_three (epsilon : Kˣ) :
    quaternaryMultiplierPrefix (quaternaryUniformMultipliers epsilon) 3 =
      epsilon ^ 3 := by
  unfold quaternaryMultiplierPrefix
  rw [show Finset.univ.filter (fun j : Fin 4 => j.1 < 3) = {0, 1, 2} by
    decide]
  simp [pow_succ]

theorem quaternaryUniformMultiplierPrefix_four (epsilon : Kˣ) :
    quaternaryMultiplierPrefix (quaternaryUniformMultipliers epsilon) 4 =
      (epsilon ^ 2) ^ 2 := by
  unfold quaternaryMultiplierPrefix
  rw [show Finset.univ.filter (fun j : Fin 4 => j.1 < 4) =
      Finset.univ by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact iff_true_intro j.isLt]
  simp only [Fin.prod_univ_four, quaternaryUniformMultipliers_apply]
  simp only [pow_two]
  ac_rfl

/-- Alternating orders identify the first and third alpha values. -/
theorem alpha_zero_eq_alpha_two_of_quaternaryAlternating
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L 4) (h : a.HasQuaternaryAlternatingOrders) :
    a.alphaValue (0 : Fin 3) = a.alphaValue (2 : Fin 3) := by
  have hendpoints :=
    (a.alphaLeftEndpoints_eq_of_quaternaryAlternating h).1.trans
      (a.alphaLeftEndpoints_eq_of_quaternaryAlternating h).2
  unfold alphaLeftEndpoint at hendpoints
  change
    (a.order (0 : Fin 4) : ℚ) + a.alphaValue (0 : Fin 3) =
      (a.order (2 : Fin 4) : ℚ) + a.alphaValue (2 : Fin 3)
    at hendpoints
  rw [← h.1] at hendpoints
  linarith

/-- A uniformly scaled prescribed basis has unchanged adjacent defects. -/
theorem quaternaryUniform_adjacentDefect
    [QuadraticDefectLaws K]
    (a : GoodBONG q L 4) (X : BONG.OrthogonalBasisData q 4)
    (epsilon : Kˣ)
    (hvalues : ∀ i, X.valueUnit i =
      a.quaternaryMultiplierValues (quaternaryUniformMultipliers epsilon) i)
    (j : Fin 3) :
    X.adjacentDefect j = a.adjacentDefect j := by
  unfold BONG.OrthogonalBasisData.adjacentDefect
    BONG.OrthogonalBasisData.adjacentProduct adjacentDefect adjacentProduct
  rw [hvalues j.castSucc, hvalues j.succ]
  have hproduct :
      -(a.quaternaryMultiplierValues
          (quaternaryUniformMultipliers epsilon) j.castSucc *
        a.quaternaryMultiplierValues
          (quaternaryUniformMultipliers epsilon) j.succ) =
        (-(a.valueUnit j.castSucc * a.valueUnit j.succ)) * epsilon ^ 2 := by
    apply Units.ext
    simp only [quaternaryMultiplierValues,
      quaternaryUniformMultipliers_apply,
      Units.val_neg, Units.val_mul, Units.val_pow_eq_pow_val]
    ring
  rw [hproduct, defectOrder_mul_square]

/-- Uniform scaling leaves the first alpha candidate set unchanged. -/
theorem quaternaryUniform_firstAlpha_eq
    [QuadraticDefectLaws K]
    (a : GoodBONG q L 4) (X : BONG.OrthogonalBasisData q 4)
    (epsilon : Kˣ) (hepsilonUnit : IsValuationUnit K (epsilon : K))
    (hvalues : ∀ i, X.valueUnit i =
      a.quaternaryMultiplierValues (quaternaryUniformMultipliers epsilon) i) :
    X.alphaValue (0 : Fin 3) = a.alphaValue (0 : Fin 3) := by
  have hmUnit : ∀ i : Fin 4,
      IsValuationUnit K (quaternaryUniformMultipliers epsilon i : K) := by
    intro i
    fin_cases i <;> exact hepsilonUnit
  have horders := a.quaternaryMultiplier_sameOrders X
    (quaternaryUniformMultipliers epsilon) hmUnit hvalues
  have hadjacent : ∀ j : Fin 3,
      X.adjacentDefect j = a.adjacentDefect j :=
    a.quaternaryUniform_adjacentDefect X epsilon hvalues
  have hhalf : X.halfGapCandidate (0 : Fin 3) =
      a.halfGapCandidate (0 : Fin 3) := by
    unfold BONG.OrthogonalBasisData.halfGapCandidate halfGapCandidate
    rw [horders (0 : Fin 3).succ, horders (0 : Fin 3).castSucc]
  have hleft : X.leftDefectCandidate (0 : Fin 3) =
      a.leftDefectCandidate (0 : Fin 3) := by
    funext j
    unfold BONG.OrthogonalBasisData.leftDefectCandidate leftDefectCandidate
    rw [horders (0 : Fin 3).succ, horders j.castSucc, hadjacent j]
  have hright : X.rightDefectCandidate (0 : Fin 3) =
      a.rightDefectCandidate (0 : Fin 3) := by
    funext j
    unfold BONG.OrthogonalBasisData.rightDefectCandidate rightDefectCandidate
    rw [horders j.succ, horders (0 : Fin 3).castSucc, hadjacent j]
  have hcandidates : X.alphaCandidates (0 : Fin 3) =
      a.alphaCandidates (0 : Fin 3) := by
    unfold BONG.OrthogonalBasisData.alphaCandidates alphaCandidates
    rw [hhalf, hleft, hright]
  apply WithTop.coe_injective
  rw [X.coe_alphaValue, a.coe_alphaValue]
  unfold BONG.OrthogonalBasisData.alpha alpha
  simpa only [hcandidates]

/-- The direct Hasse-compatible uniform scaling supplies the complete
certificate input. -/
theorem quaternaryUniformCertificateInput
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L 4) (halternating : a.HasQuaternaryAlternatingOrders)
    (epsilon : Kˣ) (hepsilonUnit : IsValuationUnit K (epsilon : K))
    (hdefect : (a.alphaValue (0 : Fin 3) : WithTop ℚ) ≤
      defectOrder (K := K) epsilon)
    (hhilbert : hilbertSymbol K epsilon
      (diagonalUnitDeterminant a.valueUnit) = 1) :
    QuaternaryMultiplierCertificateInput a epsilon
      (quaternaryUniformMultipliers epsilon) := by
  refine {
    firstMultiplier_eq := rfl
    multiplier_isValuationUnit := ?_
    prefixDefectBounds := ?_
    totalMultiplierSquare := ?_
    hasse_eq := ?_
    firstAlpha_eq := ?_
  }
  · intro i
    fin_cases i <;> exact hepsilonUnit
  · intro i
    fin_cases i
    · rw [quaternaryUniformMultiplierPrefix_one]
      exact hdefect
    · rw [quaternaryUniformMultiplierPrefix_two]
      rw [defectOrder_eq_top_of_isSquare
        ⟨epsilon, by simp only [pow_two]⟩]
      exact le_top
    · rw [quaternaryUniformMultiplierPrefix_three]
      have hcube : epsilon ^ 3 = epsilon * epsilon ^ 2 := by group
      rw [hcube, defectOrder_mul_square]
      change (a.alphaValue (2 : Fin 3) : WithTop ℚ) ≤
        defectOrder (K := K) epsilon
      rw [← a.alpha_zero_eq_alpha_two_of_quaternaryAlternating
        halternating]
      exact hdefect
  · rw [quaternaryUniformMultiplierPrefix_four]
    exact ⟨epsilon ^ 2, by simp only [pow_two]⟩
  · have hscale :=
      QuaternaryHasse.diagonalHasseSymbol_fin_four_scale
        a.valueUnit epsilon
    have hvalues :
        a.quaternaryMultiplierValues
            (quaternaryUniformMultipliers epsilon) =
          (fun i => epsilon * a.valueUnit i) := by
      funext i
      fin_cases i <;> rfl
    rw [hvalues, hscale, hhilbert, one_mul]
  · intro X hvalues
    exact a.quaternaryUniform_firstAlpha_eq X epsilon hepsilonUnit hvalues

/-- The first and last binary defects both dominate the middle alpha in an
alternating quaternary good BONG. -/
theorem quaternaryAlternating_outerAdjacentDefectBounds
    (a : GoodBONG q L 4) (halternating : a.HasQuaternaryAlternatingOrders) :
    (a.alphaValue (1 : Fin 3) : WithTop ℚ) ≤
        a.adjacentDefect (0 : Fin 3) ∧
      (a.alphaValue (1 : Fin 3) : WithTop ℚ) ≤
        a.adjacentDefect (2 : Fin 3) := by
  constructor
  · have h := a.alpha_le_leftDefectCandidate
      (i := (1 : Fin 3)) (j := (0 : Fin 3)) (by decide)
    rw [← a.coe_alphaValue] at h
    unfold leftDefectCandidate at h
    change (a.alphaValue (1 : Fin 3) : WithTop ℚ) ≤
      (((a.order (2 : Fin 4) - a.order (0 : Fin 4) : Int) : ℚ) :
          WithTop ℚ) + a.adjacentDefect (0 : Fin 3) at h
    rw [halternating.1] at h
    simpa using h
  · have h := a.alpha_le_rightDefectCandidate
      (i := (1 : Fin 3)) (j := (2 : Fin 3)) (by decide)
    rw [← a.coe_alphaValue] at h
    unfold rightDefectCandidate at h
    change (a.alphaValue (1 : Fin 3) : WithTop ℚ) ≤
      (((a.order (3 : Fin 4) - a.order (1 : Fin 4) : Int) : ℚ) :
          WithTop ℚ) + a.adjacentDefect (2 : Fin 3) at h
    rw [halternating.2] at h
    simpa using h

/-- The middle binary defect dominates the first alpha. -/
theorem quaternaryAlternating_middleAdjacentDefectBound
    (a : GoodBONG q L 4) (halternating : a.HasQuaternaryAlternatingOrders) :
    (a.alphaValue (0 : Fin 3) : WithTop ℚ) ≤
      a.adjacentDefect (1 : Fin 3) := by
  have h := a.alpha_le_rightDefectCandidate
    (i := (0 : Fin 3)) (j := (1 : Fin 3)) (by decide)
  rw [← a.coe_alphaValue] at h
  unfold rightDefectCandidate at h
  change (a.alphaValue (0 : Fin 3) : WithTop ℚ) ≤
    (((a.order (2 : Fin 4) - a.order (0 : Fin 4) : Int) : ℚ) :
        WithTop ℚ) + a.adjacentDefect (1 : Fin 3) at h
  rw [halternating.1] at h
  simpa using h

/-- The determinant defect is bounded below by the middle alpha. -/
theorem quaternaryAlternating_determinantDefectBound
    [QuadraticDefectLaws K]
    (a : GoodBONG q L 4) (halternating : a.HasQuaternaryAlternatingOrders) :
    (a.alphaValue (1 : Fin 3) : WithTop ℚ) ≤
      defectOrder (K := K) (diagonalUnitDeterminant a.valueUnit) := by
  have houter := a.quaternaryAlternating_outerAdjacentDefectBounds
    halternating
  have hproduct := defectOrder_mul_ge_min (K := K)
    (a.adjacentProduct (0 : Fin 3))
    (a.adjacentProduct (2 : Fin 3))
  have hdet :
      a.adjacentProduct (0 : Fin 3) *
          a.adjacentProduct (2 : Fin 3) =
        diagonalUnitDeterminant a.valueUnit := by
    unfold adjacentProduct diagonalUnitDeterminant
    simp only [Fin.prod_univ_four]
    change (-(a.valueUnit (0 : Fin 4) * a.valueUnit (1 : Fin 4))) *
        (-(a.valueUnit (2 : Fin 4) * a.valueUnit (3 : Fin 4))) =
      a.valueUnit (0 : Fin 4) * a.valueUnit (1 : Fin 4) *
        a.valueUnit (2 : Fin 4) * a.valueUnit (3 : Fin 4)
    rw [neg_mul_neg]
    ac_rfl
  rw [hdet] at hproduct
  exact (le_min houter.1 houter.2).trans hproduct

/-- Alternating orders make the determinant square class have even
valuation. -/
theorem quaternaryAlternating_determinantOrder_even
    (a : GoodBONG q L 4) (halternating : a.HasQuaternaryAlternatingOrders) :
    Even (ordUnit K (diagonalUnitDeterminant a.valueUnit)) := by
  refine ⟨a.order (0 : Fin 4) + a.order (1 : Fin 4), ?_⟩
  simp only [diagonalUnitDeterminant, Fin.prod_univ_four,
    ordUnit_mul]
  change ordUnit K (a.toBONG.valueUnit (0 : Fin 4)) +
      ordUnit K (a.toBONG.valueUnit (1 : Fin 4)) +
      ordUnit K (a.toBONG.valueUnit (2 : Fin 4)) +
      ordUnit K (a.toBONG.valueUnit (3 : Fin 4)) =
    a.order (0 : Fin 4) + a.order (1 : Fin 4) +
      (a.order (0 : Fin 4) + a.order (1 : Fin 4))
  rw [← a.toBONG.order_eq_ordUnit (0 : Fin 4),
    ← a.toBONG.order_eq_ordUnit (1 : Fin 4),
    ← a.toBONG.order_eq_ordUnit (2 : Fin 4),
    ← a.toBONG.order_eq_ordUnit (3 : Fin 4)]
  change a.toBONG.order (0 : Fin 4) + a.toBONG.order (1 : Fin 4) +
      a.toBONG.order (2 : Fin 4) + a.toBONG.order (3 : Fin 4) =
    a.toBONG.order (0 : Fin 4) + a.toBONG.order (1 : Fin 4) +
      (a.toBONG.order (0 : Fin 4) + a.toBONG.order (1 : Fin 4))
  have h02 : a.toBONG.order (0 : Fin 4) =
      a.toBONG.order (2 : Fin 4) := halternating.1
  have h13 : a.toBONG.order (1 : Fin 4) =
      a.toBONG.order (3 : Fin 4) := halternating.2
  rw [← h02, ← h13]
  ring

/-- Property P6 at the first alternating return. -/
theorem quaternaryAlternating_alphaSum_le_twoE
    (a : GoodBONG q L 4) (halternating : a.HasQuaternaryAlternatingOrders) :
    a.alphaValue (0 : Fin 3) + a.alphaValue (1 : Fin 3) ≤
      2 * (ramificationIndex K : ℚ) := by
  exact a.alpha_p6 (0 : Fin 3) (by omega) halternating.1

/-- The two consecutive order gaps in the first alternating triple are
opposites. -/
theorem quaternaryAlternating_orderGap_one_eq_neg_zero
    (a : GoodBONG q L 4) (halternating : a.HasQuaternaryAlternatingOrders) :
    a.orderGap (1 : Fin 3) = -a.orderGap (0 : Fin 3) := by
  unfold orderGap
  change a.order (2 : Fin 4) - a.order (1 : Fin 4) =
    -(a.order (1 : Fin 4) - a.order (0 : Fin 4))
  rw [halternating.1]
  ring

/-- Hence the first order gap is even. -/
theorem quaternaryAlternating_orderGap_zero_even
    (a : GoodBONG q L 4) (halternating : a.HasQuaternaryAlternatingOrders) :
    Even (a.orderGap (0 : Fin 3)) := by
  by_cases hnonpositive : a.orderGap (0 : Fin 3) ≤ 0
  · exact a.orderGap_even_of_nonpositive (0 : Fin 3) hnonpositive
  · have hsecondNonpositive : a.orderGap (1 : Fin 3) ≤ 0 := by
      rw [a.quaternaryAlternating_orderGap_one_eq_neg_zero halternating]
      omega
    have hsecondEven :=
      a.orderGap_even_of_nonpositive (1 : Fin 3) hsecondNonpositive
    rw [a.quaternaryAlternating_orderGap_one_eq_neg_zero halternating]
      at hsecondEven
    simpa using hsecondEven.neg

/-- Equality of the first two left endpoints gives the alpha-shift formula
used for parity transfer. -/
theorem quaternaryAlternating_alpha_one_eq
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L 4) (halternating : a.HasQuaternaryAlternatingOrders) :
    a.alphaValue (1 : Fin 3) =
      ((-a.orderGap (0 : Fin 3) : Int) : ℚ) +
        a.alphaValue (0 : Fin 3) := by
  have hendpoint :=
    (a.alphaLeftEndpoints_eq_of_quaternaryAlternating halternating).1
  unfold alphaLeftEndpoint at hendpoint
  change (a.order (0 : Fin 4) : ℚ) + a.alphaValue (0 : Fin 3) =
    (a.order (1 : Fin 4) : ℚ) + a.alphaValue (1 : Fin 3) at hendpoint
  unfold orderGap
  change a.alphaValue (1 : Fin 3) =
    ((-(a.order (1 : Fin 4) - a.order (0 : Fin 4) : Int) : Int) : ℚ) +
      a.alphaValue (0 : Fin 3)
  push_cast at hendpoint ⊢
  linarith

/-- An odd rational integer which is nonnegative is positive. -/
theorem oddRationalInteger_pos_of_nonnegative {x : ℚ}
    (hodd : IsOddRationalInteger x) (hnonnegative : 0 ≤ x) : 0 < x := by
  rcases hodd with ⟨z, hzOdd, rfl⟩
  have hzNonnegative : 0 ≤ z := by exact_mod_cast hnonnegative
  rcases hzOdd with ⟨k, hk⟩
  have hzPositive : 0 < z := by omega
  exact_mod_cast hzPositive

/-- The arithmetic package forced by the Hasse-changing branch of Lemma
8.3. -/
structure QuaternaryNegativeScaleAlphaData
    (a : GoodBONG q L 4) : Prop where
  first_odd : IsOddRationalInteger (a.alphaValue (0 : Fin 3))
  second_odd : IsOddRationalInteger (a.alphaValue (1 : Fin 3))
  first_pos : 0 < a.alphaValue (0 : Fin 3)
  second_pos : 0 < a.alphaValue (1 : Fin 3)
  first_lt_twoE : a.alphaValue (0 : Fin 3) <
    2 * (ramificationIndex K : ℚ)
  second_lt_twoE : a.alphaValue (1 : Fin 3) <
    2 * (ramificationIndex K : ℚ)

/-- If uniform scaling reverses the Hasse invariant, both relevant alpha
values are positive odd integers strictly below the dyadic endpoint.  This
is the formal version of Beli's argument at pp. 7483--7492 of the v2 source.
-/
theorem quaternaryNegativeScale_alphaData
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [UnitQuadraticDefectParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L 4) (halternating : a.HasQuaternaryAlternatingOrders)
    (epsilon : Kˣ) (hepsilonUnit : IsValuationUnit K (epsilon : K))
    (hdefect : (a.alphaValue (0 : Fin 3) : WithTop ℚ) ≤
      defectOrder (K := K) epsilon)
    (hhilbert : hilbertSymbol K epsilon
      (diagonalUnitDeterminant a.valueUnit) = -1) :
    QuaternaryNegativeScaleAlphaData a := by
  have hdetLower :=
    a.quaternaryAlternating_determinantDefectBound halternating
  have hdefectSumUpper :
      defectOrder (K := K) epsilon +
          defectOrder (K := K) (diagonalUnitDeterminant a.valueUnit) ≤
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
    by_contra hnot
    have hstrict :
        (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
          defectOrder (K := K) epsilon +
            defectOrder (K := K)
              (diagonalUnitDeterminant a.valueUnit) :=
      lt_of_not_ge hnot
    have hone :=
      hilbertSymbol_eq_one_of_defectOrder_add_gt_two_mul_e hstrict
    rw [hhilbert] at hone
    norm_num at hone
  have hfirstOdd :
      IsOddRationalInteger (a.alphaValue (0 : Fin 3)) := by
    by_contra hnotOdd
    have hhalf : a.alphaValue (0 : Fin 3) =
        a.halfGapValue (0 : Fin 3) := by
      by_contra hnotHalf
      exact hnotOdd (a.beli2009Lemma27_iv (0 : Fin 3) hnotHalf)
    have hendpoint :=
      (a.alphaLeftEndpoints_eq_of_quaternaryAlternating halternating).1
    unfold alphaLeftEndpoint at hendpoint
    change (a.order (0 : Fin 4) : ℚ) +
        a.alphaValue (0 : Fin 3) =
      (a.order (1 : Fin 4) : ℚ) +
        a.alphaValue (1 : Fin 3) at hendpoint
    unfold halfGapValue orderGap at hhalf
    change a.alphaValue (0 : Fin 3) =
      ((a.order (1 : Fin 4) - a.order (0 : Fin 4) : Int) : ℚ) / 2 +
        (ramificationIndex K : ℚ) at hhalf
    have halphaSum :
        a.alphaValue (0 : Fin 3) + a.alphaValue (1 : Fin 3) =
          2 * (ramificationIndex K : ℚ) := by
      push_cast at hendpoint hhalf ⊢
      linarith
    have halphaSumTop :
        (a.alphaValue (0 : Fin 3) : WithTop ℚ) +
            (a.alphaValue (1 : Fin 3) : WithTop ℚ) =
          (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
      exact_mod_cast halphaSum
    have hepsilonUpperForm :
        defectOrder (K := K) epsilon +
            (a.alphaValue (1 : Fin 3) : WithTop ℚ) ≤
          (a.alphaValue (0 : Fin 3) : WithTop ℚ) +
            (a.alphaValue (1 : Fin 3) : WithTop ℚ) := by
      calc
        defectOrder (K := K) epsilon +
              (a.alphaValue (1 : Fin 3) : WithTop ℚ) ≤
            defectOrder (K := K) epsilon +
              defectOrder (K := K)
                (diagonalUnitDeterminant a.valueUnit) := by
                  gcongr
        _ ≤ (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) :=
          hdefectSumUpper
        _ = (a.alphaValue (0 : Fin 3) : WithTop ℚ) +
            (a.alphaValue (1 : Fin 3) : WithTop ℚ) :=
          halphaSumTop.symm
    have hepsilonUpper :
        defectOrder (K := K) epsilon ≤
          (a.alphaValue (0 : Fin 3) : WithTop ℚ) :=
      (WithTop.add_le_add_iff_right WithTop.coe_ne_top).mp
        hepsilonUpperForm
    have hepsilonDefect :
        defectOrder (K := K) epsilon =
          (a.alphaValue (0 : Fin 3) : WithTop ℚ) :=
      le_antisymm hepsilonUpper hdefect
    have hdetUpperForm :
        (a.alphaValue (0 : Fin 3) : WithTop ℚ) +
            defectOrder (K := K)
              (diagonalUnitDeterminant a.valueUnit) ≤
          (a.alphaValue (0 : Fin 3) : WithTop ℚ) +
            (a.alphaValue (1 : Fin 3) : WithTop ℚ) := by
      calc
        (a.alphaValue (0 : Fin 3) : WithTop ℚ) +
              defectOrder (K := K)
                (diagonalUnitDeterminant a.valueUnit) ≤
            defectOrder (K := K) epsilon +
              defectOrder (K := K)
                (diagonalUnitDeterminant a.valueUnit) := by
                  gcongr
        _ ≤ (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) :=
          hdefectSumUpper
        _ = (a.alphaValue (0 : Fin 3) : WithTop ℚ) +
            (a.alphaValue (1 : Fin 3) : WithTop ℚ) :=
          halphaSumTop.symm
    have hdetUpper :
        defectOrder (K := K) (diagonalUnitDeterminant a.valueUnit) ≤
          (a.alphaValue (1 : Fin 3) : WithTop ℚ) :=
      (WithTop.add_le_add_iff_left WithTop.coe_ne_top).mp hdetUpperForm
    have hdetDefect :
        defectOrder (K := K) (diagonalUnitDeterminant a.valueUnit) =
          (a.alphaValue (1 : Fin 3) : WithTop ℚ) :=
      le_antisymm hdetUpper hdetLower
    have hepsilonOrder : ordUnit K epsilon = 0 :=
      (isValuationUnit_iff_ordUnit_eq_zero K epsilon).1 hepsilonUnit
    have hepsilonEven : Even (ordUnit K epsilon) := by
      rw [hepsilonOrder]
      exact ⟨0, by simp⟩
    have hfirstNotLt : ¬ a.alphaValue (0 : Fin 3) <
        2 * (ramificationIndex K : ℚ) := by
      intro hlt
      exact hnotOdd
        (isOddRationalInteger_of_even_ordUnit_of_defectOrder_eq
          epsilon (a.alphaValue (0 : Fin 3)) hepsilonEven
          hepsilonDefect hlt)
    have hfirstGe : 2 * (ramificationIndex K : ℚ) ≤
        a.alphaValue (0 : Fin 3) := le_of_not_gt hfirstNotLt
    have hsecondNonnegative := (a.beli2009Lemma27_i (1 : Fin 3)).1
    have hfirstLe : a.alphaValue (0 : Fin 3) ≤
        2 * (ramificationIndex K : ℚ) := by linarith
    have hfirstEndpoint : a.alphaValue (0 : Fin 3) =
        2 * (ramificationIndex K : ℚ) :=
      le_antisymm hfirstLe hfirstGe
    have hsecondZero : a.alphaValue (1 : Fin 3) = 0 := by
      linarith
    have hrawZero :
        defectOrder (K := K) (diagonalUnitDeterminant a.valueUnit) = 0 := by
      rw [hdetDefect, hsecondZero]
      rfl
    have hquadraticZero :
        quadraticDefect K (diagonalUnitDeterminant a.valueUnit) = 0 :=
      quadraticDefect_eq_zero_of_defectOrder_eq_zero
        (diagonalUnitDeterminant a.valueUnit) hrawZero
    exact (quadraticDefect_ne_zero_of_even_ordUnit
      (diagonalUnitDeterminant a.valueUnit)
      (a.quaternaryAlternating_determinantOrder_even halternating)
      hquadraticZero).elim
  have hsecondOdd :
      IsOddRationalInteger (a.alphaValue (1 : Fin 3)) := by
    rw [a.quaternaryAlternating_alpha_one_eq halternating]
    exact oddRationalInteger_add_evenInteger hfirstOdd
      (a.quaternaryAlternating_orderGap_zero_even halternating).neg
  have hfirstNonnegative := (a.beli2009Lemma27_i (0 : Fin 3)).1
  have hsecondNonnegative := (a.beli2009Lemma27_i (1 : Fin 3)).1
  have hfirstPositive :=
    oddRationalInteger_pos_of_nonnegative hfirstOdd hfirstNonnegative
  have hsecondPositive :=
    oddRationalInteger_pos_of_nonnegative hsecondOdd hsecondNonnegative
  have hsum := a.quaternaryAlternating_alphaSum_le_twoE halternating
  exact {
    first_odd := hfirstOdd
    second_odd := hsecondOdd
    first_pos := hfirstPositive
    second_pos := hsecondPositive
    first_lt_twoE := by linarith
    second_lt_twoE := by linarith
  }

/-- Explicit formulas for the four possible multiplier prefixes. -/
theorem quaternaryMultiplierPrefix_eq_one (m : Fin 4 → Kˣ) :
    quaternaryMultiplierPrefix m 1 = m 0 := by
  unfold quaternaryMultiplierPrefix
  rw [show Finset.univ.filter (fun j : Fin 4 => j.1 < 1) = {0} by
    decide]
  simp

theorem quaternaryMultiplierPrefix_eq_two (m : Fin 4 → Kˣ) :
    quaternaryMultiplierPrefix m 2 = m 0 * m 1 := by
  unfold quaternaryMultiplierPrefix
  rw [show Finset.univ.filter (fun j : Fin 4 => j.1 < 2) = {0, 1} by
    decide]
  simp

theorem quaternaryMultiplierPrefix_eq_three (m : Fin 4 → Kˣ) :
    quaternaryMultiplierPrefix m 3 = m 0 * m 1 * m 2 := by
  unfold quaternaryMultiplierPrefix
  rw [show Finset.univ.filter (fun j : Fin 4 => j.1 < 3) = {0, 1, 2} by
    decide]
  simp
  ac_rfl

theorem quaternaryMultiplierPrefix_eq_four (m : Fin 4 → Kˣ) :
    quaternaryMultiplierPrefix m 4 = m 0 * m 1 * m 2 * m 3 := by
  unfold quaternaryMultiplierPrefix
  rw [show Finset.univ.filter (fun j : Fin 4 => j.1 < 4) =
      Finset.univ by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact iff_true_intro j.isLt]
  exact Fin.prod_univ_four _

/-- The adjacent defect of a prescribed multiplier presentation is the
defect of the original adjacent product times the two local multipliers. -/
theorem quaternaryMultiplier_adjacentDefect
    [QuadraticDefectLaws K]
    (a : GoodBONG q L 4) (X : BONG.OrthogonalBasisData q 4)
    (m : Fin 4 → Kˣ)
    (hvalues : ∀ i, X.valueUnit i = a.quaternaryMultiplierValues m i)
    (j : Fin 3) :
    X.adjacentDefect j =
      defectOrder (K := K)
        ((m j.castSucc * m j.succ) * a.adjacentProduct j) := by
  unfold BONG.OrthogonalBasisData.adjacentDefect
    BONG.OrthogonalBasisData.adjacentProduct
    BONG.GoodBONG.adjacentProduct
  rw [hvalues j.castSucc, hvalues j.succ]
  unfold quaternaryMultiplierValues
  congr 1
  apply Units.ext
  simp only [Units.val_neg, Units.val_mul]
  ring

/-- A tail-defect computation supplies the final alpha equality required by
the multiplier certificate. -/
theorem quaternaryMultiplierCertificateInput_of_tail
    [QuadraticDefectLaws K] [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L 4) (halternating : a.HasQuaternaryAlternatingOrders)
    (epsilon : Kˣ) (m : Fin 4 → Kˣ)
    (hfirst : m (0 : Fin 4) = epsilon)
    (hunit : ∀ i, IsValuationUnit K (m i : K))
    (hprefix : ∀ i : Fin 3,
      (a.alphaValue i : WithTop ℚ) ≤
        defectOrder (K := K) (quaternaryMultiplierPrefix m (i.1 + 1)))
    (hfull : IsSquare (quaternaryMultiplierPrefix m 4))
    (hhasse : diagonalHasseSymbol K (a.quaternaryMultiplierValues m) =
      diagonalHasseSymbol K a.valueUnit)
    (htail : ∀ (X : BONG.OrthogonalBasisData q 4),
      (∀ i, X.valueUnit i = a.quaternaryMultiplierValues m i) →
        X.adjacentDefect (2 : Fin 3) =
          (a.alphaValue (1 : Fin 3) : WithTop ℚ)) :
    QuaternaryMultiplierCertificateInput a epsilon m := by
  refine {
    firstMultiplier_eq := hfirst
    multiplier_isValuationUnit := hunit
    prefixDefectBounds := hprefix
    totalMultiplierSquare := hfull
    hasse_eq := hhasse
    firstAlpha_eq := ?_
  }
  intro X hvalues
  have horders := a.quaternaryMultiplier_sameOrders X m hunit hvalues
  have hprefix' :=
    a.quaternaryMultiplier_prefixDefectBounds X m hvalues hprefix
  have hfull' :=
    a.quaternaryMultiplier_fullComparisonSquare X m hvalues hfull
  exact X.firstAlphaValue_eq_of_tailAdjacentDefect a halternating
    horders hprefix' hfull' (htail X hvalues)

/-- A square auxiliary total multiplier does not change the Hilbert pairing
of its determinant with a fixed square class. -/
theorem hilbert_quaternaryMultiplierDeterminant_eq
    [HilbertSymbolLaws K]
    (a : GoodBONG q L 4) (epsilon : Kˣ) (n : Fin 4 → Kˣ)
    (hfull : IsSquare (quaternaryMultiplierPrefix n 4)) :
    hilbertSymbol K epsilon
        (diagonalUnitDeterminant (a.quaternaryMultiplierValues n)) =
      hilbertSymbol K epsilon (diagonalUnitDeterminant a.valueUnit) := by
  rw [a.quaternaryMultiplierValues_determinant n]
  rcases hfull with ⟨s, hs⟩
  rw [hs]
  have hcomm : s * s * diagonalUnitDeterminant a.valueUnit =
      diagonalUnitDeterminant a.valueUnit * s ^ 2 := by
    simp only [pow_two]
    ac_rfl
  rw [hcomm, hilbertSymbol_mul_square_right]

/-- Two unequal signs in `ℤˣ` are negatives of one another. -/
theorem intUnits_eq_neg_of_ne (x y : ℤˣ) (hxy : x ≠ y) : x = -y := by
  rcases Int.units_eq_one_or x with hx | hx <;>
    rcases Int.units_eq_one_or y with hy | hy
  · exact (hxy (hx.trans hy.symm)).elim
  · rw [hx, hy]
    simp
  · rw [hx, hy]
  · exact (hxy (hx.trans hy.symm)).elim

/-- If an auxiliary diagonal presentation has the opposite Hasse sign and
square-equivalent determinant, then uniform scaling by a class pairing
negatively with the original determinant restores the original Hasse sign.
-/
theorem quaternaryUniformAfterAuxiliary_hasse_eq
    [HilbertSymbolLaws K]
    (a : GoodBONG q L 4) (epsilon : Kˣ)
    (n m : Fin 4 → Kˣ)
    (hvalues : a.quaternaryMultiplierValues m =
      (fun i => epsilon * a.quaternaryMultiplierValues n i))
    (hfullAux : IsSquare (quaternaryMultiplierPrefix n 4))
    (hauxiliary :
      diagonalHasseSymbol K (a.quaternaryMultiplierValues n) =
        -diagonalHasseSymbol K a.valueUnit)
    (hepsilon : hilbertSymbol K epsilon
      (diagonalUnitDeterminant a.valueUnit) = -1) :
    diagonalHasseSymbol K (a.quaternaryMultiplierValues m) =
      diagonalHasseSymbol K a.valueUnit := by
  rw [hvalues,
    QuaternaryHasse.diagonalHasseSymbol_fin_four_scale,
    a.hilbert_quaternaryMultiplierDeterminant_eq epsilon n hfullAux,
    hepsilon, hauxiliary]
  simp

/-- Final multipliers in case 1: uniformly scale after changing the last
binary pair. -/
noncomputable def quaternaryLastPairMultipliers
    (epsilon eta : Kˣ) : Fin 4 → Kˣ :=
  ![epsilon, epsilon, epsilon * eta, epsilon * eta]

/-- Final multipliers in the first part of case 2: uniformly scale after
changing the middle binary pair. -/
noncomputable def quaternaryMiddlePairMultipliers
    (epsilon eta : Kˣ) : Fin 4 → Kˣ :=
  ![epsilon, epsilon * eta, epsilon * eta, epsilon]

/-- Final multipliers in the fallback part of case 2. -/
noncomputable def quaternaryMiddleThenLastPairMultipliers
    (epsilon eta theta : Kˣ) : Fin 4 → Kˣ :=
  ![epsilon, epsilon * eta, epsilon * eta * theta,
    epsilon * theta]

@[simp] theorem quaternaryLastPairMultipliers_apply
    (epsilon eta : Kˣ) (i : Fin 4) :
    quaternaryLastPairMultipliers epsilon eta i =
      ![epsilon, epsilon, epsilon * eta, epsilon * eta] i := rfl

@[simp] theorem quaternaryMiddlePairMultipliers_apply
    (epsilon eta : Kˣ) (i : Fin 4) :
    quaternaryMiddlePairMultipliers epsilon eta i =
      ![epsilon, epsilon * eta, epsilon * eta, epsilon] i := rfl

@[simp] theorem quaternaryMiddleThenLastPairMultipliers_apply
    (epsilon eta theta : Kˣ) (i : Fin 4) :
    quaternaryMiddleThenLastPairMultipliers epsilon eta theta i =
      ![epsilon, epsilon * eta, epsilon * eta * theta,
        epsilon * theta] i := rfl

/-- Products of valuation-unit square classes remain valuation units. -/
theorem isValuationUnit_units_mul (x y : Kˣ)
    (hx : IsValuationUnit K (x : K))
    (hy : IsValuationUnit K (y : K)) :
    IsValuationUnit K ((x * y : Kˣ) : K) := by
  apply (isValuationUnit_iff_ordUnit_eq_zero K (x * y)).2
  rw [ordUnit_mul,
    (isValuationUnit_iff_ordUnit_eq_zero K x).1 hx,
    (isValuationUnit_iff_ordUnit_eq_zero K y).1 hy,
    zero_add]

/-- Certificate input for case 1 of Beli's proof, where the original final
binary defect is exactly the middle alpha. -/
theorem quaternaryLastPairCertificateInput
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L 4) (halternating : a.HasQuaternaryAlternatingOrders)
    (epsilon eta : Kˣ)
    (hepsilonUnit : IsValuationUnit K (epsilon : K))
    (hetaUnit : IsValuationUnit K (eta : K))
    (hepsilonDefect : (a.alphaValue (0 : Fin 3) : WithTop ℚ) ≤
      defectOrder (K := K) epsilon)
    (hetaDefect : defectOrder (K := K) eta =
      ((2 * (ramificationIndex K : ℚ) -
        a.alphaValue (1 : Fin 3) : ℚ) : WithTop ℚ))
    (htail : a.adjacentDefect (2 : Fin 3) =
      (a.alphaValue (1 : Fin 3) : WithTop ℚ))
    (hetaHilbert : hilbertSymbol K eta
      (a.adjacentProduct (2 : Fin 3)) = -1)
    (hepsilonHilbert : hilbertSymbol K epsilon
      (diagonalUnitDeterminant a.valueUnit) = -1) :
    QuaternaryMultiplierCertificateInput a epsilon
      (quaternaryLastPairMultipliers epsilon eta) := by
  let m := quaternaryLastPairMultipliers epsilon eta
  let n : Fin 4 → Kˣ := ![1, 1, eta, eta]
  have hetaBoundQ : a.alphaValue (0 : Fin 3) ≤
      2 * (ramificationIndex K : ℚ) -
        a.alphaValue (1 : Fin 3) := by
    have hsum := a.quaternaryAlternating_alphaSum_le_twoE halternating
    linarith
  have hetaBound : (a.alphaValue (0 : Fin 3) : WithTop ℚ) ≤
      defectOrder (K := K) eta := by
    rw [hetaDefect]
    exact_mod_cast hetaBoundQ
  have hunit : ∀ i, IsValuationUnit K (m i : K) := by
    intro i
    fin_cases i
    · exact hepsilonUnit
    · exact hepsilonUnit
    · exact isValuationUnit_units_mul epsilon eta
        hepsilonUnit hetaUnit
    · exact isValuationUnit_units_mul epsilon eta
        hepsilonUnit hetaUnit
  have hprefix : ∀ i : Fin 3,
      (a.alphaValue i : WithTop ℚ) ≤
        defectOrder (K := K)
          (quaternaryMultiplierPrefix m (i.1 + 1)) := by
    intro i
    fin_cases i
    · rw [quaternaryMultiplierPrefix_eq_one]
      exact hepsilonDefect
    · rw [quaternaryMultiplierPrefix_eq_two]
      change (a.alphaValue (1 : Fin 3) : WithTop ℚ) ≤
        defectOrder (K := K) (epsilon * epsilon)
      rw [defectOrder_eq_top_of_isSquare
        ⟨epsilon, by simp only [pow_two]⟩]
      exact le_top
    · rw [quaternaryMultiplierPrefix_eq_three]
      have hp : m 0 * m 1 * m 2 =
          (epsilon * eta) * epsilon ^ 2 := by
        dsimp [m, quaternaryLastPairMultipliers]
        simp only [pow_two]
        ac_rfl
      rw [hp, defectOrder_mul_square]
      change (a.alphaValue (2 : Fin 3) : WithTop ℚ) ≤
        defectOrder (K := K) (epsilon * eta)
      rw [← a.alpha_zero_eq_alpha_two_of_quaternaryAlternating
        halternating]
      exact (le_min hepsilonDefect hetaBound).trans
        (defectOrder_mul_ge_min (K := K) epsilon eta)
  have hfull : IsSquare (quaternaryMultiplierPrefix m 4) := by
    rw [quaternaryMultiplierPrefix_eq_four]
    refine ⟨epsilon ^ 2 * eta, ?_⟩
    dsimp [m, quaternaryLastPairMultipliers]
    simp only [pow_two]
    ac_rfl
  have hauxFull : IsSquare (quaternaryMultiplierPrefix n 4) := by
    rw [quaternaryMultiplierPrefix_eq_four]
    refine ⟨eta, ?_⟩
    dsimp [n]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons, one_mul]
  have hauxValues : a.quaternaryMultiplierValues n =
      ![a.valueUnit 0, a.valueUnit 1,
        eta * a.valueUnit 2, eta * a.valueUnit 3] := by
    funext i
    fin_cases i <;> simp [quaternaryMultiplierValues, n]
  have hsignedTail : -(a.valueUnit (2 : Fin 4) *
        a.valueUnit (3 : Fin 4)) =
      a.adjacentProduct (2 : Fin 3) := by rfl
  have hauxiliary :
      diagonalHasseSymbol K (a.quaternaryMultiplierValues n) =
        -diagonalHasseSymbol K a.valueUnit := by
    rw [hauxValues,
      QuaternaryHasse.diagonalHasseSymbol_fin_four_scale_last_pair,
      hsignedTail, hetaHilbert]
    simp
  have hfinalValues : a.quaternaryMultiplierValues m =
      (fun i => epsilon * a.quaternaryMultiplierValues n i) := by
    funext i
    fin_cases i <;> dsimp [m, n, quaternaryLastPairMultipliers,
      quaternaryMultiplierValues] <;> group
  have hhasse :
      diagonalHasseSymbol K (a.quaternaryMultiplierValues m) =
        diagonalHasseSymbol K a.valueUnit :=
    a.quaternaryUniformAfterAuxiliary_hasse_eq epsilon n m
      hfinalValues hauxFull hauxiliary hepsilonHilbert
  have htailFinal : ∀ (X : BONG.OrthogonalBasisData q 4),
      (∀ i, X.valueUnit i = a.quaternaryMultiplierValues m i) →
        X.adjacentDefect (2 : Fin 3) =
          (a.alphaValue (1 : Fin 3) : WithTop ℚ) := by
    intro X hvalues
    rw [a.quaternaryMultiplier_adjacentDefect X m hvalues]
    change defectOrder (K := K)
      ((m (2 : Fin 4) * m (3 : Fin 4)) *
        a.adjacentProduct (2 : Fin 3)) =
        (a.alphaValue (1 : Fin 3) : WithTop ℚ)
    have hfactor :
        (m (2 : Fin 4) * m (3 : Fin 4)) *
            a.adjacentProduct (2 : Fin 3) =
          a.adjacentProduct (2 : Fin 3) * (epsilon * eta) ^ 2 := by
      dsimp [m, quaternaryLastPairMultipliers]
      simp only [pow_two]
      ac_rfl
    rw [hfactor, defectOrder_mul_square]
    exact htail
  exact a.quaternaryMultiplierCertificateInput_of_tail halternating
    epsilon m rfl hunit hprefix hfull hhasse htailFinal

/-- Certificate input for the direct subcase of case 2, where changing the
middle binary pair already reverses the Hasse invariant. -/
theorem quaternaryMiddlePairCertificateInput
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L 4) (halternating : a.HasQuaternaryAlternatingOrders)
    (epsilon eta : Kˣ)
    (hepsilonUnit : IsValuationUnit K (epsilon : K))
    (hetaUnit : IsValuationUnit K (eta : K))
    (hepsilonDefect : (a.alphaValue (0 : Fin 3) : WithTop ℚ) ≤
      defectOrder (K := K) epsilon)
    (hetaDefect : defectOrder (K := K) eta =
      (a.alphaValue (1 : Fin 3) : WithTop ℚ))
    (htailStrict : (a.alphaValue (1 : Fin 3) : WithTop ℚ) <
      a.adjacentDefect (2 : Fin 3))
    (hauxiliaryNe :
      diagonalHasseSymbol K
          ![a.valueUnit 0, eta * a.valueUnit 1,
            eta * a.valueUnit 2, a.valueUnit 3] ≠
        diagonalHasseSymbol K a.valueUnit)
    (hepsilonHilbert : hilbertSymbol K epsilon
      (diagonalUnitDeterminant a.valueUnit) = -1) :
    QuaternaryMultiplierCertificateInput a epsilon
      (quaternaryMiddlePairMultipliers epsilon eta) := by
  let m := quaternaryMiddlePairMultipliers epsilon eta
  let n : Fin 4 → Kˣ := ![1, eta, eta, 1]
  have hunit : ∀ i, IsValuationUnit K (m i : K) := by
    intro i
    fin_cases i
    · exact hepsilonUnit
    · exact isValuationUnit_units_mul epsilon eta
        hepsilonUnit hetaUnit
    · exact isValuationUnit_units_mul epsilon eta
        hepsilonUnit hetaUnit
    · exact hepsilonUnit
  have hprefix : ∀ i : Fin 3,
      (a.alphaValue i : WithTop ℚ) ≤
        defectOrder (K := K)
          (quaternaryMultiplierPrefix m (i.1 + 1)) := by
    intro i
    fin_cases i
    · rw [quaternaryMultiplierPrefix_eq_one]
      exact hepsilonDefect
    · rw [quaternaryMultiplierPrefix_eq_two]
      have hp : m 0 * m 1 = eta * epsilon ^ 2 := by
        dsimp [m, quaternaryMiddlePairMultipliers]
        simp only [pow_two]
        ac_rfl
      change (a.alphaValue (1 : Fin 3) : WithTop ℚ) ≤
        defectOrder (K := K) (m 0 * m 1)
      rw [hp, defectOrder_mul_square, hetaDefect]
    · rw [quaternaryMultiplierPrefix_eq_three]
      have hp : m 0 * m 1 * m 2 =
          epsilon * (epsilon * eta) ^ 2 := by
        dsimp [m, quaternaryMiddlePairMultipliers]
        simp only [pow_two]
        ac_rfl
      rw [hp, defectOrder_mul_square]
      change (a.alphaValue (2 : Fin 3) : WithTop ℚ) ≤
        defectOrder (K := K) epsilon
      rw [← a.alpha_zero_eq_alpha_two_of_quaternaryAlternating
        halternating]
      exact hepsilonDefect
  have hfull : IsSquare (quaternaryMultiplierPrefix m 4) := by
    rw [quaternaryMultiplierPrefix_eq_four]
    refine ⟨epsilon ^ 2 * eta, ?_⟩
    dsimp [m, quaternaryMiddlePairMultipliers]
    simp only [pow_two]
    ac_rfl
  have hauxFull : IsSquare (quaternaryMultiplierPrefix n 4) := by
    rw [quaternaryMultiplierPrefix_eq_four]
    refine ⟨eta, ?_⟩
    dsimp [n]
    simp
  have hauxValues : a.quaternaryMultiplierValues n =
      ![a.valueUnit 0, eta * a.valueUnit 1,
        eta * a.valueUnit 2, a.valueUnit 3] := by
    funext i
    fin_cases i <;> simp [quaternaryMultiplierValues, n]
  have hauxiliary :
      diagonalHasseSymbol K (a.quaternaryMultiplierValues n) =
        -diagonalHasseSymbol K a.valueUnit := by
    rw [hauxValues]
    exact intUnits_eq_neg_of_ne _ _ hauxiliaryNe
  have hfinalValues : a.quaternaryMultiplierValues m =
      (fun i => epsilon * a.quaternaryMultiplierValues n i) := by
    funext i
    fin_cases i <;> dsimp [m, n, quaternaryMiddlePairMultipliers,
      quaternaryMultiplierValues] <;> group
  have hhasse :
      diagonalHasseSymbol K (a.quaternaryMultiplierValues m) =
        diagonalHasseSymbol K a.valueUnit :=
    a.quaternaryUniformAfterAuxiliary_hasse_eq epsilon n m
      hfinalValues hauxFull hauxiliary hepsilonHilbert
  have htailFinal : ∀ (X : BONG.OrthogonalBasisData q 4),
      (∀ i, X.valueUnit i = a.quaternaryMultiplierValues m i) →
        X.adjacentDefect (2 : Fin 3) =
          (a.alphaValue (1 : Fin 3) : WithTop ℚ) := by
    intro X hvalues
    rw [a.quaternaryMultiplier_adjacentDefect X m hvalues]
    change defectOrder (K := K)
      ((m (2 : Fin 4) * m (3 : Fin 4)) *
        a.adjacentProduct (2 : Fin 3)) =
        (a.alphaValue (1 : Fin 3) : WithTop ℚ)
    have hfactor :
        (m (2 : Fin 4) * m (3 : Fin 4)) *
            a.adjacentProduct (2 : Fin 3) =
          (eta * a.adjacentProduct (2 : Fin 3)) * epsilon ^ 2 := by
      dsimp [m, quaternaryMiddlePairMultipliers]
      simp only [pow_two]
      ac_rfl
    rw [hfactor, defectOrder_mul_square,
      defectOrder_mul_eq_left_of_lt_right
        (hetaDefect ▸ htailStrict), hetaDefect]
  exact a.quaternaryMultiplierCertificateInput_of_tail halternating
    epsilon m rfl hunit hprefix hfull hhasse htailFinal

/-- Certificate input for the fallback subcase of case 2.  A second
last-pair change reverses the Hasse invariant of the Hasse-compatible middle
pair presentation. -/
theorem quaternaryMiddleThenLastPairCertificateInput
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L 4) (halternating : a.HasQuaternaryAlternatingOrders)
    (epsilon eta theta : Kˣ)
    (hepsilonUnit : IsValuationUnit K (epsilon : K))
    (hetaUnit : IsValuationUnit K (eta : K))
    (hthetaUnit : IsValuationUnit K (theta : K))
    (hepsilonDefect : (a.alphaValue (0 : Fin 3) : WithTop ℚ) ≤
      defectOrder (K := K) epsilon)
    (hetaDefect : defectOrder (K := K) eta =
      (a.alphaValue (1 : Fin 3) : WithTop ℚ))
    (hthetaDefect : defectOrder (K := K) theta =
      ((2 * (ramificationIndex K : ℚ) -
        a.alphaValue (1 : Fin 3) : ℚ) : WithTop ℚ))
    (htailStrict : (a.alphaValue (1 : Fin 3) : WithTop ℚ) <
      a.adjacentDefect (2 : Fin 3))
    (hmiddleAuxiliary :
      diagonalHasseSymbol K
          ![a.valueUnit 0, eta * a.valueUnit 1,
            eta * a.valueUnit 2, a.valueUnit 3] =
        diagonalHasseSymbol K a.valueUnit)
    (hthetaHilbert : hilbertSymbol K theta
      (eta * a.adjacentProduct (2 : Fin 3)) = -1)
    (hepsilonHilbert : hilbertSymbol K epsilon
      (diagonalUnitDeterminant a.valueUnit) = -1) :
    QuaternaryMultiplierCertificateInput a epsilon
      (quaternaryMiddleThenLastPairMultipliers epsilon eta theta) := by
  let m := quaternaryMiddleThenLastPairMultipliers epsilon eta theta
  let n : Fin 4 → Kˣ := ![1, eta, eta * theta, theta]
  let c : Fin 4 → Kˣ :=
    ![a.valueUnit 0, eta * a.valueUnit 1,
      eta * a.valueUnit 2, a.valueUnit 3]
  have hthetaBoundQ : a.alphaValue (0 : Fin 3) ≤
      2 * (ramificationIndex K : ℚ) -
        a.alphaValue (1 : Fin 3) := by
    have hsum := a.quaternaryAlternating_alphaSum_le_twoE halternating
    linarith
  have hthetaBound : (a.alphaValue (0 : Fin 3) : WithTop ℚ) ≤
      defectOrder (K := K) theta := by
    rw [hthetaDefect]
    exact_mod_cast hthetaBoundQ
  have hunit : ∀ i, IsValuationUnit K (m i : K) := by
    intro i
    fin_cases i
    · exact hepsilonUnit
    · exact isValuationUnit_units_mul epsilon eta
        hepsilonUnit hetaUnit
    · exact isValuationUnit_units_mul (epsilon * eta) theta
        (isValuationUnit_units_mul epsilon eta hepsilonUnit hetaUnit)
        hthetaUnit
    · exact isValuationUnit_units_mul epsilon theta
        hepsilonUnit hthetaUnit
  have hprefix : ∀ i : Fin 3,
      (a.alphaValue i : WithTop ℚ) ≤
        defectOrder (K := K)
          (quaternaryMultiplierPrefix m (i.1 + 1)) := by
    intro i
    fin_cases i
    · rw [quaternaryMultiplierPrefix_eq_one]
      exact hepsilonDefect
    · rw [quaternaryMultiplierPrefix_eq_two]
      have hp : m 0 * m 1 = eta * epsilon ^ 2 := by
        dsimp [m, quaternaryMiddleThenLastPairMultipliers]
        simp only [pow_two]
        ac_rfl
      change (a.alphaValue (1 : Fin 3) : WithTop ℚ) ≤
        defectOrder (K := K) (m 0 * m 1)
      rw [hp, defectOrder_mul_square, hetaDefect]
    · rw [quaternaryMultiplierPrefix_eq_three]
      have hp : m 0 * m 1 * m 2 =
          (epsilon * theta) * (epsilon * eta) ^ 2 := by
        dsimp [m, quaternaryMiddleThenLastPairMultipliers]
        simp only [pow_two]
        ac_rfl
      rw [hp, defectOrder_mul_square]
      change (a.alphaValue (2 : Fin 3) : WithTop ℚ) ≤
        defectOrder (K := K) (epsilon * theta)
      rw [← a.alpha_zero_eq_alpha_two_of_quaternaryAlternating
        halternating]
      exact (le_min hepsilonDefect hthetaBound).trans
        (defectOrder_mul_ge_min (K := K) epsilon theta)
  have hfull : IsSquare (quaternaryMultiplierPrefix m 4) := by
    rw [quaternaryMultiplierPrefix_eq_four]
    refine ⟨epsilon ^ 2 * eta * theta, ?_⟩
    dsimp [m, quaternaryMiddleThenLastPairMultipliers]
    simp only [pow_two]
    ac_rfl
  have hauxFull : IsSquare (quaternaryMultiplierPrefix n 4) := by
    rw [quaternaryMultiplierPrefix_eq_four]
    refine ⟨eta * theta, ?_⟩
    dsimp [n]
    ac_rfl
  have hauxShape : a.quaternaryMultiplierValues n =
      ![c 0, c 1, theta * c 2, theta * c 3] := by
    funext i
    fin_cases i
    · simp [n, c, quaternaryMultiplierValues]
    · simp [n, c, quaternaryMultiplierValues]
    · dsimp [n, c, quaternaryMultiplierValues]
      ac_rfl
    · simp [n, c, quaternaryMultiplierValues]
  have hsignedTail : -(c 2 * c 3) =
      eta * a.adjacentProduct (2 : Fin 3) := by
    dsimp [c]
    unfold adjacentProduct
    change -(eta * a.valueUnit (2 : Fin 4) *
        a.valueUnit (3 : Fin 4)) =
      eta * (-(a.valueUnit (2 : Fin 4) * a.valueUnit (3 : Fin 4)))
    apply Units.ext
    simp only [Units.val_neg, Units.val_mul]
    ring
  have hauxiliary :
      diagonalHasseSymbol K (a.quaternaryMultiplierValues n) =
        -diagonalHasseSymbol K a.valueUnit := by
    rw [hauxShape,
      QuaternaryHasse.diagonalHasseSymbol_fin_four_scale_last_pair,
      hsignedTail, hthetaHilbert]
    change (-1 : ℤˣ) * diagonalHasseSymbol K c =
      -diagonalHasseSymbol K a.valueUnit
    rw [show diagonalHasseSymbol K c =
        diagonalHasseSymbol K a.valueUnit by
      exact hmiddleAuxiliary]
    simp
  have hfinalValues : a.quaternaryMultiplierValues m =
      (fun i => epsilon * a.quaternaryMultiplierValues n i) := by
    funext i
    fin_cases i <;> dsimp [m, n,
      quaternaryMiddleThenLastPairMultipliers,
      quaternaryMultiplierValues] <;> group
  have hhasse :
      diagonalHasseSymbol K (a.quaternaryMultiplierValues m) =
        diagonalHasseSymbol K a.valueUnit :=
    a.quaternaryUniformAfterAuxiliary_hasse_eq epsilon n m
      hfinalValues hauxFull hauxiliary hepsilonHilbert
  have htailFinal : ∀ (X : BONG.OrthogonalBasisData q 4),
      (∀ i, X.valueUnit i = a.quaternaryMultiplierValues m i) →
        X.adjacentDefect (2 : Fin 3) =
          (a.alphaValue (1 : Fin 3) : WithTop ℚ) := by
    intro X hvalues
    rw [a.quaternaryMultiplier_adjacentDefect X m hvalues]
    change defectOrder (K := K)
      ((m (2 : Fin 4) * m (3 : Fin 4)) *
        a.adjacentProduct (2 : Fin 3)) =
        (a.alphaValue (1 : Fin 3) : WithTop ℚ)
    have hfactor :
        (m (2 : Fin 4) * m (3 : Fin 4)) *
            a.adjacentProduct (2 : Fin 3) =
          (eta * a.adjacentProduct (2 : Fin 3)) *
            (epsilon * theta) ^ 2 := by
      dsimp [m, quaternaryMiddleThenLastPairMultipliers]
      simp only [pow_two]
      ac_rfl
    rw [hfactor, defectOrder_mul_square,
      defectOrder_mul_eq_left_of_lt_right
        (hetaDefect ▸ htailStrict), hetaDefect]
  exact a.quaternaryMultiplierCertificateInput_of_tail halternating
    epsilon m rfl hunit hprefix hfull hhasse htailFinal

/-- Beli (2019), Lemma 8.3: the quaternary first-scaling law follows from
the already proved dyadic defect spectrum, complementary Hilbert choice,
alpha parity, and local diagonal classification. -/
noncomputable instance dyadicQuaternaryFirstScalingLawsProved
    [QuadraticDefectLaws K] [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [DyadicDiagonalClassificationLaws K] :
    DyadicQuaternaryFirstScalingLaws.{u, v} K where
  exists_basisCertificate b halternating epsilon hepsilonUnit
      hepsilonDefect := by
    by_cases hepsilonHilbertOne : hilbertSymbol K epsilon
        (diagonalUnitDeterminant b.valueUnit) = 1
    · exact (b.quaternaryUniformCertificateInput halternating epsilon
        hepsilonUnit hepsilonDefect hepsilonHilbertOne).toCertificate
    · have hepsilonHilbertNeg : hilbertSymbol K epsilon
          (diagonalUnitDeterminant b.valueUnit) = -1 :=
        (Int.units_eq_one_or (hilbertSymbol K epsilon
          (diagonalUnitDeterminant b.valueUnit))).resolve_left
            hepsilonHilbertOne
      have D := b.quaternaryNegativeScale_alphaData halternating epsilon
        hepsilonUnit hepsilonDefect hepsilonHilbertNeg
      have htailLower :=
        (b.quaternaryAlternating_outerAdjacentDefectBounds
          halternating).2
      rcases eq_or_lt_of_le htailLower with htailEq | htailStrict
      · have htailDefect : defectOrder (K := K)
            (b.adjacentProduct (2 : Fin 3)) =
          (b.alphaValue (1 : Fin 3) : WithTop ℚ) := by
          simpa only [adjacentDefect] using htailEq.symm
        rcases exists_complementaryDefect_hilbert_neg
            (b.adjacentProduct (2 : Fin 3))
            (b.alphaValue (1 : Fin 3)) htailDefect
            D.second_pos D.second_lt_twoE with
          ⟨eta, hetaUnit, hetaDefect, hetaHilbert⟩
        exact (b.quaternaryLastPairCertificateInput halternating
          epsilon eta hepsilonUnit hetaUnit hepsilonDefect hetaDefect
          htailEq.symm hetaHilbert hepsilonHilbertNeg).toCertificate
      · rcases
          DyadicUnitDefectSpectrumLaws.exists_unit_of_odd_rational_defect
            (K := K) (b.alphaValue (1 : Fin 3)) D.second_odd
              D.second_pos.le D.second_lt_twoE with
          ⟨eta, hetaUnit, hetaDefect⟩
        let middleValues : Fin 4 → Kˣ :=
          ![b.valueUnit 0, eta * b.valueUnit 1,
            eta * b.valueUnit 2, b.valueUnit 3]
        by_cases hmiddle : diagonalHasseSymbol K middleValues ≠
            diagonalHasseSymbol K b.valueUnit
        · exact (b.quaternaryMiddlePairCertificateInput halternating
            epsilon eta hepsilonUnit hetaUnit hepsilonDefect hetaDefect
            htailStrict hmiddle hepsilonHilbertNeg).toCertificate
        · have hmiddleEq : diagonalHasseSymbol K middleValues =
              diagonalHasseSymbol K b.valueUnit :=
            not_ne_iff.mp hmiddle
          have hchangedTailDefect : defectOrder (K := K)
                (eta * b.adjacentProduct (2 : Fin 3)) =
              (b.alphaValue (1 : Fin 3) : WithTop ℚ) := by
            rw [defectOrder_mul_eq_left_of_lt_right
              (hetaDefect ▸ htailStrict), hetaDefect]
          rcases exists_complementaryDefect_hilbert_neg
              (eta * b.adjacentProduct (2 : Fin 3))
              (b.alphaValue (1 : Fin 3)) hchangedTailDefect
              D.second_pos D.second_lt_twoE with
            ⟨theta, hthetaUnit, hthetaDefect, hthetaHilbert⟩
          exact (b.quaternaryMiddleThenLastPairCertificateInput
            halternating epsilon eta theta hepsilonUnit hetaUnit
            hthetaUnit hepsilonDefect hetaDefect hthetaDefect
            htailStrict hmiddleEq hthetaHilbert
            hepsilonHilbertNeg).toCertificate

end BONG.GoodBONG

end Bong
