/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.AlternatingEndpointProduct
import Bong.Bong.Beli2009JordanWeightOrderProof
import Bong.Dyadic.UnitsCongruentModuloAlgebra
import Bong.Lattice.OmearaNormGeneratorDefect

/-!
# Weight bounds for signed determinants in arbitrary even rank

This file isolates the elementary many-pair extension of the binary
determinant estimate used in Beli (2019), Lemma 5.13.  Adjacent BONG pairs
multiply to the signed determinant.  If the second order in every pair is
no larger than the first BONG order, the defining right-defect candidates
bound every pair defect below by `alpha_1`; the dyadic domination principle
then gives the same bound for the complete signed determinant.

No new local law is introduced here.  The argument uses only the definition
of Beli's alpha invariant, determinant invariance of a BONG, and quadratic
defect domination under products.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG

/-- The tail value at `i` is the original value at `i + 1`.  This local
name keeps the 2009 determinant calculation independent of the later
Section 9 tail API. -/
@[simp]
theorem valueUnit_tail_eq_succ_for_signedDeterminant
    {n : Nat} (b : BONG V q L (n + 1)) (i : Fin n) :
    b.tail.valueUnit i = b.valueUnit i.succ := by
  apply Units.ext
  simp only [coe_valueUnit, value_tail]

/-- A nonempty prefix is its head times the corresponding tail prefix. -/
theorem prefixProduct_succ_eq_head_mul_tail_for_signedDeterminant
    {n : Nat} (b : BONG V q L (n + 1)) (i : Nat) (hi : i <= n) :
    b.prefixProduct (i + 1) =
      b.valueUnit 0 * b.tail.prefixProduct i := by
  induction i with
  | zero =>
      rw [b.prefixProduct_succ 0 (by omega), b.prefixProduct_zero,
        b.tail.prefixProduct_zero]
      simp
  | succ i ih =>
      rw [b.prefixProduct_succ (i + 1) (by omega), ih (by omega),
        b.tail.prefixProduct_succ i (by omega)]
      let j : Fin n := ⟨i, by omega⟩
      have hindex :
          (⟨i + 1, by omega⟩ : Fin (n + 1)) = j.succ := by
        apply Fin.ext
        rfl
      rw [hindex, ← b.valueUnit_tail_eq_succ_for_signedDeterminant j]
      simp only [j, mul_assoc]

end BONG

namespace BONG.GoodBONG

/-- Deleting the BONG head shifts an adjacent defect by one.  This is the
small tail identity needed by the odd-rank determinant calculation below. -/
@[simp]
theorem adjacentDefect_tail_for_signedDeterminant
    {n : Nat} (b : GoodBONG q L (n + 2)) (i : Fin n) :
    b.tail.adjacentDefect i = b.adjacentDefect i.succ := by
  unfold adjacentDefect adjacentProduct GoodBONG.valueUnit
  change defectOrder (K := K)
      (-(b.toBONG.tail.valueUnit i.castSucc *
        b.toBONG.tail.valueUnit i.succ)) =
    defectOrder (K := K)
      (-(b.toBONG.valueUnit i.succ.castSucc *
        b.toBONG.valueUnit i.succ.succ))
  rw [b.toBONG.valueUnit_tail_eq_succ_for_signedDeterminant i.castSucc,
    b.toBONG.valueUnit_tail_eq_succ_for_signedDeterminant i.succ]
  congr 3

/-- If the right endpoint of an adjacent pair has order no larger than the
first BONG value, `alpha_1` is bounded by the defect of that pair. -/
theorem alphaValue_zero_le_adjacentDefect_of_order_succ_le
    {n : Nat} (b : GoodBONG q L (n + 2)) (j : Fin (n + 1))
    (horder : b.order j.succ <= b.order (0 : Fin (n + 2))) :
    (b.alphaValue (0 : Fin (n + 1)) : WithTop ℚ) <=
      b.adjacentDefect j := by
  have hcandidate := b.alpha_le_rightDefectCandidate
    (i := (0 : Fin (n + 1))) (j := j) (Fin.zero_le j)
  rw [← b.coe_alphaValue] at hcandidate
  unfold rightDefectCandidate at hcandidate
  have hgap :
      ((((b.order j.succ - b.order (0 : Fin (n + 2)) : Int) : ℚ) :
          WithTop ℚ)) <= 0 := by
    norm_cast
    push_cast
    exact_mod_cast sub_nonpos.mpr horder
  exact hcandidate.trans <| by
    calc
      ((((b.order j.succ - b.order (0 : Fin (n + 2)) : Int) : ℚ) :
            WithTop ℚ)) + b.adjacentDefect j =
          b.adjacentDefect j +
            ((((b.order j.succ - b.order (0 : Fin (n + 2)) : Int) : ℚ) :
              WithTop ℚ)) := add_comm _ _
      _ <= b.adjacentDefect j + 0 :=
        add_le_add_right hgap (b.adjacentDefect j)
      _ = b.adjacentDefect j := add_zero _

/-- Beli's weight formula and the right-defect candidate at `j` give the
arbitrary-rank version of the binary estimate
`ord w(L) - F <= d(-a_j a_{j+1})`, provided the second value of the pair
has order at most `F`. -/
theorem weightIdealOrder_sub_le_adjacentDefect_of_order_succ_le
    {n : Nat} (b : GoodBONG q L (n + 2)) (j : Fin (n + 1))
    (F : Int) (horder : b.order j.succ <= F) :
    (((Lattice.weightIdealOrder q L - F : Int) : ℚ) : WithTop ℚ) <=
      b.adjacentDefect j := by
  have hweightFormula := b.lemma214_weightIdealOrder_all
  have hweight : (Lattice.weightIdealOrder q L : ℚ) <=
      (b.order (0 : Fin (n + 2)) : ℚ) +
        b.alphaValue (0 : Fin (n + 1)) := by
    rw [hweightFormula]
    exact min_le_left _ _
  have hcandidate := b.alpha_le_rightDefectCandidate
    (i := (0 : Fin (n + 1))) (j := j) (Fin.zero_le j)
  rw [← b.coe_alphaValue] at hcandidate
  unfold rightDefectCandidate at hcandidate
  by_cases htop : b.adjacentDefect j = ⊤
  · rw [htop]
    exact le_top
  · obtain ⟨delta, hdelta⟩ := WithTop.ne_top_iff_exists.mp htop
    rw [← hdelta] at hcandidate ⊢
    norm_cast at hcandidate ⊢
    push_cast at hcandidate ⊢
    simp only [Fin.castSucc_zero] at hcandidate
    have horderQ : (b.order j.succ : ℚ) <= (F : ℚ) := by
      exact_mod_cast horder
    linarith

/-- A common lower bound for all adjacent-pair defects is a lower bound for
the defect of their complete signed even product. -/
theorem le_defectOrder_signedEvenPrefixProduct
    {n : Nat} (b : GoodBONG q L (n + 1)) (pairs : Nat)
    (hbound : 2 * pairs <= n + 1) (d : WithTop ℚ)
    (hpairs : ∀ (t : Nat) (ht : t < pairs),
      d <= b.adjacentDefect ⟨2 * t, by omega⟩) :
    d <= defectOrder (K := K) (b.toBONG.signedEvenPrefixProduct pairs) := by
  induction pairs with
  | zero =>
      have hone : b.toBONG.signedEvenPrefixProduct 0 = 1 := by
        simp [BONG.signedEvenPrefixProduct, BONG.prefixProduct]
      rw [hone]
      unfold defectOrder
      rw [quadraticDefect_eq_top_of_isSquare K
        (show IsSquare (1 : Kˣ) by exact ⟨1, by simp⟩)]
      exact le_top
  | succ pairs ih =>
      have hprevious : 2 * pairs <= n + 1 := by omega
      have hpairBound : 2 * pairs + 1 < n + 1 := by omega
      have hrecurrence :=
        b.toBONG.signedEvenPrefixProduct_succ pairs hpairBound
      rw [hrecurrence]
      have hleft : d <=
          defectOrder (K := K)
            (b.toBONG.signedEvenPrefixProduct pairs) :=
        ih hprevious (fun t ht ↦ hpairs t (Nat.lt_succ_of_lt ht))
      have hright : d <= defectOrder (K := K)
          (-(b.valueUnit ⟨2 * pairs, by omega⟩ *
            b.valueUnit ⟨2 * pairs + 1, hpairBound⟩)) := by
        let j : Fin n := ⟨2 * pairs, by omega⟩
        have hraw := hpairs pairs (Nat.lt_succ_self pairs)
        change d <= defectOrder (K := K)
          (-(b.valueUnit j.castSucc * b.valueUnit j.succ)) at hraw
        have hj0 : j.castSucc =
            (⟨2 * pairs, by omega⟩ : Fin (n + 1)) := by
          apply Fin.ext
          rfl
        have hj1 : j.succ =
            (⟨2 * pairs + 1, hpairBound⟩ : Fin (n + 1)) := by
          apply Fin.ext
          rfl
        rw [hj0, hj1] at hraw
        exact hraw
      exact (le_min hleft hright).trans
        (defectOrder_mul_ge_min
          (b.toBONG.signedEvenPrefixProduct pairs)
          (-(b.valueUnit ⟨2 * pairs, by omega⟩ *
            b.valueUnit ⟨2 * pairs + 1, hpairBound⟩)))

/-- Pairwise order control turns the preceding product lemma into the
`alpha_1` bound used for an improper even modular component. -/
theorem alphaValue_zero_le_defectOrder_signedEvenPrefixProduct
    {n : Nat} (b : GoodBONG q L (n + 2)) (pairs : Nat)
    (hbound : 2 * pairs <= n + 2)
    (horders : ∀ (t : Nat) (ht : t < pairs),
      b.order ⟨2 * t + 1, by omega⟩ <=
        b.order (0 : Fin (n + 2))) :
    (b.alphaValue (0 : Fin (n + 1)) : WithTop ℚ) <=
      defectOrder (K := K) (b.toBONG.signedEvenPrefixProduct pairs) := by
  apply b.le_defectOrder_signedEvenPrefixProduct pairs hbound
    (b.alphaValue (0 : Fin (n + 1)) : WithTop ℚ)
  intro t ht
  exact b.alphaValue_zero_le_adjacentDefect_of_order_succ_le
    ⟨2 * t, by omega⟩ (horders t ht)

/-- In full even rank, the signed BONG product and the signed refined
determinant differ by a square.  Hence the pairwise alpha bound is a bound
for the intrinsic determinant defect. -/
theorem alphaValue_zero_le_defectOrder_signedDeterminant
    (pairs : Nat) (b : GoodBONG q L (2 * pairs + 2))
    (horders : ∀ (t : Nat) (ht : t < pairs + 1),
      b.order ⟨2 * t + 1, by omega⟩ <=
        b.order ⟨0, by omega⟩) :
    (b.alphaValue ⟨0, by omega⟩ : WithTop ℚ) <=
      defectOrder (K := K)
        (((-1 : Kˣ) ^ (pairs + 1)) * Lattice.determinantUnit q L) := by
  have hsigned :
      (b.alphaValue ⟨0, by omega⟩ : WithTop ℚ) <=
        defectOrder (K := K)
          (b.toBONG.signedEvenPrefixProduct (pairs + 1)) := by
    apply b.alphaValue_zero_le_defectOrder_signedEvenPrefixProduct
      (pairs + 1) (by omega)
    intro t ht
    exact horders t ht
  have hdet := b.toBONG.determinantClass_eq_valueProduct
  have hprefixClass :
      unitSquareClass K
          (b.toBONG.prefixProduct (2 * pairs + 2)) =
        unitSquareClass K (Lattice.determinantUnit q L) := by
    simpa only [BONG.valueProduct, Lattice.determinantClass] using hdet.symm
  have hclass :
      unitSquareClass K (b.toBONG.signedEvenPrefixProduct (pairs + 1)) =
        unitSquareClass K
          (((-1 : Kˣ) ^ (pairs + 1)) * Lattice.determinantUnit q L) := by
    unfold BONG.signedEvenPrefixProduct
    have hlength : 2 * (pairs + 1) = 2 * pairs + 2 := by omega
    rw [unitSquareClass_mul, unitSquareClass_mul, hlength, hprefixClass]
  obtain ⟨s, hs⟩ := exists_square_mul_eq_of_unitSquareClass_eq
    (K := K) (b.toBONG.signedEvenPrefixProduct (pairs + 1))
      (((-1 : Kˣ) ^ (pairs + 1)) * Lattice.determinantUnit q L) hclass
  rw [← hs, defectOrder_mul_square]
  exact hsigned

/-- The complete even-rank determinant form of the weight estimate.  This
is the many-pair extension of
`weightIdealOrder_le_order_one_add_defect_neg_determinantUnit`: if the
second order of every adjacent pair is at most `F`, then the signed full
determinant has defect at least `ord w(L) - F`. -/
theorem weightIdealOrder_sub_le_defectOrder_signedDeterminant
    (pairs : Nat) (b : GoodBONG q L (2 * pairs + 2)) (F : Int)
    (horders : ∀ (t : Nat) (ht : t < pairs + 1),
      b.order ⟨2 * t + 1, by omega⟩ <= F) :
    (((Lattice.weightIdealOrder q L - F : Int) : ℚ) : WithTop ℚ) <=
      defectOrder (K := K)
        (((-1 : Kˣ) ^ (pairs + 1)) * Lattice.determinantUnit q L) := by
  let d : WithTop ℚ :=
    (((Lattice.weightIdealOrder q L - F : Int) : ℚ) : WithTop ℚ)
  have hsigned : d <= defectOrder (K := K)
      (b.toBONG.signedEvenPrefixProduct (pairs + 1)) := by
    apply b.le_defectOrder_signedEvenPrefixProduct (pairs + 1) (by omega) d
    intro t ht
    exact b.weightIdealOrder_sub_le_adjacentDefect_of_order_succ_le
      ⟨2 * t, by omega⟩ F (horders t ht)
  have hdet := b.toBONG.determinantClass_eq_valueProduct
  have hprefixClass :
      unitSquareClass K (b.toBONG.prefixProduct (2 * pairs + 2)) =
        unitSquareClass K (Lattice.determinantUnit q L) := by
    simpa only [BONG.valueProduct, Lattice.determinantClass] using hdet.symm
  have hclass :
      unitSquareClass K (b.toBONG.signedEvenPrefixProduct (pairs + 1)) =
        unitSquareClass K
          (((-1 : Kˣ) ^ (pairs + 1)) * Lattice.determinantUnit q L) := by
    unfold BONG.signedEvenPrefixProduct
    have hlength : 2 * (pairs + 1) = 2 * pairs + 2 := by omega
    rw [unitSquareClass_mul, unitSquareClass_mul, hlength, hprefixClass]
  obtain ⟨s, hs⟩ := exists_square_mul_eq_of_unitSquareClass_eq
    (K := K) (b.toBONG.signedEvenPrefixProduct (pairs + 1))
      (((-1 : Kˣ) ^ (pairs + 1)) * Lattice.determinantUnit q L) hclass
  rw [← hs, defectOrder_mul_square]
  exact hsigned

/-- Odd-rank companion to the signed-determinant estimate.  The head BONG
value and an arbitrary norm generator `A` have relative defect at least
`ord w(L) - ord(A)`.  Pairing all remaining BONG values and multiplying the
two estimates gives the intrinsic defect of
`(-1)^(pairs+1) * A * det(L)`.

This is precisely the proper odd modular endpoint needed at the silent
right-boundary step in Beli (2019), Lemma 5.13. -/
theorem weightIdealOrder_sub_le_defectOrder_norm_mul_signedDeterminant
    (pairs : Nat) (b : GoodBONG q L (2 * pairs + 1))
    (A : Kˣ) (hA : Lattice.IsNormGeneratorValue q L A)
    (F : Int) (hAF : ordUnit K A = F)
    (horders : ∀ (t : Nat) (ht : t < pairs),
      b.order ⟨2 * t + 2, by omega⟩ <= F) :
    (((Lattice.weightIdealOrder q L - F : Int) : ℚ) : WithTop ℚ) <=
      defectOrder (K := K)
        (((-1 : Kˣ) ^ (pairs + 1)) * A *
          Lattice.determinantUnit q L) := by
  let d : WithTop ℚ :=
    (((Lattice.weightIdealOrder q L - F : Int) : ℚ) : WithTop ℚ)
  have hhead :=
    b.toBONG.lemma214_valueUnit_zero_isNormGeneratorValue_nonempty
  have hheadOrder : ordUnit K (b.valueUnit 0) = ordUnit K A := by
    apply (Lattice.principalIdeal_eq_iff_ordUnit_eq _ _).mp
    exact hhead.2.symm.trans hA.2
  have hratio : d <= defectOrder (K := K) (-(A / b.valueUnit 0)) := by
    have h :=
      Lattice.weightIdealOrder_sub_ordUnit_le_defectOrder_neg_div_of_normGenerators
        A (b.valueUnit 0) hA hhead hheadOrder
    simpa only [d, hAF] using h
  have htail : d <= defectOrder (K := K)
      (b.toBONG.tail.signedEvenPrefixProduct pairs) := by
    cases pairs with
    | zero =>
        have hone : b.toBONG.tail.signedEvenPrefixProduct 0 = 1 := by
          simp [BONG.signedEvenPrefixProduct, BONG.prefixProduct]
        rw [hone]
        unfold defectOrder
        rw [quadraticDefect_eq_top_of_isSquare K
          (show IsSquare (1 : Kˣ) by exact ⟨1, by simp⟩)]
        exact le_top
    | succ p =>
        apply b.tail.le_defectOrder_signedEvenPrefixProduct (p + 1)
          (by simp [Nat.mul_succ]) d
        intro t ht
        let jTail : Fin (2 * p + 1) := ⟨2 * t, by omega⟩
        have hrightOrder : b.order jTail.succ.succ <= F := by
          have hindex : jTail.succ.succ =
              (⟨2 * t + 2, by omega⟩ : Fin (2 * (p + 1) + 1)) := by
            apply Fin.ext
            rfl
          rw [hindex]
          exact horders t ht
        have hpair :=
          b.weightIdealOrder_sub_le_adjacentDefect_of_order_succ_le
            jTail.succ F hrightOrder
        change d <= b.tail.adjacentDefect jTail
        rw [b.adjacentDefect_tail_for_signedDeterminant jTail]
        exact hpair
  have hcombined : d <= defectOrder (K := K)
      ((-(A / b.valueUnit 0)) *
        b.toBONG.tail.signedEvenPrefixProduct pairs) :=
    (le_min hratio htail).trans
      (defectOrder_mul_ge_min (-(A / b.valueUnit 0))
        (b.toBONG.tail.signedEvenPrefixProduct pairs))
  have hfactor :
      ((-(A / b.valueUnit 0)) *
          b.toBONG.tail.signedEvenPrefixProduct pairs) *
          b.valueUnit 0 ^ 2 =
        ((-1 : Kˣ) ^ (pairs + 1)) * A *
          b.prefixProduct (2 * pairs + 1) := by
    change ((-(A / b.toBONG.valueUnit 0)) *
        b.toBONG.tail.signedEvenPrefixProduct pairs) *
        b.toBONG.valueUnit 0 ^ 2 =
      ((-1 : Kˣ) ^ (pairs + 1)) * A *
        b.toBONG.prefixProduct (2 * pairs + 1)
    rw [b.toBONG.prefixProduct_succ_eq_head_mul_tail_for_signedDeterminant
      (2 * pairs) (by omega)]
    unfold BONG.signedEvenPrefixProduct
    apply Units.ext
    simp only [Units.val_mul, Units.val_neg, Units.val_div_eq_div_val,
      Units.val_pow_eq_pow_val]
    rw [pow_succ]
    field_simp [Units.ne_zero (b.toBONG.valueUnit 0)]
    simp
    rw [pow_succ]
    ring
  have hprefix : d <= defectOrder (K := K)
      (((-1 : Kˣ) ^ (pairs + 1)) * A *
        b.prefixProduct (2 * pairs + 1)) := by
    rw [← hfactor, defectOrder_mul_square]
    exact hcombined
  have hdet := b.toBONG.determinantClass_eq_valueProduct
  have hprefixClass :
      unitSquareClass K (b.toBONG.prefixProduct (2 * pairs + 1)) =
        unitSquareClass K (Lattice.determinantUnit q L) := by
    simpa only [BONG.valueProduct, Lattice.determinantClass] using hdet.symm
  have hclass :
      unitSquareClass K
          (((-1 : Kˣ) ^ (pairs + 1)) * A *
            b.prefixProduct (2 * pairs + 1)) =
        unitSquareClass K
          (((-1 : Kˣ) ^ (pairs + 1)) * A *
            Lattice.determinantUnit q L) := by
    change unitSquareClass K
        (((-1 : Kˣ) ^ (pairs + 1)) * A *
          b.toBONG.prefixProduct (2 * pairs + 1)) = _
    simp only [unitSquareClass_mul, hprefixClass]
  obtain ⟨s, hs⟩ := exists_square_mul_eq_of_unitSquareClass_eq
    (K := K)
      (((-1 : Kˣ) ^ (pairs + 1)) * A *
        b.prefixProduct (2 * pairs + 1))
      (((-1 : Kˣ) ^ (pairs + 1)) * A *
        Lattice.determinantUnit q L) hclass
  rw [← hs, defectOrder_mul_square]
  exact hprefix

end BONG.GoodBONG

end Bong
