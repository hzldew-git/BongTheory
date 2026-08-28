/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009ClassificationPropagation
import Bong.Bong.Beli2019KeyLemma

/-!
# Beli (2019), Lemma 9.3: condition (ii) after deleting equal heads

This file isolates the exact defect calculation in the proof of Lemma 9.3.
Deleting a common first BONG value removes a square from every comparison
prefix product, so its raw quadratic defect is unchanged.  The alpha caps of
the projected tails are weakly larger, hence the corresponding truncated
defect can only increase.

At an essential endpoint the hypothesis `A_i = A^*_i` therefore transfers
condition 2.1(ii) from the original pair to its tails.  When neither endpoint
is essential, the remaining branch is precisely the vacuity assertion of
Lemma 2.13, exposed below as a local hypothesis rather than hidden in a
global representation law.
-/

namespace Bong

open Dyadic

universe u v w

namespace RepresentationIndex

/-- The original boundary corresponding to a boundary after deleting the
first entry of two equal-rank BONGs. -/
def tailShift {n : Nat}
    (i : RepresentationIndex (n + 1) (n + 1)) :
    RepresentationIndex (n + 2) (n + 2) where
  val := i.val + 1
  pos := by omega
  lt_large := by have := i.lt_large; omega
  le_small := by have := i.le_small; omega

@[simp]
theorem tailShift_val {n : Nat}
    (i : RepresentationIndex (n + 1) (n + 1)) :
    i.tailShift.val = i.val + 1 :=
  rfl

end RepresentationIndex

namespace BONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

@[simp]
theorem valueUnit_tail_general (b : BONG V q L (n + 1)) (i : Fin n) :
    b.tail.valueUnit i = b.valueUnit i.succ := by
  apply Units.ext
  simp only [coe_valueUnit, value_tail]

/-- Removing the first BONG entry factors every nonempty prefix product into
the head value and the corresponding tail prefix product. -/
theorem prefixProduct_succ_eq_head_mul_tail
    (b : BONG V q L (n + 1)) (i : Nat) (hi : i ≤ n) :
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
      rw [hindex, ← b.valueUnit_tail_general j]
      simp only [j, mul_assoc]

end BONG

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}

/-- Good-BONG wrapper for the head/tail prefix-product factorization. -/
theorem prefixProduct_succ_eq_head_mul_tail
    (b : GoodBONG q L (n + 1)) (i : Nat) (hi : i ≤ n) :
    b.prefixProduct (i + 1) =
      b.valueUnit 0 * b.tail.prefixProduct i := by
  exact b.toBONG.prefixProduct_succ_eq_head_mul_tail i hi

/-- Equal first values contribute a common square to the original comparison
prefix, so deleting them leaves its raw defect unchanged. -/
theorem defectOrder_shiftedPrefix_eq_tail
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (hhead : a.value 0 = b.value 0) (ε : Kˣ)
    (i : Nat) (hi : i ≤ n + 1) :
    defectOrder (K := K)
        (ε * a.prefixProduct (i + 1) * b.prefixProduct (i + 1)) =
      defectOrder (K := K)
        (ε * a.tail.prefixProduct i * b.tail.prefixProduct i) := by
  have hheadUnit : a.valueUnit 0 = b.valueUnit 0 := by
    apply Units.ext
    simpa only [GoodBONG.coe_valueUnit] using hhead
  rw [a.prefixProduct_succ_eq_head_mul_tail i hi,
    b.prefixProduct_succ_eq_head_mul_tail i hi, ← hheadUnit]
  have hfactor :
      ε * (a.valueUnit 0 * a.tail.prefixProduct i) *
          (a.valueUnit 0 * b.tail.prefixProduct i) =
        (ε * a.tail.prefixProduct i * b.tail.prefixProduct i) *
          a.valueUnit 0 ^ 2 := by
    simp only [pow_two]
    ac_rfl
  rw [hfactor, defectOrder_mul_square]

/-- The alpha cap at an original shifted boundary is no larger than the cap
at the corresponding tail boundary, provided the projected alpha dominates
the shifted original alpha as in the proof of Lemma 9.3. -/
theorem prefixAlphaCap_shift_le_tail
    (a : GoodBONG q L (n + 2))
    (halpha : ∀ j : Fin n,
      (a.alphaValue j.succ : WithTop ℚ) ≤
        (a.tail.alphaValue j : WithTop ℚ))
    (i : Nat) (hi0 : 0 < i) (hin : i < n + 1) :
    a.prefixAlphaCap (i + 1) ≤ a.tail.prefixAlphaCap i := by
  rw [a.prefixAlphaCap_of_internal (by omega) (by omega),
    a.tail.prefixAlphaCap_of_internal hi0 hin]
  let j : Fin n := ⟨i - 1, by omega⟩
  have hsucc : j.succ = (⟨i + 1 - 1, by omega⟩ : Fin (n + 1)) := by
    apply Fin.ext
    simp only [j, Fin.val_succ]
    omega
  have hj := halpha j
  rw [hsucc] at hj
  simpa only [j] using hj

/-- The truncated comparison defect weakly increases after deleting equal
heads.  This is the exact inequality used in condition (ii*) of Lemma 9.3. -/
theorem truncatedPrefixDefect_shift_le_tail
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (hhead : a.value 0 = b.value 0)
    (halphaA : ∀ j : Fin n,
      (a.alphaValue j.succ : WithTop ℚ) ≤
        (a.tail.alphaValue j : WithTop ℚ))
    (halphaB : ∀ j : Fin n,
      (b.alphaValue j.succ : WithTop ℚ) ≤
        (b.tail.alphaValue j : WithTop ℚ))
    (ε : Kˣ) (i : Nat) (hi0 : 0 < i) (hin : i < n + 1) :
    a.truncatedPrefixDefect b ε (i + 1) (i + 1) ≤
      a.tail.truncatedPrefixDefect b.tail ε i i := by
  unfold truncatedPrefixDefect
  apply min_le_min
  · exact (a.defectOrder_shiftedPrefix_eq_tail b hhead ε i
      (by omega)).le
  · apply min_le_min
    · exact a.prefixAlphaCap_shift_le_tail halphaA i hi0 hin
    · exact b.prefixAlphaCap_shift_le_tail halphaB i hi0 hin

/-- Condition 2.1(ii) descends to the tails.  Equality of the representation
alphas is needed only when one of the two adjacent tail indices is essential;
the last hypothesis is exactly the nonessential conclusion of Lemma 2.13. -/
theorem representationDefectCondition_tail
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (hhead : a.value 0 = b.value 0)
    (halphaA : ∀ j : Fin n,
      (a.alphaValue j.succ : WithTop ℚ) ≤
        (a.tail.alphaValue j : WithTop ℚ))
    (halphaB : ∀ j : Fin n,
      (b.alphaValue j.succ : WithTop ℚ) ≤
        (b.tail.alphaValue j : WithTop ℚ))
    (hrepresentationAlpha :
      ∀ i : RepresentationIndex (n + 1) (n + 1),
        (a.tail.IsCurrentEssential b.tail i ∨
          a.tail.IsNextEssential b.tail i) →
        a.tail.representationAlpha b.tail i =
          a.representationAlpha b i.tailShift)
    (hnonessential :
      ∀ i : RepresentationIndex (n + 1) (n + 1),
        ¬a.tail.IsCurrentEssential b.tail i →
        ¬a.tail.IsNextEssential b.tail i →
        a.tail.RepresentationDefectAt b.tail i) :
    a.tail.RepresentationDefectCondition b.tail := by
  rw [a.tail.representationDefectCondition_iff_forall_at b.tail]
  intro i
  by_cases hcurrent : a.tail.IsCurrentEssential b.tail i
  · have horiginal := hdefect i.tailShift
    have horiginal' :
        a.representationAlpha b i.tailShift ≤
          a.truncatedPrefixDefect b 1 (i.val + 1) (i.val + 1) := by
      simpa only [a.coe_representationAlphaValue b i.tailShift,
        RepresentationIndex.tailShift_val] using horiginal
    unfold RepresentationDefectAt
    calc
      a.tail.representationAlpha b.tail i =
          a.representationAlpha b i.tailShift :=
        hrepresentationAlpha i (Or.inl hcurrent)
      _ ≤ a.truncatedPrefixDefect b 1 (i.val + 1) (i.val + 1) :=
        horiginal'
      _ ≤ a.tail.truncatedPrefixDefect b.tail 1 i.val i.val :=
        a.truncatedPrefixDefect_shift_le_tail b hhead halphaA halphaB
          1 i.val i.pos i.lt_large
  · by_cases hnext : a.tail.IsNextEssential b.tail i
    · have horiginal := hdefect i.tailShift
      have horiginal' :
          a.representationAlpha b i.tailShift ≤
            a.truncatedPrefixDefect b 1 (i.val + 1) (i.val + 1) := by
        simpa only [a.coe_representationAlphaValue b i.tailShift,
          RepresentationIndex.tailShift_val] using horiginal
      unfold RepresentationDefectAt
      calc
        a.tail.representationAlpha b.tail i =
            a.representationAlpha b i.tailShift :=
          hrepresentationAlpha i (Or.inr hnext)
        _ ≤ a.truncatedPrefixDefect b 1 (i.val + 1) (i.val + 1) :=
          horiginal'
        _ ≤ a.tail.truncatedPrefixDefect b.tail 1 i.val i.val :=
          a.truncatedPrefixDefect_shift_le_tail b hhead halphaA halphaB
            1 i.val i.pos i.lt_large
    · exact hnonessential i hcurrent hnext

end BONG.GoodBONG

end Bong
