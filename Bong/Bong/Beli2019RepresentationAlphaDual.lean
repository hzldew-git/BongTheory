/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019DefectDual
import Bong.Bong.Beli2019AuxiliaryAlphaNormalForm

/-!
# Beli (2019): reverse-duality of the representation alpha

At equal rank, the boundary complementary to `i` is `N - i`.  After
reversing both BONGs and swapping source and target, the half-gap, primary
defect, and secondary defect candidates at that complementary boundary are
exactly the original candidates at `i`.  Hence the representation invariant
`A_i` itself is preserved.
-/

namespace Bong

open Dyadic

namespace RepresentationIndex

/-- The boundary complementary to `i` under reversal of an equal-rank pair. -/
def reverse {N : Nat} (i : RepresentationIndex N N) :
    RepresentationIndex N N where
  val := N - i.val
  pos := by
    have := i.lt_large
    omega
  lt_large := by
    have hpos := i.pos
    have hlt := i.lt_large
    omega
  le_small := Nat.sub_le N i.val

@[simp]
theorem reverse_val {N : Nat} (i : RepresentationIndex N N) :
    i.reverse.val = N - i.val :=
  rfl

@[simp]
theorem reverse_reverse {N : Nat} (i : RepresentationIndex N N) :
    i.reverse.reverse = i := by
  cases i with
  | mk val hpos hlt hle =>
      simp only [reverse]
      congr
      omega

theorem reverse_interior_iff {N : Nat} (i : RepresentationIndex N N) :
    (1 < i.reverse.val ∧ i.reverse.val + 1 < N) ↔
      (1 < i.val ∧ i.val + 1 < N) := by
  simp only [reverse_val]
  omega

end RepresentationIndex

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- The half-gap candidate is invariant under swapped reverse-duality. -/
theorem representationHalfGap_reverseDual_swap
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (aDual : GoodBONG q (Lattice.dualLattice q L) (n + 1))
    (bDual : GoodBONG q (Lattice.dualLattice q M) (n + 1))
    (haOrders : ∀ j, aDual.order j = -a.order (Fin.rev j))
    (hbOrders : ∀ j, bDual.order j = -b.order (Fin.rev j))
    (i : RepresentationIndex (n + 1) (n + 1)) :
    bDual.representationHalfGap aDual i.reverse =
      a.representationHalfGap b i := by
  have hbIndex :
      Fin.rev (⟨i.reverse.val, i.reverse.lt_large⟩ : Fin (n + 1)) =
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 1)) := by
    apply Fin.ext
    simp only [Fin.rev, RepresentationIndex.reverse_val]
    have hpos := i.pos
    have hlt := i.lt_large
    omega
  have haIndex :
      Fin.rev (⟨i.reverse.val - 1, by
        have := i.reverse.lt_large
        omega⟩ : Fin (n + 1)) =
        (⟨i.val, i.lt_large⟩ : Fin (n + 1)) := by
    apply Fin.ext
    simp only [Fin.rev, RepresentationIndex.reverse_val]
    have hpos := i.pos
    have hlt := i.lt_large
    omega
  have hgap :
      bDual.order ⟨i.reverse.val, i.reverse.lt_large⟩ -
          aDual.order ⟨i.reverse.val - 1, by
            have := i.reverse.lt_large
            omega⟩ =
        a.order ⟨i.val, i.lt_large⟩ -
          b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ := by
    rw [hbOrders, haOrders, hbIndex, haIndex]
    ring
  unfold representationHalfGap
  rw [hgap]

/-- The primary defect candidate is invariant under swapped reverse-duality. -/
theorem representationPrimaryDefect_reverseDual_swap
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (aDual : GoodBONG q (Lattice.dualLattice q L) (n + 1))
    (bDual : GoodBONG q (Lattice.dualLattice q M) (n + 1))
    (haOrders : ∀ j, aDual.order j = -a.order (Fin.rev j))
    (hbOrders : ∀ j, bDual.order j = -b.order (Fin.rev j))
    (hDefect : ∀ (p r : Nat), p ≤ n + 1 → r ≤ n + 1 →
      ∀ epsilon : Kˣ,
        bDual.truncatedPrefixDefect aDual epsilon p r =
          a.truncatedPrefixDefect b epsilon
            (n + 1 - r) (n + 1 - p))
    (i : RepresentationIndex (n + 1) (n + 1)) :
    bDual.representationPrimaryDefect aDual i.reverse =
      a.representationPrimaryDefect b i := by
  have hbIndex :
      Fin.rev (⟨i.reverse.val, i.reverse.lt_large⟩ : Fin (n + 1)) =
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 1)) := by
    apply Fin.ext
    simp only [Fin.rev, RepresentationIndex.reverse_val]
    have hpos := i.pos
    have hlt := i.lt_large
    omega
  have haIndex :
      Fin.rev (⟨i.reverse.val - 1, by
        have := i.reverse.lt_large
        omega⟩ : Fin (n + 1)) =
        (⟨i.val, i.lt_large⟩ : Fin (n + 1)) := by
    apply Fin.ext
    simp only [Fin.rev, RepresentationIndex.reverse_val]
    have hpos := i.pos
    have hlt := i.lt_large
    omega
  have hDefect' := hDefect (i.reverse.val + 1) (i.reverse.val - 1)
    (by have := i.reverse.lt_large; omega)
    (by have := i.reverse.lt_large; omega) (-1)
  have hleft : n + 1 - (i.reverse.val - 1) = i.val + 1 := by
    simp only [RepresentationIndex.reverse_val]
    have hpos := i.pos
    have hlt := i.lt_large
    omega
  have hright : n + 1 - (i.reverse.val + 1) = i.val - 1 := by
    simp only [RepresentationIndex.reverse_val]
    have hpos := i.pos
    have hlt := i.lt_large
    omega
  rw [hleft, hright] at hDefect'
  have hgap :
      bDual.order ⟨i.reverse.val, i.reverse.lt_large⟩ -
          aDual.order ⟨i.reverse.val - 1, by
            have := i.reverse.lt_large
            omega⟩ =
        a.order ⟨i.val, i.lt_large⟩ -
          b.order ⟨i.val - 1, by have := i.lt_large; omega⟩ := by
    rw [hbOrders, haOrders, hbIndex, haIndex]
    ring
  unfold representationPrimaryDefect
  rw [hgap, hDefect']

/-- The secondary defect candidate is invariant under swapped reverse-duality. -/
theorem representationSecondaryDefect_reverseDual_swap
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (aDual : GoodBONG q (Lattice.dualLattice q L) (n + 1))
    (bDual : GoodBONG q (Lattice.dualLattice q M) (n + 1))
    (haOrders : ∀ j, aDual.order j = -a.order (Fin.rev j))
    (hbOrders : ∀ j, bDual.order j = -b.order (Fin.rev j))
    (hDefect : ∀ (p r : Nat), p ≤ n + 1 → r ≤ n + 1 →
      ∀ epsilon : Kˣ,
        bDual.truncatedPrefixDefect aDual epsilon p r =
          a.truncatedPrefixDefect b epsilon
            (n + 1 - r) (n + 1 - p))
    (i : RepresentationIndex (n + 1) (n + 1))
    (hi : 1 < i.val ∧ i.val + 1 < n + 1)
    (hiDual : 1 < i.reverse.val ∧ i.reverse.val + 1 < n + 1) :
    bDual.representationSecondaryDefect aDual i.reverse hiDual =
      a.representationSecondaryDefect b i hi := by
  have hbIndex0 :
      Fin.rev (⟨i.reverse.val, i.reverse.lt_large⟩ : Fin (n + 1)) =
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 1)) := by
    apply Fin.ext
    simp only [Fin.rev, RepresentationIndex.reverse_val]
    have hpos := i.pos
    have hlt := i.lt_large
    omega
  have hbIndex1 :
      Fin.rev (⟨i.reverse.val + 1, hiDual.2⟩ : Fin (n + 1)) =
        (⟨i.val - 2, by omega⟩ : Fin (n + 1)) := by
    apply Fin.ext
    simp only [Fin.rev, RepresentationIndex.reverse_val]
    have hpos := i.pos
    have hlt := i.lt_large
    omega
  have haIndex0 :
      Fin.rev (⟨i.reverse.val - 2, by omega⟩ : Fin (n + 1)) =
        (⟨i.val + 1, hi.2⟩ : Fin (n + 1)) := by
    apply Fin.ext
    simp only [Fin.rev, RepresentationIndex.reverse_val]
    have hpos := i.pos
    have hlt := i.lt_large
    omega
  have haIndex1 :
      Fin.rev (⟨i.reverse.val - 1, by omega⟩ : Fin (n + 1)) =
        (⟨i.val, i.lt_large⟩ : Fin (n + 1)) := by
    apply Fin.ext
    simp only [Fin.rev, RepresentationIndex.reverse_val]
    have hpos := i.pos
    have hlt := i.lt_large
    omega
  have hDefect' := hDefect (i.reverse.val + 2) (i.reverse.val - 2)
    (by omega) (by omega) 1
  have hleft : n + 1 - (i.reverse.val - 2) = i.val + 2 := by
    simp only [RepresentationIndex.reverse_val]
    omega
  have hright : n + 1 - (i.reverse.val + 2) = i.val - 2 := by
    simp only [RepresentationIndex.reverse_val]
    omega
  rw [hleft, hright] at hDefect'
  have horders :
      bDual.order ⟨i.reverse.val, i.reverse.lt_large⟩ +
            bDual.order ⟨i.reverse.val + 1, hiDual.2⟩ -
          aDual.order ⟨i.reverse.val - 2, by omega⟩ -
            aDual.order ⟨i.reverse.val - 1, by omega⟩ =
        a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hi.2⟩ -
          b.order ⟨i.val - 2, by have := i.le_small; omega⟩ -
            b.order ⟨i.val - 1, by have := i.le_small; omega⟩ := by
    rw [hbOrders, hbOrders, haOrders, haOrders,
      hbIndex0, hbIndex1, haIndex0, haIndex1]
    ring
  unfold representationSecondaryDefect
  rw [horders, hDefect']

/-- The auxiliary invariant `A'_i` is invariant under swapped reverse-duality
at the complementary boundary. -/
theorem representationAlphaPrime_reverseDual_swap
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (aDual : GoodBONG q (Lattice.dualLattice q L) (n + 1))
    (bDual : GoodBONG q (Lattice.dualLattice q M) (n + 1))
    (haOrders : ∀ j, aDual.order j = -a.order (Fin.rev j))
    (hbOrders : ∀ j, bDual.order j = -b.order (Fin.rev j))
    (hDefect : ∀ (p r : Nat), p ≤ n + 1 → r ≤ n + 1 →
      ∀ epsilon : Kˣ,
        bDual.truncatedPrefixDefect aDual epsilon p r =
          a.truncatedPrefixDefect b epsilon
            (n + 1 - r) (n + 1 - p))
    (i : RepresentationIndex (n + 1) (n + 1)) :
    bDual.representationAlphaPrime aDual i.reverse =
      a.representationAlphaPrime b i := by
  have hprimary := a.representationPrimaryDefect_reverseDual_swap
    b aDual bDual haOrders hbOrders hDefect i
  by_cases hi : 1 < i.val ∧ i.val + 1 < n + 1
  · have hiDual :
        1 < i.reverse.val ∧ i.reverse.val + 1 < n + 1 :=
      i.reverse_interior_iff.mpr hi
    have hsecondary := a.representationSecondaryDefect_reverseDual_swap
      b aDual bDual haOrders hbOrders hDefect i hi hiDual
    rw [bDual.representationAlphaPrime_eq_min_primary_secondary
        aDual i.reverse hiDual,
      a.representationAlphaPrime_eq_min_primary_secondary b i hi,
      hprimary, hsecondary]
  · have hiDual :
        ¬(1 < i.reverse.val ∧ i.reverse.val + 1 < n + 1) := by
      simpa only [i.reverse_interior_iff] using hi
    rw [bDual.representationAlphaPrime_eq_primary_of_not_interior
        aDual i.reverse hiDual,
      a.representationAlphaPrime_eq_primary_of_not_interior b i hi,
      hprimary]

/-- The complete representation invariant is invariant under swapped
reverse-duality at complementary equal-rank boundaries. -/
theorem representationAlpha_reverseDual_swap
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (aDual : GoodBONG q (Lattice.dualLattice q L) (n + 1))
    (bDual : GoodBONG q (Lattice.dualLattice q M) (n + 1))
    (haOrders : ∀ j, aDual.order j = -a.order (Fin.rev j))
    (hbOrders : ∀ j, bDual.order j = -b.order (Fin.rev j))
    (hDefect : ∀ (p r : Nat), p ≤ n + 1 → r ≤ n + 1 →
      ∀ epsilon : Kˣ,
        bDual.truncatedPrefixDefect aDual epsilon p r =
          a.truncatedPrefixDefect b epsilon
            (n + 1 - r) (n + 1 - p))
    (i : RepresentationIndex (n + 1) (n + 1)) :
    bDual.representationAlpha aDual i.reverse =
      a.representationAlpha b i := by
  have hhalf := a.representationHalfGap_reverseDual_swap
    b aDual bDual haOrders hbOrders i
  have hprimary := a.representationPrimaryDefect_reverseDual_swap
    b aDual bDual haOrders hbOrders hDefect i
  rw [bDual.representationAlpha_eq_min_halfGap_prime aDual i.reverse,
    a.representationAlpha_eq_min_halfGap_prime b i, hhalf]
  by_cases hi : 1 < i.val ∧ i.val + 1 < n + 1
  · have hiDual :
        1 < i.reverse.val ∧ i.reverse.val + 1 < n + 1 :=
      i.reverse_interior_iff.mpr hi
    have hsecondary := a.representationSecondaryDefect_reverseDual_swap
      b aDual bDual haOrders hbOrders hDefect i hi hiDual
    rw [bDual.representationAlphaPrime_eq_min_primary_secondary
        aDual i.reverse hiDual,
      a.representationAlphaPrime_eq_min_primary_secondary b i hi,
      hprimary, hsecondary]
  · have hiDual :
        ¬(1 < i.reverse.val ∧ i.reverse.val + 1 < n + 1) := by
      simpa only [i.reverse_interior_iff] using hi
    rw [bDual.representationAlphaPrime_eq_primary_of_not_interior
        aDual i.reverse hiDual,
      a.representationAlphaPrime_eq_primary_of_not_interior b i hi,
      hprimary]

/-- Finite rational representation-alpha values obey the same duality. -/
theorem representationAlphaValue_reverseDual_swap
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (aDual : GoodBONG q (Lattice.dualLattice q L) (n + 1))
    (bDual : GoodBONG q (Lattice.dualLattice q M) (n + 1))
    (haOrders : ∀ j, aDual.order j = -a.order (Fin.rev j))
    (hbOrders : ∀ j, bDual.order j = -b.order (Fin.rev j))
    (hDefect : ∀ (p r : Nat), p ≤ n + 1 → r ≤ n + 1 →
      ∀ epsilon : Kˣ,
        bDual.truncatedPrefixDefect aDual epsilon p r =
          a.truncatedPrefixDefect b epsilon
            (n + 1 - r) (n + 1 - p))
    (i : RepresentationIndex (n + 1) (n + 1)) :
    bDual.representationAlphaValue aDual i.reverse =
      a.representationAlphaValue b i := by
  apply WithTop.coe_injective
  rw [bDual.coe_representationAlphaValue aDual i.reverse,
    a.coe_representationAlphaValue b i,
    a.representationAlpha_reverseDual_swap b aDual bDual
      haOrders hbOrders hDefect i]

/-- Reverse-dual BONGs can be chosen so that every complementary
representation alpha agrees with the original one. -/
theorem exists_reverseDualPair_with_representationAlpha
    [Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1)) :
    ∃ (aDual : GoodBONG q (Lattice.dualLattice q L) (n + 1))
      (bDual : GoodBONG q (Lattice.dualLattice q M) (n + 1)),
      (∀ j, aDual.order j = -a.order (Fin.rev j)) ∧
      (∀ j, bDual.order j = -b.order (Fin.rev j)) ∧
      (∀ j, aDual.alphaValue j = a.alphaValue (Fin.rev j)) ∧
      (∀ j, bDual.alphaValue j = b.alphaValue (Fin.rev j)) ∧
      ∀ i : RepresentationIndex (n + 1) (n + 1),
        bDual.representationAlpha aDual i.reverse =
          a.representationAlpha b i := by
  rcases a.exists_reverseDualPair_with_truncatedPrefixDefect b with
    ⟨aDual, bDual, haOrders, hbOrders, haAlpha, hbAlpha, hDefect⟩
  refine ⟨aDual, bDual, haOrders, hbOrders, haAlpha, hbAlpha, ?_⟩
  intro i
  exact a.representationAlpha_reverseDual_swap b aDual bDual
    haOrders hbOrders hDefect i

end BONG.GoodBONG

end Bong
