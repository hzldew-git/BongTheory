/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma910Representation
import Bong.Bong.GoodBONGSameRankIntegralImage
import Bong.Bong.Beli2019VolumeOrders
import Bong.Bong.Beli2019SectionFive

/-!
# Beli (2019), Lemma 9.10: the literal index-uniformizer sublattice

The full-rank representation constructed in the preceding file is replaced by
its literal image inside the original lattice.  Its BONG retains the prescribed
scalar sequence.  The volume-order formula for BONGs then shows that changing
only `R₂` to `R₂ + 2` gives an index-`p` inclusion in the exact sense used by
Section 5.
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {M : Lattice K V} {P : Lattice K W} {tailLength : Nat}

/-- The literal output of Lemma 9.10 before the final alpha computation. -/
structure Beli2019Lemma910IndexPData
    {R₁ R₂ β₁ : Int}
    (a : GoodBONG q M (3 + tailLength))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁) where
  lattice : Lattice K V
  bong : GoodBONG q lattice (3 + tailLength)
  inclusion : Beli2019IndexPInclusion q M lattice
  values : ∀ i, bong.valueUnit i = beli2019Lemma910Values D a i

/-- Orders in the replaced ternary prefix are the orders supplied by the
Lemma 9.9 realization. -/
theorem beli2019Lemma910FullCoefficientRealization_order_left
    {R₁ R₂ β₁ : Int}
    (a : GoodBONG q M (3 + tailLength))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (C : BONG.PrescribedValuesGoodBONGData q (3 + tailLength)
      (beli2019Lemma910Values D a)) (i : Fin 3) :
    C.bong.order (Fin.castAdd tailLength i) = D.bong.order i := by
  unfold GoodBONG.order
  rw [C.bong.toBONG.order_eq_ordUnit]
  change ordUnit K (C.bong.valueUnit (Fin.castAdd tailLength i)) =
    D.bong.order i
  rw [C.values, ordUnit_beli2019Lemma910Values_left]

/-- Orders in the unchanged tail remain the original orders. -/
theorem beli2019Lemma910FullCoefficientRealization_order_right
    {R₁ R₂ β₁ : Int}
    (a : GoodBONG q M (3 + tailLength))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (C : BONG.PrescribedValuesGoodBONGData q (3 + tailLength)
      (beli2019Lemma910Values D a)) (j : Fin tailLength) :
    C.bong.order (Fin.natAdd 3 j) = a.order (Fin.natAdd 3 j) := by
  unfold GoodBONG.order
  rw [C.bong.toBONG.order_eq_ordUnit]
  change ordUnit K (C.bong.valueUnit (Fin.natAdd 3 j)) =
    a.order (Fin.natAdd 3 j)
  rw [C.values, ordUnit_beli2019Lemma910Values_right]

/-- Replacing the second order `R₂` by `R₂ + 2` raises the volume order by
exactly two. -/
theorem volumeOrder_beli2019Lemma910FullCoefficientRealization
    {R₁ R₂ β₁ : Int}
    (a : GoodBONG q M (3 + tailLength))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (C : BONG.PrescribedValuesGoodBONGData q (3 + tailLength)
      (beli2019Lemma910Values D a))
    (horders : ∀ i : Fin 3,
      a.order (Fin.castAdd tailLength i) = ![R₁, R₂, R₁] i) :
    Lattice.volumeOrder q C.lattice = Lattice.volumeOrder q M + 2 := by
  rw [C.bong.toBONG.volumeOrder_eq_sum_order,
    a.toBONG.volumeOrder_eq_sum_order,
    Fin.sum_univ_add, Fin.sum_univ_add]
  have hleftC : (∑ i : Fin 3,
        C.bong.order (Fin.castAdd tailLength i)) =
      ∑ i : Fin 3, D.bong.order i := by
    apply Finset.sum_congr rfl
    intro i _
    exact beli2019Lemma910FullCoefficientRealization_order_left a D C i
  have hrightC : (∑ j : Fin tailLength,
        C.bong.order (Fin.natAdd 3 j)) =
      ∑ j : Fin tailLength, a.order (Fin.natAdd 3 j) := by
    apply Finset.sum_congr rfl
    intro j _
    exact beli2019Lemma910FullCoefficientRealization_order_right a D C j
  have hleftC' : (∑ i : Fin 3,
        C.bong.toBONG.order (Fin.castAdd tailLength i)) =
      ∑ i : Fin 3, D.bong.toBONG.order i := hleftC
  have hrightC' : (∑ j : Fin tailLength,
        C.bong.toBONG.order (Fin.natAdd 3 j)) =
      ∑ j : Fin tailLength, a.toBONG.order (Fin.natAdd 3 j) := hrightC
  rw [hleftC', hrightC']
  have hprefix : (∑ i : Fin 3, D.bong.toBONG.order i) =
      (∑ i : Fin 3, a.toBONG.order (Fin.castAdd tailLength i)) + 2 := by
    rw [Fin.sum_univ_three, Fin.sum_univ_three]
    change D.bong.order 0 + D.bong.order 1 + D.bong.order 2 =
      (a.order (Fin.castAdd tailLength 0) +
        a.order (Fin.castAdd tailLength 1) +
        a.order (Fin.castAdd tailLength 2)) + 2
    rw [D.order_zero, D.order_one, D.order_two,
      horders (0 : Fin 3), horders (1 : Fin 3), horders (2 : Fin 3)]
    simp
    omega
  rw [hprefix]
  omega

/-- Turn the full coefficient representation into the literal index-`p`
sublattice asserted by Lemma 9.10. -/
theorem exists_beli2019Lemma910IndexPData
    [structuralAmbient : BONGStructuralLaws.{u, v} K]
    [structuralPrefix : BONGStructuralLaws.{u, w} K]
    {R₁ R₂ β₁ : Int}
    (reference : GoodBONG r P 3)
    (a : GoodBONG q M (3 + tailLength))
    (D : Beli2019Lemma99Realization (q := r) R₁ (R₂ + 2) R₁ β₁)
    (C : BONG.PrescribedValuesGoodBONGData q (3 + tailLength)
      (beli2019Lemma910Values D a))
    (hprefix : ∀ i : Fin 3,
      reference.valueUnit i = a.valueUnit (Fin.castAdd tailLength i))
    (hternary : Lattice.Represents r r P D.lattice)
    (horders : ∀ i : Fin 3,
      a.order (Fin.castAdd tailLength i) = ![R₁, R₂, R₁] i) :
    Nonempty (Beli2019Lemma910IndexPData a D) := by
  rcases beli2019Lemma910FullCoefficientRealization_represents
      (structuralAmbient := structuralAmbient)
      (structuralPrefix := structuralPrefix)
      reference a D C hprefix hternary with ⟨f⟩
  let hlength : 3 + tailLength = tailLength + 3 := by omega
  let aCast : GoodBONG q M (tailLength + 3) := a.castLength hlength
  let cCast : GoodBONG q C.lattice (tailLength + 3) :=
    C.bong.castLength hlength
  rcases exists_goodBONGSameRankIntegralImageData aCast cCast f with ⟨I⟩
  let imageBONG : GoodBONG q I.imageLattice (3 + tailLength) :=
    I.imageBONG.castLength hlength.symm
  have himageVolume : Lattice.volumeOrder q I.imageLattice =
      Lattice.volumeOrder q C.lattice := by
    rw [I.imageBONG.toBONG.volumeOrder_eq_sum_order,
      cCast.toBONG.volumeOrder_eq_sum_order]
    apply Finset.sum_congr rfl
    intro i _
    exact I.scalarAgreement.order_eq i
  have hvolume : Lattice.volumeOrder q I.imageLattice =
      Lattice.volumeOrder q M + 2 := by
    rw [himageVolume]
    exact volumeOrder_beli2019Lemma910FullCoefficientRealization
      a D C horders
  refine ⟨{
    lattice := I.imageLattice
    bong := imageBONG
    inclusion := ⟨I.image_le, hvolume⟩
    values := ?_
  }⟩
  intro i
  rw [show imageBONG = I.imageBONG.castLength hlength.symm by rfl,
    valueUnit_castLength]
  let j : Fin (tailLength + 3) := ⟨i.val, by omega⟩
  have hj : (⟨i.val, by omega⟩ : Fin (tailLength + 3)) = j := rfl
  rw [hj, I.scalarAgreement.valueUnit_eq]
  change cCast.valueUnit j = beli2019Lemma910Values D a i
  rw [show cCast = C.bong.castLength hlength by rfl,
    valueUnit_castLength, C.values]

end BONG.GoodBONG

end Bong
