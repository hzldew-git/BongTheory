/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.Beli2019Lemma912TypeIIIRepresentation
import Bong.Bong.GoodBONGSameRankIntegralImage
import Bong.Bong.Beli2019VolumeOrders
import Bong.Bong.Beli2019SectionFive
import Bong.Bong.Beli2019Necessity
/-!
# Beli (2019), Lemma 9.12: the literal type-III index-p sublattice

The represented coefficient realization is replaced by its integral image in
the original lattice. Its first order is unchanged, the next two orders rise
by one, and the common tail is unchanged. The BONG volume formula therefore
shows that the image has volume order two larger, which is the normalized
index-p condition used in Section 5.
-/


namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {T : Nat}

variable [BeliCorollary44Laws.{u, v} K]

structure Beli2019Lemma912TypeIIIIndexPData
    (a : GoodBONG q L (3 + T))
    (D : Beli2019Lemma911Data a.typeIIIPair) where
  lattice : Lattice K V
  bong : GoodBONG q lattice (3 + T)
  inclusion : Beli2019IndexPInclusion q L lattice
  values : ∀ i, bong.valueUnit i = typeIIIValues a D i

/-- The original lattice represents its literal type-III image by inclusion;
the 2006 representation theorem therefore supplies all four representation
conditions for the pair. -/
theorem Beli2019Lemma912TypeIIIIndexPData.sourceRepresentationConditions
    [representationLaws : Beli2019InclusionConditionsLaws.{u, v} K]
    (a : GoodBONG q L (3 + T))
    (D : Beli2019Lemma911Data a.typeIIIPair)
    (I : Beli2019Lemma912TypeIIIIndexPData a D)
    (hlength : 3 + T = T + 3) :
    RepresentationConditions (a.castLength hlength)
      (I.bong.castLength hlength) le_rfl := by
  exact (a.castLength hlength).representationConditions_of_lattice_le_via_adapter
    (I.bong.castLength hlength) I.inclusion.lattice_le

theorem beli2019Lemma912TypeIIIRealization_order_zero
    (a : GoodBONG q L (3 + T))
    (D : Beli2019Lemma911Data a.typeIIIPair)
    (C : BONG.PrescribedValuesGoodBONGData q (3 + T)
      (typeIIIValues a D)) :
    C.bong.order (0 : Fin (3 + T)) = a.order (0 : Fin (3 + T)) := by
  unfold GoodBONG.order
  rw [C.bong.toBONG.order_eq_ordUnit]
  change ordUnit K (C.bong.valueUnit (0 : Fin (3 + T))) =
    a.toBONG.order (0 : Fin (3 + T))
  rw [C.values]
  simpa [typeIIIValues, GoodBONG.valueUnit] using
    (a.toBONG.order_eq_ordUnit (0 : Fin (3 + T))).symm

theorem beli2019Lemma912TypeIIIRealization_order_one
    (a : GoodBONG q L (3 + T))
    (D : Beli2019Lemma911Data a.typeIIIPair)
    (C : BONG.PrescribedValuesGoodBONGData q (3 + T)
      (typeIIIValues a D)) :
    C.bong.order (1 : Fin (3 + T)) = a.order (1 : Fin (3 + T)) + 1 := by
  unfold GoodBONG.order
  rw [C.bong.toBONG.order_eq_ordUnit]
  change ordUnit K (C.bong.valueUnit (1 : Fin (3 + T))) =
    a.toBONG.order (1 : Fin (3 + T)) + 1
  rw [C.values]
  let one : Fin (3 + T) := ⟨1, by omega⟩
  have hone : (1 : Fin (3 + T)) = one := by
    apply Fin.ext
    change 1 % (3 + T) = 1
    exact Nat.mod_eq_of_lt (by omega)
  rw [hone]
  simpa only [one, GoodBONG.order] using ordUnit_typeIIIValues_one a D

theorem beli2019Lemma912TypeIIIRealization_order_two
    (a : GoodBONG q L (3 + T))
    (D : Beli2019Lemma911Data a.typeIIIPair)
    (C : BONG.PrescribedValuesGoodBONGData q (3 + T)
      (typeIIIValues a D)) :
    C.bong.order (2 : Fin (3 + T)) = a.order (2 : Fin (3 + T)) + 1 := by
  unfold GoodBONG.order
  rw [C.bong.toBONG.order_eq_ordUnit]
  change ordUnit K (C.bong.valueUnit (2 : Fin (3 + T))) =
    a.toBONG.order (2 : Fin (3 + T)) + 1
  rw [C.values]
  let two : Fin (3 + T) := ⟨2, by omega⟩
  have htwo : (2 : Fin (3 + T)) = two := by
    apply Fin.ext
    change 2 % (3 + T) = 2
    exact Nat.mod_eq_of_lt (by omega)
  rw [htwo]
  simpa only [two, GoodBONG.order] using ordUnit_typeIIIValues_two a D

theorem beli2019Lemma912TypeIIIRealization_order_right
    (a : GoodBONG q L (3 + T))
    (D : Beli2019Lemma911Data a.typeIIIPair)
    (C : BONG.PrescribedValuesGoodBONGData q (3 + T)
      (typeIIIValues a D)) (j : Fin T) :
    C.bong.order (Fin.natAdd 3 j) = a.order (Fin.natAdd 3 j) := by
  unfold GoodBONG.order
  rw [C.bong.toBONG.order_eq_ordUnit]
  change ordUnit K (C.bong.valueUnit (Fin.natAdd 3 j)) =
    a.toBONG.order (Fin.natAdd 3 j)
  rw [C.values, typeIIIValues_of_three_le a D _ (by
    simp only [Fin.val_natAdd]
    omega)]
  exact a.toBONG.order_eq_ordUnit _

/-- The literal integral image preserves the first order of the type-III
realization. -/
theorem beli2019Lemma912TypeIIIIndexPData_order_zero
    (a : GoodBONG q L (3 + T))
    (D : Beli2019Lemma911Data a.typeIIIPair)
    (I : Beli2019Lemma912TypeIIIIndexPData a D) :
    I.bong.order (0 : Fin (3 + T)) = a.order (0 : Fin (3 + T)) := by
  unfold GoodBONG.order
  rw [I.bong.toBONG.order_eq_ordUnit]
  change ordUnit K (I.bong.valueUnit (0 : Fin (3 + T))) =
    a.toBONG.order (0 : Fin (3 + T))
  rw [I.values]
  simpa [typeIIIValues, GoodBONG.valueUnit] using
    (a.toBONG.order_eq_ordUnit (0 : Fin (3 + T))).symm

/-- The second order of the literal type-III index-`p` image rises by one. -/
theorem beli2019Lemma912TypeIIIIndexPData_order_one
    (a : GoodBONG q L (3 + T))
    (D : Beli2019Lemma911Data a.typeIIIPair)
    (I : Beli2019Lemma912TypeIIIIndexPData a D) :
    I.bong.order (1 : Fin (3 + T)) = a.order (1 : Fin (3 + T)) + 1 := by
  unfold GoodBONG.order
  rw [I.bong.toBONG.order_eq_ordUnit]
  change ordUnit K (I.bong.valueUnit (1 : Fin (3 + T))) =
    a.toBONG.order (1 : Fin (3 + T)) + 1
  rw [I.values]
  let one : Fin (3 + T) := ⟨1, by omega⟩
  have hone : (1 : Fin (3 + T)) = one := by
    apply Fin.ext
    change 1 % (3 + T) = 1
    exact Nat.mod_eq_of_lt (by omega)
  rw [hone]
  simpa only [one, GoodBONG.order] using ordUnit_typeIIIValues_one a D

/-- The third order of the literal type-III index-`p` image rises by one. -/
theorem beli2019Lemma912TypeIIIIndexPData_order_two
    (a : GoodBONG q L (3 + T))
    (D : Beli2019Lemma911Data a.typeIIIPair)
    (I : Beli2019Lemma912TypeIIIIndexPData a D) :
    I.bong.order (2 : Fin (3 + T)) = a.order (2 : Fin (3 + T)) + 1 := by
  unfold GoodBONG.order
  rw [I.bong.toBONG.order_eq_ordUnit]
  change ordUnit K (I.bong.valueUnit (2 : Fin (3 + T))) =
    a.toBONG.order (2 : Fin (3 + T)) + 1
  rw [I.values]
  let two : Fin (3 + T) := ⟨2, by omega⟩
  have htwo : (2 : Fin (3 + T)) = two := by
    apply Fin.ext
    change 2 % (3 + T) = 2
    exact Nat.mod_eq_of_lt (by omega)
  rw [htwo]
  simpa only [two, GoodBONG.order] using ordUnit_typeIIIValues_two a D

/-- After changing to the `T + 3` rank convention, the first order is still
unchanged. -/
theorem beli2019Lemma912TypeIIIIndexPData_order_castLength_zero
    (a : GoodBONG q L (3 + T))
    (D : Beli2019Lemma911Data a.typeIIIPair)
    (I : Beli2019Lemma912TypeIIIIndexPData a D)
    (hlength : 3 + T = T + 3) :
    (I.bong.castLength hlength).order (0 : Fin (T + 3)) =
      (a.castLength hlength).order (0 : Fin (T + 3)) := by
  simp only [GoodBONG.order_castLength]
  change I.bong.order (⟨0, by omega⟩ : Fin (3 + T)) =
    a.order (⟨0, by omega⟩ : Fin (3 + T))
  have hzero : (⟨0, by omega⟩ : Fin (3 + T)) = 0 := by
    apply Fin.ext
    simp
  rw [hzero]
  exact beli2019Lemma912TypeIIIIndexPData_order_zero a D I

/-- After changing to the `T + 3` rank convention, the second order is the
source second order plus one. -/
theorem beli2019Lemma912TypeIIIIndexPData_order_castLength_one
    (a : GoodBONG q L (3 + T))
    (D : Beli2019Lemma911Data a.typeIIIPair)
    (I : Beli2019Lemma912TypeIIIIndexPData a D)
    (hlength : 3 + T = T + 3) :
    (I.bong.castLength hlength).order (1 : Fin (T + 3)) =
      (a.castLength hlength).order (1 : Fin (T + 3)) + 1 := by
  simp only [GoodBONG.order_castLength]
  change I.bong.order (⟨1, by omega⟩ : Fin (3 + T)) =
    a.order (⟨1, by omega⟩ : Fin (3 + T)) + 1
  have hone : (⟨1, by omega⟩ : Fin (3 + T)) = 1 := by
    apply Fin.ext
    change 1 = 1 % (3 + T)
    exact (Nat.mod_eq_of_lt (by omega)).symm
  rw [hone]
  exact beli2019Lemma912TypeIIIIndexPData_order_one a D I

/-- After changing to the `T + 3` rank convention, the third order is the
source third order plus one. -/
theorem beli2019Lemma912TypeIIIIndexPData_order_castLength_two
    (a : GoodBONG q L (3 + T))
    (D : Beli2019Lemma911Data a.typeIIIPair)
    (I : Beli2019Lemma912TypeIIIIndexPData a D)
    (hlength : 3 + T = T + 3) :
    (I.bong.castLength hlength).order (2 : Fin (T + 3)) =
      (a.castLength hlength).order (2 : Fin (T + 3)) + 1 := by
  simp only [GoodBONG.order_castLength]
  change I.bong.order (⟨2, by omega⟩ : Fin (3 + T)) =
    a.order (⟨2, by omega⟩ : Fin (3 + T)) + 1
  have htwo : (⟨2, by omega⟩ : Fin (3 + T)) = 2 := by
    apply Fin.ext
    change 2 = 2 % (3 + T)
    exact (Nat.mod_eq_of_lt (by omega)).symm
  rw [htwo]
  exact beli2019Lemma912TypeIIIIndexPData_order_two a D I

/-- After changing to the representation-theorem rank convention, every
coefficient from the fourth onward is literally the source coefficient. -/
theorem beli2019Lemma912TypeIIIIndexPData_valueUnit_castLength_eq_source_of_three_le
    (a : GoodBONG q L (3 + T))
    (D : Beli2019Lemma911Data a.typeIIIPair)
    (I : Beli2019Lemma912TypeIIIIndexPData a D)
    (hlength : 3 + T = T + 3) (i : Fin (T + 3)) (hi : 3 ≤ i.val) :
    (I.bong.castLength hlength).valueUnit i =
      (a.castLength hlength).valueUnit i := by
  rw [valueUnit_castLength, valueUnit_castLength, I.values]
  exact typeIIIValues_of_three_le a D _ (by simpa using hi)

/-- From the fourth coordinate on, the literal type-III index-`p` image has
the same order sequence as the source. -/
theorem beli2019Lemma912TypeIIIIndexPData_order_right
    (a : GoodBONG q L (3 + T))
    (D : Beli2019Lemma911Data a.typeIIIPair)
    (I : Beli2019Lemma912TypeIIIIndexPData a D) (j : Fin T) :
    I.bong.order (Fin.natAdd 3 j) = a.order (Fin.natAdd 3 j) := by
  unfold GoodBONG.order
  rw [I.bong.toBONG.order_eq_ordUnit]
  change ordUnit K (I.bong.valueUnit (Fin.natAdd 3 j)) =
    a.toBONG.order (Fin.natAdd 3 j)
  rw [I.values, typeIIIValues_of_three_le a D _ (by
    simp only [Fin.val_natAdd]
    omega)]
  exact a.toBONG.order_eq_ordUnit _

/-- After changing from the construction's `3 + T` convention to the
representation theorem's `T + 3` convention, every order from the fourth
coordinate onward is still unchanged. -/
theorem beli2019Lemma912TypeIIIIndexPData_order_castLength_eq_source_of_three_le
    (a : GoodBONG q L (3 + T))
    (D : Beli2019Lemma911Data a.typeIIIPair)
    (I : Beli2019Lemma912TypeIIIIndexPData a D)
    (hlength : 3 + T = T + 3) (i : Fin (T + 3)) (hi : 3 ≤ i.val) :
    (I.bong.castLength hlength).order i =
      (a.castLength hlength).order i := by
  let j : Fin T := ⟨i.val - 3, by omega⟩
  let iRaw : Fin (3 + T) := ⟨i.val, by omega⟩
  have hij : Fin.natAdd 3 j = iRaw := by
    apply Fin.ext
    simp only [Fin.val_natAdd, j, iRaw]
    omega
  have hraw := beli2019Lemma912TypeIIIIndexPData_order_right a D I j
  rw [hij] at hraw
  simpa only [GoodBONG.order_castLength, iRaw] using hraw

theorem volumeOrder_beli2019Lemma912TypeIIIRealization
    (a : GoodBONG q L (3 + T))
    (D : Beli2019Lemma911Data a.typeIIIPair)
    (C : BONG.PrescribedValuesGoodBONGData q (3 + T)
      (typeIIIValues a D)) :
    Lattice.volumeOrder q C.lattice = Lattice.volumeOrder q L + 2 := by
  rw [C.bong.toBONG.volumeOrder_eq_sum_order,
    a.toBONG.volumeOrder_eq_sum_order,
    Fin.sum_univ_add, Fin.sum_univ_add]
  have hleftC : (∑ i : Fin 3,
        C.bong.order (Fin.castAdd T i)) =
      (∑ i : Fin 3, a.order (Fin.castAdd T i)) + 2 := by
    rw [Fin.sum_univ_three, Fin.sum_univ_three]
    have hcastZero : Fin.castAdd T (0 : Fin 3) =
        (0 : Fin (3 + T)) := by
      apply Fin.ext
      rfl
    have hcastOne : Fin.castAdd T (1 : Fin 3) =
        (1 : Fin (3 + T)) := by
      apply Fin.ext
      change 1 % 3 = 1 % (3 + T)
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    have hcastTwo : Fin.castAdd T (2 : Fin 3) =
        (2 : Fin (3 + T)) := by
      apply Fin.ext
      change 2 % 3 = 2 % (3 + T)
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hcastZero, hcastOne, hcastTwo]
    change C.bong.order (0 : Fin (3 + T)) +
        C.bong.order (1 : Fin (3 + T)) +
        C.bong.order (2 : Fin (3 + T)) =
      (a.order (0 : Fin (3 + T)) +
        a.order (1 : Fin (3 + T)) +
        a.order (2 : Fin (3 + T))) + 2
    rw [beli2019Lemma912TypeIIIRealization_order_zero a D C,
      beli2019Lemma912TypeIIIRealization_order_one a D C,
      beli2019Lemma912TypeIIIRealization_order_two a D C]
    omega
  have hrightC : (∑ j : Fin T,
        C.bong.order (Fin.natAdd 3 j)) =
      ∑ j : Fin T, a.order (Fin.natAdd 3 j) := by
    apply Finset.sum_congr rfl
    intro j _
    exact beli2019Lemma912TypeIIIRealization_order_right a D C j
  change (∑ i : Fin 3, C.bong.order (Fin.castAdd T i)) +
      (∑ j : Fin T, C.bong.order (Fin.natAdd 3 j)) =
    (∑ i : Fin 3, a.order (Fin.castAdd T i)) +
      (∑ j : Fin T, a.order (Fin.natAdd 3 j)) + 2
  rw [hleftC, hrightC]
  omega

theorem exists_beli2019Lemma912TypeIIIIndexPData
    [structural : BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q L (3 + T))
    (D : Beli2019Lemma911Data a.typeIIIPair)
    (C : BONG.PrescribedValuesGoodBONGData q (3 + T)
      (typeIIIValues a D)) :
    Nonempty (Beli2019Lemma912TypeIIIIndexPData a D) := by
  rcases beli2019Lemma912TypeIIIRealization_represents
      (structural := structural) a D C with ⟨f⟩
  let hlength : 3 + T = T + 3 := by omega
  let aCast : GoodBONG q L (T + 3) := a.castLength hlength
  let cCast : GoodBONG q C.lattice (T + 3) :=
    C.bong.castLength hlength
  rcases exists_goodBONGSameRankIntegralImageData aCast cCast f with ⟨I⟩
  let imageBONG : GoodBONG q I.imageLattice (3 + T) :=
    I.imageBONG.castLength hlength.symm
  have himageVolume : Lattice.volumeOrder q I.imageLattice =
      Lattice.volumeOrder q C.lattice := by
    rw [I.imageBONG.toBONG.volumeOrder_eq_sum_order,
      cCast.toBONG.volumeOrder_eq_sum_order]
    apply Finset.sum_congr rfl
    intro i _
    exact I.scalarAgreement.order_eq i
  have hvolume : Lattice.volumeOrder q I.imageLattice =
      Lattice.volumeOrder q L + 2 := by
    rw [himageVolume]
    exact volumeOrder_beli2019Lemma912TypeIIIRealization a D C
  refine ⟨{
    lattice := I.imageLattice
    bong := imageBONG
    inclusion := ⟨I.image_le, hvolume⟩
    values := ?_
  }⟩
  intro i
  rw [show imageBONG = I.imageBONG.castLength hlength.symm by rfl,
    valueUnit_castLength]
  let j : Fin (T + 3) := ⟨i.val, by omega⟩
  have hj : (⟨i.val, by omega⟩ : Fin (T + 3)) = j := rfl
  rw [hj, I.scalarAgreement.valueUnit_eq]
  change cCast.valueUnit j = typeIIIValues a D i
  rw [show cCast = C.bong.castLength hlength by rfl,
    valueUnit_castLength, C.values]

end BONG.GoodBONG

end Bong
