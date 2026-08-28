/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma714NonNormTransport
import Bong.Bong.TwoBlockProductIsometry
import Bong.Lattice.VolumeInclusion

/-!
# Beli (2019), Lemma 7.14: the special lattice without a scale hypothesis

In the equal-first-gap branch of Section 7, the paper replaces the initial
binary summand `J` by `pi J`.  The resulting lattice is therefore most
faithfully defined as the image of `pi J perp T` under the actual two-block
product isometry.  This definition is unconditional; the scale hypothesis
needed by the general `nonNormGeneratorLattice` constructor is not present in
this branch of the paper.

The pointwise split-model calculation still proves that this image consists
exactly of the vectors of the parent lattice which are not norm generators.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.TwoBlockSplitWitness

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
  {b : BONG V q L n}

/-- The literal Section-7 special lattice: the image of `pi J perp T` in
the original ambient quadratic space. -/
noncomputable def lemma714SpecialLattice
    {hcut : 2 ≤ n} (S : TwoBlockSplitWitness b 2 hcut) : Lattice K V :=
  Lattice.map S.toProductLatticeIsometry.toLinearEquiv
    (Lattice.product
      (Lattice.rescale (uniformizerUnit K) S.left.lattice)
      S.right.lattice)

/-- The defining map is an integral isometry from `pi J perp T` to the
special lattice. -/
noncomputable def rescaledLeftProductToLemma714SpecialLattice
    {hcut : 2 ≤ n} (S : TwoBlockSplitWitness b 2 hcut) :
    Lattice.Isometry
      ((q.restrict S.left.carrier S.left.nondegenerate).orthogonalSum
        (q.restrict S.right.carrier S.right.nondegenerate))
      q
      (Lattice.product
        (Lattice.rescale (uniformizerUnit K) S.left.lattice)
        S.right.lattice)
      S.lemma714SpecialLattice :=
  Lattice.Isometry.toMap _
    S.toProductLatticeIsometry.toQuadraticSpaceIsometry _

/-- The special lattice is contained in its parent lattice. -/
theorem lemma714SpecialLattice_le
    {hcut : 2 ≤ n} (S : TwoBlockSplitWitness b 2 hcut) :
    S.lemma714SpecialLattice ≤ L := by
  intro y hy
  have hzScaled := (Lattice.mem_map_iff
    S.toProductLatticeIsometry.toLinearEquiv
    (Lattice.product
      (Lattice.rescale (uniformizerUnit K) S.left.lattice)
      S.right.lattice) y).1 hy
  have hpiLe : Lattice.rescale (uniformizerUnit K) S.left.lattice ≤
      S.left.lattice := by
    apply Lattice.rescale_le_self_of_mem_integerRing
    rw [coe_uniformizerUnit, mem_integerRing_iff, Dyadic.IsIntegral,
      ord_uniformizer]
    norm_num
  have hzProduct :
      S.toProductLatticeIsometry.toLinearEquiv.symm y ∈
        Lattice.product S.left.lattice S.right.lattice :=
    Lattice.mem_product_iff.mpr
      ⟨hpiLe (Lattice.mem_product_iff.mp hzScaled).1,
        (Lattice.mem_product_iff.mp hzScaled).2⟩
  have hmapped := (S.toProductLatticeIsometry.map_mem _).1 hzProduct
  simpa using hmapped

/-- Pointwise identification used in the paper: the special lattice is
exactly the set of non-norm generators of the parent lattice.  Unlike the
general lattice constructor from Lemma 7.1, this theorem needs no scale
hypothesis. -/
theorem mem_lemma714SpecialLattice_iff
    {hcut : 2 ≤ n} (S : TwoBlockSplitWitness b 2 hcut) (R : Int)
    (hnormJ : Lattice.normIdeal
      (q.restrict S.left.carrier S.left.nondegenerate) S.left.lattice =
        Lattice.powerIdeal (K := K) R)
    (hnormT : Lattice.normIdeal
      (q.restrict S.right.carrier S.right.nondegenerate) S.right.lattice ≤
        Lattice.powerIdeal (K := K) (R + 1))
    (hprimitive : Lattice.EveryPrimitiveIsNormGenerator
      (q.restrict S.left.carrier S.left.nondegenerate) S.left.lattice)
    (y : V) :
    y ∈ S.lemma714SpecialLattice ↔
      y ∈ L ∧ ¬ Lattice.IsNormGenerator q L y := by
  let z := S.toProductLatticeIsometry.toLinearEquiv.symm y
  have hmapz : S.toProductLatticeIsometry.toLinearEquiv z = y := by
    simp [z]
  rw [show y ∈ S.lemma714SpecialLattice ↔
      z ∈ Lattice.product
        (Lattice.rescale (uniformizerUnit K) S.left.lattice)
        S.right.lattice by
      exact Lattice.mem_map_iff _ _ _]
  constructor
  · intro hzScaled
    have hpiLe : Lattice.rescale (uniformizerUnit K) S.left.lattice ≤
        S.left.lattice := by
      apply Lattice.rescale_le_self_of_mem_integerRing
      rw [coe_uniformizerUnit, mem_integerRing_iff, Dyadic.IsIntegral,
        ord_uniformizer]
      norm_num
    have hzProduct : z ∈
        Lattice.product S.left.lattice S.right.lattice :=
      Lattice.mem_product_iff.mpr
        ⟨hpiLe (Lattice.mem_product_iff.mp hzScaled).1,
          (Lattice.mem_product_iff.mp hzScaled).2⟩
    constructor
    · simpa [hmapz] using
        (S.toProductLatticeIsometry.map_mem z).1 hzProduct
    · intro hyGenerator
      have hzGenerator : Lattice.IsNormGenerator
          ((q.restrict S.left.carrier S.left.nondegenerate).orthogonalSum
            (q.restrict S.right.carrier S.right.nondegenerate))
          (Lattice.product S.left.lattice S.right.lattice) z :=
        (Lattice.isNormGenerator_map_iff
          S.toProductLatticeIsometry z).1 (by simpa [hmapz] using hyGenerator)
      exact
        (Lattice.not_isNormGenerator_orthogonalProduct_iff_left_mem_rescale
          R hnormJ hnormT hprimitive z hzProduct).2
            (Lattice.mem_product_iff.mp hzScaled).1 hzGenerator
  · rintro ⟨hyL, hyNotGenerator⟩
    have hzProduct : z ∈
        Lattice.product S.left.lattice S.right.lattice :=
      (S.toProductLatticeIsometry.map_mem z).2 (by simpa [hmapz] using hyL)
    have hzNotGenerator : ¬ Lattice.IsNormGenerator
        ((q.restrict S.left.carrier S.left.nondegenerate).orthogonalSum
          (q.restrict S.right.carrier S.right.nondegenerate))
        (Lattice.product S.left.lattice S.right.lattice) z := by
      intro hzGenerator
      apply hyNotGenerator
      have := (Lattice.isNormGenerator_map_iff
        S.toProductLatticeIsometry z).2 hzGenerator
      simpa [hmapz] using this
    have hxScaled :=
      (Lattice.not_isNormGenerator_orthogonalProduct_iff_left_mem_rescale
        R hnormJ hnormT hprimitive z hzProduct).1 hzNotGenerator
    exact Lattice.mem_product_iff.mpr
      ⟨hxScaled, (Lattice.mem_product_iff.mp hzProduct).2⟩

/-- Once one norm generator is exhibited, the special lattice is a strict
sub-lattice and hence has strictly larger volume order. -/
theorem lemma714SpecialLattice_volumeOrder_lt
    {hcut : 2 ≤ n} (S : TwoBlockSplitWitness b 2 hcut) (R : Int)
    (hnormJ : Lattice.normIdeal
      (q.restrict S.left.carrier S.left.nondegenerate) S.left.lattice =
        Lattice.powerIdeal (K := K) R)
    (hnormT : Lattice.normIdeal
      (q.restrict S.right.carrier S.right.nondegenerate) S.right.lattice ≤
        Lattice.powerIdeal (K := K) (R + 1))
    (hprimitive : Lattice.EveryPrimitiveIsNormGenerator
      (q.restrict S.left.carrier S.left.nondegenerate) S.left.lattice)
    (x : V) (hxGenerator : Lattice.IsNormGenerator q L x) :
    Lattice.volumeOrder q L <
      Lattice.volumeOrder q S.lemma714SpecialLattice := by
  have hle := Lattice.volumeOrder_mono_of_le q S.lemma714SpecialLattice_le
  have hne : S.lemma714SpecialLattice ≠ L := by
    intro heq
    have hxSpecial : x ∈ S.lemma714SpecialLattice := by
      rw [heq]
      exact hxGenerator.mem
    have hxNot := (S.mem_lemma714SpecialLattice_iff R hnormJ hnormT
      hprimitive x).1 hxSpecial
    exact hxNot.2 hxGenerator
  have hvolumeNe : Lattice.volumeOrder q S.lemma714SpecialLattice ≠
      Lattice.volumeOrder q L := by
    intro hvolume
    exact hne (Lattice.eq_of_le_of_volumeOrder_eq q
      S.lemma714SpecialLattice L S.lemma714SpecialLattice_le hvolume)
  omega

end BONG.TwoBlockSplitWitness

end Bong
