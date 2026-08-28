/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma513DualAssembly
import Bong.Bong.Beli2019AlmostJordanProfile

/-!
# Beli (2019), Section 5.2 reduced ranges

The direct Section 5 calculation stops immediately before the last coordinate
of the distinguished unary-or-binary block.  The swapped reverse-dual
calculation covers the complementary numerical range.  This file defines the
cutoff from the weak almost-Jordan profile and proves the arithmetic cover.
-/

open scoped BigOperators

namespace Bong

open Dyadic
open Module

universe u v

namespace Lattice.Beli2019Lemma51Data

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V}

/-- The number of coordinates strictly before the distinguished block in
the smaller almost-Jordan decomposition. -/
noncomputable def smallSelectedStart (D : Beli2019Lemma51Data q M N) : Nat :=
  ∑ p ∈ Finset.Iio D.smallSelectedPosition,
    finrank K (D.smallAlmostJordan.component p).carrier

/-- The number `n_{k₁}` of coordinates strictly before the distinguished
block in the larger almost-Jordan decomposition.  This is the left endpoint
used in Lemma 5.17; in the exceptional unary transposition it is strictly
smaller than `smallSelectedStart`. -/
noncomputable def largeSelectedStart (D : Beli2019Lemma51Data q M N) : Nat :=
  ∑ p ∈ Finset.Iio D.largeSelectedPosition,
    finrank K (D.largeAlmostJordan.component p).carrier

/-- The last boundary `n_{k₁} + a - 1` to which Lemma 5.17 applies. -/
noncomputable def lemma517Cutoff
    (D : Beli2019Lemma51Data q M N) : Nat :=
  D.largeSelectedStart +
    finrank K (D.largeAlmostJordan.component D.largeSelectedPosition).carrier - 1

/-- The first direct range in Section 5.2, which is exactly the range of
Lemma 5.17.  It must not be replaced by `DefectReducedRange`: the latter
also contains the exceptional interval created by a unary transposition. -/
def Lemma517Range
    (D : Beli2019Lemma51Data q M N) {rank : Nat}
    (i : RepresentationIndex rank rank) : Prop :=
  i.val ≤ D.lemma517Cutoff

/-- The last boundary covered directly in Section 5.13.  If the selected
block has rank `a`, this is `n_{k₂} + a - 1` in the paper. -/
noncomputable def defectReducedCutoff
    (D : Beli2019Lemma51Data q M N) : Nat :=
  D.smallSelectedStart +
    finrank K (D.smallAlmostJordan.component D.smallSelectedPosition).carrier - 1

/-- The direct reduced range for condition 2.1(ii). -/
def DefectReducedRange
    (D : Beli2019Lemma51Data q M N) {rank : Nat}
    (i : RepresentationIndex rank rank) : Prop :=
  i.val ≤ D.defectReducedCutoff

/-- The complementary range, expressed in reverse-dual coordinates. -/
def DefectReverseRange
    (D : Beli2019Lemma51Data q M N) {rank : Nat}
    (j : RepresentationIndex rank rank) : Prop :=
  j.val + D.defectReducedCutoff < rank

/-- Every equal-rank boundary is either in the direct range or its reverse
is in the complementary dual range. -/
theorem defectReducedRange_or_reverseRange
    (D : Beli2019Lemma51Data q M N) {rank : Nat}
    (i : RepresentationIndex rank rank) :
    D.DefectReducedRange i ∨ D.DefectReverseRange i.reverse := by
  by_cases hi : i.val ≤ D.defectReducedCutoff
  · exact Or.inl hi
  · right
    change i.reverse.val + D.defectReducedCutoff < rank
    simp only [RepresentationIndex.reverse_val]
    have hpos := i.pos
    have hlt := i.lt_large
    omega

end Lattice.Beli2019Lemma51Data

end Bong
