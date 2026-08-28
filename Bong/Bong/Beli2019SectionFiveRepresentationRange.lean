/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFiveCutoffGeometry
import Bong.Bong.Beli2019SectionFiveRepresentationDual

/-!
# Reduced ranges for Beli (2019), conditions 2.1(iii) and 2.1(iv)

Section 5.2 reduces condition (iii) to `i \le n_{k_2}+1` and condition
(iv) to `i \le n_{k_2}+a-1`.  The second cutoff is the defect cutoff
already used for condition (ii).  This file records both direct ranges and
proves that every remaining boundary belongs to the direct range of the
swapped reverse-dual inclusion.
-/

namespace Bong

open Dyadic Module

universe u v

namespace Lattice.Beli2019Lemma51Data

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V}

/-- The direct cutoff `n_{k_2}+1` in the proof of condition 2.1(iii). -/
noncomputable def centralReducedCutoff
    (D : Beli2019Lemma51Data q M N) : Nat :=
  D.smallSelectedStart + 1

/-- The direct range in Section 5.14 for condition 2.1(iii). -/
def CentralReducedRange
    (D : Beli2019Lemma51Data q M N) {rank : Nat}
    (i : CentralRepresentationIndex rank rank) : Prop :=
  i.val ≤ D.centralReducedCutoff

/-- The direct range in Section 5.15 for condition 2.1(iv). -/
def LongReducedRange
    (D : Beli2019Lemma51Data q M N) {rank : Nat}
    (i : LongRepresentationIndex rank rank) : Prop :=
  i.val ≤ D.defectReducedCutoff

/-- In a selected unary block the central cutoff is one greater than the
defect cutoff; in a selected binary block the two cutoffs agree. -/
theorem centralReducedCutoff_eq_defectReducedCutoff_add
    (D : Beli2019Lemma51Data q M N) :
    D.centralReducedCutoff = D.defectReducedCutoff +
      (2 - finrank K D.input.block.component.carrier) := by
  rcases D.rank_one_or_two with hfin | hfin
  · simp only [centralReducedCutoff, defectReducedCutoff,
      D.smallAlmostJordan_finrank_selected, hfin]
    omega
  · simp only [centralReducedCutoff, defectReducedCutoff,
      D.smallAlmostJordan_finrank_selected, hfin]
    omega

/-- The original and swapped reverse-dual central cutoffs cover the ambient
rank.  This is the numerical content of the reduction `i \le n_{k_2}+1`.
-/
theorem centralReducedCutoff_add_reverseDual_ge
    (D : Beli2019Lemma51Data q M N)
    (E : Beli2019Lemma51Data q (Lattice.dualLattice q N)
      (Lattice.dualLattice q M)) :
    (finrank K V : Int) ≤
      (D.centralReducedCutoff : Int) +
        (E.centralReducedCutoff : Int) := by
  have hstrong :=
    D.defectReducedCutoff_add_reverseDual_ge_rank_add_selected_sub_two E
  have hrank := D.reverseDual_selectedRank E
  have hD := D.centralReducedCutoff_eq_defectReducedCutoff_add
  have hE := E.centralReducedCutoff_eq_defectReducedCutoff_add
  rcases D.rank_one_or_two with hfin | hfin
  · have hfinE : finrank K E.input.block.component.carrier = 1 := by
      omega
    rw [hD, hE, hfin, hfinE]
    norm_num
    omega
  · have hfinE : finrank K E.input.block.component.carrier = 2 := by
      omega
    rw [hD, hE, hfin, hfinE]
    norm_num
    omega

/-- Every central boundary is covered directly on the original side or at
the complementary central boundary of the swapped reverse-dual side. -/
theorem centralReducedRange_or_reverseDualReducedRange
    (D : Beli2019Lemma51Data q M N)
    (E : Beli2019Lemma51Data q (Lattice.dualLattice q N)
      (Lattice.dualLattice q M))
    {rank : Nat} (i : CentralRepresentationIndex rank rank)
    (hrank : rank = finrank K V) :
    D.CentralReducedRange i ∨
      E.CentralReducedRange i.reversePrevious := by
  by_cases hi : i.val ≤ D.centralReducedCutoff
  · exact Or.inl hi
  · right
    have hcover := D.centralReducedCutoff_add_reverseDual_ge E
    change i.reversePrevious.val ≤ E.centralReducedCutoff
    simp only [CentralRepresentationIndex.reversePrevious_val]
    have := i.one_lt
    have := i.lt_large
    omega

/-- Every long boundary is covered directly on the original side or at the
complementary long boundary of the swapped reverse-dual side. -/
theorem longReducedRange_or_reverseDualReducedRange
    (D : Beli2019Lemma51Data q M N)
    (E : Beli2019Lemma51Data q (Lattice.dualLattice q N)
      (Lattice.dualLattice q M))
    {rank : Nat} (i : LongRepresentationIndex rank rank)
    (hrank : rank = finrank K V) :
    D.LongReducedRange i ∨
      E.LongReducedRange i.reverseComplement := by
  by_cases hi : i.val ≤ D.defectReducedCutoff
  · exact Or.inl hi
  · right
    have hcover := D.defectReducedCutoff_add_reverseDual_ge E
    change i.reverseComplement.val ≤ E.defectReducedCutoff
    simp only [LongRepresentationIndex.reverseComplement_val]
    have := i.one_lt
    have := i.succ_lt_large
    omega

end Lattice.Beli2019Lemma51Data

end Bong
