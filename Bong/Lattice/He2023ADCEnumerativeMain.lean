/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Mathlib.Tactic
import Bong.Lattice.He2023ADCSectionEight

/-!
# He (2025), Corollary 1.8 and Theorem 1.11

This file formalizes the finite-enumeration deductions at the end of the
paper.  The external classification inputs remain explicit: Corollary 1.8
uses Hanke's 115 rational classes and Kirschmer's 471 non-rational classes;
Theorem 1.11 uses Oh's 48 stable `2`-regular candidates and the local checks
printed in Tables 1--2.

The literal 21 source rows selected by Table 2 are encoded and checked for
membership and nonrepetition.  The global `2`-ADC conclusion is then derived
from the already formalized Corollary 8.5, rather than included in the table
law package.
-/

namespace Bong

universe u v w

/-- The two cited one-class enumeration results and their disjoint union.
The three types represent isometry classes, not raw lattice presentations. -/
structure HeADC2025Corollary18EnumerationData where
  RationalClasses : Type u
  OtherTotallyRealClasses : Type u
  AllClasses : Type u
  rationalFintype : Fintype RationalClasses
  otherFintype : Fintype OtherTotallyRealClasses
  allFintype : Fintype AllClasses
  partition : AllClasses ≃ RationalClasses ⊕ OtherTotallyRealClasses
  rational_card : @Fintype.card RationalClasses rationalFintype = 115
  other_card : @Fintype.card OtherTotallyRealClasses otherFintype = 471

namespace HeADC2025Corollary18EnumerationData

/-- He (2025), Corollary 1.8: the two published external catalogues contain
`115 + 471 = 586` isometry classes in total. -/
theorem heADC2025Corollary18
    (E : HeADC2025Corollary18EnumerationData.{u}) :
    @Fintype.card E.AllClasses E.allFintype = 586 := by
  letI : Fintype E.RationalClasses := E.rationalFintype
  letI : Fintype E.OtherTotallyRealClasses := E.otherFintype
  letI : Fintype E.AllClasses := E.allFintype
  rw [Fintype.card_congr E.partition, Fintype.card_sum,
    E.rational_card, E.other_card]

end HeADC2025Corollary18EnumerationData

/-! ## The literal Table 2 selection -/

/-- The source-row numbers in Table 1, written with zero-based `Fin 48`
indices.  These are rows 1--15, 19, 25, 30--32, and 44 in the paper. -/
def heADC2025Theorem111TableTwoSourceIndex : Fin 21 → Fin 48 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14,
    18, 24, 29, 30, 31, 43]

/-- Predicate selecting exactly the Table 1 candidates retained in Table 2. -/
def HeADC2025Theorem111IsSelected (i : Fin 48) : Prop :=
  i.val < 15 ∨ i.val = 18 ∨ i.val = 24 ∨ i.val = 29 ∨
    i.val = 30 ∨ i.val = 31 ∨ i.val = 43

/-- The subtype of Oh candidates retained by the published local checks. -/
abbrev HeADC2025Theorem111Index :=
  {i : Fin 48 // HeADC2025Theorem111IsSelected i}

instance (i : Fin 48) : Decidable (HeADC2025Theorem111IsSelected i) := by
  unfold HeADC2025Theorem111IsSelected
  infer_instance

theorem heADC2025Theorem111TableTwoSourceIndex_selected
    (i : Fin 21) :
    HeADC2025Theorem111IsSelected
      (heADC2025Theorem111TableTwoSourceIndex i) := by
  fin_cases i <;>
    simp [heADC2025Theorem111TableTwoSourceIndex,
      HeADC2025Theorem111IsSelected]

theorem heADC2025Theorem111TableTwoSourceIndex_injective :
    Function.Injective heADC2025Theorem111TableTwoSourceIndex := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [heADC2025Theorem111TableTwoSourceIndex]

theorem card_heADC2025Theorem111Index :
    Fintype.card HeADC2025Theorem111Index = 21 := by
  decide

/-- The literal Table 2 numbering is equivalent to the selected subtype. -/
noncomputable def heADC2025Theorem111TableTwoEquiv :
    Fin 21 ≃ HeADC2025Theorem111Index :=
  Equiv.ofBijective
    (fun i ↦ ⟨heADC2025Theorem111TableTwoSourceIndex i,
      heADC2025Theorem111TableTwoSourceIndex_selected i⟩)
    ((Fintype.bijective_iff_injective_and_card _).2 ⟨by
      intro i j hij
      exact heADC2025Theorem111TableTwoSourceIndex_injective
        (congrArg Subtype.val hij), by
      rw [Fintype.card_fin, card_heADC2025Theorem111Index]⟩)

/-- The sole nonmaximal Table 2 row is row 10 in either numbering. -/
theorem heADC2025Theorem111TableTwoSourceIndex_ne_nine_iff
    (i : Fin 21) :
    (heADC2025Theorem111TableTwoSourceIndex i).val ≠ 9 ↔ i.val ≠ 9 := by
  fin_cases i <;> decide

/-! ## Abstract lattice data and the exact 21-row theorem -/

/-- The 48 stable candidates and the lattices obtained from them by the
paper's half-scaling convention. -/
structure HeADC2025Theorem111Data
    (S : GlobalLocalLatticeSystem.{u, v, w}) where
  stableSource : Fin 48 → S.GlobalLattice
  candidate : Fin 48 → S.GlobalLattice

namespace HeADC2025Theorem111Data

variable {S : GlobalLocalLatticeSystem.{u, v, w}}
  (D : HeADC2025Theorem111Data S)

/-- Table 2 as a 21-entry family in its printed order. -/
def tableTwoModel (i : Fin 21) : S.GlobalLattice :=
  D.candidate (heADC2025Theorem111TableTwoSourceIndex i)

end HeADC2025Theorem111Data

/-- External enumeration and local-verification inputs used by the published
proof of Theorem 1.11.  The `2`-ADC property of the selected rows is not a
field: it is derived below from local `2`-ADC and Corollary 8.5. -/
structure HeADC2025Theorem111Laws
    {S : GlobalLocalLatticeSystem.{u, v, w}}
    (G : HeADC2025GlobalData S) (D : HeADC2025Theorem111Data S)
    (positiveDefinite : S.GlobalLattice → Prop) : Prop where
  theorem13 : S.Theorem13Laws
  sectionEight : G.SectionEightLaws
  candidate_rank (i : Fin 48) : S.globalRank (D.candidate i) = 4
  candidate_positiveDefinite (i : Fin 48) :
    positiveDefinite (D.candidate i)
  source_stable (i : Fin 48) : G.isStable (D.stableSource i)
  source_twoRegular (i : Fin 48) : S.IsNRegular (D.stableSource i) 2
  candidate_halfScale (i : Fin 48) :
    G.isHalfScaleOf (D.candidate i) (D.stableSource i)
  candidate_localTwoADC_iff (i : Fin 48) :
    S.IsLocallyNADC (D.candidate i) 2 ↔
      HeADC2025Theorem111IsSelected i
  candidate_exhaustion (M : S.GlobalLattice) :
    positiveDefinite M → S.globalRank M = 4 → S.IsGloballyNADC M 2 →
      ∃ i : Fin 48, G.isIsometric M (D.candidate i)
  isometric_globalTwoADC_iff {M N : S.GlobalLattice} :
    G.isIsometric M N →
      (S.IsGloballyNADC M 2 ↔ S.IsGloballyNADC N 2)
  candidate_irredundant {i j : Fin 48} :
    HeADC2025Theorem111IsSelected i →
      HeADC2025Theorem111IsSelected j →
      G.isIsometric (D.candidate i) (D.candidate j) → i = j
  candidate_classNumberOne (i : Fin 48) :
    HeADC2025Theorem111IsSelected i →
      G.HasClassNumberOne (D.candidate i)
  candidate_maximal_iff (i : Fin 48) :
    HeADC2025Theorem111IsSelected i →
      (G.isGlobalMaximal (D.candidate i) ↔ i.val ≠ 9)

namespace HeADC2025Theorem111Laws

variable {S : GlobalLocalLatticeSystem.{u, v, w}}
  {G : HeADC2025GlobalData S} {D : HeADC2025Theorem111Data S}
  {positiveDefinite : S.GlobalLattice → Prop}

/-- Exact semantic content of Theorem 1.11 for the literal 21-entry Table 2
family. -/
structure Conclusion : Prop where
  rank (i : Fin 21) : S.globalRank (D.tableTwoModel i) = 4
  isPositiveDefinite (i : Fin 21) : positiveDefinite (D.tableTwoModel i)
  twoADC (i : Fin 21) : S.IsGloballyNADC (D.tableTwoModel i) 2
  complete (M : S.GlobalLattice) :
    positiveDefinite M → S.globalRank M = 4 → S.IsGloballyNADC M 2 →
      ∃ i : Fin 21, G.isIsometric M (D.tableTwoModel i)
  irredundant {i j : Fin 21} :
    G.isIsometric (D.tableTwoModel i) (D.tableTwoModel j) → i = j
  card : Fintype.card (Fin 21) = 21
  halfScale (i : Fin 21) :
    G.isHalfScaleOf (D.tableTwoModel i)
      (D.stableSource (heADC2025Theorem111TableTwoSourceIndex i))
  classNumberOne (i : Fin 21) :
    G.HasClassNumberOne (D.tableTwoModel i)
  maximal_iff_not_rowTen (i : Fin 21) :
    G.isGlobalMaximal (D.tableTwoModel i) ↔ i.val ≠ 9

/-- He (2025), Theorem 1.11, relative to the explicit Oh-table and local
verification laws above. -/
theorem heADC2025Theorem111
    (H : HeADC2025Theorem111Laws G D positiveDefinite) :
    Conclusion (G := G) (D := D) (positiveDefinite := positiveDefinite) where
  rank i := H.candidate_rank _
  isPositiveDefinite i := H.candidate_positiveDefinite _
  twoADC i := by
    apply (H.sectionEight.heADC2025Corollary85 H.theorem13
      (D.tableTwoModel i)).mpr
    refine ⟨(H.candidate_localTwoADC_iff _).mpr
      (heADC2025Theorem111TableTwoSourceIndex_selected i), ?_⟩
    exact ⟨D.stableSource _, H.source_stable _, H.source_twoRegular _,
      H.candidate_halfScale _⟩
  complete M hPositive hRank hADC := by
    obtain ⟨j, hIso⟩ := H.candidate_exhaustion M hPositive hRank hADC
    have hCandidateADC : S.IsGloballyNADC (D.candidate j) 2 :=
      (H.isometric_globalTwoADC_iff hIso).mp hADC
    have hLocal : S.IsLocallyNADC (D.candidate j) 2 :=
      (H.theorem13.globallyNADC_implies_locallyNADC_and_nRegular
        (D.candidate j) 2 hCandidateADC).1
    have hSelected : HeADC2025Theorem111IsSelected j :=
      (H.candidate_localTwoADC_iff j).mp hLocal
    let k : HeADC2025Theorem111Index := ⟨j, hSelected⟩
    let i : Fin 21 := heADC2025Theorem111TableTwoEquiv.symm k
    have hi : heADC2025Theorem111TableTwoSourceIndex i = j := by
      exact congrArg Subtype.val
        (heADC2025Theorem111TableTwoEquiv.apply_symm_apply k)
    exact ⟨i, by simpa [HeADC2025Theorem111Data.tableTwoModel, hi] using hIso⟩
  irredundant {i j} hIso := by
    apply heADC2025Theorem111TableTwoSourceIndex_injective
    exact H.candidate_irredundant
      (heADC2025Theorem111TableTwoSourceIndex_selected i)
      (heADC2025Theorem111TableTwoSourceIndex_selected j) hIso
  card := Fintype.card_fin 21
  halfScale i := H.candidate_halfScale _
  classNumberOne i := H.candidate_classNumberOne _
    (heADC2025Theorem111TableTwoSourceIndex_selected i)
  maximal_iff_not_rowTen i := by
    change G.isGlobalMaximal
      (D.candidate (heADC2025Theorem111TableTwoSourceIndex i)) ↔ i.val ≠ 9
    rw [H.candidate_maximal_iff _
      (heADC2025Theorem111TableTwoSourceIndex_selected i)]
    exact heADC2025Theorem111TableTwoSourceIndex_ne_nine_iff i

end HeADC2025Theorem111Laws

end Bong
