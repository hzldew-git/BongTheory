/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma716AtS
import Bong.Bong.Beli2019Lemma716Nonessential
import Bong.Bong.Beli2019Lemma716DefectEasy
import Bong.Bong.Beli2019Lemma716TypeISMinusTwo
import Bong.Bong.Beli2019Lemma716TypeISMinusOne
import Bong.Bong.Beli2019Lemma716TypeIISMinusTwo
import Bong.Bong.Beli2019Lemma716TypeIISMinusOne

/-!
# Beli (2019), Lemma 7.16: condition 2.1(ii)

This file assembles the pointwise defect estimates over every ordinary
representation index.  The case `s = 2` is separated because the first
boundary then coincides with `s - 1`; for `s > 2`, the evenness of the
stopping index gives `4 ≤ s` and the paper's ranges are disjoint.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- Representation indices are determined by their natural-number value. -/
theorem representationIndex_eq_of_val_eq
    {largeRank smallRank : Nat}
    (i j : RepresentationIndex largeRank smallRank)
    (h : i.val = j.val) : i = j := by
  cases i with
  | mk iv ip il is =>
      cases j with
      | mk jv jp jl js =>
          simp only [RepresentationIndex.val] at h
          subst jv
          rfl

/-- Transport a pointwise defect statement between proof-irrelevant
representatives of the same paper index. -/
theorem representationDefectAt_of_val_eq
    (a : GoodBONG q L (n + 3)) (c : GoodBONG q N (n + 3))
    (i j : RepresentationIndex (n + 3) (n + 3))
    (hval : i.val = j.val) (hj : a.RepresentationDefectAt c j) :
    a.RepresentationDefectAt c i := by
  rw [representationIndex_eq_of_val_eq i j hval]
  exact hj

variable [Beli2006AlphaLaws.{u, v} K]
variable [Beli2009AlphaParityLaws.{u, v} K]
variable [laws : DyadicDiscriminantClassLaws K]
variable [DyadicAlternatingEndpointTowerRepresentationLaws K]

/-- Complete condition 2.1(ii) in the type-I branch of Lemma 7.16. -/
theorem lemma716_typeI_defectCondition
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData a R s)
    (hfirst : a.order 0 = R)
    (hsecond : a.order 1 =
      R - 2 * (ramificationIndex K : Int))
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (hac : RepresentationConditionsPrime a c le_rfl)
    (hI : Lemma714IsTypeI a R s)
    (hdiscriminant : a.toBONG.adjacentUnitSquareClass
      (0 : Fin (n + 3)) (by simp) = unitSquareClass K
        (lemma712DiscriminantParameter (K := K)))
    (hvalues : ∀ j, b.valueUnit j =
      lemma714TypeITargetValues a s D.two_le D.le_rank j)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (horders : ∀ j, s ≤ j.val → a.order j = b.order j)
    (halphas : ∀ j, s ≤ j.val → a.alphaValue j = b.alphaValue j)
    (hprefix : ∀ (k : Nat), s ≤ k → (hk : k ≤ n + 3) →
      (a.prefixDiagonalSpace k hk).IsIsometric
        (b.prefixDiagonalSpace k hk)) :
    b.RepresentationDefectCondition c := by
  apply (b.representationDefectCondition_iff_forall_at c).mpr
  intro i
  by_cases hsTwo : s = 2
  · by_cases hiOne : i.val = 1
    · let j : RepresentationIndex (n + 3) (n + 3) :=
        { val := s - 1
          pos := by have := D.two_le; omega
          lt_large := by have := D.le_rank; omega
          le_small := by have := D.le_rank; omega }
      apply b.representationDefectAt_of_val_eq c i j (by
        dsimp only [j]
        omega)
      simpa only [j] using
        a.lemma716_typeI_sMinusOne_representationDefectAt b c R s D
          hfirst hsecond hthird hnorm hvalues horderBC
    · by_cases hiS : i.val = s
      · have hsInterior : s < n + 3 := by
          rw [← hiS]
          exact i.lt_large
        let j : RepresentationIndex (n + 3) (n + 3) :=
          { val := s
            pos := by have := D.two_le; omega
            lt_large := hsInterior
            le_small := hsInterior.le }
        apply b.representationDefectAt_of_val_eq c i j (by
          dsimp only [j]
          exact hiS)
        simpa only [j] using
          a.lemma716_typeI_s_representationDefectAt b c R s D hsecond hac
            hI hvalues horderBC horders halphas hprefix hsInterior
      · have htail : s + 1 ≤ i.val := by
          have := i.pos
          omega
        exact a.lemma716_tail_representationDefectAt b c s
          hac.defectCondition horders halphas
          (fun k hsk hk => hprefix k (by omega) hk) i htail
  · have hsFour : 4 ≤ s := by
      rcases D.even with ⟨d, hd⟩
      have := D.two_le
      omega
    by_cases hiOne : i.val = 1
    · let j : RepresentationIndex (n + 3) (n + 3) :=
        { val := 1
          pos := by omega
          lt_large := by omega
          le_small := by omega }
      apply b.representationDefectAt_of_val_eq c i j (by
        dsimp only [j]
        exact hiOne)
      simpa only [j] using
        a.lemma716_typeI_first_representationDefectAt_of_gt_two b c R s D
          hfirst hthird hnorm hvalues (by omega)
    · by_cases hiInterior : i.val ≤ s - 4
      · have hiTwo : 1 < i.val := by
          have hiPos := i.pos
          omega
        exact a.lemma716_typeI_representationDefectAt_of_interior b c R s D
          hfirst hthird hnorm hvalues i hiTwo hiInterior
      · by_cases hiMinusThree : i.val = s - 3
        · let j : RepresentationIndex (n + 3) (n + 3) :=
            { val := s - 3
              pos := by omega
              lt_large := by have := D.le_rank; omega
              le_small := by have := D.le_rank; omega }
          apply b.representationDefectAt_of_val_eq c i j (by
            dsimp only [j]
            exact hiMinusThree)
          simpa only [j] using
            a.lemma716_typeI_sMinusThree_representationDefectAt b c R s D
              hfirst hthird hnorm hvalues hsFour
        · by_cases hiMinusTwo : i.val = s - 2
          · let j : RepresentationIndex (n + 3) (n + 3) :=
              { val := s - 2
                pos := by omega
                lt_large := by have := D.le_rank; omega
                le_small := by have := D.le_rank; omega }
            apply b.representationDefectAt_of_val_eq c i j (by
              dsimp only [j]
              exact hiMinusTwo)
            simpa only [j] using
              a.lemma716_typeI_sMinusTwo_representationDefectAt b c R s D
                hfirst hsecond hthird hnorm hvalues horderBC hac hI
                  hdiscriminant hsFour
          · by_cases hiMinusOne : i.val = s - 1
            · let j : RepresentationIndex (n + 3) (n + 3) :=
                { val := s - 1
                  pos := by have := D.two_le; omega
                  lt_large := by have := D.le_rank; omega
                  le_small := by have := D.le_rank; omega }
              apply b.representationDefectAt_of_val_eq c i j (by
                dsimp only [j]
                exact hiMinusOne)
              simpa only [j] using
                a.lemma716_typeI_sMinusOne_representationDefectAt b c R s D
                  hfirst hsecond hthird hnorm hvalues horderBC
            · by_cases hiS : i.val = s
              · have hsInterior : s < n + 3 := by
                  rw [← hiS]
                  exact i.lt_large
                let j : RepresentationIndex (n + 3) (n + 3) :=
                  { val := s
                    pos := by have := D.two_le; omega
                    lt_large := hsInterior
                    le_small := hsInterior.le }
                apply b.representationDefectAt_of_val_eq c i j (by
                  dsimp only [j]
                  exact hiS)
                simpa only [j] using
                  a.lemma716_typeI_s_representationDefectAt b c R s D
                    hsecond hac hI hvalues horderBC horders halphas hprefix
                      hsInterior
              · have htail : s + 1 ≤ i.val := by omega
                exact a.lemma716_tail_representationDefectAt b c s
                  hac.defectCondition horders halphas
                  (fun k hsk hk => hprefix k (by omega) hk) i htail

variable [PerfectResidueFieldLaws K]

/-- Complete condition 2.1(ii) in the type-II branch of Lemma 7.16. -/
theorem lemma716_typeII_defectCondition
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData a R s)
    (hfirst : a.order 0 = R)
    (hsecond : a.order 1 =
      R - 2 * (ramificationIndex K : Int))
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (hac : RepresentationConditionsPrime a c le_rfl)
    (hII : Lemma714IsTypeII a R s) (epsilon eta : Kˣ)
    (hepsilonUnit : IsValuationUnit K (epsilon : K))
    (hetaUnit : IsValuationUnit K (eta : K))
    (hetaDefect : defectOrder (K := K) eta =
      (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ))
    (hvalues : ∀ j, b.valueUnit j =
      lemma714TypeIITargetValues a s D.two_le
        (Classical.choose hII) epsilon eta j)
    (horderBC : b.RepresentationOrderCondition c le_rfl)
    (horders : ∀ j, s ≤ j.val → a.order j = b.order j)
    (halphas : ∀ j, s ≤ j.val → a.alphaValue j = b.alphaValue j)
    (hprefix : ∀ (k : Nat), s + 1 ≤ k → (hk : k ≤ n + 3) →
      (a.prefixDiagonalSpace k hk).IsIsometric
        (b.prefixDiagonalSpace k hk)) :
    b.RepresentationDefectCondition c := by
  apply (b.representationDefectCondition_iff_forall_at c).mpr
  intro i
  by_cases hsTwo : s = 2
  · by_cases hiOne : i.val = 1
    · let j : RepresentationIndex (n + 3) (n + 3) :=
        { val := s - 1
          pos := by have := D.two_le; omega
          lt_large := by have := Classical.choose hII; omega
          le_small := by have := Classical.choose hII; omega }
      apply b.representationDefectAt_of_val_eq c i j (by
        dsimp only [j]
        omega)
      simpa only [j] using
        a.lemma716_typeII_sMinusOne_representationDefectAt b c R s D
          hfirst hthird hnorm hII epsilon eta hepsilonUnit hetaUnit hvalues
            horderBC
    · by_cases hiS : i.val = s
      · let j : RepresentationIndex (n + 3) (n + 3) :=
          { val := s
            pos := by have := D.two_le; omega
            lt_large := Classical.choose hII
            le_small := (Classical.choose hII).le }
        apply b.representationDefectAt_of_val_eq c i j (by
          dsimp only [j]
          exact hiS)
        simpa only [j] using
          a.lemma716_typeII_s_representationDefectAt b c R s D hac hII
            epsilon eta hepsilonUnit hetaUnit hetaDefect hvalues horderBC
              horders halphas hprefix
      · have htail : s + 1 ≤ i.val := by
          have := i.pos
          omega
        exact a.lemma716_tail_representationDefectAt b c s
          hac.defectCondition horders halphas hprefix i htail
  · have hsFour : 4 ≤ s := by
      rcases D.even with ⟨d, hd⟩
      have := D.two_le
      omega
    by_cases hiOne : i.val = 1
    · let j : RepresentationIndex (n + 3) (n + 3) :=
        { val := 1
          pos := by omega
          lt_large := by omega
          le_small := by omega }
      apply b.representationDefectAt_of_val_eq c i j (by
        dsimp only [j]
        exact hiOne)
      simpa only [j] using
        a.lemma716_typeII_first_representationDefectAt_of_gt_two b c R s D
          hfirst hthird hnorm hII epsilon eta hvalues (by omega)
    · by_cases hiInterior : i.val ≤ s - 3
      · have hiTwo : 1 < i.val := by
          have hiPos := i.pos
          omega
        exact a.lemma716_typeII_representationDefectAt_of_interior b c R s D
          hfirst hthird hnorm hII epsilon eta hepsilonUnit hetaUnit hvalues
            i hiTwo hiInterior
      · by_cases hiMinusTwo : i.val = s - 2
        · let j : RepresentationIndex (n + 3) (n + 3) :=
            { val := s - 2
              pos := by omega
              lt_large := by have := D.le_rank; omega
              le_small := by have := D.le_rank; omega }
          apply b.representationDefectAt_of_val_eq c i j (by
            dsimp only [j]
            exact hiMinusTwo)
          simpa only [j] using
            a.lemma716_typeII_sMinusTwo_representationDefectAt b c R s D
              hfirst hthird hnorm hII epsilon eta hepsilonUnit hetaUnit
                hvalues hsFour
        · by_cases hiMinusOne : i.val = s - 1
          · let j : RepresentationIndex (n + 3) (n + 3) :=
              { val := s - 1
                pos := by have := D.two_le; omega
                lt_large := by have := Classical.choose hII; omega
                le_small := by have := Classical.choose hII; omega }
            apply b.representationDefectAt_of_val_eq c i j (by
              dsimp only [j]
              exact hiMinusOne)
            simpa only [j] using
              a.lemma716_typeII_sMinusOne_representationDefectAt b c R s D
                hfirst hthird hnorm hII epsilon eta hepsilonUnit hetaUnit
                  hvalues horderBC
          · by_cases hiS : i.val = s
            · let j : RepresentationIndex (n + 3) (n + 3) :=
                { val := s
                  pos := by have := D.two_le; omega
                  lt_large := Classical.choose hII
                  le_small := (Classical.choose hII).le }
              apply b.representationDefectAt_of_val_eq c i j (by
                dsimp only [j]
                exact hiS)
              simpa only [j] using
                a.lemma716_typeII_s_representationDefectAt b c R s D hac
                  hII epsilon eta hepsilonUnit hetaUnit hetaDefect hvalues
                    horderBC horders halphas hprefix
            · have htail : s + 1 ≤ i.val := by omega
              exact a.lemma716_tail_representationDefectAt b c s
                hac.defectCondition horders halphas hprefix i htail

end BONG.GoodBONG

end Bong
