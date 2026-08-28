/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019AuxiliaryAlphaNormalForm

/-!
# Beli (2019), Lemma 1.4 for capped prefix defects

The paper observes that Lemma 1.4 remains valid for the bracketed defects
`d[ε a_(1,i) b_(1,j)]`.  This file proves the part needed in Lemma 2.7(i):
two prefixes can be removed from the left product under an outer minimum,
provided the cut lies below the intervening capped segment defect.
-/

namespace Bong

open Dyadic

universe u v w

/-- Lemma 1.4(c) in an abstract domination triangle.  The two domination
inequalities are exactly what is needed; no multiplication is hidden in the
statement. -/
theorem withTop_shifted_min_eq_of_domination
    (y : ℚ) (z da db dc : WithTop ℚ)
    (hbc : min da db ≤ dc) (hcb : min da dc ≤ db)
    (hcut : z ≤ (y : WithTop ℚ) + da) :
    min ((y : WithTop ℚ) + db) z =
      min ((y : WithTop ℚ) + dc) z := by
  apply le_antisymm
  · apply le_min
    · by_cases h : da ≤ db
      · have hadc : da ≤ dc := by
          simpa [min_eq_left h] using hbc
        exact (min_le_right _ _).trans
          (hcut.trans (add_le_add_right hadc _))
      · have hbad : db ≤ da := le_of_not_ge h
        have hbdc : db ≤ dc := by
          simpa [min_eq_right hbad] using hbc
        exact (min_le_left _ _).trans (add_le_add_right hbdc _)
    · exact min_le_right _ _
  · apply le_min
    · by_cases h : da ≤ dc
      · have hadb : da ≤ db := by
          simpa [min_eq_left h] using hcb
        exact (min_le_right _ _).trans
          (hcut.trans (add_le_add_right hadb _))
      · have hcad : dc ≤ da := le_of_not_ge h
        have hcdb : dc ≤ db := by
          simpa [min_eq_right hcad] using hcb
        exact (min_le_left _ _).trans (add_le_add_right hcdb _)
    · exact min_le_right _ _

/-- Lemma 1.4(a) in an abstract capped-defect triangle.  If the first
offset is strictly smaller and the first shifted defect bounds the outer
minimum, the second defect may be replaced by the third one.

Unlike the raw-defect version, the statement uses only the two domination
inequalities.  It therefore applies directly to capped prefix defects,
including the value `⊤`. -/
theorem withTop_shifted_min_eq_of_lt_of_domination
    (x y : ℚ) (z da db dc : WithTop ℚ)
    (hxy : x < y)
    (hbc : min da db ≤ dc) (hcb : min da dc ≤ db)
    (hbound : min ((y : WithTop ℚ) + db) z ≤
      (x : WithTop ℚ) + da) :
    min ((y : WithTop ℚ) + db) z =
      min ((y : WithTop ℚ) + dc) z := by
  by_cases hrealized : (y : WithTop ℚ) + db ≤ z
  · have hleft : min ((y : WithTop ℚ) + db) z =
        (y : WithTop ℚ) + db := min_eq_left hrealized
    by_cases hadb : da ≤ db
    · by_cases htop : da = ⊤
      · have hbtop : db = ⊤ := by
          apply top_unique
          simpa only [htop] using hadb
        have hctop : dc = ⊤ := by
          apply top_unique
          simpa only [htop, hbtop, min_self] using hbc
        have hztop : z = ⊤ := by
          apply top_unique
          simpa only [hbtop, add_top] using hrealized
        simp only [hbtop, hctop, hztop, add_top, min_self]
      · have hxyTop : (x : WithTop ℚ) + da <
            (y : WithTop ℚ) + da :=
          WithTop.add_lt_add_right htop (by exact_mod_cast hxy)
        have hada : (y : WithTop ℚ) + da ≤
            (y : WithTop ℚ) + db := add_le_add le_rfl hadb
        have hcontradiction : (x : WithTop ℚ) + da <
            min ((y : WithTop ℚ) + db) z := by
          rw [hleft]
          exact hxyTop.trans_le hada
        exact False.elim ((not_lt_of_ge hbound) hcontradiction)
    · have hbda : db < da := lt_of_not_ge hadb
      have hbdc : db ≤ dc := by
        simpa only [min_eq_right hbda.le] using hbc
      have hcdb : dc ≤ db := by
        by_cases hadc : da ≤ dc
        · have hadb' : da ≤ db := by
            simpa only [min_eq_left hadc] using hcb
          exact False.elim ((not_le_of_gt hbda) hadb')
        · have hcda : dc ≤ da := le_of_not_ge hadc
          simpa only [min_eq_right hcda] using hcb
      have hdc : dc = db := le_antisymm hcdb hbdc
      rw [hleft, hdc, min_eq_left hrealized]
  · have hzlt : z < (y : WithTop ℚ) + db := lt_of_not_ge hrealized
    have hleft : min ((y : WithTop ℚ) + db) z = z :=
      min_eq_right hzlt.le
    have hcutX : z ≤ (x : WithTop ℚ) + da := by
      simpa only [hleft] using hbound
    have hxyTop : (x : WithTop ℚ) ≤ (y : WithTop ℚ) := by
      exact_mod_cast hxy.le
    have hcut : z ≤ (y : WithTop ℚ) + da :=
      hcutX.trans (add_le_add hxyTop le_rfl)
    exact withTop_shifted_min_eq_of_domination y z da db dc
      hbc hcb hcut

/-- Lemma 1.4(b) in the equal-offset form used in Beli (2019), line 2269.
If the outer minimum is strictly below the shifted comparison defect, the
second defect can be replaced by the third one. -/
theorem withTop_shifted_min_eq_of_lt_cut_of_domination
    (y : ℚ) (z da db dc : WithTop ℚ)
    (hbc : min da db ≤ dc) (hcb : min da dc ≤ db)
    (hbound : min ((y : WithTop ℚ) + db) z <
      (y : WithTop ℚ) + da) :
    min ((y : WithTop ℚ) + db) z =
      min ((y : WithTop ℚ) + dc) z := by
  by_cases hrealized : (y : WithTop ℚ) + db ≤ z
  · have hleft : min ((y : WithTop ℚ) + db) z =
        (y : WithTop ℚ) + db := min_eq_left hrealized
    have hdbdaShift : (y : WithTop ℚ) + db <
        (y : WithTop ℚ) + da := by
      simpa only [hleft] using hbound
    have hdbda : db < da := by
      exact (WithTop.add_lt_add_iff_left WithTop.coe_ne_top).mp hdbdaShift
    have hbdc : db ≤ dc := by
      simpa only [min_eq_right hdbda.le] using hbc
    have hcdb : dc ≤ db := by
      by_cases hadc : da ≤ dc
      · have hadb : da ≤ db := by
          simpa only [min_eq_left hadc] using hcb
        exact False.elim ((not_le_of_gt hdbda) hadb)
      · have hcda : dc ≤ da := le_of_not_ge hadc
        simpa only [min_eq_right hcda] using hcb
    have hdc : dc = db := le_antisymm hcdb hbdc
    rw [hleft, hdc, min_eq_left hrealized]
  · have hzlt : z < (y : WithTop ℚ) + db := lt_of_not_ge hrealized
    have hleft : min ((y : WithTop ℚ) + db) z = z :=
      min_eq_right hzlt.le
    have hcut : z ≤ (y : WithTop ℚ) + da := by
      exact (by simpa only [hleft] using hbound.le)
    exact withTop_shifted_min_eq_of_domination y z da db dc
      hbc hcb hcut

/-- Lemma 1.4(b) in the offset-monotone form used in Beli (2019), line 2312.
If `x ≤ y` and the outer minimum is strictly below the comparison defect at
offset `x`, then it is also below that defect at offset `y`; hence the second
defect can be replaced by the third one. -/
theorem withTop_shifted_min_eq_of_le_of_lt_cut_of_domination
    (x y : ℚ) (z da db dc : WithTop ℚ)
    (hxy : x ≤ y)
    (hbc : min da db ≤ dc) (hcb : min da dc ≤ db)
    (hbound : min ((y : WithTop ℚ) + db) z <
      (x : WithTop ℚ) + da) :
    min ((y : WithTop ℚ) + db) z =
      min ((y : WithTop ℚ) + dc) z := by
  have hxyTop : (x : WithTop ℚ) ≤ (y : WithTop ℚ) := by
    exact_mod_cast hxy
  apply withTop_shifted_min_eq_of_lt_cut_of_domination y z da db dc hbc hcb
  exact hbound.trans_le (add_le_add hxyTop le_rfl)

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {m n : Nat}

/-- Swapping the two prefix factors does not change a capped defect. -/
theorem truncatedPrefixDefect_comm
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (ε : Kˣ) (i j : Nat) :
    a.truncatedPrefixDefect b ε i j =
      b.truncatedPrefixDefect a ε j i := by
  unfold truncatedPrefixDefect
  congr 1
  · apply congrArg (defectOrder (K := K))
    ac_rfl
  · exact min_comm _ _

/-- The forward domination inequality for deleting two source prefixes. -/
theorem truncatedPrefixDefect_add_two_domination
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i j : Nat) :
    min (a.truncatedPrefixDefect a (-1) i (i + 2))
        (a.truncatedPrefixDefect b 1 (i + 2) j) ≤
      a.truncatedPrefixDefect b (-1) i j := by
  simpa using
    (a.truncatedPrefixDefect_domination a b (-1) 1 i (i + 2) j)

/-- The reverse domination inequality for deleting two source prefixes. -/
theorem truncatedPrefixDefect_add_two_domination_reverse
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i j : Nat) :
    min (a.truncatedPrefixDefect a (-1) i (i + 2))
        (a.truncatedPrefixDefect b (-1) i j) ≤
      a.truncatedPrefixDefect b 1 (i + 2) j := by
  have h := a.truncatedPrefixDefect_domination a b
    (-1) (-1) (i + 2) i j
  rw [a.truncatedPrefixDefect_comm a (-1) (i + 2) i] at h
  simpa using h

/-- Lemma 1.4(c) for the capped defects occurring in Lemma 2.7(i). -/
theorem shiftedTruncatedPrefixDefect_add_two_replace_of_cut_le
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i j : Nat) (y : ℚ) (z : WithTop ℚ)
    (hcut : z ≤ (y : WithTop ℚ) +
      a.truncatedPrefixDefect a (-1) i (i + 2)) :
    min ((y : WithTop ℚ) +
        a.truncatedPrefixDefect b 1 (i + 2) j) z =
      min ((y : WithTop ℚ) +
        a.truncatedPrefixDefect b (-1) i j) z :=
  withTop_shifted_min_eq_of_domination y z
    (a.truncatedPrefixDefect a (-1) i (i + 2))
    (a.truncatedPrefixDefect b 1 (i + 2) j)
    (a.truncatedPrefixDefect b (-1) i j)
    (a.truncatedPrefixDefect_add_two_domination b i j)
    (a.truncatedPrefixDefect_add_two_domination_reverse b i j) hcut

/-- The right-prefix addition form used in Lemma 2.7(ii). -/
theorem shiftedTruncatedPrefixDefect_right_add_two_replace_of_cut_le
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (i j : Nat) (y : ℚ) (z : WithTop ℚ)
    (hcut : z ≤ (y : WithTop ℚ) +
      b.truncatedPrefixDefect b (-1) j (j + 2)) :
    min ((y : WithTop ℚ) +
        a.truncatedPrefixDefect b 1 i j) z =
      min ((y : WithTop ℚ) +
        a.truncatedPrefixDefect b (-1) i (j + 2)) z := by
  have hforward :
      min (b.truncatedPrefixDefect b (-1) j (j + 2))
          (a.truncatedPrefixDefect b 1 i j) ≤
        a.truncatedPrefixDefect b (-1) i (j + 2) := by
    have h := a.truncatedPrefixDefect_domination b b
      1 (-1) i j (j + 2)
    simpa only [one_mul, min_comm] using h
  have hreverse :
      min (b.truncatedPrefixDefect b (-1) j (j + 2))
          (a.truncatedPrefixDefect b (-1) i (j + 2)) ≤
        a.truncatedPrefixDefect b 1 i j := by
    have h := a.truncatedPrefixDefect_domination b b
      (-1) (-1) i (j + 2) j
    rw [b.truncatedPrefixDefect_comm b (-1) (j + 2) j] at h
    simpa only [neg_mul_neg, one_mul, min_comm] using h
  exact withTop_shifted_min_eq_of_domination y z
    (b.truncatedPrefixDefect b (-1) j (j + 2))
    (a.truncatedPrefixDefect b 1 i j)
    (a.truncatedPrefixDefect b (-1) i (j + 2))
    hforward hreverse hcut

end BONG.GoodBONG

end Bong
