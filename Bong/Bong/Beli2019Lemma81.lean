/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma317
import Bong.Bong.ResidueDefectProduct

/-!
# Beli (2019), Lemma 8.1

This file isolates the residue-field calculation used throughout Sections 8
and 9.  The two genuinely local statements are exposed as a field-level
interface: over a residue field with more than two elements one can choose a
second square class with the same finite non-boundary defect and unchanged
product defect; over the two-element residue field, multiplying two classes
of the same finite defect raises that defect.

The paper's two formulations are then derived from this interface.  In
particular, the assertion that equal defects are preserved by multiplication
exactly for two square classes is not an additional law.
-/

namespace Bong

open Dyadic

universe u

namespace BONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [QuadraticDefectLaws K]
  [DyadicResidueDefectProductLaws K]

/-- Lemma 8.1(i): away from defects `0` and `2e`, a residue field with more
than two elements supplies a second class having the same defect, while the
product still has that defect.  The square case is handled without invoking
the finite-defect field of the local interface. -/
theorem beli2019Lemma81_i
    (hres : HasResidueFieldMoreThanTwoElements (K := K))
    (a : Kˣ)
    (hzero : quadraticDefect K a ≠ 0)
    (htwoE : quadraticDefect K a ≠
      ((2 * ramificationIndex K : Nat) : ℕ∞)) :
    ∃ b : Kˣ,
      quadraticDefect K b = quadraticDefect K a ∧
        quadraticDefect K (a * b) = quadraticDefect K a := by
  by_cases hfinite : quadraticDefect K a = ⊤
  · refine ⟨1, ?_, ?_⟩
    · rw [hfinite]
      exact quadraticDefect_eq_top_of_isSquare
        (K := K) (a := (1 : Kˣ)) ⟨1, by simp⟩
    · simpa using rfl
  · exact
      DyadicResidueDefectProductLaws.exists_same_defect_product_of_large_residue
        hres a hfinite hzero htwoE

/-- Lemma 8.1(ii), strict form: over the two-element residue field, equal
finite defects strictly increase after multiplication. -/
theorem beli2019Lemma81_ii_strict
    (hres : ¬HasResidueFieldMoreThanTwoElements (K := K))
    (a b : Kˣ)
    (heq : quadraticDefect K a = quadraticDefect K b)
    (hfinite : quadraticDefect K a ≠ ⊤) :
    quadraticDefect K a < quadraticDefect K (a * b) :=
  DyadicResidueDefectProductLaws.product_defect_strict_of_residue_two
    hres a b heq hfinite

/-- Lemma 8.1(ii), square-class form: in residue cardinality two, three
equal defects `d(a)=d(b)=d(ab)` occur exactly when both factors are squares.
-/
theorem beli2019Lemma81_ii_iff
    (hres : ¬HasResidueFieldMoreThanTwoElements (K := K))
    (a b : Kˣ) :
    (quadraticDefect K a = quadraticDefect K b ∧
        quadraticDefect K (a * b) = quadraticDefect K a) ↔
      IsSquare a ∧ IsSquare b := by
  constructor
  · rintro ⟨heq, hproduct⟩
    have htop : quadraticDefect K a = ⊤ := by
      by_contra hfinite
      have hstrict := beli2019Lemma81_ii_strict hres a b heq hfinite
      rw [hproduct] at hstrict
      exact (lt_irrefl _ hstrict)
    have ha : IsSquare a :=
      (quadraticDefect_eq_top_iff_isSquare (K := K) a).mp htop
    have hbtop : quadraticDefect K b = ⊤ := heq.symm.trans htop
    exact ⟨ha,
      (quadraticDefect_eq_top_iff_isSquare (K := K) b).mp hbtop⟩
  · rintro ⟨ha, hb⟩
    have hab : IsSquare (a * b) := ha.mul hb
    have haTop := (quadraticDefect_eq_top_iff_isSquare (K := K) a).2 ha
    have hbTop := (quadraticDefect_eq_top_iff_isSquare (K := K) b).2 hb
    have habTop :=
      (quadraticDefect_eq_top_iff_isSquare (K := K) (a * b)).2 hab
    exact ⟨haTop.trans hbTop.symm, habTop.trans haTop.symm⟩

end BONG

end Bong
