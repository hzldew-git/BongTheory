/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma716DefectComplete

/-!
# Beli (2019), Lemma 7.16(iii'): the unchanged tail

For a central index at or beyond the paper's boundary `i = s + 1`, all
orders and both capped defects in the revised condition-(iii') trigger are
unchanged.  Lemma 7.15 also identifies the corresponding length-`i`
prefixes.  Thus the source representation supplied by condition (iii')
transports directly to the BONG constructed in Lemma 7.14.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- On the common tail, the revised condition-(iii') trigger is literally
the same for the original and constructed BONGs. -/
theorem lemma716_tail_centralDefectTrigger_iff
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (s : Nat)
    (horders : ∀ j, s ≤ j.val → a.order j = b.order j)
    (halphas : ∀ j, s ≤ j.val → a.alphaValue j = b.alphaValue j)
    (hprefix : ∀ (k : Nat), s + 1 ≤ k → (hk : k ≤ n + 3) →
      (a.prefixDiagonalSpace k hk).IsIsometric
        (b.prefixDiagonalSpace k hk))
    (i : CentralRepresentationIndex (n + 3) (n + 3))
    (hsi : s + 1 ≤ i.val) :
    a.centralDefectTrigger c i ↔ b.centralDefectTrigger c i := by
  have hsival : s ≤ i.val := by omega
  have horder : a.order ⟨i.val, i.lt_large⟩ =
      b.order ⟨i.val, i.lt_large⟩ :=
    horders ⟨i.val, i.lt_large⟩ (by
      simpa only [Fin.val_mk] using hsival)
  have hprevious : a.centralPreviousDefect c i =
      b.centralPreviousDefect c i := by
    unfold centralPreviousDefect
    exact a.lemma716_tail_truncatedPrefixDefect_eq b c s halphas hprefix
      (-1) i.val (i.val - 2) hsi i.lt_large.le
  have hcurrent : a.centralCurrentDefect c i =
      b.centralCurrentDefect c i := by
    unfold centralCurrentDefect
    exact a.lemma716_tail_truncatedPrefixDefect_eq b c s halphas hprefix
      (-1) (i.val + 1) (i.val - 1) (by omega) i.lt_large
  unfold centralDefectTrigger
  rw [horder, hprevious, hcurrent]

/-- Condition (iii') transports pointwise on the paper's range
`i ≥ s + 1`. -/
theorem lemma716_tail_centralRepresentationAt
    (a : GoodBONG q L (n + 3)) (b : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (s : Nat)
    (hac : RepresentationConditionsPrime a c le_rfl)
    (horders : ∀ j, s ≤ j.val → a.order j = b.order j)
    (halphas : ∀ j, s ≤ j.val → a.alphaValue j = b.alphaValue j)
    (hprefix : ∀ (k : Nat), s + 1 ≤ k → (hk : k ≤ n + 3) →
      (a.prefixDiagonalSpace k hk).IsIsometric
        (b.prefixDiagonalSpace k hk))
    (i : CentralRepresentationIndex (n + 3) (n + 3))
    (hsi : s + 1 ≤ i.val)
    (htrigger : b.centralDefectTrigger c i) :
    DiagonalRepresents
      (c.prefixValues (i.val - 1) (by
        have := i.le_small_succ
        omega))
      (b.prefixValues i.val (by
        have := i.lt_large
        omega)) := by
  have hsourceTrigger : a.centralDefectTrigger c i :=
    (a.lemma716_tail_centralDefectTrigger_iff b c s horders halphas
      hprefix i hsi).mpr htrigger
  have hsource := hac.centralRepresentations i hsourceTrigger
  have htransport := diagonalRepresents_prefixValues_of_prefix_isometric
    a b i.val i.lt_large.le (hprefix i.val hsi i.lt_large.le)
  exact hsource.trans htransport

end BONG.GoodBONG

end Bong
