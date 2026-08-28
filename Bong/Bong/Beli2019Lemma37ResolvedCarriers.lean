/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma37ResolvedModels
import Bong.Bong.Beli2019Lemma37ModelPairs
import Bong.Lattice.OrthogonalDecompositionPrefixCarrier

/-!
# Prefix carriers of collision-safe Lemma 3.7 resolutions

A strict coordinate resolution may merge the unique equal-scale pair.  If
the selected coordinate has zero left offset, however, every strict component
strictly before it is literally the correspondingly numbered component of
the original weak decomposition.  This file turns that stored componentwise
information into the prefix-space identity used by Section 5.
-/

namespace Bong

open Dyadic Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG.StrictCoordinateResolution

/-- With zero left offset, the strict prefix immediately before the resolved
component has exactly the carrier of the original weak prefix immediately
before the weak component containing the coordinate. -/
theorem prefixCarrier_eq_weakPrefix_of_offset_zero
    {n t : Nat} {b : BONG V q L n}
    {W : Lattice.WeakJordanDecomposition q L t}
    {x : BONG.WeakJordanOrderProfileWitness b W} {I : Fin n}
    (R : StrictCoordinateResolution b W x I)
    (hoffset : R.localCoordinateOffset = 0) :
    R.jordan.toOrthogonalDecomposition.prefixCarrier R.component.val =
      W.toOrthogonalDecomposition.prefixCarrier (x.indexEquiv I).1.val := by
  let P := R.jordan.toOrthogonalDecomposition
  let Q := W.toOrthogonalDecomposition
  have hcomponent : R.component.val = (x.indexEquiv I).1.val :=
    R.component_val_eq_of_offset_zero hoffset
  apply le_antisymm
  · apply P.prefixCarrier_le_of_component_le_general Q
    intro j hj
    obtain ⟨old, holdVal, hold⟩ := R.prefixComponent_eq j (by
      change j.val < R.component.val
      exact hj)
    have holdBefore : old.val < (x.indexEquiv I).1.val := by
      rw [holdVal, ← hcomponent]
      exact hj
    change (R.strictWeak.component j).carrier ≤
      Q.prefixCarrier (x.indexEquiv I).1.val
    rw [hold]
    exact Q.component_carrier_le_prefixCarrier old holdBefore
  · apply Q.prefixCarrier_le_of_component_le_general P
    intro old holdBefore
    have hjBound : old.val < R.componentCount := by
      have hcomponentBound := R.component.isLt
      rw [hcomponent] at hcomponentBound
      omega
    let j : Fin R.componentCount := ⟨old.val, hjBound⟩
    have hj : j < R.component := by
      change old.val < R.component.val
      rw [hcomponent]
      exact holdBefore
    obtain ⟨old', holdVal, hold⟩ := R.prefixComponent_eq j hj
    have holdEq : old' = old := by
      apply Fin.ext
      change old'.val = old.val
      rw [holdVal]
    subst old'
    change (W.component old).carrier ≤ P.prefixCarrier R.component.val
    rw [← hold]
    exact P.component_carrier_le_prefixCarrier j hj

/-- If, in addition, the resolved current component is literally the old
weak component, the equality of prefix carriers extends through that
component.  This is the form needed for a penultimate case-(iii) model,
whose defining complete prefix includes the current component. -/
theorem prefixCarrier_succ_eq_weakPrefix_succ_of_offset_zero_of_component_eq
    {n t : Nat} {b : BONG V q L n}
    {W : Lattice.WeakJordanDecomposition q L t}
    {x : BONG.WeakJordanOrderProfileWitness b W} {I : Fin n}
    (R : StrictCoordinateResolution b W x I)
    (hoffset : R.localCoordinateOffset = 0)
    (hcurrent : R.strictWeak.component R.component =
      W.component (x.indexEquiv I).1) :
    R.jordan.toOrthogonalDecomposition.prefixCarrier
        (R.component.val + 1) =
      W.toOrthogonalDecomposition.prefixCarrier
        ((x.indexEquiv I).1.val + 1) := by
  let P := R.jordan.toOrthogonalDecomposition
  let Q := W.toOrthogonalDecomposition
  have hcomponent : R.component.val = (x.indexEquiv I).1.val :=
    R.component_val_eq_of_offset_zero hoffset
  apply le_antisymm
  · apply P.prefixCarrier_le_of_component_le_general Q
    intro j hj
    by_cases hjCurrent : j = R.component
    · subst j
      change (R.strictWeak.component R.component).carrier ≤
        Q.prefixCarrier ((x.indexEquiv I).1.val + 1)
      rw [hcurrent]
      exact Q.component_carrier_le_prefixCarrier (x.indexEquiv I).1 (by omega)
    · have hjBefore : j < R.component := by
        change j.val < R.component.val
        change j.val < R.component.val + 1 at hj
        have hne : j.val ≠ R.component.val := by
          intro hval
          exact hjCurrent (Fin.ext hval)
        omega
      obtain ⟨old, holdVal, hold⟩ := R.prefixComponent_eq j hjBefore
      change (R.strictWeak.component j).carrier ≤
        Q.prefixCarrier ((x.indexEquiv I).1.val + 1)
      rw [hold]
      apply Q.component_carrier_le_prefixCarrier old
      change old.val < (x.indexEquiv I).1.val + 1
      rw [holdVal, ← hcomponent]
      omega
  · apply Q.prefixCarrier_le_of_component_le_general P
    intro old hold
    by_cases holdCurrent : old = (x.indexEquiv I).1
    · subst old
      change (W.component (x.indexEquiv I).1).carrier ≤
        P.prefixCarrier (R.component.val + 1)
      rw [← hcurrent]
      exact P.component_carrier_le_prefixCarrier R.component (by omega)
    · have holdBefore : old.val < (x.indexEquiv I).1.val := by
        have hne : old.val ≠ (x.indexEquiv I).1.val := by
          intro hval
          exact holdCurrent (Fin.ext hval)
        omega
      have hjBound : old.val < R.componentCount := by
        have hp := R.component.isLt
        rw [hcomponent] at hp
        omega
      let j : Fin R.componentCount := ⟨old.val, hjBound⟩
      have hjBefore : j < R.component := by
        change old.val < R.component.val
        rw [hcomponent]
        exact holdBefore
      obtain ⟨old', holdVal, holdComponent⟩ :=
        R.prefixComponent_eq j hjBefore
      have holdEq : old' = old := by
        apply Fin.ext
        change old'.val = old.val
        rw [holdVal]
      subst old'
      change (W.component old).carrier ≤ P.prefixCarrier (R.component.val + 1)
      rw [← holdComponent]
      exact P.component_carrier_le_prefixCarrier j (by omega)

end BONG.StrictCoordinateResolution

end Bong
