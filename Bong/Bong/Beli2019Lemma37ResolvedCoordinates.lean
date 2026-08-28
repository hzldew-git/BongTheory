/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma37CoordinateRange
import Bong.Bong.Beli2019Lemma513CollisionApproximation
import Bong.Bong.Beli2019Lemma218TwoStep

/-!
# Collision-safe Lemma 3.7 coordinate classification

The weak Jordan decompositions in Section 5 may have one scale collision.
`StrictCoordinateResolution` merges precisely that collision and supplies a
genuine strict Jordan profile.  This file combines that resolution with
the strict two-step consequences of Lemma 2.18.

The result is the exact coordinate trichotomy used in the proof of Section
5: both the target approximation coordinate and the source approximation
coordinate are the first, penultimate, or last coordinate of their
resolved strict Jordan block.  Global endpoints are handled directly, so
the statements have no artificial nonterminal hypothesis.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n t : Nat}

namespace BONG.StrictCoordinateResolution

variable {a : BONG.GoodBONG q L (n + 2)}
  {W : Lattice.WeakJordanDecomposition q L t}
  {x : BONG.WeakJordanOrderProfileWitness a.toBONG W}
  {I : Fin (n + 2)}

/-- The selected global coordinate lies weakly after the start of its
resolved strict Jordan block. -/
theorem coordinates_start_le_index
    (R : StrictCoordinateResolution a.toBONG W x I) :
    R.coordinates.start ≤ I.val := by
  rw [R.index_val_eq_coordinates_start_add_local]
  exact Nat.le_add_right _ _

/-- The global zeroth coordinate belongs to the first resolved strict Jordan
component.  This is the endpoint counterpart of positivity for an interior
binary penultimate coordinate. -/
theorem component_val_eq_zero_of_index_val_eq_zero
    (R : StrictCoordinateResolution a.toBONG W x I)
    (hzero : I.val = 0) :
    R.component.val = 0 := by
  have hstart : R.coordinates.start = 0 := by
    have hle := R.coordinates_start_le_index
    omega
  by_contra hne
  have hcomponentPositive : 0 < R.component.val :=
    Nat.pos_of_ne_zero hne
  let previous : Fin R.componentCount :=
    ⟨R.component.val - 1, by
      have := R.component.isLt
      omega⟩
  have hprevious : previous ∈ Finset.Iio R.component := by
    simp only [Finset.mem_Iio]
    change R.component.val - 1 < R.component.val
    omega
  have hpositive : 0 <
      Module.finrank K (R.strictWeak.component previous).carrier :=
    R.strictWeak.component_finrank_pos previous
  have hsingle : Module.finrank K (R.strictWeak.component previous).carrier ≤
      ∑ k ∈ Finset.Iio R.component,
        Module.finrank K (R.strictWeak.component k).carrier :=
    Finset.single_le_sum
      (s := Finset.Iio R.component)
      (f := fun k ↦ Module.finrank K (R.strictWeak.component k).carrier)
      (fun _ _ ↦ Nat.zero_le _) hprevious
  unfold BONG.StrictCoordinateResolution.coordinates at hstart
  unfold BONG.WeakJordanOrderProfileWitness.jordanBlockCoordinates at hstart
  unfold BONG.WeakJordanOrderProfileWitness.componentStart at hstart
  change (∑ k ∈ Finset.Iio R.component,
    Module.finrank K (R.strictWeak.component k).carrier) = 0 at hstart
  omega

/-- A resolved coordinate with a strict outer two-step inequality is one
of the three coordinates occurring in Lemma 3.7. -/
theorem lemma37_endpoint_trichotomy_of_twoStep_strict
    (R : StrictCoordinateResolution a.toBONG W x I)
    (hpositive : 0 < I.val) (hinternal : I.val + 2 < n + 2)
    (hstrict :
      a.order ⟨I.val - 1, by omega⟩ <
          a.order ⟨I.val + 1, by omega⟩ ∨
        a.order I < a.order ⟨I.val + 2, hinternal⟩) :
    I.val = R.coordinates.start ∨
      I.val + 1 = R.coordinates.stop ∨
      I.val + 2 = R.coordinates.stop := by
  exact R.coordinates.endpoint_trichotomy_of_twoStep_strict
    a I hpositive hinternal R.coordinates_start_le_index
      R.index_val_lt_coordinates_stop hstrict

/-- A positive binary penultimate coordinate cannot belong to the first
strict Jordan component: in a binary component the penultimate coordinate is
its first coordinate, while the first component starts globally at zero. -/
theorem component_pos_of_binary_penultimate_of_pos
    (R : StrictCoordinateResolution a.toBONG W x I)
    (hpositive : 0 < I.val)
    (hpenultimate : I.val + 2 = R.coordinates.stop)
    (hrank : R.jordan.componentRank R.component = 2) :
    0 < R.component.val := by
  have hstop : R.coordinates.stop = R.coordinates.start +
      R.jordan.componentRank R.component := by
    rfl
  have hstart : I.val = R.coordinates.start := by omega
  by_contra hnot
  have hcountPos : 0 < R.componentCount := by
    have := R.component.isLt
    omega
  let z : Fin R.componentCount := ⟨0, hcountPos⟩
  have hcomponentZero : R.component = z := by
    apply Fin.ext
    dsimp only [z, Fin.val_mk]
    exact Nat.eq_zero_of_not_pos hnot
  have hstartZero : R.coordinates.start = 0 := by
    unfold coordinates
    unfold BONG.WeakJordanOrderProfileWitness.jordanBlockCoordinates
    unfold BONG.WeakJordanOrderProfileWitness.componentStart
    rw [hcomponentZero]
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_Iio] at hj
    change j.val < 0 at hj
    omega
  omega

/-- Backward-compatible form of
`component_pos_of_binary_penultimate_of_pos`. -/
theorem component_pos_of_binary_penultimate_of_two_le
    (R : StrictCoordinateResolution a.toBONG W x I)
    (htwo : 2 ≤ I.val)
    (hpenultimate : I.val + 2 = R.coordinates.stop)
    (hrank : R.jordan.componentRank R.component = 2) :
    0 < R.component.val :=
  R.component_pos_of_binary_penultimate_of_pos (by omega)
    hpenultimate hrank

end BONG.StrictCoordinateResolution

namespace BONG.GoodBONG

variable {a : GoodBONG q M (n + 2)} {b : GoodBONG q N (n + 2)}

/-- The target coordinate `i-1` of an active central trigger is in one of
the three Lemma 3.7 positions in every collision-safe strict resolution.
At the global right endpoint the conclusion follows directly from the
block stop bound. -/
theorem centralTrigger_targetResolvedEndpointTrichotomy
    [Beli2006AlphaLaws.{u, v} K]
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (htrigger : a.centralAlphaTrigger b i)
    {c : Nat} {W : Lattice.WeakJordanDecomposition q M c}
    {x : BONG.WeakJordanOrderProfileWitness a.toBONG W}
    (I : Fin (n + 2)) (hIval : I.val = i.val - 1)
    (R : BONG.StrictCoordinateResolution a.toBONG W x I) :
    I.val = R.coordinates.start ∨
      I.val + 1 = R.coordinates.stop ∨
      I.val + 2 = R.coordinates.stop := by
  by_cases hiNext : i.val + 1 < n + 2
  · have hstrictRaw := a.centralTrigger_targetLemma37TwoStepAlternative
      b hdefect i hiNext htrigger
    have hpositive : 0 < I.val := by
      have hiOne := i.one_lt
      omega
    have hinternal : I.val + 2 < n + 2 := by omega
    refine R.lemma37_endpoint_trichotomy_of_twoStep_strict
      hpositive hinternal ?_
    rcases hstrictRaw with hleft | hright
    · left
      have hleftIndex : (⟨I.val - 1, by
          have := I.isLt
          omega⟩ : Fin (n + 2)) =
          ⟨i.val - 2, by
            have := i.lt_large
            omega⟩ := by
        apply Fin.ext
        change I.val - 1 = i.val - 2
        omega
      have hrightIndex : (⟨I.val + 1, by omega⟩ : Fin (n + 2)) =
          ⟨i.val, i.lt_large⟩ := by
        apply Fin.ext
        change I.val + 1 = i.val
        omega
      calc
        a.order ⟨I.val - 1, by omega⟩ =
            a.order ⟨i.val - 2, by omega⟩ := congrArg a.order hleftIndex
        _ < a.order ⟨i.val, i.lt_large⟩ := hleft
        _ = a.order ⟨I.val + 1, by omega⟩ :=
          (congrArg a.order hrightIndex).symm
    · right
      have hleftIndex : I = (⟨i.val - 1, by
          have := i.lt_large
          omega⟩ : Fin (n + 2)) := by
        apply Fin.ext
        exact hIval
      have hrightIndex : (⟨I.val + 2, hinternal⟩ : Fin (n + 2)) =
          ⟨i.val + 1, hiNext⟩ := by
        apply Fin.ext
        change I.val + 2 = i.val + 1
        omega
      calc
        a.order I = a.order ⟨i.val - 1, by omega⟩ :=
          congrArg a.order hleftIndex
        _ < a.order ⟨i.val + 1, hiNext⟩ := hright
        _ = a.order ⟨I.val + 2, hinternal⟩ :=
          (congrArg a.order hrightIndex).symm
  · have hinside := R.index_val_lt_coordinates_stop
    have hstop := R.coordinates.stop_le
    right
    have hiLarge := i.lt_large
    omega

/-- The source coordinate `i-2` of an active central trigger is in one of
the three Lemma 3.7 positions in every collision-safe strict resolution.
For `i=2` this is the first global coordinate; otherwise Lemma 2.18(ii)
supplies the strict outer two-step inequality. -/
theorem centralTrigger_sourceResolvedEndpointTrichotomy
    [Beli2006AlphaLaws.{u, v} K]
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (htrigger : a.centralAlphaTrigger b i)
    {c : Nat} {W : Lattice.WeakJordanDecomposition q N c}
    {x : BONG.WeakJordanOrderProfileWitness b.toBONG W}
    (I : Fin (n + 2)) (hIval : I.val = i.val - 2)
    (R : BONG.StrictCoordinateResolution b.toBONG W x I) :
    I.val = R.coordinates.start ∨
      I.val + 1 = R.coordinates.stop ∨
      I.val + 2 = R.coordinates.stop := by
  by_cases hiPrevious : 2 < i.val
  · have hstrictRaw := a.centralTrigger_sourceLemma37TwoStepAlternative
      b hdefect i hiPrevious htrigger
    have hpositive : 0 < I.val := by omega
    have hinternal : I.val + 2 < n + 2 := by
      have := i.lt_large
      omega
    refine R.lemma37_endpoint_trichotomy_of_twoStep_strict
      hpositive hinternal ?_
    rcases hstrictRaw with hleft | hright
    · left
      have hleftIndex : (⟨I.val - 1, by
          have := I.isLt
          omega⟩ : Fin (n + 2)) =
          ⟨i.val - 3, by
            have := i.lt_large
            omega⟩ := by
        apply Fin.ext
        change I.val - 1 = i.val - 3
        omega
      have hrightIndex : (⟨I.val + 1, by omega⟩ : Fin (n + 2)) =
          ⟨i.val - 1, by
            have := i.lt_large
            omega⟩ := by
        apply Fin.ext
        change I.val + 1 = i.val - 1
        omega
      calc
        b.order ⟨I.val - 1, by omega⟩ =
            b.order ⟨i.val - 3, by omega⟩ := congrArg b.order hleftIndex
        _ < b.order ⟨i.val - 1, by omega⟩ := hleft
        _ = b.order ⟨I.val + 1, by omega⟩ :=
          (congrArg b.order hrightIndex).symm
    · right
      have hleftIndex : I = (⟨i.val - 2, by
          have := i.lt_large
          omega⟩ : Fin (n + 2)) := by
        apply Fin.ext
        exact hIval
      have hrightIndex : (⟨I.val + 2, hinternal⟩ : Fin (n + 2)) =
          ⟨i.val, i.lt_large⟩ := by
        apply Fin.ext
        change I.val + 2 = i.val
        omega
      calc
        b.order I = b.order ⟨i.val - 2, by omega⟩ :=
          congrArg b.order hleftIndex
        _ < b.order ⟨i.val, i.lt_large⟩ := hright
        _ = b.order ⟨I.val + 2, hinternal⟩ :=
          (congrArg b.order hrightIndex).symm
  · left
    have hstart := R.coordinates_start_le_index
    have hiOne := i.one_lt
    omega

end BONG.GoodBONG

end Bong
