/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma513Approximation
import Bong.Bong.Beli2019Lemma517CollisionProfiles
import Bong.Bong.Beli2009OrthogonalIdealProof
import Bong.Bong.Beli2009BinaryDeterminantWeight
import Bong.Bong.Beli2019Corollary33Jordan
import Bong.Bong.JordanEffectiveNormGenerator
import Bong.Bong.StructuralProof
import Bong.Lattice.OmearaModularDecompositionTruncation
import Bong.Lattice.JordanAmalgamationPrefixDeterminant
import Bong.Lattice.OrthogonalDecompositionDeterminant
import Bong.Lattice.OrthogonalDecompositionPrefixComponentwise

/-!
# Collision-resolved approximations in Beli (2019), Lemma 5.13

The almost-Jordan families used in Section 5 may contain one adjacent pair
of equal scales.  `StrictCoordinateResolution` replaces that weak pair by
its strict amalgamation.  This file proves that its fundamental lattice is
still the intrinsic scale truncation seen by the original weak coordinate,
and transports norm generators between the two resolved sides.
-/

namespace Bong

open Dyadic Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V}

namespace Lattice.WeakJordanDecomposition

/-- A weak Jordan component is unchanged in the intrinsic truncation at
its own scale, so Beli's orthogonal-sum formula puts its weight ideal inside
the weight ideal of that truncation.  No strictness of the weak scale
sequence is needed; in particular this survives the scale collision in
Beli (2019), Lemma 5.13. -/
theorem componentWeight_le_weightIdeal_scaleTruncation
    {t : Nat} (W : WeakJordanDecomposition q L t) (p : Fin t)
    (a : Kˣ)
    (ha : IsNormGeneratorValue q
      (scaleTruncation q L (ordUnit K (W.scaleGenerator p))) a) :
    weightIdeal (W.component p).space (W.component p).lattice ≤
      weightIdeal q
        (scaleTruncation q L (ordUnit K (W.scaleGenerator p))) := by
  let T := W.toOrthogonalDecomposition.modularScaleTruncationDecomposition
    W.scaleGenerator W.modular (ordUnit K (W.scaleGenerator p))
  let c : Fin t → Kˣ := fun i ↦
    Lattice.OrthogonalDecomposition.modularScaleTruncationFactor
      W.scaleGenerator (ordUnit K (W.scaleGenerator p)) i
  let ak : Fin t → Kˣ := fun i ↦ c i ^ 2 * W.normGeneratorUnit i
  have hak : ∀ i, IsNormGeneratorValue
      (T.component i).space (T.component i).lattice (ak i) := by
    intro i
    change IsNormGeneratorValue (W.component i).space
      (Lattice.rescale (c i) (W.component i).lattice)
        (c i ^ 2 * W.normGeneratorUnit i)
    exact W.rescaledNormGeneratorUnit_spec i (c i)
  have h := T.componentWeight_le_weightIdeal a ha ak hak p
  have hcomponent : T.component p = W.component p := by
    dsimp only [T]
    exact W.toOrthogonalDecomposition
      |>.modularScaleTruncationDecomposition_component_self
        W.scaleGenerator W.modular p
  rw [hcomponent] at h
  exact h

end Lattice.WeakJordanDecomposition

namespace BONG.StrictCoordinateResolution

variable {n t : Nat} {b : BONG V q L n}
  {W : Lattice.WeakJordanDecomposition q L t}
  {x : BONG.WeakJordanOrderProfileWitness b W} {I : Fin n}

/-- The strict component selected by a coordinate resolution. -/
def component
    (R : StrictCoordinateResolution b W x I) : Fin R.componentCount :=
  (R.profile.indexEquiv I).1

/-- Its intrinsic fundamental lattice. -/
noncomputable def fundamentalLattice
    (R : StrictCoordinateResolution b W x I) : Lattice K V :=
  R.jordan.fundamentalLattice R.component

/-- The resolved fundamental lattice is exactly the scale truncation at the
scale of the original weak coordinate. -/
theorem fundamentalLattice_eq_scaleTruncation
    (R : StrictCoordinateResolution b W x I) :
    R.fundamentalLattice =
      Lattice.scaleTruncation q L
        (ordUnit K (W.scaleGenerator (x.indexEquiv I).1)) := by
  unfold fundamentalLattice component
  unfold Lattice.JordanDecomposition.fundamentalLattice
  rw [R.scaleOrder_eq]

/-- The norm ideal of the resolved fundamental lattice is the power ideal
at the effective norm order computed in the original weak family. -/
theorem normIdeal_fundamentalLattice_eq_powerIdeal
    (R : StrictCoordinateResolution b W x I) :
    Lattice.normIdeal q R.fundamentalLattice =
      Lattice.powerIdeal (K := K)
        (W.effectiveNormOrderAt (x.indexEquiv I).1
          (ordUnit K (W.scaleGenerator (x.indexEquiv I).1))) := by
  unfold fundamentalLattice component
  unfold Lattice.JordanDecomposition.fundamentalLattice
  rw [R.scaleOrder_eq,
    R.jordan.normIdeal_scaleTruncation_eq_powerIdeal]
  exact congrArg (Lattice.powerIdeal (K := K)) R.effectiveNormOrder_eq

/-- A resolved fundamental lattice has a concrete norm generator. -/
noncomputable def fundamentalNormGenerator
    (R : StrictCoordinateResolution b W x I) : Kˣ :=
  R.jordan.fundamentalNormGenerator R.component

theorem fundamentalNormGenerator_spec
    (R : StrictCoordinateResolution b W x I) :
    Lattice.IsNormGeneratorValue q R.fundamentalLattice
      R.fundamentalNormGenerator := by
  exact R.jordan.fundamentalNormGenerator_spec R.component

/-- The weight of the original weak component selected by a strict
resolution lies in the weight of the resolved fundamental lattice.  This
is the collision-safe form of the component inclusion used in the proof of
Lemma 5.13. -/
theorem weakComponentWeight_le_fundamentalWeightIdeal
    (R : StrictCoordinateResolution b W x I) :
    Lattice.weightIdeal (W.component (x.indexEquiv I).1).space
        (W.component (x.indexEquiv I).1).lattice ≤
      Lattice.weightIdeal q R.fundamentalLattice := by
  rw [R.fundamentalLattice_eq_scaleTruncation]
  exact W.componentWeight_le_weightIdeal_scaleTruncation
    (x.indexEquiv I).1 R.fundamentalNormGenerator
      (by
        rw [← R.fundamentalLattice_eq_scaleTruncation]
        exact R.fundamentalNormGenerator_spec)

/-- The Jordan-block coordinates carried by a strict coordinate
resolution.  This is the collision-tolerant counterpart of the coordinates
used in the no-collision proof of Lemma 5.13. -/
noncomputable def coordinates
    {m : Nat} {a : BONG.GoodBONG q L (m + 2)}
    {W : Lattice.WeakJordanDecomposition q L t}
    {x : BONG.WeakJordanOrderProfileWitness a.toBONG W} {I : Fin (m + 2)}
    (R : StrictCoordinateResolution a.toBONG W x I) :
    a.JordanBlockCoordinates :=
  let w := BONG.WeakJordanOrderProfileWitness.ofStrict
    R.strictWeak R.scaleOrder_strict R.profile
  w.jordanBlockCoordinates R.hasImproperEvenRank R.component

/-- The global coordinate is the resolved block start plus its resolved
local coordinate. -/
theorem index_val_eq_coordinates_start_add_local
    {m : Nat} {a : BONG.GoodBONG q L (m + 2)}
    {W : Lattice.WeakJordanDecomposition q L t}
    {x : BONG.WeakJordanOrderProfileWitness a.toBONG W} {I : Fin (m + 2)}
    (R : StrictCoordinateResolution a.toBONG W x I) :
    I.val = R.coordinates.start + (R.profile.indexEquiv I).2.val := by
  let w := BONG.WeakJordanOrderProfileWitness.ofStrict
    R.strictWeak R.scaleOrder_strict R.profile
  have h := w.index_val_eq_componentStart_add_local I
  change I.val =
    (∑ k ∈ Finset.Iio (R.profile.indexEquiv I).1,
      finrank K (R.strictWeak.component k).carrier) +
        (R.profile.indexEquiv I).2.val at h
  change I.val =
    (∑ k ∈ Finset.Iio (R.profile.indexEquiv I).1,
      finrank K (R.strictWeak.component k).carrier) +
        (R.profile.indexEquiv I).2.val
  exact h

/-- The offset records exactly how far the resolved component begins before
the original weak component. -/
theorem coordinates_start_add_offset_eq_weak_componentStart
    {m : Nat} {a : BONG.GoodBONG q L (m + 2)}
    {W : Lattice.WeakJordanDecomposition q L t}
    {x : BONG.WeakJordanOrderProfileWitness a.toBONG W} {I : Fin (m + 2)}
    (R : StrictCoordinateResolution a.toBONG W x I) :
    R.coordinates.start + R.localCoordinateOffset =
      x.componentStart (x.indexEquiv I).1 := by
  have hresolved := R.index_val_eq_coordinates_start_add_local
  have hweak := x.index_val_eq_componentStart_add_local I
  rw [R.localCoordinate_eq] at hresolved
  unfold BONG.WeakJordanOrderProfileWitness.componentStart
  omega

/-- The coordinate used to select a resolution lies in its resolved block. -/
theorem index_val_lt_coordinates_stop
    {m : Nat} {a : BONG.GoodBONG q L (m + 2)}
    {W : Lattice.WeakJordanDecomposition q L t}
    {x : BONG.WeakJordanOrderProfileWitness a.toBONG W} {I : Fin (m + 2)}
    (R : StrictCoordinateResolution a.toBONG W x I) :
    I.val < R.coordinates.stop := by
  rw [R.index_val_eq_coordinates_start_add_local]
  change R.coordinates.start + (R.profile.indexEquiv I).2.val <
    R.coordinates.start +
      finrank K (R.strictWeak.component R.component).carrier
  exact Nat.add_lt_add_left (R.profile.indexEquiv I).2.isLt _

/-- The canonical determinant seed at the left boundary of the resolved
strict component. -/
noncomputable def determinantSeedData
    [Beli2006AlphaLaws.{u, v} K]
    {m : Nat} {a : BONG.GoodBONG q L (m + 2)}
    {W : Lattice.WeakJordanDecomposition q L t}
    {x : BONG.WeakJordanOrderProfileWitness a.toBONG W} {I : Fin (m + 2)}
    (R : StrictCoordinateResolution a.toBONG W x I) :
    BONG.GoodBONG.Omeara9328DeterminantSeedData a R.coordinates := by
  exact BONG.WeakJordanOrderProfileWitness.strictDeterminantSeedDataAny
    R.strictWeak R.hasImproperEvenRank R.scaleOrder_strict R.profile R.component

@[simp]
theorem determinantSeedData_leftDet_of_component_zero
    [Beli2006AlphaLaws.{u, v} K]
    {m : Nat} {a : BONG.GoodBONG q L (m + 2)}
    {W : Lattice.WeakJordanDecomposition q L t}
    {x : BONG.WeakJordanOrderProfileWitness a.toBONG W} {I : Fin (m + 2)}
    (R : StrictCoordinateResolution a.toBONG W x I)
    (hp : R.component.val = 0) :
    R.determinantSeedData.leftDet = 1 := by
  exact BONG.WeakJordanOrderProfileWitness.strictDeterminantSeedDataAny_leftDet_of_component_zero
      R.strictWeak R.hasImproperEvenRank R.scaleOrder_strict R.profile
        R.component hp

@[simp]
theorem determinantSeedData_leftDet_of_component_ne_zero
    [Beli2006AlphaLaws.{u, v} K]
    {m : Nat} {a : BONG.GoodBONG q L (m + 2)}
    {W : Lattice.WeakJordanDecomposition q L t}
    {x : BONG.WeakJordanOrderProfileWitness a.toBONG W} {I : Fin (m + 2)}
    (R : StrictCoordinateResolution a.toBONG W x I)
    (hp : R.component.val ≠ 0) :
    R.determinantSeedData.leftDet =
      (R.jordan.toOrthogonalDecomposition.prefixQuadraticSublattice
        R.component.val).refinedDeterminantUnit := by
  exact BONG.WeakJordanOrderProfileWitness.strictDeterminantSeedDataAny_leftDet_of_component_ne_zero
      R.strictWeak R.hasImproperEvenRank R.scaleOrder_strict R.profile
        R.component hp

/-- If a strict coordinate resolution does not absorb an old component on
its left, its determinant seed is the determinant of the old weak prefix,
up to a unit square.  This isolates the determinant transport needed on the
small side of the terminal collision in Lemma 5.13(i). -/
theorem exists_determinantSeedData_eq_weakPrefix_mul_square
    [Beli2006AlphaLaws.{u, v} K]
    {m : Nat} {a : BONG.GoodBONG q L (m + 2)}
    {W : Lattice.WeakJordanDecomposition q L t}
    {x : BONG.WeakJordanOrderProfileWitness a.toBONG W} {I : Fin (m + 2)}
    (R : StrictCoordinateResolution a.toBONG W x I)
    (hoffset : R.localCoordinateOffset = 0) :
    ∃ s : Kˣ,
      (W.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice (x.indexEquiv I).1.val
          |>.refinedDeterminantUnit) =
        R.determinantSeedData.leftDet * s ^ 2 := by
  let p := (x.indexEquiv I).1
  have hcomponent : R.component.val = p.val :=
    R.component_val_eq_of_offset_zero hoffset
  by_cases hpzero : p.val = 0
  · have hRzero : R.component.val = 0 := hcomponent.trans hpzero
    refine ⟨1, ?_⟩
    rw [R.determinantSeedData_leftDet_of_component_zero hRzero]
    rw [show (x.indexEquiv I).1.val = 0 by exact hpzero]
    change
      (W.toOrthogonalDecomposition.prefixQuadraticSublattice 0
        |>.refinedDeterminantUnit) = 1 * 1 ^ 2
    simp only [one_pow, mul_one]
    unfold Lattice.QuadraticSublattice.refinedDeterminantUnit
    exact Lattice.determinantUnit_eq_one_of_subsingleton _ _
      (Lattice.WeakJordanDecomposition.prefixCarrier_zero_subsingleton
        W.toOrthogonalDecomposition)
  · let cut := p.val
    let P := R.jordan.toOrthogonalDecomposition
    let Q := W.toOrthogonalDecomposition
    have hcut : cut - 1 + 1 = cut := by
      dsimp only [cut]
      omega
    have hP : cut - 1 + 1 ≤ R.componentCount := by
      rw [hcut]
      dsimp only [cut]
      rw [← hcomponent]
      exact R.component.isLt.le
    have hQ : cut - 1 + 1 ≤ t := by
      rw [hcut]
      exact p.isLt.le
    have hprefixComponent (z : Fin (cut - 1 + 1)) :
        P.component (P.prefixIndexEquiv (cut - 1 + 1) hP z).1 =
          Q.component (Q.prefixIndexEquiv (cut - 1 + 1) hQ z).1 := by
      let jP := (P.prefixIndexEquiv (cut - 1 + 1) hP z).1
      let jQ := (Q.prefixIndexEquiv (cut - 1 + 1) hQ z).1
      have hjPVal : jP.val = z.val :=
        P.prefixIndexEquiv_val (cut - 1 + 1) hP z
      have hjQVal : jQ.val = z.val :=
        Q.prefixIndexEquiv_val (cut - 1 + 1) hQ z
      have hjP : jP < R.component := by
        change jP.val < R.component.val
        rw [hjPVal, hcomponent]
        have hz := z.isLt
        dsimp only [cut] at hz
        omega
      obtain ⟨old, holdVal, hold⟩ := R.prefixComponent_eq jP hjP
      have holdEq : old = jQ := by
        apply Fin.ext
        rw [holdVal, hjPVal, hjQVal]
      change R.strictWeak.component jP = W.component jQ
      rw [hold, holdEq]
    obtain ⟨s, hs⟩ :=
      P.exists_prefixDeterminantUnit_eq_mul_square_of_componentwiseIsometry_of_differentCounts
        Q hP hQ (fun z ↦ by
          rw [hprefixComponent z]
          exact Lattice.Isometry.refl _ _)
    refine ⟨s, ?_⟩
    rw [R.determinantSeedData_leftDet_of_component_ne_zero (by omega)]
    change
      (Q.prefixQuadraticSublattice p.val).refinedDeterminantUnit =
        (P.prefixQuadraticSublattice R.component.val).refinedDeterminantUnit *
          s ^ 2
    rw [hcomponent]
    simpa only [hcut] using hs

/-- Assemble all resolved Jordan-approximation seeds from a chosen
determinant seed and a chosen generator of the resolved fundamental norm
ideal. -/
noncomputable def approximationSeedsWith
    [Beli2006AlphaLaws.{u, v} K]
    {m : Nat} {a : BONG.GoodBONG q L (m + 2)}
    {W : Lattice.WeakJordanDecomposition q L t}
    {x : BONG.WeakJordanOrderProfileWitness a.toBONG W} {I : Fin (m + 2)}
    (R : StrictCoordinateResolution a.toBONG W x I)
    (determinant :
      BONG.GoodBONG.Omeara9328DeterminantSeedData a R.coordinates)
    (A : Kˣ)
    (hA : Lattice.IsNormGeneratorValue q R.fundamentalLattice A) :
    BONG.GoodBONG.JordanApproximationSeeds a R.coordinates := by
  exact BONG.WeakJordanOrderProfileWitness.strictJordanApproximationSeedsWithAny
    R.strictWeak R.hasImproperEvenRank R.scaleOrder_strict R.profile R.component
      determinant A hA

@[simp]
theorem approximationSeedsWith_leftDet
    [Beli2006AlphaLaws.{u, v} K]
    {m : Nat} {a : BONG.GoodBONG q L (m + 2)}
    {W : Lattice.WeakJordanDecomposition q L t}
    {x : BONG.WeakJordanOrderProfileWitness a.toBONG W} {I : Fin (m + 2)}
    (R : StrictCoordinateResolution a.toBONG W x I)
    (determinant :
      BONG.GoodBONG.Omeara9328DeterminantSeedData a R.coordinates)
    (A : Kˣ)
    (hA : Lattice.IsNormGeneratorValue q R.fundamentalLattice A) :
    (R.approximationSeedsWith determinant A hA).leftDet =
      determinant.leftDet := by
  exact BONG.WeakJordanOrderProfileWitness.strictJordanApproximationSeedsWithAny_leftDet
      R.strictWeak R.hasImproperEvenRank R.scaleOrder_strict R.profile R.component
        determinant A hA

@[simp]
theorem approximationSeedsWith_normGenerator
    [Beli2006AlphaLaws.{u, v} K]
    {m : Nat} {a : BONG.GoodBONG q L (m + 2)}
    {W : Lattice.WeakJordanDecomposition q L t}
    {x : BONG.WeakJordanOrderProfileWitness a.toBONG W} {I : Fin (m + 2)}
    (R : StrictCoordinateResolution a.toBONG W x I)
    (determinant :
      BONG.GoodBONG.Omeara9328DeterminantSeedData a R.coordinates)
    (A : Kˣ)
    (hA : Lattice.IsNormGeneratorValue q R.fundamentalLattice A) :
    (R.approximationSeedsWith determinant A hA).normGenerator = A := by
  exact BONG.WeakJordanOrderProfileWitness.strictJordanApproximationSeedsWithAny_normGenerator
      R.strictWeak R.hasImproperEvenRank R.scaleOrder_strict R.profile R.component
        determinant A hA

/-- The canonical resolved approximation seeds. -/
noncomputable def approximationSeeds
    [Beli2006AlphaLaws.{u, v} K]
    {m : Nat} {a : BONG.GoodBONG q L (m + 2)}
    {W : Lattice.WeakJordanDecomposition q L t}
    {x : BONG.WeakJordanOrderProfileWitness a.toBONG W} {I : Fin (m + 2)}
    (R : StrictCoordinateResolution a.toBONG W x I) :
    BONG.GoodBONG.JordanApproximationSeeds a R.coordinates :=
  R.approximationSeedsWith R.determinantSeedData R.fundamentalNormGenerator
    R.fundamentalNormGenerator_spec

/-- Corollary 3.3 at the right end of a collision-resolved Jordan block.
The rescaled terminal value differs from the last good-BONG value by a
square.  Multiplying it by the prefix product through the whole block
therefore gives, up to a square, the prefix product with the last coordinate
removed.  This is the exact algebraic content of the right-end
approximation; no additional local law is involved. -/
theorem terminalValue_mul_prefixProduct_stop_isPrefixApproximation
    {m : Nat} {a : BONG.GoodBONG q L (m + 2)}
    {W : Lattice.WeakJordanDecomposition q L t}
    {x : BONG.WeakJordanOrderProfileWitness a.toBONG W} {I : Fin (m + 2)}
    (R : StrictCoordinateResolution a.toBONG W x I) :
    a.IsPrefixApproximation (R.coordinates.stop - 1)
      (R.profile.terminalValue R.component *
        a.prefixProduct R.coordinates.stop) := by
  let C := R.coordinates
  let last : Fin (R.jordan.componentRank R.component) :=
    ⟨R.jordan.componentRank R.component - 1, by
      exact Nat.sub_lt (R.jordan.component_finrank_pos R.component)
        Nat.zero_lt_one⟩
  have hstopPos : 0 < C.stop :=
    C.start_lt_stop.trans_le' (Nat.zero_le C.start)
  have htargetLt : C.stop - 1 < m + 2 := by
    have := C.stop_le
    omega
  have hlastGlobal :
      R.profile.indexEquiv.symm ⟨R.component, last⟩ = C.lastIndex := by
    apply Fin.ext
    rw [R.profile.inverse_index_val]
    change
      (∑ k ∈ Finset.Iio R.component,
          finrank K (R.strictWeak.component k).carrier) +
          (R.jordan.componentRank R.component - 1) =
        C.stop - 1
    change C.start +
        (finrank K (R.strictWeak.component R.component).carrier - 1) =
      C.stop - 1
    have hCstop : C.stop = C.start +
        finrank K (R.strictWeak.component R.component).carrier := rfl
    have hrankPos :
        0 < finrank K (R.strictWeak.component R.component).carrier :=
      R.strictWeak.component_finrank_pos R.component
    rw [hCstop]
    omega
  let exponent : Int :=
    ordUnit K (R.jordan.normGenerator R.component) -
      ordUnit K (R.jordan.scaleGenerator R.component)
  let squareRoot : Kˣ :=
    uniformizerPowerUnit K exponent * a.valueUnit C.lastIndex
  have hpower : uniformizerPowerUnit K (2 * exponent) =
      uniformizerPowerUnit K exponent ^ 2 := by
    unfold uniformizerPowerUnit
    rw [pow_two, ← zpow_add]
    congr 1
    omega
  have hterminal : R.profile.terminalValue R.component =
      uniformizerPowerUnit K (2 * exponent) *
        a.valueUnit C.lastIndex := by
    unfold BONG.JordanOrderProfileWitness.terminalValue
    change uniformizerPowerUnit K
          (2 * ordUnit K (R.jordan.normGenerator R.component) -
            2 * ordUnit K (R.jordan.scaleGenerator R.component)) *
        a.valueUnit (R.profile.indexEquiv.symm ⟨R.component, last⟩) =
      uniformizerPowerUnit K (2 * exponent) *
        a.valueUnit C.lastIndex
    rw [hlastGlobal]
    have hexponent :
        2 * ordUnit K (R.jordan.normGenerator R.component) -
            2 * ordUnit K (R.jordan.scaleGenerator R.component) =
          2 * exponent := by
      dsimp only [exponent]
      omega
    rw [hexponent]
  have hstop : C.stop = (C.stop - 1) + 1 := by omega
  have hlastIndex :
      (⟨C.stop - 1, htargetLt⟩ : Fin (m + 2)) = C.lastIndex := by
    apply Fin.ext
    rfl
  have hprefix : a.prefixProduct C.stop =
      a.prefixProduct (C.stop - 1) * a.valueUnit C.lastIndex := by
    calc
      a.prefixProduct C.stop =
          a.prefixProduct ((C.stop - 1) + 1) :=
        congrArg a.prefixProduct hstop
      _ = a.prefixProduct (C.stop - 1) *
          a.valueUnit ⟨C.stop - 1, htargetLt⟩ := by
        exact a.toBONG.prefixProduct_succ (C.stop - 1) htargetLt
      _ = a.prefixProduct (C.stop - 1) *
          a.valueUnit C.lastIndex := by rw [hlastIndex]
  have hscalar :
      R.profile.terminalValue R.component * a.prefixProduct C.stop =
        a.prefixProduct (C.stop - 1) * squareRoot ^ 2 := by
    rw [hterminal, hpower, hprefix]
    dsimp only [squareRoot]
    rw [mul_pow]
    simp only [pow_two]
    ac_rfl
  rw [hscalar]
  exact (a.isPrefixApproximation_mul_square_iff
    (C.stop - 1) (a.prefixProduct (C.stop - 1)) squareRoot).2
      (a.isPrefixApproximation_prefixProduct (C.stop - 1))

/-- The same right-end square calculation using the effective
(`fundamental`) terminal norm value.  This is the canonical right seed even
when the displayed modular component does not itself attain the norm of the
whole scale truncation. -/
theorem fundamentalTerminalValue_mul_prefixProduct_stop_isPrefixApproximation
    {m : Nat} {a : BONG.GoodBONG q L (m + 2)}
    {W : Lattice.WeakJordanDecomposition q L t}
    {x : BONG.WeakJordanOrderProfileWitness a.toBONG W} {I : Fin (m + 2)}
    (R : StrictCoordinateResolution a.toBONG W x I) :
    a.IsPrefixApproximation (R.coordinates.stop - 1)
      (R.profile.fundamentalTerminalValue R.component *
        a.prefixProduct R.coordinates.stop) := by
  let C := R.coordinates
  let last : Fin (R.jordan.componentRank R.component) :=
    ⟨R.jordan.componentRank R.component - 1, by
      exact Nat.sub_lt (R.jordan.component_finrank_pos R.component)
        Nat.zero_lt_one⟩
  have hstopPos : 0 < C.stop :=
    C.start_lt_stop.trans_le' (Nat.zero_le C.start)
  have htargetLt : C.stop - 1 < m + 2 := by
    have := C.stop_le
    omega
  have hlastGlobal :
      R.profile.indexEquiv.symm ⟨R.component, last⟩ = C.lastIndex := by
    apply Fin.ext
    rw [R.profile.inverse_index_val]
    change C.start +
        (finrank K (R.strictWeak.component R.component).carrier - 1) =
      C.stop - 1
    have hCstop : C.stop = C.start +
        finrank K (R.strictWeak.component R.component).carrier := rfl
    have hrankPos :
        0 < finrank K (R.strictWeak.component R.component).carrier :=
      R.strictWeak.component_finrank_pos R.component
    rw [hCstop]
    omega
  let exponent : Int :=
    ordUnit K (R.jordan.fundamentalNormGenerator R.component) -
      ordUnit K (R.jordan.scaleGenerator R.component)
  let squareRoot : Kˣ :=
    uniformizerPowerUnit K exponent * a.valueUnit C.lastIndex
  have hpower : uniformizerPowerUnit K (2 * exponent) =
      uniformizerPowerUnit K exponent ^ 2 := by
    unfold uniformizerPowerUnit
    rw [pow_two, ← zpow_add]
    congr 1
    omega
  have hterminal : R.profile.fundamentalTerminalValue R.component =
      uniformizerPowerUnit K (2 * exponent) *
        a.valueUnit C.lastIndex := by
    unfold BONG.JordanOrderProfileWitness.fundamentalTerminalValue
    change uniformizerPowerUnit K
          (2 * ordUnit K (R.jordan.fundamentalNormGenerator R.component) -
            2 * ordUnit K (R.jordan.scaleGenerator R.component)) *
        a.valueUnit (R.profile.indexEquiv.symm ⟨R.component, last⟩) =
      uniformizerPowerUnit K (2 * exponent) *
        a.valueUnit C.lastIndex
    rw [hlastGlobal]
    have hexponent :
        2 * ordUnit K (R.jordan.fundamentalNormGenerator R.component) -
            2 * ordUnit K (R.jordan.scaleGenerator R.component) =
          2 * exponent := by
      dsimp only [exponent]
      omega
    rw [hexponent]
  have hstop : C.stop = (C.stop - 1) + 1 := by omega
  have hlastIndex :
      (⟨C.stop - 1, htargetLt⟩ : Fin (m + 2)) = C.lastIndex := by
    apply Fin.ext
    rfl
  have hprefix : a.prefixProduct C.stop =
      a.prefixProduct (C.stop - 1) * a.valueUnit C.lastIndex := by
    calc
      a.prefixProduct C.stop =
          a.prefixProduct ((C.stop - 1) + 1) :=
        congrArg a.prefixProduct hstop
      _ = a.prefixProduct (C.stop - 1) *
          a.valueUnit ⟨C.stop - 1, htargetLt⟩ := by
        exact a.toBONG.prefixProduct_succ (C.stop - 1) htargetLt
      _ = a.prefixProduct (C.stop - 1) *
          a.valueUnit C.lastIndex := by rw [hlastIndex]
  have hscalar :
      R.profile.fundamentalTerminalValue R.component *
          a.prefixProduct C.stop =
        a.prefixProduct (C.stop - 1) * squareRoot ^ 2 := by
    rw [hterminal, hpower, hprefix]
    dsimp only [squareRoot]
    rw [mul_pow]
    simp only [pow_two]
    ac_rfl
  rw [hscalar]
  exact (a.isPrefixApproximation_mul_square_iff
    (C.stop - 1) (a.prefixProduct (C.stop - 1)) squareRoot).2
      (a.isPrefixApproximation_prefixProduct (C.stop - 1))

/-- At the last internal boundary of a resolved strict component, the prefix
alpha cap is the fundamental weight order minus the fundamental norm order.
This is the collision-safe form of Beli's identity
`ord w(M^{p^r}) = R_i + alpha_i`. -/
theorem prefixAlphaCap_stop_sub_one_eq_fundamentalWeight_sub_normGenerator
    {m : Nat} {a : BONG.GoodBONG q L (m + 2)}
    {W : Lattice.WeakJordanDecomposition q L t}
    {x : BONG.WeakJordanOrderProfileWitness a.toBONG W} {I : Fin (m + 2)}
    (R : StrictCoordinateResolution a.toBONG W x I)
    (hrank : 2 ≤ R.jordan.componentRank R.component) :
    a.prefixAlphaCap (R.coordinates.stop - 1) =
      (((R.jordan.fundamentalWeightOrder R.component -
          ordUnit K (R.profile.fundamentalTerminalValue R.component) : Int) :
        ℚ) : WithTop ℚ) := by
  let C := R.coordinates
  let F := R.profile.fundamentalTerminalValue R.component
  have hCstop : C.stop = C.start + R.jordan.componentRank R.component := rfl
  have htargetPos : 0 < C.stop - 1 := by
    rw [hCstop]
    omega
  have htargetLt : C.stop - 1 < m + 2 := by
    have := C.stop_le
    omega
  have halphaLt : C.stop - 2 < m + 1 := by
    have := C.stop_le
    omega
  let alphaIndex : Fin (m + 1) := ⟨C.stop - 2, halphaLt⟩
  let penult : Fin (R.jordan.componentRank R.component) :=
    ⟨R.jordan.componentRank R.component - 2, by omega⟩
  have hpenultGlobal :
      R.profile.indexEquiv.symm ⟨R.component, penult⟩ =
        alphaIndex.castSucc := by
    apply Fin.ext
    rw [R.profile.inverse_index_val]
    change C.start + (R.jordan.componentRank R.component - 2) =
      C.stop - 2
    rw [hCstop]
    omega
  have hcoordinates : R.profile.indexEquiv alphaIndex.castSucc =
      ⟨R.component, penult⟩ := by
    rw [← hpenultGlobal, R.profile.indexEquiv.apply_symm_apply]
  have hlocal :
      (R.profile.indexEquiv alphaIndex.castSucc).2.val + 1 <
        R.jordan.componentRank
          (R.profile.indexEquiv alphaIndex.castSucc).1 := by
    rw [hcoordinates]
    dsimp only [penult]
    omega
  have hweight :=
    R.profile.internal_weightOrder_eq_order_add_alpha alphaIndex hlocal
  rw [hcoordinates] at hweight
  have hleftLt : C.stop - 2 < C.stop := by omega
  have hleftStart : C.start ≤ C.stop - 2 := by
    rw [hCstop]
    omega
  have hleftIndex : C.index (C.stop - 2) hleftLt =
      alphaIndex.castSucc := by
    apply Fin.ext
    rfl
  have hrightParity : (C.stop - (C.stop - 2)) % 2 = 0 := by omega
  have hleftOrder :=
    (C.beli2009Lemma213_ii (C.stop - 2) hleftStart hleftLt).1
      hrightParity
  rw [hleftIndex] at hleftOrder
  have hnormIdeal : Lattice.normIdeal q R.fundamentalLattice =
      Lattice.powerIdeal (K := K) C.normOrder := by
    unfold fundamentalLattice
    unfold Lattice.JordanDecomposition.fundamentalLattice
    rw [R.jordan.normIdeal_scaleTruncation_eq_powerIdeal R.component
      (R.jordan.fundamentalScaleOrder R.component)]
    rfl
  have hF : Lattice.IsNormGeneratorValue q R.fundamentalLattice F := by
    exact R.profile.fundamentalTerminalValue_isNormGeneratorValue R.component
  have hFOrder : ordUnit K F = C.normOrder := by
    have hideal : Lattice.principalIdeal (K := K) (F : K) =
      Lattice.powerIdeal (K := K) C.normOrder :=
      hF.2.symm.trans hnormIdeal
    rw [Lattice.principalIdeal_eq_powerIdeal] at hideal
    exact Lattice.powerIdeal_injective hideal
  have halpha : a.alphaValue alphaIndex =
      ((R.jordan.fundamentalWeightOrder R.component - ordUnit K F : Int) :
        ℚ) := by
    have hleftOrderQ : (a.order alphaIndex.castSucc : ℚ) =
        (ordUnit K F : ℚ) := by
      rw [hleftOrder, hFOrder]
    push_cast
    linarith
  rw [a.prefixAlphaCap_of_internal htargetPos htargetLt]
  have hidx : (⟨C.stop - 1 - 1, by omega⟩ : Fin (m + 1)) =
      alphaIndex := by
    apply Fin.ext
    dsimp only [alphaIndex]
    omega
  rw [hidx, halpha]

/-- At any positive local coordinate of a collision-resolved strict block,
the prefix alpha cap is the fundamental weight order minus the order of the
immediately preceding BONG value.  The terminal formula above is the special
case in which that preceding order is represented by the fundamental
terminal norm generator. -/
theorem prefixAlphaCap_eq_fundamentalWeight_sub_previousOrder
    {m : Nat} {a : BONG.GoodBONG q L (m + 2)}
    {W : Lattice.WeakJordanDecomposition q L t}
    {x : BONG.WeakJordanOrderProfileWitness a.toBONG W} {I : Fin (m + 2)}
    (R : StrictCoordinateResolution a.toBONG W x I)
    (hlocalPos : 0 < (R.profile.indexEquiv I).2.val) :
    a.prefixAlphaCap I.val =
      (((R.jordan.fundamentalWeightOrder R.component -
          a.order ⟨I.val - 1, by
            have := I.isLt
            omega⟩ : Int) : ℚ) : WithTop ℚ) := by
  let C := R.coordinates
  let j := (R.profile.indexEquiv I).2.val
  have hglobal := R.index_val_eq_coordinates_start_add_local
  have hIpos : 0 < I.val := by
    change I.val = C.start + j at hglobal
    omega
  let alphaIndex : Fin (m + 1) := ⟨I.val - 1, by
    have := I.isLt
    omega⟩
  let previousLocal : Fin (R.jordan.componentRank R.component) :=
    ⟨j - 1, by
      have hj := (R.profile.indexEquiv I).2.isLt
      change j < R.jordan.componentRank R.component at hj
      omega⟩
  have hpreviousGlobal :
      R.profile.indexEquiv.symm ⟨R.component, previousLocal⟩ =
        alphaIndex.castSucc := by
    apply Fin.ext
    rw [R.profile.inverse_index_val]
    change C.start + (j - 1) = I.val - 1
    change I.val = C.start + j at hglobal
    rw [hglobal]
    omega
  have hcoordinates :
      R.profile.indexEquiv alphaIndex.castSucc =
        ⟨R.component, previousLocal⟩ := by
    rw [← hpreviousGlobal, R.profile.indexEquiv.apply_symm_apply]
  have hinternal :
      (R.profile.indexEquiv alphaIndex.castSucc).2.val + 1 <
        R.jordan.componentRank
          (R.profile.indexEquiv alphaIndex.castSucc).1 := by
    rw [hcoordinates]
    change j - 1 + 1 < R.jordan.componentRank R.component
    have hj := (R.profile.indexEquiv I).2.isLt
    change j < R.jordan.componentRank R.component at hj
    omega
  have hweight :=
    R.profile.internal_weightOrder_eq_order_add_alpha alphaIndex hinternal
  rw [hcoordinates] at hweight
  have halpha : a.alphaValue alphaIndex =
      ((R.jordan.fundamentalWeightOrder R.component -
          a.order alphaIndex.castSucc : Int) : ℚ) := by
    push_cast
    linarith
  rw [a.prefixAlphaCap_of_internal hIpos I.isLt]
  have hidx : (⟨I.val - 1, by omega⟩ : Fin (m + 1)) = alphaIndex := by
    apply Fin.ext
    rfl
  rw [hidx, halpha]
  congr 4

/-- The preceding BONG order at a positive resolved local coordinate is the
alternating local order at `local - 1`. -/
theorem previousOrder_eq_resolvedLocalOrder
    {m : Nat} {a : BONG.GoodBONG q L (m + 2)}
    {W : Lattice.WeakJordanDecomposition q L t}
    {x : BONG.WeakJordanOrderProfileWitness a.toBONG W} {I : Fin (m + 2)}
    (R : StrictCoordinateResolution a.toBONG W x I)
    (hlocalPos : 0 < (R.profile.indexEquiv I).2.val) :
    a.order ⟨I.val - 1, by
        have := I.isLt
        omega⟩ =
      JordanProfileOrder.localOrder
        (ordUnit K (R.strictWeak.scaleGenerator R.component))
        (R.strictWeak.effectiveNormOrderAt R.component
          (ordUnit K (R.strictWeak.scaleGenerator R.component)))
        ((R.profile.indexEquiv I).2.val - 1) := by
  let C := R.coordinates
  let j := (R.profile.indexEquiv I).2.val
  have hglobal := R.index_val_eq_coordinates_start_add_local
  let previousIndex : Fin (m + 2) := ⟨I.val - 1, by
    have := I.isLt
    omega⟩
  let previousLocal : Fin (R.jordan.componentRank R.component) :=
    ⟨j - 1, by
      have hj := (R.profile.indexEquiv I).2.isLt
      change j < R.jordan.componentRank R.component at hj
      omega⟩
  have hpreviousGlobal :
      R.profile.indexEquiv.symm ⟨R.component, previousLocal⟩ =
        previousIndex := by
    apply Fin.ext
    rw [R.profile.inverse_index_val]
    change C.start + (j - 1) = I.val - 1
    change I.val = C.start + j at hglobal
    rw [hglobal]
    omega
  have hcoordinates : R.profile.indexEquiv previousIndex =
      ⟨R.component, previousLocal⟩ := by
    rw [← hpreviousGlobal, R.profile.indexEquiv.apply_symm_apply]
  let w := BONG.WeakJordanOrderProfileWitness.ofStrict
    R.strictWeak R.scaleOrder_strict R.profile
  have horder := w.order_eq previousIndex
  change a.order previousIndex = JordanProfileOrder.localOrder
      (ordUnit K (R.strictWeak.scaleGenerator (w.indexEquiv previousIndex).1))
      (R.strictWeak.effectiveNormOrderAt (w.indexEquiv previousIndex).1
        (ordUnit K
          (R.strictWeak.scaleGenerator (w.indexEquiv previousIndex).1)))
      (w.indexEquiv previousIndex).2.val at horder
  change w.indexEquiv previousIndex =
      ⟨R.component, previousLocal⟩ at hcoordinates
  rw [hcoordinates] at horder
  simpa only [previousIndex, previousLocal, j] using horder

/-- Beli (2019), Lemma 5.13, last collision case: at the last internal
boundary of a resolved block, a binary weak component supplies enough
determinant defect to dominate the prefix alpha.  The proof is exactly the
chain

`w(J') ⊆ w(L^{p^r})`,
`ord w(J') ≤ R₂(J') + d(-det J')`, and
`R₂(J') ≤ r ≤ ord n(L^{p^r})`.

The binary good BONG used to invoke Beli (2009), Lemma 2.14 is constructed
from the already-proved arbitrary-rank existence theorem. -/
theorem prefixAlphaCap_stop_sub_one_le_defect_neg_weakComponentDeterminant
    {m : Nat} {a : BONG.GoodBONG q L (m + 2)}
    {W : Lattice.WeakJordanDecomposition q L t}
    {x : BONG.WeakJordanOrderProfileWitness a.toBONG W} {I : Fin (m + 2)}
    (R : StrictCoordinateResolution a.toBONG W x I)
    (hweakRank :
      finrank K (W.component (x.indexEquiv I).1).carrier = 2)
    (hrank : 2 ≤ R.jordan.componentRank R.component) :
    a.prefixAlphaCap (R.coordinates.stop - 1) ≤
      BONG.GoodBONG.defectOrder (K := K)
        (-(W.component (x.indexEquiv I).1).refinedDeterminantUnit) := by
  let p := (x.indexEquiv I).1
  let J := W.component p
  let F := R.profile.fundamentalTerminalValue R.component
  have hJrank : finrank K J.carrier = 2 := by
    simpa only [J, p] using hweakRank
  let cRaw := Classical.choice (Bong.exists_good_bong J.space J.lattice)
  let c : BONG.GoodBONG J.space J.lattice 2 := cRaw.castLength hJrank
  have hmodular : Lattice.IsModular J.space J.lattice
      (W.scaleGenerator p) := by
    simpa only [J, p] using W.modular p
  have hsecondLeScale : c.order 1 ≤ ordUnit K (W.scaleGenerator p) := by
    have hzero := c.toBONG.modularOrder_le_order_zero
      (W.scaleGenerator p) hmodular
    have hone := c.toBONG.order_one_eq_of_isModular
      (W.scaleGenerator p) hmodular
    change ordUnit K (W.scaleGenerator p) ≤ c.order 0 at hzero
    change c.order 1 = 2 * ordUnit K (W.scaleGenerator p) - c.order 0 at hone
    omega
  have hF : Lattice.IsNormGeneratorValue q R.fundamentalLattice F := by
    exact R.profile.fundamentalTerminalValue_isNormGeneratorValue R.component
  have hFOrder : ordUnit K F =
      W.effectiveNormOrderAt p (ordUnit K (W.scaleGenerator p)) := by
    have hideal : Lattice.principalIdeal (K := K) (F : K) =
        Lattice.powerIdeal (K := K)
          (W.effectiveNormOrderAt p (ordUnit K (W.scaleGenerator p))) :=
      hF.2.symm.trans R.normIdeal_fundamentalLattice_eq_powerIdeal
    rw [Lattice.principalIdeal_eq_powerIdeal] at hideal
    exact Lattice.powerIdeal_injective hideal
  have hscaleLeF : ordUnit K (W.scaleGenerator p) ≤ ordUnit K F := by
    rw [hFOrder]
    exact W.targetScale_le_effectiveNormOrderAt p
      (ordUnit K (W.scaleGenerator p))
  have hsecondLeF : c.order 1 ≤ ordUnit K F :=
    hsecondLeScale.trans hscaleLeF
  have hweightInclusion := R.weakComponentWeight_le_fundamentalWeightIdeal
  rw [Lattice.weightIdeal_eq_powerIdeal,
    Lattice.weightIdeal_eq_powerIdeal,
    Lattice.powerIdeal_le_iff] at hweightInclusion
  have hfundWeightLe : R.jordan.fundamentalWeightOrder R.component ≤
      Lattice.weightIdealOrder J.space J.lattice := by
    simpa only [Lattice.JordanDecomposition.fundamentalWeightOrder,
      fundamentalLattice, J, p] using hweightInclusion
  let d := BONG.GoodBONG.defectOrder (K := K)
    (-J.refinedDeterminantUnit)
  by_cases htop : d = ⊤
  · rw [show BONG.GoodBONG.defectOrder (K := K)
          (-(W.component (x.indexEquiv I).1).refinedDeterminantUnit) = d by
        rfl,
      htop]
    exact le_top
  · obtain ⟨δ, hδ⟩ := WithTop.ne_top_iff_exists.mp htop
    have hbinary :=
      c.weightIdealOrder_le_order_one_add_defect_neg_determinantUnit
    change (((Lattice.weightIdealOrder J.space J.lattice : ℚ) :
        WithTop ℚ)) ≤
      ((c.order 1 : ℚ) : WithTop ℚ) + d at hbinary
    rw [← hδ] at hbinary
    norm_cast at hbinary
    rw [R.prefixAlphaCap_stop_sub_one_eq_fundamentalWeight_sub_normGenerator
      hrank]
    change ((((R.jordan.fundamentalWeightOrder R.component -
        ordUnit K F : Int) : ℚ) : WithTop ℚ)) ≤ d
    rw [← hδ]
    norm_cast
    push_cast
    have hfundWeightLeQ :
        (R.jordan.fundamentalWeightOrder R.component : ℚ) ≤
          (Lattice.weightIdealOrder J.space J.lattice : ℚ) := by
      exact_mod_cast hfundWeightLe
    have hsecondLeFQ : (c.order 1 : ℚ) ≤ (ordUnit K F : ℚ) := by
      exact_mod_cast hsecondLeF
    linarith

/-- Arbitrary-generator form of Beli (2019), Corollary 3.3 at the right
end of a resolved strict block.  The fundamental terminal value gives one
right approximation.  O'Meara's norm-group defect estimate then replaces
it by any other norm generator of the same fundamental lattice. -/
theorem fundamentalNormGenerator_mul_prefixProduct_stop_isPrefixApproximation
    {m : Nat} {a : BONG.GoodBONG q L (m + 2)}
    {W : Lattice.WeakJordanDecomposition q L t}
    {x : BONG.WeakJordanOrderProfileWitness a.toBONG W} {I : Fin (m + 2)}
    (R : StrictCoordinateResolution a.toBONG W x I)
    (A : Kˣ)
    (hA : Lattice.IsNormGeneratorValue q R.fundamentalLattice A)
    (hrank : 2 ≤ R.jordan.componentRank R.component) :
    a.IsPrefixApproximation (R.coordinates.stop - 1)
      (A * a.prefixProduct R.coordinates.stop) := by
  let C := R.coordinates
  let F := R.profile.fundamentalTerminalValue R.component
  have hF : Lattice.IsNormGeneratorValue q R.fundamentalLattice F := by
    exact R.profile.fundamentalTerminalValue_isNormGeneratorValue R.component
  have hCstop : C.stop = C.start + R.jordan.componentRank R.component := rfl
  have htargetPos : 0 < C.stop - 1 := by
    rw [hCstop]
    omega
  have htargetLt : C.stop - 1 < m + 2 := by
    have := C.stop_le
    omega
  have halphaLt : C.stop - 2 < m + 1 := by
    have := C.stop_le
    omega
  let alphaIndex : Fin (m + 1) := ⟨C.stop - 2, halphaLt⟩
  let penult : Fin (R.jordan.componentRank R.component) :=
    ⟨R.jordan.componentRank R.component - 2, by omega⟩
  have hpenultGlobal :
      R.profile.indexEquiv.symm ⟨R.component, penult⟩ =
        alphaIndex.castSucc := by
    apply Fin.ext
    rw [R.profile.inverse_index_val]
    change C.start + (R.jordan.componentRank R.component - 2) =
      C.stop - 2
    rw [hCstop]
    omega
  have hcoordinates : R.profile.indexEquiv alphaIndex.castSucc =
      ⟨R.component, penult⟩ := by
    rw [← hpenultGlobal, R.profile.indexEquiv.apply_symm_apply]
  have hlocal :
      (R.profile.indexEquiv alphaIndex.castSucc).2.val + 1 <
        R.jordan.componentRank
          (R.profile.indexEquiv alphaIndex.castSucc).1 := by
    rw [hcoordinates]
    dsimp only [penult]
    omega
  have hweight :=
    R.profile.internal_weightOrder_eq_order_add_alpha alphaIndex hlocal
  rw [hcoordinates] at hweight
  have hleftLt : C.stop - 2 < C.stop := by omega
  have hleftStart : C.start ≤ C.stop - 2 := by
    rw [hCstop]
    omega
  have hleftIndex : C.index (C.stop - 2) hleftLt =
      alphaIndex.castSucc := by
    apply Fin.ext
    rfl
  have hrightParity : (C.stop - (C.stop - 2)) % 2 = 0 := by omega
  have hleftOrder :=
    (C.beli2009Lemma213_ii (C.stop - 2) hleftStart hleftLt).1
      hrightParity
  rw [hleftIndex] at hleftOrder
  have hnormIdeal : Lattice.normIdeal q R.fundamentalLattice =
      Lattice.powerIdeal (K := K) C.normOrder := by
    unfold fundamentalLattice
    unfold Lattice.JordanDecomposition.fundamentalLattice
    rw [R.jordan.normIdeal_scaleTruncation_eq_powerIdeal R.component
      (R.jordan.fundamentalScaleOrder R.component)]
    rfl
  have hFOrder : ordUnit K F = C.normOrder := by
    have hideal : Lattice.principalIdeal (K := K) (F : K) =
      Lattice.powerIdeal (K := K) C.normOrder :=
      hF.2.symm.trans hnormIdeal
    rw [Lattice.principalIdeal_eq_powerIdeal] at hideal
    exact Lattice.powerIdeal_injective hideal
  have halpha : a.alphaValue alphaIndex =
      ((R.jordan.fundamentalWeightOrder R.component - ordUnit K F : Int) :
        ℚ) := by
    have hleftOrderQ : (a.order alphaIndex.castSucc : ℚ) =
        (ordUnit K F : ℚ) := by
      rw [hleftOrder, hFOrder]
    push_cast
    linarith
  have hcap : a.prefixAlphaCap (C.stop - 1) =
      (((R.jordan.fundamentalWeightOrder R.component - ordUnit K F : Int) :
        ℚ) : WithTop ℚ) := by
    rw [a.prefixAlphaCap_of_internal htargetPos htargetLt]
    have hidx : (⟨C.stop - 1 - 1, by omega⟩ : Fin (m + 1)) =
        alphaIndex := by
      apply Fin.ext
      dsimp only [alphaIndex]
      omega
    rw [hidx, halpha]
  have hAFOrder : ordUnit K A = ordUnit K F := by
    apply (Lattice.principalIdeal_eq_iff_ordUnit_eq A F).mp
    exact hA.2.symm.trans hF.2
  have hnegAOrder : ordUnit K (-A) = ordUnit K F := by
    simpa only [ordUnit_neg] using hAFOrder
  have hraw :=
    Lattice.weightIdealOrder_sub_ordUnit_le_defectOrder_neg_div_of_normGenerators
      F (-A) hF hA.neg hnegAOrder
  have hproduct : (-(F / (-A))) * A ^ 2 = F * A := by
    apply Units.ext
    simp only [Units.val_neg, Units.val_div_eq_div_val,
      Units.val_mul, Units.val_pow_eq_pow_val]
    field_simp [Units.ne_zero F, Units.ne_zero A]
  have hdefectEq : BONG.GoodBONG.defectOrder (K := K) (-(F / (-A))) =
      BONG.GoodBONG.defectOrder (K := K) (F * A) := by
    rw [← hproduct]
    exact (BONG.GoodBONG.defectOrder_mul_square (-(F / (-A))) A).symm
  have hFA : a.prefixAlphaCap (C.stop - 1) ≤
      BONG.GoodBONG.defectOrder (K := K) (F * A) := by
    rw [hcap]
    simpa only [fundamentalLattice,
      Lattice.JordanDecomposition.fundamentalWeightOrder,
      hdefectEq] using hraw
  have hseed :=
    R.fundamentalTerminalValue_mul_prefixProduct_stop_isPrefixApproximation
  have hreplace : a.prefixAlphaCap (C.stop - 1) ≤
      BONG.GoodBONG.defectOrder (K := K)
        ((F * a.prefixProduct C.stop) *
          (A * a.prefixProduct C.stop)) := by
    have hmul :
        (F * a.prefixProduct C.stop) * (A * a.prefixProduct C.stop) =
          (F * A) * (a.prefixProduct C.stop) ^ 2 := by
      simp only [pow_two]
      ac_rfl
    rw [hmul, BONG.GoodBONG.defectOrder_mul_square]
    exact hFA
  exact a.isPrefixApproximation_of_defect_mul (C.stop - 1)
    (F * a.prefixProduct C.stop) (A * a.prefixProduct C.stop)
      hseed hreplace

end BONG.StrictCoordinateResolution

namespace BONG

/-- Equal weak effective norm orders and an inclusion of the resolved
fundamental lattices give one literal norm generator on both sides. -/
theorem StrictCoordinateResolution.exists_commonNormGenerator_of_effective_eq
    {n s t : Nat}
    {a : BONG V q M n} {b : BONG V q N n}
    {W : Lattice.WeakJordanDecomposition q M s}
    {Z : Lattice.WeakJordanDecomposition q N t}
    {x : WeakJordanOrderProfileWitness a W}
    {y : WeakJordanOrderProfileWitness b Z} {I : Fin n}
    (R : StrictCoordinateResolution a W x I)
    (S : StrictCoordinateResolution b Z y I)
    (hinclude : S.fundamentalLattice ≤ R.fundamentalLattice)
    (heffective :
      W.effectiveNormOrderAt (x.indexEquiv I).1
          (ordUnit K (W.scaleGenerator (x.indexEquiv I).1)) =
        Z.effectiveNormOrderAt (y.indexEquiv I).1
          (ordUnit K (Z.scaleGenerator (y.indexEquiv I).1))) :
    ∃ A : Kˣ,
      Lattice.IsNormGeneratorValue q R.fundamentalLattice A ∧
        Lattice.IsNormGeneratorValue q S.fundamentalLattice A := by
  let A := S.fundamentalNormGenerator
  have hS : Lattice.IsNormGeneratorValue q S.fundamentalLattice A :=
    S.fundamentalNormGenerator_spec
  have hideal : Lattice.normIdeal q R.fundamentalLattice =
      Lattice.normIdeal q S.fundamentalLattice := by
    rw [R.normIdeal_fundamentalLattice_eq_powerIdeal,
      S.normIdeal_fundamentalLattice_eq_powerIdeal, heffective]
  exact ⟨A, hS.of_le_of_normIdeal_eq hinclude hideal, hS⟩

/-- If the target norm order rises by two, rescaling a source generator by
`π²` gives a generator on the target resolved fundamental lattice. -/
theorem StrictCoordinateResolution.normGenerator_pair_of_effective_add_two
    {n s t : Nat}
    {a : BONG V q M n} {b : BONG V q N n}
    {W : Lattice.WeakJordanDecomposition q M s}
    {Z : Lattice.WeakJordanDecomposition q N t}
    {x : WeakJordanOrderProfileWitness a W}
    {y : WeakJordanOrderProfileWitness b Z} {I : Fin n}
    (R : StrictCoordinateResolution a W x I)
    (S : StrictCoordinateResolution b Z y I)
    (hpos : 0 < finrank K V)
    (hinclude : Lattice.rescale (uniformizerUnit K)
      R.fundamentalLattice ≤ S.fundamentalLattice)
    (heffective :
      Z.effectiveNormOrderAt (y.indexEquiv I).1
          (ordUnit K (Z.scaleGenerator (y.indexEquiv I).1)) =
        W.effectiveNormOrderAt (x.indexEquiv I).1
            (ordUnit K (W.scaleGenerator (x.indexEquiv I).1)) + 2) :
    let A := R.fundamentalNormGenerator
    Lattice.IsNormGeneratorValue q R.fundamentalLattice A ∧
      Lattice.IsNormGeneratorValue q S.fundamentalLattice
        ((uniformizerUnit K) ^ 2 * A) := by
  dsimp only
  let A := R.fundamentalNormGenerator
  let B := S.fundamentalNormGenerator
  have hR : Lattice.IsNormGeneratorValue q R.fundamentalLattice A :=
    R.fundamentalNormGenerator_spec
  have hS : Lattice.IsNormGeneratorValue q S.fundamentalLattice B :=
    S.fundamentalNormGenerator_spec
  have hrescaled := hR.rescale_of_finrank_pos
    (c := uniformizerUnit K) hpos
  have hpi : ordUnit K (uniformizerUnit K) = 1 := by
    simpa [uniformizerPowerUnit] using
      (ordUnit_uniformizerPowerUnit (K := K) (1 : Int))
  have horderA : ordUnit K A =
      W.effectiveNormOrderAt (x.indexEquiv I).1
        (ordUnit K (W.scaleGenerator (x.indexEquiv I).1)) := by
    have hideal := R.normIdeal_fundamentalLattice_eq_powerIdeal
    rw [hR.2, Lattice.principalIdeal_eq_powerIdeal] at hideal
    exact Lattice.powerIdeal_injective hideal
  have horderB : ordUnit K B =
      Z.effectiveNormOrderAt (y.indexEquiv I).1
        (ordUnit K (Z.scaleGenerator (y.indexEquiv I).1)) := by
    have hideal := S.normIdeal_fundamentalLattice_eq_powerIdeal
    rw [hS.2, Lattice.principalIdeal_eq_powerIdeal] at hideal
    exact Lattice.powerIdeal_injective hideal
  have horder : ordUnit K ((uniformizerUnit K) ^ 2 * A) = ordUnit K B := by
    rw [ordUnit_mul, ordUnit_pow, hpi, horderA, horderB, heffective]
    omega
  exact ⟨hR, hrescaled.of_le_of_order_eq hS hinclude horder⟩

end BONG

namespace Lattice.Beli2019Lemma51Data

/-- The small-side resolution never absorbs a component on the left: its
only possible collision has the selected component as the left member. -/
theorem smallStrictCoordinateResolution_localCoordinateOffset_eq_zero
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    {n : Nat} (b : BONG.GoodBONG q N n) (I : Fin n)
    (hle : ((D.smallWeakProfileWitness b).indexEquiv I).1 ≤
      D.smallSelectedPosition) :
    (D.smallStrictCoordinateResolution b I hle).localCoordinateOffset = 0 := by
  classical
  simp only [smallStrictCoordinateResolution]
  split
  · split <;> rfl
  · rfl

/-- Strictly before the selected large component, a large-side resolution
also has zero left offset.  The nonzero branch is exactly the right member
of the collision pair, hence the selected component itself. -/
theorem largeStrictCoordinateResolution_localCoordinateOffset_eq_zero_of_lt
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    {n : Nat} (a : BONG.GoodBONG q M n) (I : Fin n)
    (hle : ((D.largeWeakProfileWitness a).indexEquiv I).1 ≤
      D.largeSelectedPosition)
    (hlt : ((D.largeWeakProfileWitness a).indexEquiv I).1 <
      D.largeSelectedPosition) :
    (D.largeStrictCoordinateResolution a I hle).localCoordinateOffset = 0 := by
  classical
  simp only [largeStrictCoordinateResolution]
  split
  next hcollision =>
    let c := Classical.choose hcollision
    have hscale := Classical.choose_spec hcollision
    let hadj := D.largeCollision_adjacent c hscale
    let k := Classical.choose hadj
    have hk := Classical.choose_spec hadj
    split
    next _hstrictBefore => rfl
    next hnotBefore =>
      split
      next _hleft => rfl
      next hnotLeft =>
        exfalso
        have hlePair : ((D.largeWeakProfileWitness a).indexEquiv I).1 ≤
            k.succ := by
          rw [hk.2]
          exact hle
        have hright : ((D.largeWeakProfileWitness a).indexEquiv I).1 =
            k.succ := by
          apply Fin.ext
          change ((D.largeWeakProfileWitness a).indexEquiv I).1.val = k.val + 1
          change ¬((D.largeWeakProfileWitness a).indexEquiv I).1.val < k.val
            at hnotBefore
          have hneVal :
              ((D.largeWeakProfileWitness a).indexEquiv I).1.val ≠ k.val := by
            intro hval
            apply hnotLeft
            apply Fin.ext
            exact hval
          change ((D.largeWeakProfileWitness a).indexEquiv I).1.val ≤
            k.val + 1 at hlePair
          omega
        have hltPair : ((D.largeWeakProfileWitness a).indexEquiv I).1 <
            k.succ := by
          rw [hk.2]
          exact hlt
        exact (ne_of_lt hltPair) hright
  · rfl

/-- In the binary aligned case, if the large selected component has an
equal-scale common component immediately on its left, the determinant of
the large prefix through the selected component is, up to a square, the
determinant of the small prefix before the selected component times the
determinant of the enlarged selected binary lattice.  This is the lattice
identity `det F(K_(k₁) ⊥ J') = det F K_(k₁) det F J'` used in the last
paragraph of Beli (2019), Lemma 5.13(i). -/
theorem exists_largeSelectedPrefixDeterminant_eq_smallPrefix_mul_enlarged_square
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    (c : Fin D.complementComponentCount)
    (hscale : ordUnit K (D.complementStrictWeak.scaleGenerator c) =
      ordUnit K D.input.block.enlargedScaleGenerator) :
    ∃ s : Kˣ,
      (D.smallAlmostJordan.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice D.smallSelectedPosition.val
          |>.refinedDeterminantUnit) *
          D.input.enlargedComponent.refinedDeterminantUnit * s ^ 2 =
        (D.largeAlmostJordan.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice
            (D.largeSelectedPosition.val + 1)
          |>.refinedDeterminantUnit) := by
  let P := D.largeAlmostJordan.toOrthogonalDecomposition
  let Q := D.smallAlmostJordan.toOrthogonalDecomposition
  let p := D.largeSelectedPosition
  obtain ⟨k, _hkCommon, hkSelected⟩ :=
    D.largeCollision_adjacent c hscale
  have hpPos : 0 < p.val := by
    have hval := congrArg Fin.val hkSelected
    change k.val + 1 = p.val at hval
    omega
  let cut := p.val
  have hcut : cut - 1 + 1 = cut := by
    dsimp only [cut]
    omega
  have hP : cut - 1 + 1 ≤ D.complementComponentCount + 1 := by
    rw [hcut]
    exact p.isLt.le
  have hQ : cut - 1 + 1 ≤ D.complementComponentCount + 1 := hP
  have hprefixComponent (z : Fin (cut - 1 + 1)) :
      P.component (P.prefixIndexEquiv (cut - 1 + 1) hP z).1 =
        Q.component (Q.prefixIndexEquiv (cut - 1 + 1) hQ z).1 := by
    let jP := (P.prefixIndexEquiv (cut - 1 + 1) hP z).1
    let jQ := (Q.prefixIndexEquiv (cut - 1 + 1) hQ z).1
    have hjPVal : jP.val = z.val :=
      P.prefixIndexEquiv_val (cut - 1 + 1) hP z
    have hjQVal : jQ.val = z.val :=
      Q.prefixIndexEquiv_val (cut - 1 + 1) hQ z
    have hjEq : jP = jQ := by
      apply Fin.ext
      rw [hjPVal, hjQVal]
    have hjBefore : jP < D.largeSelectedPosition := by
      change jP.val < p.val
      rw [hjPVal]
      have hz := z.isLt
      omega
    change D.largeAlmostJordan.component jP =
      D.smallAlmostJordan.component jQ
    rw [← hjEq]
    exact D.aligned_component_eq hselected jP (ne_of_lt hjBefore)
  let F := P.prefixComponentwiseIsometryOfDifferentCounts Q hP hQ
    (fun z ↦ by
      rw [hprefixComponent z]
      exact Lattice.Isometry.refl _ _)
  have hprefixClass := Lattice.determinantClass_eq_of_isometry F
  have hprefixClass' :
      unitSquareClass K
          ((P.prefixQuadraticSublattice cut).refinedDeterminantUnit) =
        unitSquareClass K
          ((Q.prefixQuadraticSublattice cut).refinedDeterminantUnit) := by
    change unitSquareClass K
          ((P.prefixQuadraticSublattice (cut - 1 + 1)).refinedDeterminantUnit) =
        unitSquareClass K
          ((Q.prefixQuadraticSublattice (cut - 1 + 1)).refinedDeterminantUnit)
      at hprefixClass
    rw [hcut] at hprefixClass
    exact hprefixClass
  have happend := P.unitSquareClass_prefix_succ_eq_mul_component p
  rw [D.largeAlmostJordan_component_selected] at happend
  have htarget :
      unitSquareClass K
          ((Q.prefixQuadraticSublattice cut).refinedDeterminantUnit *
            D.input.enlargedComponent.refinedDeterminantUnit) =
        unitSquareClass K
          ((P.prefixQuadraticSublattice (cut + 1)).refinedDeterminantUnit) := by
    calc
      unitSquareClass K
          ((Q.prefixQuadraticSublattice cut).refinedDeterminantUnit *
            D.input.enlargedComponent.refinedDeterminantUnit) =
          unitSquareClass K
              ((Q.prefixQuadraticSublattice cut).refinedDeterminantUnit) *
            unitSquareClass K
              D.input.enlargedComponent.refinedDeterminantUnit :=
        by rw [unitSquareClass_mul]
      _ = unitSquareClass K
              ((P.prefixQuadraticSublattice cut).refinedDeterminantUnit) *
            unitSquareClass K
              D.input.enlargedComponent.refinedDeterminantUnit := by
        rw [hprefixClass']
      _ = unitSquareClass K
          ((P.prefixQuadraticSublattice cut).refinedDeterminantUnit *
            D.input.enlargedComponent.refinedDeterminantUnit) :=
        by rw [unitSquareClass_mul]
      _ = unitSquareClass K
          ((P.prefixQuadraticSublattice (cut + 1)).refinedDeterminantUnit) := by
        simpa only [P, p, cut] using happend.symm
  obtain ⟨s, hs⟩ :=
    BONG.GoodBONG.exists_square_mul_eq_of_unitSquareClass_eq
      ((Q.prefixQuadraticSublattice cut).refinedDeterminantUnit *
        D.input.enlargedComponent.refinedDeterminantUnit)
      ((P.prefixQuadraticSublattice (cut + 1)).refinedDeterminantUnit)
      htarget
  refine ⟨s, ?_⟩
  simpa only [P, Q, p, cut, ← hselected] using hs

/-- In the aligned case, collision resolution does not change the common
block start at a coordinate strictly before the selected component. -/
theorem weakAligned_strictResolution_start_eq_before_selected
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (I : Fin (n + 2))
    (hbefore : ((D.largeWeakProfileWitness a).indexEquiv I).1 <
      D.largeSelectedPosition) :
    let hlargeLe := hbefore.le
    let hsmallLe : ((D.smallWeakProfileWitness b).indexEquiv I).1 ≤
        D.smallSelectedPosition := by
      have hcoordinates := D.weakProfile_coordinates_eq hselected a b I
      rw [hselected, ← hcoordinates.1]
      exact hbefore.le
    let Rlarge := D.largeStrictCoordinateResolution a I hlargeLe
    let Rsmall := D.smallStrictCoordinateResolution b I hsmallLe
    Rlarge.coordinates.start = Rsmall.coordinates.start := by
  dsimp only
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  have hcoordinates := D.weakProfile_coordinates_eq hselected a b I
  have hsmallBefore : (y.indexEquiv I).1 < D.smallSelectedPosition := by
    rw [hselected, ← hcoordinates.1]
    exact hbefore
  let hlargeLe := hbefore.le
  let hsmallLe := hsmallBefore.le
  let Rlarge := D.largeStrictCoordinateResolution a I hlargeLe
  let Rsmall := D.smallStrictCoordinateResolution b I hsmallLe
  have hoffLarge : Rlarge.localCoordinateOffset = 0 :=
    D.largeStrictCoordinateResolution_localCoordinateOffset_eq_zero_of_lt
      a I hlargeLe hbefore
  have hoffSmall : Rsmall.localCoordinateOffset = 0 :=
    D.smallStrictCoordinateResolution_localCoordinateOffset_eq_zero
      b I hsmallLe
  have hstartLarge := Rlarge.coordinates_start_add_offset_eq_weak_componentStart
  have hstartSmall := Rsmall.coordinates_start_add_offset_eq_weak_componentStart
  rw [hoffLarge, Nat.add_zero] at hstartLarge
  rw [hoffSmall, Nat.add_zero] at hstartSmall
  have hweakStart : x.componentStart (x.indexEquiv I).1 =
      y.componentStart (y.indexEquiv I).1 := by
    rw [hcoordinates.1]
    unfold BONG.WeakJordanOrderProfileWitness.componentStart
    apply Finset.sum_congr rfl
    intro k _hk
    exact congrFun (D.almostJordan_componentRank_eq hselected) k
  exact hstartLarge.trans (hweakStart.trans hstartSmall.symm)

/-- The resolved local coordinates also agree strictly before the aligned
selected component. -/
theorem weakAligned_strictResolution_local_eq_before_selected
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (I : Fin (n + 2))
    (hbefore : ((D.largeWeakProfileWitness a).indexEquiv I).1 <
      D.largeSelectedPosition) :
    let hlargeLe := hbefore.le
    let hsmallLe : ((D.smallWeakProfileWitness b).indexEquiv I).1 ≤
        D.smallSelectedPosition := by
      have hcoordinates := D.weakProfile_coordinates_eq hselected a b I
      rw [hselected, ← hcoordinates.1]
      exact hbefore.le
    let Rlarge := D.largeStrictCoordinateResolution a I hlargeLe
    let Rsmall := D.smallStrictCoordinateResolution b I hsmallLe
    (Rlarge.profile.indexEquiv I).2.val =
      (Rsmall.profile.indexEquiv I).2.val := by
  dsimp only
  have hcoordinates := D.weakProfile_coordinates_eq hselected a b I
  have hsmallBefore :
      ((D.smallWeakProfileWitness b).indexEquiv I).1 <
        D.smallSelectedPosition := by
    rw [hselected, ← hcoordinates.1]
    exact hbefore
  let hlargeLe := hbefore.le
  let hsmallLe := hsmallBefore.le
  let Rlarge := D.largeStrictCoordinateResolution a I hlargeLe
  let Rsmall := D.smallStrictCoordinateResolution b I hsmallLe
  have hoffLarge : Rlarge.localCoordinateOffset = 0 :=
    D.largeStrictCoordinateResolution_localCoordinateOffset_eq_zero_of_lt
      a I hlargeLe hbefore
  have hoffSmall : Rsmall.localCoordinateOffset = 0 :=
    D.smallStrictCoordinateResolution_localCoordinateOffset_eq_zero
      b I hsmallLe
  rw [Rlarge.localCoordinate_eq, Rsmall.localCoordinate_eq,
    hoffLarge, hoffSmall, hcoordinates.2]

/-- The determinant seeds of the two collision-resolved blocks differ by a
square at every coordinate strictly before the aligned selected component.
The proof compares equal-length prefixes of strict decompositions whose
ambient component counts may differ. -/
theorem weakAligned_strictResolution_determinantSeeds_square_before_selected
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (I : Fin (n + 2))
    (hbefore : ((D.largeWeakProfileWitness a).indexEquiv I).1 <
      D.largeSelectedPosition) :
    let hlargeLe := hbefore.le
    let hsmallLe : ((D.smallWeakProfileWitness b).indexEquiv I).1 ≤
        D.smallSelectedPosition := by
      have hcoordinates := D.weakProfile_coordinates_eq hselected a b I
      rw [hselected, ← hcoordinates.1]
      exact hbefore.le
    let Rlarge := D.largeStrictCoordinateResolution a I hlargeLe
    let Rsmall := D.smallStrictCoordinateResolution b I hsmallLe
    ∃ s : Kˣ,
      Rsmall.determinantSeedData.leftDet =
        Rlarge.determinantSeedData.leftDet * s ^ 2 := by
  dsimp only
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  have hcoordinates := D.weakProfile_coordinates_eq hselected a b I
  have hsmallBefore : (y.indexEquiv I).1 < D.smallSelectedPosition := by
    rw [hselected, ← hcoordinates.1]
    exact hbefore
  let hlargeLe := hbefore.le
  let hsmallLe := hsmallBefore.le
  let Rlarge := D.largeStrictCoordinateResolution a I hlargeLe
  let Rsmall := D.smallStrictCoordinateResolution b I hsmallLe
  have hoffLarge : Rlarge.localCoordinateOffset = 0 :=
    D.largeStrictCoordinateResolution_localCoordinateOffset_eq_zero_of_lt
      a I hlargeLe hbefore
  have hoffSmall : Rsmall.localCoordinateOffset = 0 :=
    D.smallStrictCoordinateResolution_localCoordinateOffset_eq_zero
      b I hsmallLe
  have hcomponentLarge : Rlarge.component.val = (x.indexEquiv I).1.val :=
    Rlarge.component_val_eq_of_offset_zero hoffLarge
  have hcomponentSmall : Rsmall.component.val = (y.indexEquiv I).1.val :=
    Rsmall.component_val_eq_of_offset_zero hoffSmall
  have hcomponentVal : Rlarge.component.val = Rsmall.component.val :=
    hcomponentLarge.trans <|
      (congrArg Fin.val hcoordinates.1).trans hcomponentSmall.symm
  by_cases hpzero : Rlarge.component.val = 0
  · have hsmallZero : Rsmall.component.val = 0 := hcomponentVal.symm.trans hpzero
    refine ⟨1, ?_⟩
    rw [Rsmall.determinantSeedData_leftDet_of_component_zero hsmallZero,
      Rlarge.determinantSeedData_leftDet_of_component_zero hpzero]
    simp
  · let cut := Rlarge.component.val
    let P := Rlarge.jordan.toOrthogonalDecomposition
    let Q := Rsmall.jordan.toOrthogonalDecomposition
    have hcut : cut - 1 + 1 = cut := by
      dsimp only [cut]
      omega
    have hP : cut - 1 + 1 ≤ Rlarge.componentCount := by
      rw [hcut]
      exact Rlarge.component.isLt.le
    have hQ : cut - 1 + 1 ≤ Rsmall.componentCount := by
      rw [hcut]
      have hsmallLt := Rsmall.component.isLt
      omega
    have hprefixComponent (z : Fin (cut - 1 + 1)) :
        P.component (P.prefixIndexEquiv (cut - 1 + 1) hP z).1 =
          Q.component (Q.prefixIndexEquiv (cut - 1 + 1) hQ z).1 := by
      let jP := (P.prefixIndexEquiv (cut - 1 + 1) hP z).1
      let jQ := (Q.prefixIndexEquiv (cut - 1 + 1) hQ z).1
      have hjPVal : jP.val = z.val := by
        exact P.prefixIndexEquiv_val (cut - 1 + 1) hP z
      have hjQVal : jQ.val = z.val := by
        exact Q.prefixIndexEquiv_val (cut - 1 + 1) hQ z
      have hzCut : z.val < cut := by
        have hz := z.isLt
        omega
      have hjP : jP < Rlarge.component := by
        change jP.val < Rlarge.component.val
        dsimp only [cut] at hzCut
        omega
      have hjQ : jQ < Rsmall.component := by
        change jQ.val < Rsmall.component.val
        omega
      obtain ⟨oldP, holdPVal, holdP⟩ :=
        Rlarge.prefixComponent_eq jP hjP
      obtain ⟨oldQ, holdQVal, holdQ⟩ :=
        Rsmall.prefixComponent_eq jQ hjQ
      have holdEq : oldP = oldQ := by
        apply Fin.ext
        rw [holdPVal, holdQVal, hjPVal, hjQVal]
      have holdPBefore : oldP < D.largeSelectedPosition := by
        change oldP.val < D.largeSelectedPosition.val
        calc
          oldP.val = jP.val := holdPVal
          _ < Rlarge.component.val := hjP
          _ = (x.indexEquiv I).1.val := hcomponentLarge
          _ < D.largeSelectedPosition.val := hbefore
      change Rlarge.strictWeak.component jP = Rsmall.strictWeak.component jQ
      rw [holdP, holdQ, ← holdEq]
      exact D.aligned_component_eq hselected oldP (ne_of_lt holdPBefore)
    have hsquare :=
      P.exists_prefixDeterminantUnit_eq_mul_square_of_componentwiseIsometry_of_differentCounts
        Q hP hQ (fun z ↦ by
          rw [hprefixComponent z]
          exact Lattice.Isometry.refl _ _)
    rcases hsquare with ⟨s, hs⟩
    refine ⟨s, ?_⟩
    rw [Rsmall.determinantSeedData_leftDet_of_component_ne_zero (by
        omega),
      Rlarge.determinantSeedData_leftDet_of_component_ne_zero hpzero]
    change
      (Q.prefixQuadraticSublattice Rsmall.component.val).refinedDeterminantUnit =
        (P.prefixQuadraticSublattice Rlarge.component.val).refinedDeterminantUnit *
          s ^ 2
    rw [← hcomponentVal]
    simpa only [hcut] using hs

/-- At an odd local boundary, a one-step rise of the two weak effective norm
orders would force exactly the current-order jump excluded in Lemma 5.13. -/
theorem weakAligned_effectiveNormOrder_ne_add_one_of_current_ne
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hbefore : ((D.largeWeakProfileWitness a).indexEquiv
      ⟨i.val, i.lt_large⟩).1 < D.largeSelectedPosition)
    (hodd : Odd ((D.largeWeakProfileWitness a).indexEquiv
      ⟨i.val, i.lt_large⟩).2.val)
    (hcurrent : b.orderSequence.entryOrZero (i.val - 1) ≠
      a.orderSequence.entryOrZero (i.val - 1) + 1) :
    let R : Fin (n + 2) := ⟨i.val, i.lt_large⟩
    let x := D.largeWeakProfileWitness a
    let p := (x.indexEquiv R).1
    let target := ordUnit K (D.largeAlmostJordan.scaleGenerator p)
    D.smallAlmostJordan.effectiveNormOrderAt p target ≠
      D.largeAlmostJordan.effectiveNormOrderAt p target + 1 := by
  dsimp only
  let R : Fin (n + 2) := ⟨i.val, i.lt_large⟩
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  let p := (x.indexEquiv R).1
  let j := (x.indexEquiv R).2.val
  let target := ordUnit K (D.largeAlmostJordan.scaleGenerator p)
  change (x.indexEquiv R).1 < D.largeSelectedPosition at hbefore
  change Odd j at hodd
  intro hone
  apply hcurrent
  rcases hodd with ⟨k, hk⟩
  let I : Fin (n + 2) := ⟨i.val - 1, by
    have := i.pos
    have := i.lt_large
    omega⟩
  let localPrevious : Fin
      (finrank K (D.largeAlmostJordan.component p).carrier) :=
    ⟨j - 1, by
      have hjlt := (x.indexEquiv R).2.isLt
      change j < finrank K (D.largeAlmostJordan.component p).carrier at hjlt
      omega⟩
  have hglobal := x.index_val_eq_componentStart_add_local R
  have hiStart : i.val = x.componentStart p + j := by
    unfold BONG.WeakJordanOrderProfileWitness.componentStart
    simpa only [R, p, j] using hglobal
  have hI : I = x.indexEquiv.symm ⟨p, localPrevious⟩ := by
    apply Fin.ext
    rw [x.inverse_index_val]
    change i.val - 1 = x.componentStart p + (j - 1)
    rw [hiStart]
    omega
  have hxI : x.indexEquiv I = ⟨p, localPrevious⟩ := by
    rw [hI, x.indexEquiv.apply_symm_apply]
  have hxyI := D.weakProfile_coordinates_eq hselected a b I
  have hscale : ordUnit K (D.smallAlmostJordan.scaleGenerator p) = target :=
    (D.aligned_scaleOrder_eq_of_lt hselected p hbefore).symm
  have hevenPrevious : Even (j - 1) := ⟨k, by omega⟩
  have hlargeScale : target ≤
      D.largeAlmostJordan.effectiveNormOrderAt p target :=
    D.largeAlmostJordan.targetScale_le_effectiveNormOrderAt p target
  have hsmallScale : target ≤
      D.smallAlmostJordan.effectiveNormOrderAt p target := by
    rw [← hscale]
    exact D.smallAlmostJordan.targetScale_le_effectiveNormOrderAt p
      (ordUnit K (D.smallAlmostJordan.scaleGenerator p))
  have hlargeOrder := D.largeWeak_order_eq_localOrder a I
  have hsmallOrder := D.smallWeak_order_eq_localOrder b I
  have hxIPosition : (x.indexEquiv I).1 = p := by rw [hxI]
  have hxILocal : (x.indexEquiv I).2.val = j - 1 := by rw [hxI]
  have hyIPosition : (y.indexEquiv I).1 = p :=
    hxyI.1.symm.trans hxIPosition
  have hyILocal : (y.indexEquiv I).2.val = j - 1 :=
    hxyI.2.symm.trans hxILocal
  have hlargeOrder' : a.order I =
      JordanProfileOrder.localOrder target
        (D.largeAlmostJordan.effectiveNormOrderAt p target) (j - 1) := by
    simpa only [x, hxIPosition, hxILocal, target] using hlargeOrder
  have hsmallOrder' : b.order I =
      JordanProfileOrder.localOrder target
        (D.smallAlmostJordan.effectiveNormOrderAt p target) (j - 1) := by
    simpa only [y, hyIPosition, hyILocal, hscale, target] using hsmallOrder
  rw [JordanProfileOrder.localOrder_even_of_scale_le
      hlargeScale hevenPrevious] at hlargeOrder'
  rw [JordanProfileOrder.localOrder_even_of_scale_le
      hsmallScale hevenPrevious] at hsmallOrder'
  rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence
      (by have := i.lt_large; omega),
    BeliOrderSequence.entryOrZero_of_lt a.orderSequence
      (by have := i.lt_large; omega)]
  change b.order I = a.order I + 1
  exact hsmallOrder'.trans <| hone.trans <|
    congrArg (fun z : Int ↦ z + 1) hlargeOrder'.symm

/-- Multiplication by a uniformizer carries a large-lattice scale
truncation into the small-lattice truncation at the same target scale. -/
theorem rescale_largeScaleTruncation_le_small
    (D : Beli2019Lemma51Data q M N) (target : Int) :
    Lattice.rescale (uniformizerUnit K)
        (Lattice.scaleTruncation q M target) ≤
      Lattice.scaleTruncation q N target := by
  intro x hx
  change x ∈ Lattice.rescale (uniformizerUnit K)
    (Lattice.scaleTruncation q M target) at hx
  change x ∈ Lattice.scaleTruncation q N target
  rw [Lattice.mem_rescale_iff] at hx
  rcases hx with ⟨z, hz, rfl⟩
  rw [Lattice.mem_scaleTruncation_iff_ord_bilin_ge] at hz ⊢
  refine ⟨D.uniformizer_largeLattice_le_small
      (Lattice.smul_mem_rescale (uniformizerUnit K) M hz.1), ?_⟩
  intro y hy
  have hpair := hz.2 y (D.smallLattice_le_large hy)
  rw [LinearMap.BilinForm.smul_left, ord_mul]
  have hpi : ord K ((uniformizerUnit K : Kˣ) : K) =
      ((1 : Int) : WithTop Int) := by
    rw [← coe_ordUnit]
    congr 1
    simpa [uniformizerPowerUnit] using
      (ordUnit_uniformizerPowerUnit (K := K) (1 : Int))
  rw [hpi]
  exact hpair.trans (le_add_of_nonneg_left (by norm_num))

/-- Lemma 5.13(i) at every aligned coordinate strictly before the selected
component, allowing either or both almost-Jordan families to contain their
unique scale collision. -/
theorem weakAligned_commonApproximation_before_selected
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hbefore : ((D.largeWeakProfileWitness a).indexEquiv
      ⟨i.val, i.lt_large⟩).1 < D.largeSelectedPosition)
    (hcurrent : b.orderSequence.entryOrZero (i.val - 1) ≠
      a.orderSequence.entryOrZero (i.val - 1) + 1) :
    ∃ X : Kˣ,
      a.IsPrefixApproximation i.val X ∧
        b.IsPrefixApproximation i.val X := by
  let I : Fin (n + 2) := ⟨i.val, i.lt_large⟩
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  let p := (x.indexEquiv I).1
  let j := (x.indexEquiv I).2.val
  have hcoordinates := D.weakProfile_coordinates_eq hselected a b I
  have hsmallBefore : (y.indexEquiv I).1 < D.smallSelectedPosition := by
    rw [hselected, ← hcoordinates.1]
    exact hbefore
  let hlargeLe := hbefore.le
  let hsmallLe := hsmallBefore.le
  let Rlarge := D.largeStrictCoordinateResolution a I hlargeLe
  let Rsmall := D.smallStrictCoordinateResolution b I hsmallLe
  let C := Rlarge.coordinates
  let E := Rsmall.coordinates
  let dLarge := Rlarge.determinantSeedData
  let dSmall := Rsmall.determinantSeedData
  have hstart : C.start = E.start := by
    exact D.weakAligned_strictResolution_start_eq_before_selected
      hselected a b I hbefore
  have hlocal : (Rlarge.profile.indexEquiv I).2.val = j := by
    have hoff :=
      D.largeStrictCoordinateResolution_localCoordinateOffset_eq_zero_of_lt
        a I hlargeLe hbefore
    rw [Rlarge.localCoordinate_eq, hoff, Nat.zero_add]
  have hiStartRaw := Rlarge.index_val_eq_coordinates_start_add_local
  have hiStart : i.val = C.start + j := by
    rw [hlocal] at hiStartRaw
    exact hiStartRaw
  have hiC : i.val < C.stop := Rlarge.index_val_lt_coordinates_stop
  have hiE : i.val < E.stop := Rsmall.index_val_lt_coordinates_stop
  have hdet : ∃ s : Kˣ, dSmall.leftDet = dLarge.leftDet * s ^ 2 := by
    exact D.weakAligned_strictResolution_determinantSeeds_square_before_selected
      hselected a b I hbefore
  let target := ordUnit K (D.largeAlmostJordan.scaleGenerator p)
  let eLarge := D.largeAlmostJordan.effectiveNormOrderAt p target
  let eSmall := D.smallAlmostJordan.effectiveNormOrderAt p target
  have hscale : ordUnit K (D.smallAlmostJordan.scaleGenerator p) = target :=
    (D.aligned_scaleOrder_eq_of_lt hselected p hbefore).symm
  have htargetLarge : target ≤
      ordUnit K D.input.block.enlargedScaleGenerator := by
    have hmono := D.largeAlmostJordan.scaleOrder_mono hbefore.le
    simpa only [target, D.largeAlmostJordan_scaleGenerator_selected] using hmono
  have hinclude : Rsmall.fundamentalLattice ≤ Rlarge.fundamentalLattice := by
    rw [Rsmall.fundamentalLattice_eq_scaleTruncation,
      Rlarge.fundamentalLattice_eq_scaleTruncation]
    change Lattice.scaleTruncation q N
        (ordUnit K (D.smallAlmostJordan.scaleGenerator (y.indexEquiv I).1)) ≤
      Lattice.scaleTruncation q M
        (ordUnit K (D.largeAlmostJordan.scaleGenerator (x.indexEquiv I).1))
    rw [← hcoordinates.1, hscale]
    exact D.scaleTruncation_small_le_large target htargetLarge
  have hrescale : Lattice.rescale (uniformizerUnit K)
      Rlarge.fundamentalLattice ≤ Rsmall.fundamentalLattice := by
    rw [Rlarge.fundamentalLattice_eq_scaleTruncation,
      Rsmall.fundamentalLattice_eq_scaleTruncation]
    change Lattice.rescale (uniformizerUnit K)
        (Lattice.scaleTruncation q M
          (ordUnit K (D.largeAlmostJordan.scaleGenerator (x.indexEquiv I).1))) ≤
      Lattice.scaleTruncation q N
        (ordUnit K (D.smallAlmostJordan.scaleGenerator (y.indexEquiv I).1))
    rw [← hcoordinates.1, hscale]
    exact D.rescale_largeScaleTruncation_le_small target
  rcases Nat.even_or_odd j with heven | hodd
  · rcases heven with ⟨k, hk⟩
    let S := Rlarge.approximationSeedsWith dLarge
      Rlarge.fundamentalNormGenerator Rlarge.fundamentalNormGenerator_spec
    let T := Rsmall.approximationSeedsWith dSmall
      Rsmall.fundamentalNormGenerator Rsmall.fundamentalNormGenerator_spec
    have hdet' : ∃ s : Kˣ, T.leftDet = S.leftDet * s ^ 2 := by
      simpa only [S, T,
        BONG.StrictCoordinateResolution.approximationSeedsWith_leftDet] using hdet
    apply S.commonApproximation_even_of_squareEquivalentSeeds T hstart hdet'
      i.val k
    · calc
        i.val = C.start + j := hiStart
        _ = C.start + 2 * k := by omega
    · exact hiC
    · exact hiE
  · rcases hodd with ⟨k, hk⟩
    have hbounds := D.common_effectiveNormOrder_bounds p hbefore
    change eLarge ≤ eSmall ∧ eSmall ≤ eLarge + 2 at hbounds
    have hcases : eSmall = eLarge ∨ eSmall = eLarge + 1 ∨
        eSmall = eLarge + 2 := by omega
    have hnotOne : eSmall ≠ eLarge + 1 := by
      exact D.weakAligned_effectiveNormOrder_ne_add_one_of_current_ne
        hselected a b i hbefore ⟨k, hk⟩ hcurrent
    have heffectiveEq (hzero : eSmall = eLarge) :
        D.largeAlmostJordan.effectiveNormOrderAt (x.indexEquiv I).1
            (ordUnit K (D.largeAlmostJordan.scaleGenerator (x.indexEquiv I).1)) =
          D.smallAlmostJordan.effectiveNormOrderAt (y.indexEquiv I).1
            (ordUnit K (D.smallAlmostJordan.scaleGenerator (y.indexEquiv I).1)) := by
      change eLarge = _
      rw [← hcoordinates.1, hscale]
      exact hzero.symm
    have heffectiveTwo (htwo : eSmall = eLarge + 2) :
        D.smallAlmostJordan.effectiveNormOrderAt (y.indexEquiv I).1
            (ordUnit K (D.smallAlmostJordan.scaleGenerator (y.indexEquiv I).1)) =
          D.largeAlmostJordan.effectiveNormOrderAt (x.indexEquiv I).1
              (ordUnit K (D.largeAlmostJordan.scaleGenerator (x.indexEquiv I).1)) + 2 := by
      rw [← hcoordinates.1, hscale]
      exact htwo
    rcases hcases with hzero | hone | htwo
    · obtain ⟨A, hALarge, hASmall⟩ :=
        Rlarge.exists_commonNormGenerator_of_effective_eq Rsmall hinclude
          (heffectiveEq hzero)
      let S := Rlarge.approximationSeedsWith dLarge A hALarge
      let T := Rsmall.approximationSeedsWith dSmall A hASmall
      have hoddSeed : ∃ s : Kˣ,
          T.normGenerator * T.leftDet =
            (S.normGenerator * S.leftDet) * s ^ 2 := by
        rcases hdet with ⟨s, hs⟩
        refine ⟨s, ?_⟩
        simp only [S, T,
          BONG.StrictCoordinateResolution.approximationSeedsWith_normGenerator,
          BONG.StrictCoordinateResolution.approximationSeedsWith_leftDet]
        rw [hs]
        ac_rfl
      apply S.commonApproximation_odd_of_squareEquivalentSeeds T hstart
        hoddSeed i.val k
      · calc
          i.val = C.start + j := hiStart
          _ = C.start + 1 + 2 * k := by omega
      · exact hiC
      · exact hiE
    · exact (hnotOne hone).elim
    · have hpos : 0 < finrank K V := by
        rw [← a.toBONG.length_eq_finrank]
        omega
      have hpair := Rlarge.normGenerator_pair_of_effective_add_two Rsmall
        hpos hrescale (heffectiveTwo htwo)
      let A := Rlarge.fundamentalNormGenerator
      let B := (uniformizerUnit K) ^ 2 * A
      let S := Rlarge.approximationSeedsWith dLarge A hpair.1
      let T := Rsmall.approximationSeedsWith dSmall B hpair.2
      have hoddSeed : ∃ s : Kˣ,
          T.normGenerator * T.leftDet =
            (S.normGenerator * S.leftDet) * s ^ 2 := by
        rcases hdet with ⟨s, hs⟩
        refine ⟨uniformizerUnit K * s, ?_⟩
        simp only [S, T,
          BONG.StrictCoordinateResolution.approximationSeedsWith_normGenerator,
          BONG.StrictCoordinateResolution.approximationSeedsWith_leftDet]
        rw [hs]
        dsimp only [B]
        rw [mul_pow]
        ac_rfl
      apply S.commonApproximation_odd_of_squareEquivalentSeeds T hstart
        hoddSeed i.val k
      · calc
          i.val = C.start + j := hiStart
          _ = C.start + 1 + 2 * k := by omega
      · exact hiC
      · exact hiE

end Lattice.Beli2019Lemma51Data

end Bong
