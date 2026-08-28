/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009RepresentationBridge
import Bong.Bong.Beli2009AmbientDeterminantProof
import Bong.Bong.Beli2006AlphaP2P3Proof
import Bong.Bong.DiscriminantClassProof
import Bong.Lattice.Omeara9328UniverseBridge

namespace Bong

/-!
# Beli (2009/2010), Theorem 3.1

This module combines the concrete versions of Lemmas 3.3 and 3.9 with the
proved arbitrary-universe form of O'Meara 93:28.  It proves Beli's good-BONG
classification theorem in every positive rank and discharges the former
`GoodBONGClassificationLaws` boundary without additional mathematical laws.
-/

open Dyadic

universe u v w

namespace Lattice.JordanDecomposition

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {t : Nat}

/-- O'Meara 93:28 for an arbitrary positive number of Jordan components.
The one-component case is 93:16; every larger case is the proved 93:28
induction. -/
theorem isIsometric_iff_omeara9328Conditions_succ
    (J : JordanDecomposition q L (t + 1))
    (H : JordanDecomposition r M (t + 1))
    (ambient : q.IsIsometric r) (F : SameFundamentalType J H) :
    Lattice.IsIsometric q r L M ↔ J.Omeara9328Conditions H := by
  cases t with
  | zero =>
      exact omeara9328_singleComponent_iff J H ambient F
  | succ d =>
      exact isIsometric_iff_omeara9328Conditions_universe J H ambient F

end Lattice.JordanDecomposition

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}

/-- Beli's classification criterion in rank one.  All alpha, defect, and
internal-representation clauses are empty; equality of the sole BONG order
makes the image unary lattice equal to the target unary lattice. -/
theorem beli2009Theorem31_rankOne
    (ambient : q.IsIsometric r)
    (a : GoodBONG q L 1) (b : GoodBONG r M 1) :
    Lattice.IsIsometric q r L M ↔ ClassificationConditions a b := by
  constructor
  · rintro ⟨f⟩
    exact
      { sameOrders := a.sameOrders_of_latticeIsometry b f
        sameAlphas := fun i ↦ Fin.elim0 i
        prefixDefectBounds := fun i ↦ Fin.elim0 i
        internalRepresentations := fun i ↦ Fin.elim0 i }
  · intro conditions
    let f : QuadraticSpace.Isometry q r := Classical.choice ambient
    let mapped : GoodBONG r (Lattice.map f.toLinearEquiv L) 1 := a.map f
    have horder : mapped.order 0 = b.order 0 := by
      rw [GoodBONG.order_map]
      exact conditions.sameOrders 0
    have hlattice : Lattice.map f.toLinearEquiv L = M :=
      mapped.toBONG.lattice_eq_of_order_eq b.toBONG horder
    let lift : Lattice.Isometry q r L (Lattice.map f.toLinearEquiv L) :=
      Lattice.Isometry.toMap q f L
    rw [hlattice] at lift
    exact ⟨lift⟩

/-- Beli (2009/2010), Theorem 3.1 in rank at least two, obtained directly
from the concrete Lemmas 3.3 and 3.9 and the proved O'Meara 93:28 theorem. -/
theorem beli2009Theorem31_rankAtLeastTwo
    (ambient : q.IsIsometric r)
    (a : GoodBONG q L (n + 2)) (b : GoodBONG r M (n + 2)) :
    Lattice.IsIsometric q r L M ↔ ClassificationConditions a b := by
  constructor
  · rintro ⟨f⟩
    have horders : a.SameOrders b := a.sameOrders_of_latticeIsometry b f
    obtain ⟨S⟩ := a.nonempty_strictJordanAdaptedAlignment b horders
    let t := S.componentCount - 1
    have hcount : S.componentCount = t + 1 := by
      dsimp only [t]
      have hpositive := S.componentCount_pos
      omega
    let Fraw := Lattice.JordanDecomposition.sameFundamentalTypeOfIsometry
      S.sourceJordan S.targetJordan f
    let F := S.sameFundamentalTypeSucc Fraw hcount
    have homeara : (S.sourceJordanSucc hcount).Omeara9328Conditions
        (S.targetJordanSucc hcount) :=
      (Lattice.JordanDecomposition.isIsometric_iff_omeara9328Conditions_succ
        (S.sourceJordanSucc hcount) (S.targetJordanSucc hcount)
          ambient F).1 ⟨f⟩
    have hfirst := (S.beli2009Lemma33 hcount ambient horders).1
      ⟨⟨Fraw⟩, homeara.1⟩
    have hinternal := (S.beli2009Lemma39_concrete hcount ambient F
      horders homeara.1).2 ⟨homeara.2.1, homeara.2.2⟩
    exact
      { sameOrders := horders
        sameAlphas := hfirst.1
        prefixDefectBounds := hfirst.2
        internalRepresentations := hinternal }
  · intro conditions
    have horders := conditions.sameOrders
    obtain ⟨S⟩ := a.nonempty_strictJordanAdaptedAlignment b horders
    let t := S.componentCount - 1
    have hcount : S.componentCount = t + 1 := by
      dsimp only [t]
      have hpositive := S.componentCount_pos
      omega
    obtain ⟨⟨Fraw⟩, hI⟩ := (S.beli2009Lemma33 hcount ambient horders).2
      ⟨conditions.sameAlphas, conditions.prefixDefectBounds⟩
    let F := S.sameFundamentalTypeSucc Fraw hcount
    have hIIIII := (S.beli2009Lemma39_concrete hcount ambient F
      horders hI).1 conditions.internalRepresentations
    exact (Lattice.JordanDecomposition.isIsometric_iff_omeara9328Conditions_succ
      (S.sourceJordanSucc hcount) (S.targetJordanSucc hcount)
        ambient F).2 ⟨hI, hIIIII.1, hIIIII.2⟩

/-- Beli (2009/2010), Theorem 3.1 for every positive lattice rank. -/
theorem beli2009Theorem31_concrete
    (ambient : q.IsIsometric r)
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1)) :
    Lattice.IsIsometric q r L M ↔ ClassificationConditions a b := by
  cases n with
  | zero => exact beli2009Theorem31_rankOne ambient a b
  | succ n => exact beli2009Theorem31_rankAtLeastTwo ambient a b

end BONG.GoodBONG

/-- The former `GoodBONGClassificationLaws` boundary, discharged by the
concrete proof of Beli (2009/2010), Theorem 3.1. -/
theorem goodBONGClassificationLawsProved
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] :
    GoodBONGClassificationLaws.{u, v, w} K where
  classify := BONG.GoodBONG.beli2009Theorem31_concrete

end Bong
