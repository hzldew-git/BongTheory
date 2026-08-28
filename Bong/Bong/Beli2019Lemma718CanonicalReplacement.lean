/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma718HyperbolicBlock
import Bong.Bong.Beli2019VolumeOrders

/-!
# Beli (2019), Lemma 7.18: replacing an arbitrary canonical pair

The preceding hyperbolic-block construction uses standard coordinates.  This
file removes that coordinate choice.  Every binary good BONG with canonical
values `π^R, -π^(R-2e)` receives a literal index-`𝔭` sublattice in its own
ambient space, together with a good BONG having the two replacement values
from Lemma 7.18.
-/

namespace Bong

open Dyadic

namespace BONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M : Lattice K V}

private theorem ordUnit_neg_local (a : Kˣ) :
    ordUnit K (-a) = ordUnit K a := by
  apply WithTop.coe_injective
  rw [coe_ordUnit, coe_ordUnit]
  change ord K (-(a : K)) = ord K (a : K)
  exact ord_neg K (a : K)

/-- A canonical hyperbolic pair has the negative-quarter binary square
class. -/
theorem lemma718CanonicalPair_binaryUnitSquareClass
    (c : GoodBONG q M 2) (R : Int)
    (hzero : c.valueUnit 0 =
      GoodBONG.lemma718CanonicalHigh (K := K) R)
    (hone : c.valueUnit 1 =
      GoodBONG.lemma718CanonicalLow (K := K) R) :
    c.toBONG.binaryUnitSquareClass =
      unitSquareClass K (negativeQuarterUnit K) := by
  change unitSquareClass K (c.valueUnit 1 / c.valueUnit 0) = _
  rw [hzero, hone]
  have hratio :
      GoodBONG.lemma718CanonicalLow (K := K) R /
          GoodBONG.lemma718CanonicalHigh (K := K) R =
        lemma718IndexPLow (K := K) (R - 1) /
          lemma718IndexPHigh (K := K) (R - 1) := by
    unfold lemma718IndexPLow lemma718IndexPHigh
      GoodBONG.lemma718CanonicalLow GoodBONG.lemma718CanonicalHigh
    congr 3 <;> omega
  rw [hratio, lemma718IndexPParameter_eq]
  apply unitSquareClass_uniformizerPower_mul_eq_negativeQuarter
  · change ord K ((-1 : Kˣ) : K) = 0
    simp
  · rfl
  · exact ⟨1, by simp⟩

/-- A canonical binary good BONG is the standard lattice in the hyperbolic
plane of scale `π^(R-e)`. -/
theorem lemma718CanonicalPair_isIsometric_hyperbolic
    (c : GoodBONG q M 2) (R : Int)
    (hzero : c.valueUnit 0 =
      GoodBONG.lemma718CanonicalHigh (K := K) R)
    (hone : c.valueUnit 1 =
      GoodBONG.lemma718CanonicalLow (K := K) R) :
    Lattice.IsIsometric q
      (QuadraticSpace.hyperbolicPlane
        (uniformizerPowerUnit K (R - ramificationIndex K)))
      M (Lattice.hyperbolicPlaneLattice (K := K)) := by
  have hclass := lemma718CanonicalPair_binaryUnitSquareClass
    c R hzero hone
  have h := c.toBONG.isIsometric_hyperbolicPlane_of_binaryUnitSquareClass_eq_negativeQuarter
    hclass
  have hOrderDef :
      c.toBONG.order (0 : Fin 2) = c.order (0 : Fin 2) := rfl
  rw [hOrderDef] at h
  have horder : c.order (0 : Fin 2) = R := by
    change ordUnit K (c.valueUnit (0 : Fin 2)) = R
    rw [hzero]
    change ordUnit K (uniformizerPowerUnit K R) = R
    exact ordUnit_uniformizerPowerUnit (K := K) R
  rw [horder] at h
  exact h

/-- Coordinate-free output of replacing one canonical hyperbolic pair by
its index-`𝔭` sublattice. -/
structure Lemma718CanonicalPairReplacement
    (c : GoodBONG q M 2) (R : Int) where
  /-- The replacement lattice inside the original binary space. -/
  target : Lattice K V
  /-- The target is literally an index-`𝔭` sublattice of the source. -/
  inclusion : Beli2019IndexPInclusion q M target
  /-- The good BONG carried by the replacement lattice. -/
  bong : GoodBONG q target 2
  /-- Its exact two coefficient values. -/
  valueUnit (i : Fin 2) : bong.valueUnit i =
    ![lemma718IndexPHigh (K := K) R,
      lemma718IndexPLow (K := K) R] i

/-- Construct the coordinate-free index-`𝔭` replacement of a canonical
binary pair. -/
noncomputable def lemma718CanonicalPairReplacement
    (c : GoodBONG q M 2) (R : Int)
    (hzero : c.valueUnit 0 =
      GoodBONG.lemma718CanonicalHigh (K := K) R)
    (hone : c.valueUnit 1 =
      GoodBONG.lemma718CanonicalLow (K := K) R) :
    Lemma718CanonicalPairReplacement c R := by
  let f := Classical.choice
    (lemma718CanonicalPair_isIsometric_hyperbolic c R hzero hone)
  let N := Lattice.map f.symm.toLinearEquiv
    (Lattice.hyperbolicIndexPLattice (K := K))
  let g : Lattice.Isometry
      (QuadraticSpace.hyperbolicPlane
        (uniformizerPowerUnit K (R - ramificationIndex K))) q
      (Lattice.hyperbolicIndexPLattice (K := K)) N := by
    simpa only [N, Lattice.Isometry.toQuadraticSpaceIsometry] using
      Lattice.Isometry.toMap
        (QuadraticSpace.hyperbolicPlane
          (uniformizerPowerUnit K (R - ramificationIndex K)))
        f.symm.toQuadraticSpaceIsometry
        (Lattice.hyperbolicIndexPLattice (K := K))
  let b := (lemma718IndexPHyperbolicGoodBONG (K := K) R).mapLatticeIsometry g
  have hbValue (i : Fin 2) :
      b.valueUnit i =
        ![lemma718IndexPHigh (K := K) R,
          lemma718IndexPLow (K := K) R] i := by
    simpa only [b, GoodBONG.valueUnit_mapLatticeIsometry] using
      lemma718IndexPHyperbolicGoodBONG_valueUnit (K := K) R i
  have hle : N ≤ M := by
    intro x hx
    change x ∈ Lattice.map f.symm.toLinearEquiv
      (Lattice.hyperbolicIndexPLattice (K := K)) at hx
    rw [Lattice.mem_map_iff] at hx
    have hxIndex : f.toLinearEquiv x ∈
        Lattice.hyperbolicIndexPLattice (K := K) := by
      exact hx
    exact (f.map_mem x).mpr
      ((Lattice.hyperbolicIndexPInclusion
        (uniformizerPowerUnit K
          (R - ramificationIndex K))).lattice_le hxIndex)
  have hsourceZero : c.order 0 = R := by
    change ordUnit K (c.valueUnit 0) = R
    rw [hzero]
    exact ordUnit_uniformizerPowerUnit (K := K) R
  have hsourceOne :
      c.order 1 = R - 2 * (ramificationIndex K : Int) := by
    change ordUnit K (c.valueUnit 1) = _
    rw [hone]
    unfold GoodBONG.lemma718CanonicalLow
    rw [ordUnit_neg_local, ordUnit_uniformizerPowerUnit]
  have htargetZero : b.order 0 = R + 1 := by
    change ordUnit K (b.valueUnit 0) = _
    rw [hbValue]
    simp only [Matrix.cons_val_zero]
    unfold lemma718IndexPHigh
    rw [ordUnit_uniformizerPowerUnit]
  have htargetOne :
      b.order 1 = R - 2 * (ramificationIndex K : Int) + 1 := by
    change ordUnit K (b.valueUnit 1) = _
    rw [hbValue]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    unfold lemma718IndexPLow
    rw [ordUnit_neg_local, ordUnit_uniformizerPowerUnit]
  have hvolume : Lattice.volumeOrder q N =
      Lattice.volumeOrder q M + 2 := by
    rw [b.toBONG.volumeOrder_eq_sum_order,
      c.toBONG.volumeOrder_eq_sum_order,
      Fin.sum_univ_two, Fin.sum_univ_two]
    change b.order 0 + b.order 1 = c.order 0 + c.order 1 + 2
    rw [htargetZero, htargetOne, hsourceZero, hsourceOne]
    ring
  exact {
    target := N
    inclusion := ⟨hle, hvolume⟩
    bong := b
    valueUnit := hbValue }

end BONG

end Bong
