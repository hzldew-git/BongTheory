/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma718CanonicalReplacement
import Bong.Bong.Beli2019Lemma710BONGProduct
import Bong.Bong.TwoBlockProductIsometry

/-!
# Beli (2019), Lemma 7.18: gluing replacement blocks

This file carries out the lattice-theoretic gluing step used in Lemma 7.18.
Given a genuine two-block orthogonal split of the source lattice, replacement
sublattices in both factors are assembled as an orthogonal product and mapped
back to the original ambient quadratic space.  The result is a literal
sublattice of the source, not merely an abstract isometry class.
-/

namespace Bong

open Dyadic

namespace BONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {m : Nat}

/-- The result of replacing both factors of a genuine two-block split and
mapping the assembled good BONG back to the original ambient space. -/
structure Lemma718SplitReplacement
    (a : GoodBONG q L ((m + 1) + 2))
    (S : TwoBlockSplitWitness a.toBONG 2 (by omega))
    (J : Lattice K S.left.carrier)
    (j : GoodBONG (q.restrict S.left.carrier S.left.nondegenerate) J 2)
    (T : Lattice K S.right.carrier)
    (t : GoodBONG (q.restrict S.right.carrier S.right.nondegenerate) T (m + 1)) where
  /-- The assembled replacement lattice in the original ambient space. -/
  target : Lattice K V
  /-- Both factorwise inclusions glue to an inclusion in the source lattice. -/
  lattice_le : target ≤ L
  /-- The left-first concatenation, transported back to the ambient space. -/
  bong : GoodBONG q target ((m + 1) + 2)
  /-- The first two values are exactly the values of the left replacement. -/
  valueUnit_left (i : Fin 2) :
    bong.valueUnit (orthogonalProductLeftIndex (m + 1) i) = j.valueUnit i
  /-- All remaining values are exactly the values of the right replacement. -/
  valueUnit_right (i : Fin (m + 1)) :
    bong.valueUnit (orthogonalProductRightIndex 2 i) = t.valueUnit i

/-- Assemble two replacement sublattices along a two-block split and map the
result back to the original quadratic lattice. -/
noncomputable def lemma718SplitReplacement
    (a : GoodBONG q L ((m + 1) + 2))
    (S : TwoBlockSplitWitness a.toBONG 2 (by omega))
    (J : Lattice K S.left.carrier)
    (j : GoodBONG (q.restrict S.left.carrier S.left.nondegenerate) J 2)
    (T : Lattice K S.right.carrier)
    (t : GoodBONG (q.restrict S.right.carrier S.right.nondegenerate) T (m + 1))
    (hJ : J ≤ S.left.lattice) (hT : T ≤ S.right.lattice)
    (horder : ∀ i : Fin 2, j.order i ≤ t.order 0)
    (hlastSecond : ∀ (_ : 0 < 2) (hright : 1 < m + 1),
      j.order ⟨1, by omega⟩ ≤ t.order ⟨1, hright⟩) :
    Lemma718SplitReplacement a S J j T t := by
  let raw := j.orthogonalProductRight_of_orderBounds t horder hlastSecond
  let N := Lattice.map S.toProductLatticeIsometry.toLinearEquiv
    (Lattice.product J T)
  let g : Lattice.Isometry
      ((q.restrict S.left.carrier S.left.nondegenerate).orthogonalSum
        (q.restrict S.right.carrier S.right.nondegenerate)) q
      (Lattice.product J T) N := by
    simpa only [N, Lattice.Isometry.toQuadraticSpaceIsometry] using
      Lattice.Isometry.toMap _
        S.toProductLatticeIsometry.toQuadraticSpaceIsometry _
  let b := raw.mapLatticeIsometry g
  have hle : N ≤ L := by
    intro y hy
    have hzTarget := (Lattice.mem_map_iff
      S.toProductLatticeIsometry.toLinearEquiv
      (Lattice.product J T) y).1 hy
    have hzProduct :
        S.toProductLatticeIsometry.toLinearEquiv.symm y ∈
          Lattice.product S.left.lattice S.right.lattice :=
      Lattice.mem_product_iff.mpr
        ⟨hJ (Lattice.mem_product_iff.mp hzTarget).1,
          hT (Lattice.mem_product_iff.mp hzTarget).2⟩
    have hmapped := (S.toProductLatticeIsometry.map_mem _).1 hzProduct
    simpa using hmapped
  exact {
    target := N
    lattice_le := hle
    bong := b
    valueUnit_left := by
      intro i
      simpa only [b, GoodBONG.valueUnit_mapLatticeIsometry, raw] using
        GoodBONG.valueUnit_orthogonalProductRight_of_orderBounds_left
          j t horder hlastSecond i
    valueUnit_right := by
      intro i
      simpa only [b, GoodBONG.valueUnit_mapLatticeIsometry, raw] using
        GoodBONG.valueUnit_orthogonalProductRight_of_orderBounds_right
          j t horder hlastSecond i }

end BONG

end Bong
