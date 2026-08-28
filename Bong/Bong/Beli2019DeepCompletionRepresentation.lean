/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.GoodBONGDeepIntegralExtension
import Bong.Bong.ValueIsometry

/-!
# The original lattice inside a deep completion

The initial BONG block of a deep integral completion is isometric to the
original lower-rank lattice.  Its canonical prefix lattice is contained in
the completed lattice, so the completed lattice represents the original one.
-/

namespace Bong

open Dyadic

universe u v w

namespace GoodBONGDeepIntegralExtensionData

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {m n : Nat}
  {a : BONG.GoodBONG q L (m + 1)}
  {b : BONG.GoodBONG r M (n + 1)} {hRank : n < m}
  {f : Lattice.Representation r q M L}
  {orderBound : Int} {alphaBound : ℚ}

/-- A deep completion represents the lower-rank lattice whose BONG forms its
initial block. -/
theorem completed_represents_original
    (D : GoodBONGDeepIntegralExtensionData
      a b hRank f orderBound alphaBound) :
    Lattice.Represents q r D.completedLattice M := by
  let P := D.completedBONG.toBONG.prefixWitness (n + 1) (by omega)
  let pGood := P.toGoodBONG D.completedBONG.good
  have hvalues : ∀ i : Fin (n + 1),
      b.toBONG.value i = pGood.toBONG.value i := by
    intro i
    have hsegment :
        P.bong.value i = D.completedBONG.toBONG.value
          ⟨i.val, by omega⟩ := by
      rw [P.value_eq]
      congr 1
      apply Fin.ext
      simp only [BONG.SegmentWitness.sourceIndex_val, zero_add]
    have hagree := D.prefixAgreement.value_eq i
    calc
      b.toBONG.value i =
          D.completedBONG.toBONG.value ⟨i.val, by omega⟩ := hagree.symm
      _ = pGood.toBONG.value i := by
        change _ = P.bong.value i
        exact hsegment.symm
  let prefixIsometry :=
    b.toBONG.latticeIsometryOfValueEq pGood.toBONG hvalues
  let inclusion : Lattice.Representation
      (q.restrict P.carrier P.nondegenerate) q
      P.lattice D.completedLattice :=
    { toLinearMap := P.carrier.subtype
      injective := Subtype.val_injective
      map_bilin := by
        intro x y
        rfl
      map_mem := by
        intro x hx
        exact P.contained x hx }
  exact ⟨inclusion.trans prefixIsometry.toRepresentation⟩

end GoodBONGDeepIntegralExtensionData

end Bong
