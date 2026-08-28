/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.GoodBONGScalarAgreement
import Bong.Bong.Basis

/-!
# Deep integral extensions of good BONGs

This file isolates the geometric local input used in Beli (2019), Lemmas
2.20--2.21.  An integral isometric embedding of a lower-rank lattice can be
completed inside the target by a sufficiently deep orthogonal complement.
The interface records the geometric prefix and the two numerical boundary
bounds supplied by scaling the complement.  It does not mention any of the
four representation conditions from Theorem 2.1.
-/

namespace Bong

open Dyadic

universe u v w

/-- A full-rank lattice obtained by adjoining a sufficiently deep complement
to an integral isometric embedding. -/
structure GoodBONGDeepIntegralExtensionData
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type w} [AddCommGroup W] [Module K W]
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W} {m n : Nat}
    (a : BONG.GoodBONG q L (m + 1))
    (b : BONG.GoodBONG r M (n + 1)) (hRank : n < m)
    (f : Lattice.Representation r q M L)
    (orderBound : Int) (alphaBound : ℚ) where
  completedLattice : Lattice K V
  completedBONG : BONG.GoodBONG q completedLattice (m + 1)
  completed_le : completedLattice ≤ L
  prefixAmbient_eq (i : Fin (n + 1)) :
    completedBONG.toBONG.ambientVector ⟨i.val, by omega⟩ =
      f.toLinearMap (b.toBONG.ambientVector i)
  prefixAlphaCap_eq (i : Nat) (hi : i ≤ n) :
    completedBONG.prefixAlphaCap i = b.prefixAlphaCap i
  /-- Every newly adjoined BONG entry can be made uniformly deep.  This is
  the quantitative form of scaling the whole orthogonal complement by a
  sufficiently large power of the maximal ideal. -/
  tailOrder (i : Fin (m + 1)) (hi : n + 1 ≤ i.val) :
    orderBound ≤ completedBONG.order i
  boundaryOrder :
    orderBound ≤ completedBONG.order ⟨n + 1, by omega⟩
  boundaryAlpha :
    alphaBound < completedBONG.alphaValue ⟨n, hRank⟩

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

/-- The geometric prefix supplied by a deep extension has the same scalar
values and the same internal alpha caps as the original good BONG. -/
theorem prefixAgreement
    (D : GoodBONGDeepIntegralExtensionData
      a b hRank f orderBound alphaBound) :
    BONG.GoodBONG.PrefixAgreement D.completedBONG b hRank.le := by
  refine ⟨?_, D.prefixAlphaCap_eq⟩
  intro i
  apply Units.ext
  simp only [BONG.GoodBONG.coe_valueUnit]
  change D.completedBONG.value ⟨i.val, by omega⟩ = b.value i
  unfold BONG.GoodBONG.value
  rw [← D.completedBONG.toBONG.quadratic_ambientVector,
    D.prefixAmbient_eq, f.map_quadratic,
    b.toBONG.quadratic_ambientVector]

end GoodBONGDeepIntegralExtensionData

/-- The standard local construction that completes a strict lower-rank
integral embedding by an arbitrarily deep orthogonal complement. -/
class GoodBONGDeepIntegralExtensionLaws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  extension
    {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type w} [AddCommGroup W] [Module K W]
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W} {m n : Nat}
    (a : BONG.GoodBONG q L (m + 1))
    (b : BONG.GoodBONG r M (n + 1)) (hRank : n < m)
    (f : Lattice.Representation r q M L)
    (orderBound : Int) (alphaBound : ℚ) :
    Nonempty (GoodBONGDeepIntegralExtensionData
      a b hRank f orderBound alphaBound)

end Bong
