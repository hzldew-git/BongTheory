/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019ApproximationInvariants

/-!
# M129 Beli 2019, approximation formulas for Definition 4 smoke tests
-/

namespace BongTest.M129

open Bong

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {m n : Nat}

example (a : BONG.GoodBONG q L (m + 1))
    (b : BONG.GoodBONG r M (n + 1))
    (i : RepresentationIndex (m + 1) (n + 1)) (X Y : Nat → Kˣ)
    (hX : ∀ j, a.IsPrefixApproximation j (X j))
    (hY : ∀ j, b.IsPrefixApproximation j (Y j)) :
    a.representationApproximationAlpha b i X Y =
      a.representationAlpha b i :=
  a.representationApproximationAlpha_eq b i X Y hX hY

example (a : BONG.GoodBONG q L (m + 1))
    (b : BONG.GoodBONG r M (n + 1))
    (hgap : n + 2 < m + 1) (X Y : Nat → Kˣ)
    (hX : ∀ j, a.IsPrefixApproximation j (X j))
    (hY : ∀ j, b.IsPrefixApproximation j (Y j)) :
    a.terminalApproximationAlpha b hgap X Y =
      a.terminalAdjustedAlpha b hgap :=
  a.terminalApproximationAlpha_eq b hgap X Y hX hY

example (a : BONG.GoodBONG q L (m + 1))
    (b : BONG.GoodBONG r M (n + 1)) (X Y : Nat → Kˣ)
    (hX : ∀ j, a.IsPrefixApproximation j (X j))
    (hY : ∀ j, b.IsPrefixApproximation j (Y j)) :
    a.RepresentationDefectCondition b ↔
      a.ApproximationDefectCondition b X Y :=
  a.representationDefectCondition_iff_approximation b X Y hX hY

#print axioms Bong.BONG.GoodBONG.representationApproximationPrimary_eq
#print axioms Bong.BONG.GoodBONG.representationApproximationSecondary_eq
#print axioms Bong.BONG.GoodBONG.representationApproximationAlpha_eq
#print axioms Bong.BONG.GoodBONG.terminalApproximationAlpha_eq
#print axioms Bong.BONG.GoodBONG.representationDefectCondition_iff_approximation

end BongTest.M129
