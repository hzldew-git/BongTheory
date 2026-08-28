/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009JordanIdeals

/-!
# M111 Beli 2009/2010, Lemmas 2.10--2.12 smoke tests
-/

namespace BongTest.M111

open Bong Bong.Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {t : Nat}

variable [Beli2009WeightIdealData.{u, v} K]

example (a : Kˣ) (ha : Lattice.IsNormGeneratorValue q L a)
    (w : Lattice.OrderedFractionalIdeal K)
    (hw : Lattice.twoScaleIdeal q L ≤ w.carrier) :
    w.carrier = Lattice.weightIdeal q L ↔
      Lattice.SatisfiesWeightIdealConditions q L a w :=
  Lattice.beli2009Lemma210 a ha w hw

variable [Beli2009OrthogonalIdealLaws.{u, v} K]

example (D : Lattice.OrthogonalDecomposition q L t)
    (a : Kˣ) (ha : Lattice.IsNormGeneratorValue q L a)
    (ak : Fin t → Kˣ)
    (hak : ∀ i, Lattice.IsNormGeneratorValue
      (D.component i).space (D.component i).lattice (ak i)) :
    Lattice.normGroupSet q L = D.normGroupExpression ∧
      Lattice.weightIdeal q L = D.weightIdealExpression a ak :=
  D.beli2009Lemma211 a ha ak hak

variable [Beli2009FundamentalIdealLaws.{u} K]

example (B : Lattice.StableJordanBoundaryData K)
    (heven : Even (B.leftNormOrder + B.rightNormOrder)) :
    B.fundamentalIdeal.carrier = B.fundamentalIdealExpression :=
  B.beli2009Lemma212 heven

#print axioms Bong.Lattice.beli2009Lemma210
#print axioms Bong.Lattice.OrthogonalDecomposition.beli2009Lemma211
#print axioms Bong.Lattice.StableJordanBoundaryData.beli2009Lemma212

end BongTest.M111
