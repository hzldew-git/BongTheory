/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma96TailDefect

/-!
# Beli (2019), Lemma 9.6: assembled projected-tail conditions

This file combines the order, defect, one-step prefix, and two-step prefix
arguments into the exact lower-rank `RepresentationConditions` certificate
used by the final well-founded induction.

The three input profiles are transparent mathematical data:

* the displayed orders `R'_2`, `R'_3`, and `R'_i`;
* the prefix isometries produced by the unary--binary normal form;
* the pointwise `A_i` and capped-defect comparisons from lines 9629--9677.

No desired tail representation is stored in any of them.
-/

namespace Bong

open Dyadic

universe u v w x

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {U : Type x} [AddCommGroup U] [Module K U]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {s : QuadraticSpace K U}
  {L : Lattice K V} {M : Lattice K W} {P : Lattice K U}
  {N : Nat}

/-- The complete four-condition package for the exceptional projected pair
in Lemma 9.6. -/
theorem beli2019Lemma96_tailConditions
    [cLaws : Beli2006AlphaLaws.{u, x} K]
    [bLaws : Beli2006AlphaLaws.{u, w} K]
    (a : GoodBONG q L (N + 4))
    (b : GoodBONG r M (N + 4))
    (c : GoodBONG s P (N + 3))
    (Dorder : Beli2019Lemma96TailOrderProfile a c)
    (Dprefix : Beli2019Lemma96PrefixTransport a b c)
    (Dcomparison : Beli2019Lemma96TailComparisonProfile a b c)
    (conditions : RepresentationConditions a b (Nat.le_refl (N + 3)))
    (hfirstGap :
      a.order (1 : Fin (N + 4)) - a.order (0 : Fin (N + 4)) =
        2 * (ramificationIndex K : Int) - 2)
    (hsourceFirstOrder :
      b.order (0 : Fin (N + 4)) = a.order (0 : Fin (N + 4)))
    (hsourceFirstGap :
      2 * (ramificationIndex K : Int) ≤
        b.order (1 : Fin (N + 4)) - b.order (0 : Fin (N + 4))) :
    RepresentationConditions c b.tail (Nat.le_refl (N + 2)) where
  orderCondition := Dorder.representationOrderCondition b
    conditions.orderCondition hfirstGap hsourceFirstOrder hsourceFirstGap
  defectCondition := Dcomparison.representationDefectCondition
    (cLaws := cLaws) (bLaws := bLaws) conditions.defectCondition
  centralRepresentations := Dprefix.centralRepresentationConditions
    conditions.centralRepresentations Dcomparison.centralTrigger
  longRepresentations := Dprefix.longRepresentationConditions
    Dorder conditions.longRepresentations

end BONG.GoodBONG

end Bong
