/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma92
import Bong.Bong.Beli2019Lemma93TailEquality

/-!
# Beli (2019), Lemma 9.3: high-index branch

Lemma 9.2 aligns every sufficiently late alpha with the projected-tail alpha.
The exact candidate transport from `Beli2019Lemma93TailEquality` then aligns
the comparison invariant `A` automatically beyond the endpoint-sensitive
initial indices of Lemma 9.3.
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {N : Nat}

/-- Alpha invariance converts Lemma 9.2's equality, whose left side is
stated for the original BONG, into a self-tail equality for the transformed
BONG. -/
theorem Beli2019Lemma92Transform.transformed_laterAlpha_eq_tail
    [GoodBONGClassificationLaws.{u, v, v} K]
    {a : GoodBONG q L (N + 4)} (T : Beli2019Lemma92Transform a)
    (i : Fin (N + 2)) (hi : 2 ≤ i.1) :
    T.transformed.alphaValue i.succ =
      T.transformed.tail.alphaValue i :=
  (a.alpha_invariant T.transformed i.succ).symm.trans
    (T.laterAlpha_eq_tail i hi)

/-- Once both BONGs have been put into Lemma 9.2 normal form and their heads
agree, the selected `A=A*` equality in Lemma 9.3 is automatic at every tail
boundary with value greater than four. -/
theorem representationAlpha_tail_eq_shift_of_lemma92Transforms
    [classificationV : GoodBONGClassificationLaws.{u, v, v} K]
    [classificationW : GoodBONGClassificationLaws.{u, w, w} K]
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M (N + 4))
    (Ta : Beli2019Lemma92Transform a)
    (Tb : Beli2019Lemma92Transform b)
    (hhead : Ta.transformed.value 0 = Tb.transformed.value 0)
    (i : RepresentationIndex (N + 3) (N + 3)) (hi : 4 < i.val) :
    Ta.transformed.tail.representationAlpha Tb.transformed.tail i =
      Ta.transformed.representationAlpha Tb.transformed i.tailShift := by
  have halphaA : ∀ k : Fin (N + 2), 2 ≤ k.1 →
      Ta.transformed.alphaValue k.succ =
        Ta.transformed.tail.alphaValue k := by
    letI : GoodBONGClassificationLaws.{u, v, v} K := classificationV
    intro k hk
    exact Ta.transformed_laterAlpha_eq_tail k hk
  have halphaB : ∀ k : Fin (N + 2), 2 ≤ k.1 →
      Tb.transformed.alphaValue k.succ =
        Tb.transformed.tail.alphaValue k := by
    letI : GoodBONGClassificationLaws.{u, w, w} K := classificationW
    intro k hk
    exact Tb.transformed_laterAlpha_eq_tail k hk
  exact Ta.transformed.representationAlpha_tail_eq_shift_of_laterAlphaValue_eq
    Tb.transformed hhead halphaA halphaB i hi

end BONG.GoodBONG

end Bong
