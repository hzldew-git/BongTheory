/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma93TailAlpha

/-!
# Beli (2019), Lemma 9.2: formal statement

This file records the exact output of Lemma 9.2 independently of its two
low-rank constructions.  For a lattice of rank `N + 4`, a global alpha index
`i.succ` corresponds to the tail alpha index `i`.  Thus the paper's range
`4 <= i < n` is the zero-based condition `2 <= i.val` below.  The additional
equality at paper index `i = 3` is the pair of indices `2` and `1`.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {N : Nat}

/-- The three hypotheses under which Lemma 9.2 also supplies the equality at
paper index `i = 3`. -/
noncomputable def Lemma92EarlyAlternative (a : GoodBONG q L (N + 4)) : Prop :=
  a.order (0 : Fin (N + 4)) < a.order (2 : Fin (N + 4)) ∨
    a.order (1 : Fin (N + 4)) = a.order (3 : Fin (N + 4)) ∨
    a.orderGap (0 : Fin (N + 3)) =
      2 * (ramificationIndex K : Int)

/-- The transformed good BONG promised by Beli (2019), Lemma 9.2.

The field-value equality `a'_1 = a_1` is represented as equality of the
associated units.  `laterAlpha_eq_tail` is exactly the paper's equality for
`4 <= i < n`; `earlyAlpha_eq_tail` records its conditional extension to
`i = 3`. -/
structure Beli2019Lemma92Transform (a : GoodBONG q L (N + 4)) where
  transformed : GoodBONG q L (N + 4)
  firstValue_eq :
    transformed.valueUnit (0 : Fin (N + 4)) =
      a.valueUnit (0 : Fin (N + 4))
  laterAlpha_eq_tail (i : Fin (N + 2)) (hi : 2 ≤ i.1) :
    a.alphaValue i.succ = transformed.tail.alphaValue i
  earlyAlpha_eq_tail (hcase : a.Lemma92EarlyAlternative) :
    a.alphaValue (2 : Fin (N + 3)) =
      transformed.tail.alphaValue (1 : Fin (N + 2))

/-- A transformed BONG whose own shifted alphas agree with its tail gives the
paper's conclusion.  Alpha invariance on the fixed lattice converts those
self-equalities into equalities for the original BONG. -/
noncomputable def lemma92TransformOfSelfTailAgreement
    [GoodBONGClassificationLaws.{u, v, v} K]
    (a c : GoodBONG q L (N + 4))
    (hfirst : c.valueUnit (0 : Fin (N + 4)) =
      a.valueUnit (0 : Fin (N + 4)))
    (hlater : ∀ (i : Fin (N + 2)), 2 ≤ i.1 →
      c.alphaValue i.succ = c.tail.alphaValue i)
    (hearly : a.Lemma92EarlyAlternative →
      c.alphaValue (2 : Fin (N + 3)) =
        c.tail.alphaValue (1 : Fin (N + 2))) :
    Beli2019Lemma92Transform a where
  transformed := c
  firstValue_eq := hfirst
  laterAlpha_eq_tail i hi :=
    (a.alpha_invariant c i.succ).trans (hlater i hi)
  earlyAlpha_eq_tail hcase :=
    (a.alpha_invariant c (2 : Fin (N + 3))).trans (hearly hcase)

/-- Existential form of the preceding constructor, convenient for the two
branches of the proof of Lemma 9.2. -/
theorem exists_lemma92Transform_of_selfTailAgreement
    [GoodBONGClassificationLaws.{u, v, v} K]
    (a c : GoodBONG q L (N + 4))
    (hfirst : c.valueUnit (0 : Fin (N + 4)) =
      a.valueUnit (0 : Fin (N + 4)))
    (hlater : ∀ (i : Fin (N + 2)), 2 ≤ i.1 →
      c.alphaValue i.succ = c.tail.alphaValue i)
    (hearly : a.Lemma92EarlyAlternative →
      c.alphaValue (2 : Fin (N + 3)) =
        c.tail.alphaValue (1 : Fin (N + 2))) :
    Nonempty (Beli2019Lemma92Transform a) :=
  ⟨lemma92TransformOfSelfTailAgreement a c hfirst hlater hearly⟩

/-- In the branch where the original BONG already has all required tail
equalities, no coefficient change is needed. -/
theorem exists_lemma92Transform_identity
    [GoodBONGClassificationLaws.{u, v, v} K]
    (a : GoodBONG q L (N + 4))
    (hlater : ∀ (i : Fin (N + 2)), 2 ≤ i.1 →
      a.alphaValue i.succ = a.tail.alphaValue i)
    (hearly : a.Lemma92EarlyAlternative →
      a.alphaValue (2 : Fin (N + 3)) =
        a.tail.alphaValue (1 : Fin (N + 2))) :
    Nonempty (Beli2019Lemma92Transform a) :=
  exists_lemma92Transform_of_selfTailAgreement a a rfl hlater hearly

end BONG.GoodBONG

end Bong
