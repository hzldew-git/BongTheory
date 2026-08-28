/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.JordanOrderProfileSequence
import Bong.Lattice.OmearaJordan

/-!
# Reducing Beli (2003), Lemma 4.7 to its profile assertion

The equality of the order sequences of two good BONGs is not an independent
local input.  Once both BONGs have the Jordan profile asserted in Lemma 4.7,
the canonical lexicographic indexing of that profile identifies their orders
coordinate by coordinate.  O'Meara's Jordan theorem supplies the common
Jordan decomposition used in the comparison.
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The full law package of Lemma 4.7 follows from its Jordan-profile field.
In particular, `goodBONG_orders_eq` must not be counted as a second
mathematical assumption. -/
@[reducible] noncomputable def beliLemma47LawsOfProfile
    (profile :
      ∀ {V : Type v} [AddCommGroup V] [Module K V]
        {q : QuadraticSpace K V} {L : Lattice K V} {n t : Nat}
        (b : BONG V q L n) (hgood : b.IsGood)
        (J : Lattice.JordanDecomposition q L t),
          Nonempty (BONG.JordanOrderProfileWitness b J)) :
    BeliLemma47Laws.{u, v} K where
  jordanOrderProfile := profile
  goodBONG_orders_eq := by
    intro V _ _ q L n b c hb hc i
    let chosen := Lattice.omearaJordanDecomposition q L
    let J := chosen.2
    let wb : BONG.JordanOrderProfileWitness b J :=
      Classical.choice (profile b hb J)
    let wc : BONG.JordanOrderProfileWitness c J :=
      Classical.choice (profile c hc J)
    exact wb.orders_eq_of_profiles wc i

end Bong
