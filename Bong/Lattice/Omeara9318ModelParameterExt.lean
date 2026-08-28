/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9318DeterminantOne

/-!
# Extensionality of the rank-four O'Meara model parameters

The two quaternary models in O'Meara 93:18 are determined by the three
displayed scalars `a`, `b`, and `alpha`.  All remaining fields of
`Omeara9318RankFourModelParameters` are proofs of the ordinary integrality
and ideal conditions.  This file records the resulting extensionality
principle, so independently constructed determinant-one models with the
same norm and weight generators are literally the same model.
-/

namespace Bong

open Dyadic

namespace Lattice

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [DyadicDiscriminantClassLaws K]

namespace Omeara9318RankFourModelParameters

/-- The scalar fields `a`, `b`, and `alpha` determine the complete model
parameter package; the other fields are propositions and hence proof
irrelevant. -/
@[ext]
theorem ext
    {P Q : Omeara9318RankFourModelParameters K}
    (ha : P.a = Q.a) (hb : P.b = Q.b)
    (halpha : P.alpha = Q.alpha) :
    P = Q := by
  cases P
  cases Q
  simp only at ha hb halpha
  subst ha
  subst hb
  subst halpha
  rfl

/-- Two determinant-one specializations with the same norm and weight
generators are equal. -/
theorem zeroDiscriminant_eq_of_a_eq_b_eq
    {P Q : Omeara9318RankFourModelParameters K}
    (ha : P.a = Q.a) (hb : P.b = Q.b) :
    P.zeroDiscriminant = Q.zeroDiscriminant := by
  apply ext
  · simpa using ha
  · simpa using hb
  · simp

/-- Equal scalar parameters give the canonical integral isometry between
the corresponding untwisted (`J`) models. -/
noncomputable def jDataIsometryOfScalarEq
    (P Q : Omeara9318RankFourModelParameters K)
    (ha : P.a = Q.a) (hb : P.b = Q.b)
    (halpha : P.alpha = Q.alpha) :
    Isometry P.jData.space Q.jData.space
      P.jData.lattice Q.jData.lattice := by
  have hPQ : P = Q := ext ha hb halpha
  subst Q
  exact Isometry.refl P.jData.space P.jData.lattice

/-- Determinant-one `J` models with equal norm and weight generators are
canonically integrally isometric. -/
noncomputable def zeroDiscriminantJDataIsometryOfABEq
    (P Q : Omeara9318RankFourModelParameters K)
    (ha : P.a = Q.a) (hb : P.b = Q.b) :
    Isometry P.zeroDiscriminant.jData.space
      Q.zeroDiscriminant.jData.space
      P.zeroDiscriminant.jData.lattice
      Q.zeroDiscriminant.jData.lattice := by
  exact jDataIsometryOfScalarEq P.zeroDiscriminant Q.zeroDiscriminant
    (by simpa using ha) (by simpa using hb) (by simp)

end Omeara9318RankFourModelParameters

end Lattice

end Bong
