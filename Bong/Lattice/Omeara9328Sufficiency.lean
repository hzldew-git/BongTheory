/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9328GeneralReduction

/-!
# O'Meara 93:28: unconditional sufficiency

This file exposes the completed scale-spread construction in the semantic
form of Theorem 93:28.  The choice-free theorem specializes the coherent
generator family to the canonical fundamental norm generators.
-/

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [DyadicDiscriminantClassLaws K]
  {V : Type u} [AddCommGroup V] [Module K V]
  {W : Type u} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}

/-- The sufficiency direction of O'Meara 93:28, with the paper's canonical
fundamental norm generators and no classification-law parameter. -/
noncomputable def omeara9328Sufficiency
    (J : JordanDecomposition q L (n + 2))
    (H : JordanDecomposition r M (n + 2))
    (ambient : q.IsIsometric r)
    (F : SameFundamentalType J H)
    (conditions : J.Omeara9328Conditions H) :
    Isometry q r L M :=
  omeara9328SufficiencyWith J H ambient F
    (canonicalFundamentalNormGeneratorChoice J) conditions

/-- Proposition-valued public form of the sufficient direction. -/
theorem isIsometric_of_omeara9328Conditions
    (J : JordanDecomposition q L (n + 2))
    (H : JordanDecomposition r M (n + 2))
    (ambient : q.IsIsometric r)
    (F : SameFundamentalType J H)
    (conditions : J.Omeara9328Conditions H) :
    Lattice.IsIsometric q r L M :=
  ⟨omeara9328Sufficiency J H ambient F conditions⟩

end Lattice.JordanDecomposition

end Bong
