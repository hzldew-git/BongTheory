/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2022ClassicCorollary63

/-!
# The carrier-identification step in He Classic v6, Lemma 8.3

The corrected paper places this step in Lemma 8.3, not Lemma 8.1(iii).
The lemma below proves its algebraic content: once the lower universal lattice
and the upper good-BONG lattice both equal their displayed basis lattices, a
scalar-extension operation taking the first basis lattice to the second takes
the original lower lattice to the upper lattice.

The basis-transport hypothesis is explicit. This file does **not** construct
the scalar-extension functor or the ambient isometry for concrete number-field
completions; those remain separate prerequisites for the full Lemma 8.3.
-/

namespace Bong.HeClassic2024Carrier

open Dyadic Module

universe u v u' v'

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [QuadraticDefectLaws K] [HilbertSymbolLaws K]
  [DyadicDiscriminantClassLaws K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {E : Type u'} [Field E] [CharZero E] [ValuativeRel E]
  [TopologicalSpace E] [DyadicContext E]
  {W : Type v'} [AddCommGroup W] [Module E W]
  {q : QuadraticSpace K V} {L : Lattice K V}
  {r : QuadraticSpace E W} {M : Lattice E W}

/-- The exact carrier-equality deduction in the revised v6 Lemma 8.3.
`baseChange` is deliberately an explicit lattice map, and `hBasisTransport`
is the unproved concrete scalar-extension/ambient identification. -/
theorem he2022ClassicLemma83_carrier_eq_of_basisTransport
    {n : Nat}
    (lower : BONG.GoodBONG q L (n + 3))
    (upper : BONG.GoodBONG r M (n + 3))
    (hn : 2 ≤ n) (hnEven : Even n)
    (hClassic : Lattice.IsClassicIntegral q L)
    (hUniversal : Lattice.IsClassicNUniversal.{u, v, u} q L n)
    (baseChange : Lattice K V → Lattice E W)
    (hBasisTransport :
      baseChange (Lattice.basisLattice lower.toBONG.basis) =
        Lattice.basisLattice upper.toBONG.basis)
    (hUpperMonotone : Monotone (fun i : Fin (n + 3) => upper.order i)) :
    baseChange L = M := by
  have hLower : L = Lattice.basisLattice lower.toBONG.basis :=
    lower.he2022ClassicCorollary63_even hn hnEven hClassic hUniversal
  have hUpper : M = Lattice.basisLattice upper.toBONG.basis :=
    upper.toBONG.lattice_eq_basisLattice_of_order_monotone
      (fun i j hij => hUpperMonotone hij)
  calc
    baseChange L = baseChange (Lattice.basisLattice lower.toBONG.basis) :=
      congrArg baseChange hLower
    _ = Lattice.basisLattice upper.toBONG.basis := hBasisTransport
    _ = M := hUpper.symm

end Bong.HeClassic2024Carrier
