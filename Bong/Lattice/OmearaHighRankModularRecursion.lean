/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaHighRankModularSplitting

/-!
# Rank reduction for O'Meara 93:18(v)

The geometric splitting supplied by O'Meara 82:16 lowers the rank of an
`a`-modular lattice by exactly two.  Consequently the high-rank assertion in
93:18(v) has only two genuine base ranks: five and six.  This file records
that reduction without postulating a new typeclass or a global local law.

The remaining argument may therefore concentrate on the quinary and senary
calculations in Example 93:18.  Once those two calculations return concrete
`Omeara9318vData`, the definition below produces the result in every higher
rank by well-founded recursion.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- A rank-five-or-six constructor, quantified over every carrier in the
ambient universe.  This is a function argument used to expose the exact two
base cases of the recursion; it is deliberately not a typeclass. -/
abbrev Omeara9318vRankFiveOrSixConstructor :=
  {X : Type v} → [AddCommGroup X] → [Module K X] →
    (p : QuadraticSpace K X) → (A : Lattice K X) → (s : Kˣ) →
      IsModular p A s →
        (finrank K X = 5 ∨ finrank K X = 6) →
          Omeara9318vData p A s

/-- O'Meara 93:18(v) in all ranks at least five, reduced to its quinary and
senary cases.  At rank at least seven, split an arbitrary integral isotropic
plane, recurse on its modular orthogonal complement, and exchange the
hyperbolic plane obtained there to the front. -/
noncomputable def omeara9318vDataOfRankFiveOrSix
    (base : Omeara9318vRankFiveOrSixConstructor.{u, v} (K := K))
    {X : Type v} [AddCommGroup X] [Module K X]
    (p : QuadraticSpace K X) (A : Lattice K X) (s : Kˣ)
    (hmodular : IsModular p A s)
    (hrank : 5 ≤ finrank K X) :
    Omeara9318vData p A s := by
  letI : Module.Finite K X := A.moduleFinite
  by_cases hsmall : finrank K X ≤ 6
  · exact base p A s hmodular (by omega)
  · have hseven : 7 ≤ finrank K X := by omega
    let D := omearaHighRankModularPlaneData hmodular hrank
    let C := (D.splitting hmodular).component 1
    letI : Module.Finite K C.carrier := C.lattice.moduleFinite
    have hcomplementRank : finrank K C.carrier = finrank K X - 2 :=
      D.complement_finrank hmodular
    have hcomplementFive : 5 ≤ finrank K C.carrier := by
      rw [hcomplementRank]
      omega
    let E := omeara9318vDataOfRankFiveOrSix base C.space C.lattice s
      (D.complement_modular hmodular) hcomplementFive
    exact D.toOmeara9318vData_of_complement hmodular E
termination_by finrank K X
decreasing_by
  rw [hcomplementRank]
  omega

end Lattice

end Bong
