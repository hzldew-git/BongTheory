/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma513Profiles
import Bong.Bong.Beli2019PrefixAgreementRigidity

/-!
# Weak-profile proof of Beli (2019), Lemma 5.17(ii)

The paper applies Lemma 5.17 only through the boundary
`n_{k₁} + a - 1`.  On that range the weak almost-Jordan profiles show
that equality of the current orders gives equality of the prefix sum through
that coordinate.  Section 5.4 supplies Beli's order relation, and the two
parity classes of Lemma 5.6 then force equality of every preceding order.
-/

namespace Bong

open Dyadic
open Module

namespace Lattice.Beli2019Lemma51Data

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V}

/-- Beli (2019), Lemma 5.17(ii), for the concrete weak almost-Jordan
profiles.  The conclusion includes the current coordinate, as in the
paper's statement `R_j = S_j` for every `j ≤ i`. -/
theorem weakAllRanks_prefixAgreement_of_current_eq_lemma517Range
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    {n : Nat} (a : BONG.GoodBONG q M n) (b : BONG.GoodBONG q N n)
    (i : RepresentationIndex n n) (hi : D.Lemma517Range i)
    (hcurrent : a.orderSequence.entryOrZero (i.val - 1) =
      b.orderSequence.entryOrZero (i.val - 1)) :
    a.orderSequence.PrefixAgreement b.orderSequence i.val := by
  have hsum :=
    D.weakAllRanks_prefixSum_eq_of_current_eq_lemma517Range
      a b i hi hcurrent
  have horder := (D.weakAllRanks_orderCertificate a b).orderLE
  exact horder.prefixAgreement_of_prefixSum_eq_of_last_eq
    i.val (Nat.le_of_lt i.lt_large) hsum (fun _hpos ↦ hcurrent)

end Lattice.Beli2019Lemma51Data

end Bong
