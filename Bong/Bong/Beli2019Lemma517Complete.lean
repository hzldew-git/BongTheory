/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma517UnaryShift
import Bong.Bong.Beli2019Lemma517Profiles

/-!
# Complete proof package for Beli (2019), Lemma 5.17

This file combines the alpha-cap comparison of part (i) with the prefix
rigidity statement of part (ii), for the concrete Section 5 almost-Jordan
construction and without a separate Lemma 5.17 data parameter.
-/

namespace Bong

open Dyadic Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V}

namespace Lattice.Beli2019Lemma51Data

/-- The concrete weak almost-Jordan construction supplies all of Beli
(2019), Lemma 5.17 on its exact range. -/
theorem lemma517Data_proved
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    {n : Nat} (a : BONG.GoodBONG q M (n + 1))
    (b : BONG.GoodBONG q N (n + 1)) :
    BONG.GoodBONG.Beli2019Lemma517Data a b D.Lemma517Range where
  alphaCap_le i hi hcurrent :=
    D.weakAllRanks_prefixAlphaCap_le_lemma517Range a b i hi hcurrent
  prefixAgreement i hi hcurrent :=
    D.weakAllRanks_prefixAgreement_of_current_eq_lemma517Range
      a b i hi hcurrent

end Lattice.Beli2019Lemma51Data

end Bong
