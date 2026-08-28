/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009ClassificationProof
import Bong.Bong.Beli2019MainTheorem

/-!
# Unconditional main theorems of Beli (2006)

The 2006 paper announces two BONG criteria whose detailed proofs appeared
later.  Theorem 3.2 is discharged by the complete 2009/2010 classification
proof, and Theorem 4.5 is the original four-condition form of the
representation theorem proved in the 2019 v2 paper.
-/

namespace Bong

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- Beli (2006), Theorem 3.2, with the former classification-law boundary
discharged by the complete proof published in 2009/2010. -/
theorem beli2006Theorem32_proved
    {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type w} [AddCommGroup W] [Module K W]
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W} {n : Nat}
    (ambient : q.IsIsometric r)
    (a : BONG.GoodBONG q L (n + 1))
    (b : BONG.GoodBONG r M (n + 1)) :
    Lattice.IsIsometric q r L M ↔ ClassificationConditions a b :=
  BONG.GoodBONG.beli2009Theorem31_concrete ambient a b

/-- Beli (2006), Theorem 4.5.  This is the original four-condition form of
the representation theorem; Beli (2019) supplies its complete proof. -/
theorem beli2006Theorem45_proved
    {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type w} [AddCommGroup W] [Module K W]
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W} {m n : Nat}
    (hRank : n ≤ m) (ambient : q.Represents r)
    (a : BONG.GoodBONG q L (m + 1))
    (b : BONG.GoodBONG r M (n + 1)) :
    Lattice.Represents q r L M ↔ RepresentationConditions a b hRank :=
  beli2019Theorem21 hRank ambient a b

end Bong
