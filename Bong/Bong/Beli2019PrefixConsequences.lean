/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019PrefixExtensionFull
import Bong.Bong.Beli2009ClassificationPropagation

/-!
# Beli (2019), scalar consequences of Corollary 5.10

The later proof of condition 2.1(ii) uses Corollary 5.10 to replace a good
BONG while keeping its first ambient vectors fixed.  This file records the
resulting equalities of quadratic values, unit values, prefix products, and
finite prefix-value families.
-/

namespace Bong

open Dyadic

namespace BONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {m n p : Nat}

/-- Equal ambient prefix vectors have equal quadratic values. -/
theorem AmbientPrefixAgreement.value_eq
    {a : BONG V q L m} {b : BONG V q M n}
    (h : AmbientPrefixAgreement a b p) (j : Nat) (hj : j < p) :
    a.value ⟨j, hj.trans_le h.leftBound⟩ =
      b.value ⟨j, hj.trans_le h.rightBound⟩ := by
  calc
    a.value ⟨j, hj.trans_le h.leftBound⟩ =
        q.quadratic (a.ambientVector ⟨j, hj.trans_le h.leftBound⟩) :=
      (a.quadratic_ambientVector _).symm
    _ = q.quadratic
        (b.ambientVector ⟨j, hj.trans_le h.rightBound⟩) := by
      exact congrArg q.quadratic (h.ambient_eq j hj)
    _ = b.value ⟨j, hj.trans_le h.rightBound⟩ :=
      b.quadratic_ambientVector _

/-- Equal ambient prefix vectors give equal unit-valued BONG entries. -/
theorem AmbientPrefixAgreement.valueUnit_eq
    {a : BONG V q L m} {b : BONG V q M n}
    (h : AmbientPrefixAgreement a b p) (j : Nat) (hj : j < p) :
    a.valueUnit ⟨j, hj.trans_le h.leftBound⟩ =
      b.valueUnit ⟨j, hj.trans_le h.rightBound⟩ := by
  apply Units.ext
  simpa only [coe_valueUnit] using h.value_eq j hj

/-- Every shorter prefix product is unchanged by ambient prefix agreement. -/
theorem AmbientPrefixAgreement.prefixProduct_eq
    {a : BONG V q L m} {b : BONG V q M n}
    (h : AmbientPrefixAgreement a b p) (i : Nat) (hi : i ≤ p) :
    a.prefixProduct i = b.prefixProduct i := by
  induction i with
  | zero => simp
  | succ i ih =>
      have him : i < m :=
        (Nat.lt_succ_self i).trans_le (hi.trans h.leftBound)
      have hin : i < n :=
        (Nat.lt_succ_self i).trans_le (hi.trans h.rightBound)
      rw [a.prefixProduct_succ i him,
        b.prefixProduct_succ i hin, ih (by omega),
        h.valueUnit_eq i (by omega)]

end BONG

namespace BONG.GoodBONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {m n p : Nat}

/-- Ambient prefix agreement identifies the corresponding finite families
of scalar BONG values. -/
theorem prefixValues_eq_of_ambientPrefixAgreement
    (a : GoodBONG q L m) (b : GoodBONG q M n)
    (h : BONG.AmbientPrefixAgreement a.toBONG b.toBONG p)
    (i : Nat) (hi : i ≤ p) :
    a.prefixValues i (hi.trans h.leftBound) =
      b.prefixValues i (hi.trans h.rightBound) := by
  funext j
  change a.toBONG.value _ = b.toBONG.value _
  exact h.value_eq j.val (j.isLt.trans_le hi)

/-- Corollary 5.10 together with the prefix-product equality used later in
the proof of condition 2.1(ii). -/
theorem exists_goodBONG_with_ambientPrefix_and_prefixProduct
    [BONGStructuralLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [Beli2019OrderNecessityLaws.{u, v} K]
    (a : GoodBONG q M (n + 1)) (b : GoodBONG q N (n + 1))
    (hNM : N ≤ M)
    (h : BeliPrefixExtensionHypothesis (ramificationIndex K : Int)
      a.orderSequence b.orderSequence p) :
    ∃ c : GoodBONG q M (n + 1),
      BONG.AmbientPrefixAgreement c.toBONG b.toBONG p ∧
        c.prefixProduct p = b.prefixProduct p := by
  rcases a.exists_goodBONG_with_ambientPrefix b hNM h with ⟨c, hc⟩
  exact ⟨c, hc, hc.prefixProduct_eq p le_rfl⟩

end BONG.GoodBONG

end Bong
