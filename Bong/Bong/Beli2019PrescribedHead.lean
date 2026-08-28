/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019PrefixExtension
import Bong.Bong.Existence

/-!
# Beli (2019), prescribed heads for BONGs

The base step of Corollary 5.10 starts with a norm generator of a sublattice
whose first order agrees with that of the ambient lattice.  This file proves
that it is also a norm generator of the ambient lattice and constructs a BONG
of arbitrary positive rank beginning with that prescribed vector.
-/

namespace Bong

open Dyadic

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {x : V}

/-- A norm generator of a sublattice remains a norm generator of an ambient
lattice when their norm ideals agree. -/
theorem IsNormGenerator.of_le_of_normIdeal_eq
    (generator : IsNormGenerator q L x) (hLM : L ≤ M)
    (hnorm : normIdeal q M = normIdeal q L) :
    IsNormGenerator q M x where
  left := hLM generator.mem
  right := hnorm.trans generator.normIdeal_eq

end Lattice

namespace BONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- A prescribed anisotropic norm generator begins a BONG of every admissible
positive length. -/
noncomputable def ofNormGenerator (x : V)
    (generator : Lattice.IsNormGenerator q L x)
    (anisotropic : q.IsAnisotropic x)
    (hfin : Module.finrank K V = n + 1) : BONG V q L (n + 1) := by
  letI : Module.Finite K V := L.moduleFinite
  have horth : Module.finrank K (q.vectorOrthogonal x) = n := by
    have hdim := q.finrank_vectorOrthogonal anisotropic
    omega
  let tail := (BONG.ofLattice (q.orthogonalSpace x anisotropic)
    (L.projectedLattice q x anisotropic)).castLength horth
  exact BONG.cons x generator anisotropic tail

@[simp]
theorem head_ofNormGenerator (x : V)
    (generator : Lattice.IsNormGenerator q L x)
    (anisotropic : q.IsAnisotropic x)
    (hfin : Module.finrank K V = n + 1) :
    (ofNormGenerator x generator anisotropic hfin).head = x := by
  rw [← ambientVector_zero_eq_head, ofNormGenerator, ambientVector_cons_zero]

end BONG

namespace BONG.GoodBONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- Equal first orders transport the prescribed head's norm-generator
property across a lattice inclusion. -/
theorem prescribedHead_isNormGenerator
    (a : GoodBONG q M (n + 1)) (b : GoodBONG q L (n + 1))
    (hLM : L ≤ M) (hzero : a.order 0 = b.order 0) :
    Lattice.IsNormGenerator q M b.toBONG.head := by
  change a.toBONG.order 0 = b.toBONG.order 0 at hzero
  apply b.toBONG.head_isNormGenerator.of_le_of_normIdeal_eq hLM
  rw [a.toBONG.normIdeal_eq_powerIdeal_order_zero,
    b.toBONG.normIdeal_eq_powerIdeal_order_zero, hzero]

/-- The canonical candidate BONG of the ambient lattice with the prescribed
head of the sublattice BONG. -/
noncomputable def prescribedHeadCandidate
    (a : GoodBONG q M (n + 1)) (b : GoodBONG q L (n + 1))
    (hLM : L ≤ M) (hzero : a.order 0 = b.order 0) :
    BONG V q M (n + 1) :=
  BONG.ofNormGenerator b.toBONG.head
    (a.prescribedHead_isNormGenerator b hLM hzero)
    b.toBONG.head_isAnisotropic a.toBONG.length_eq_finrank.symm

@[simp]
theorem prescribedHeadCandidate_head
    (a : GoodBONG q M (n + 1)) (b : GoodBONG q L (n + 1))
    (hLM : L ≤ M) (hzero : a.order 0 = b.order 0) :
    (a.prescribedHeadCandidate b hLM hzero).head = b.toBONG.head := by
  apply BONG.head_ofNormGenerator

/-- The Lemma 5.7 candidate obtained by prepending the prescribed head to a
chosen good BONG of its projected ambient lattice. -/
noncomputable def prescribedHeadCandidateWithTail
    (a : GoodBONG q M (n + 1)) (b : GoodBONG q L (n + 1))
    (hLM : L ≤ M) (hzero : a.order 0 = b.order 0)
    (t : GoodBONG
      (q.orthogonalSpace b.toBONG.head b.toBONG.head_isAnisotropic)
      (M.projectedLattice q b.toBONG.head b.toBONG.head_isAnisotropic) n) :
    BONG V q M (n + 1) :=
  BONG.cons b.toBONG.head
    (a.prescribedHead_isNormGenerator b hLM hzero)
    b.toBONG.head_isAnisotropic t.toBONG

@[simp]
theorem prescribedHeadCandidateWithTail_head
    (a : GoodBONG q M (n + 1)) (b : GoodBONG q L (n + 1))
    (hLM : L ≤ M) (hzero : a.order 0 = b.order 0)
    (t : GoodBONG
      (q.orthogonalSpace b.toBONG.head b.toBONG.head_isAnisotropic)
      (M.projectedLattice q b.toBONG.head b.toBONG.head_isAnisotropic) n) :
    (a.prescribedHeadCandidateWithTail b hLM hzero t).head = b.toBONG.head :=
  rfl

@[simp]
theorem prescribedHeadCandidateWithTail_tail
    (a : GoodBONG q M (n + 1)) (b : GoodBONG q L (n + 1))
    (hLM : L ≤ M) (hzero : a.order 0 = b.order 0)
    (t : GoodBONG
      (q.orthogonalSpace b.toBONG.head b.toBONG.head_isAnisotropic)
      (M.projectedLattice q b.toBONG.head b.toBONG.head_isAnisotropic) n) :
    (a.prescribedHeadCandidateWithTail b hLM hzero t).tail = t.toBONG :=
  rfl

end BONG.GoodBONG

end Bong
