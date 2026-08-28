/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SolvedHead
import Bong.Bong.ValueIsometry

/-!
# Extending an integral representation through a BONG prefix

This file packages the repeated one-head construction used in Beli (2003),
Lemma 2.7(ii).  A representation of two projected suffix lattices lifts after
adjoining equal-valued norm-generating heads.  Iterating this operation gives
the precise dependent form needed in Beli (2019), Lemma 9.10.

The certificate keeps each projected tail in its actual orthogonal-complement
space.  Thus the result does not identify dependent tails with flattened lists
and does not add a paper-specific representation law.
-/

namespace Bong

open Dyadic
open Module

universe u v w x y

namespace BONG

/--
A representation of two suffix lattices, extended through zero or more pairs
of equal-valued BONG heads.

The first BONG is the target and the second is the source, following the
argument order of `Lattice.Represents q r L M`.
-/
inductive PrefixRepresentationExtension
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] :
    {V : Type v} -> [AddCommGroup V] -> [Module K V] ->
    {W : Type w} -> [AddCommGroup W] -> [Module K W] ->
    {q : QuadraticSpace K V} -> {r : QuadraticSpace K W} ->
    {L : Lattice K V} -> {M : Lattice K W} -> {n : Nat} ->
    BONG V q L n -> BONG W r M n -> Prop
  | suffix
      {V : Type v} [AddCommGroup V] [Module K V]
      {W : Type w} [AddCommGroup W] [Module K W]
      {q : QuadraticSpace K V} {r : QuadraticSpace K W}
      {L : Lattice K V} {M : Lattice K W} {n : Nat}
      (target : BONG V q L n) (source : BONG W r M n)
      (represents : Lattice.Represents q r L M) :
      PrefixRepresentationExtension target source
  | cons
      {V : Type v} [AddCommGroup V] [Module K V]
      {W : Type w} [AddCommGroup W] [Module K W]
      {q : QuadraticSpace K V} {r : QuadraticSpace K W}
      {L : Lattice K V} {M : Lattice K W} {n : Nat}
      {targetHead : V} {sourceHead : W}
      (targetGenerator : Lattice.IsNormGenerator q L targetHead)
      (sourceGenerator : Lattice.IsNormGenerator r M sourceHead)
      (targetAnisotropic : q.IsAnisotropic targetHead)
      (sourceAnisotropic : r.IsAnisotropic sourceHead)
      (headValue_eq : q.quadratic targetHead = r.quadratic sourceHead)
      (targetTail : BONG (q.vectorOrthogonal targetHead)
        (q.orthogonalSpace targetHead targetAnisotropic)
        (L.projectedLattice q targetHead targetAnisotropic) n)
      (sourceTail : BONG (r.vectorOrthogonal sourceHead)
        (r.orthogonalSpace sourceHead sourceAnisotropic)
        (M.projectedLattice r sourceHead sourceAnisotropic) n)
      (tail : PrefixRepresentationExtension targetTail sourceTail) :
      PrefixRepresentationExtension
        (BONG.cons targetHead targetGenerator targetAnisotropic targetTail)
        (BONG.cons sourceHead sourceGenerator sourceAnisotropic sourceTail)

namespace PrefixRepresentationExtension

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- Beli (2003), Lemma 2.7(ii), in representation form: a suffix
representation propagates through every equal-valued norm-generator head. -/
theorem represents
    {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type w} [AddCommGroup W] [Module K W]
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W} {n : Nat}
    {target : BONG V q L n} {source : BONG W r M n}
    (h : PrefixRepresentationExtension target source) :
    Lattice.Represents q r L M := by
  induction h with
  | suffix _ _ hrep =>
      exact hrep
  | @cons V _ _ W _ _ q r L M n targetHead sourceHead
      targetGenerator sourceGenerator targetAnisotropic sourceAnisotropic
      headValue_eq targetTail sourceTail _ ih =>
      have hfinrank : finrank K W = finrank K V := by
        rw [← (BONG.cons sourceHead sourceGenerator sourceAnisotropic
              sourceTail).length_eq_finrank,
          ← (BONG.cons targetHead targetGenerator targetAnisotropic
              targetTail).length_eq_finrank]
      exact Beli2019SolvedHeadData.represents_of_projected
        targetHead sourceHead targetGenerator sourceGenerator
        targetAnisotropic sourceAnisotropic headValue_eq hfinrank ih

end PrefixRepresentationExtension

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/--
Lift a represented suffix through a common scalar prefix.

The two suffix models may live in unrelated ambient spaces.  At the terminal
step, equality of complete BONG value sequences identifies the actual
dependent tails with those models by `BONG.latticeIsometryOfValueEq`.  The
proof then adjoins the common heads one at a time.  This is a flattened input
interface for the dependent certificate above and is convenient for reversed
dual arguments.
-/
theorem represents_of_prefixValueEq_of_suffixModels
    {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type w} [AddCommGroup W] [Module K W]
    {X : Type x} [AddCommGroup X] [Module K X]
    {Y : Type y} [AddCommGroup Y] [Module K Y]
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {s : QuadraticSpace K X} {t : QuadraticSpace K Y}
    {L : Lattice K V} {M : Lattice K W}
    {A : Lattice K X} {B : Lattice K Y}
    {baseLength steps : Nat}
    (target : BONG V q L (baseLength + steps))
    (source : BONG W r M (baseLength + steps))
    (targetSuffix : BONG X s A baseLength)
    (sourceSuffix : BONG Y t B baseLength)
    (prefixValue_eq : ∀ i : Fin steps,
      target.value ⟨i.val, by omega⟩ =
        source.value ⟨i.val, by omega⟩)
    (targetSuffixValues : ∀ j : Fin baseLength,
      target.value ⟨steps + j.val, by omega⟩ = targetSuffix.value j)
    (sourceSuffixValues : ∀ j : Fin baseLength,
      source.value ⟨steps + j.val, by omega⟩ = sourceSuffix.value j)
    (suffixRepresents : Lattice.Represents s t A B) :
    Lattice.Represents q r L M := by
  induction steps generalizing V W q r L M with
  | zero =>
      have htargetValues : ∀ j : Fin baseLength,
          targetSuffix.value j = target.value j := by
        intro j
        simpa using (targetSuffixValues j).symm
      have hsourceValues : ∀ j : Fin baseLength,
          sourceSuffix.value j = source.value j := by
        intro j
        simpa using (sourceSuffixValues j).symm
      let targetIso :=
        targetSuffix.latticeIsometryOfValueEq target htargetValues
      let sourceIso :=
        sourceSuffix.latticeIsometryOfValueEq source hsourceValues
      have htarget : Lattice.Represents q s L A :=
        ⟨targetIso.toRepresentation⟩
      have hsource : Lattice.Represents t r B M :=
        ⟨sourceIso.symm.toRepresentation⟩
      exact (htarget.trans suffixRepresents).trans hsource
  | succ steps ih =>
      have hhead : q.quadratic target.head = r.quadratic source.head := by
        calc
          q.quadratic target.head = target.value 0 :=
            target.value_zero_eq_quadratic_head.symm
          _ = source.value 0 := by
            simpa using prefixValue_eq (0 : Fin (steps + 1))
          _ = r.quadratic source.head :=
            source.value_zero_eq_quadratic_head
      have hfinrank : Module.finrank K W = Module.finrank K V := by
        rw [← source.length_eq_finrank, ← target.length_eq_finrank]
      have htailPrefix : ∀ i : Fin steps,
          target.tail.value
              ⟨i.val, lt_of_lt_of_le i.isLt
                (Nat.le_add_left steps baseLength)⟩ =
            source.tail.value
              ⟨i.val, lt_of_lt_of_le i.isLt
                (Nat.le_add_left steps baseLength)⟩ := by
        intro i
        rw [target.value_tail, source.value_tail]
        simpa using prefixValue_eq i.succ
      have htargetTailSuffix : ∀ j : Fin baseLength,
          target.tail.value
              ⟨steps + j.val, by
                simpa [Nat.add_comm] using
                  Nat.add_lt_add_left j.isLt steps⟩ =
            targetSuffix.value j := by
        intro j
        rw [target.value_tail]
        convert targetSuffixValues j using 1
        congr 1
        apply Fin.ext
        simp
        omega
      have hsourceTailSuffix : ∀ j : Fin baseLength,
          source.tail.value
              ⟨steps + j.val, by
                simpa [Nat.add_comm] using
                  Nat.add_lt_add_left j.isLt steps⟩ =
            sourceSuffix.value j := by
        intro j
        rw [source.value_tail]
        convert sourceSuffixValues j using 1
        congr 1
        apply Fin.ext
        simp
        omega
      have htail := ih target.tail source.tail htailPrefix
        htargetTailSuffix hsourceTailSuffix
      exact Beli2019SolvedHeadData.represents_of_projected
        target.head source.head target.head_isNormGenerator
        source.head_isNormGenerator target.head_isAnisotropic
        source.head_isAnisotropic hhead hfinrank htail

end BONG

end Bong
