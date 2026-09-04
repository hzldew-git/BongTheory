/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OMaximalRepresentation

/-!
# Local n-ADC quadratic lattices

This file formalizes Definition 1.1(ii) of Zilong He,
*On n-ADC integral quadratic lattices over algebraic number fields*.
It also proves the maximal-lattice reduction used as Lemma 2.1 in that paper.

All notions in this file are local.  The global definitions, localization
data, and `n`-regularity are deliberately kept separate so that local and
global quantifiers cannot be conflated.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- A local integral lattice is `n`-ADC when it integrally represents every
integral rank-`n` lattice whose ambient quadratic space is represented by its
own ambient quadratic space. -/
def IsNADC (q : QuadraticSpace K V) (L : Lattice K V) (n : Nat) : Prop :=
  IsIntegral q L ∧
    ∀ {W : Type w} [AddCommGroup W] [Module K W]
      (r : QuadraticSpace K W) (M : Lattice K W),
      finrank K W = n → IsIntegral r M → q.Represents r →
        Represents q r L M

namespace IsNADC

theorem isIntegral (h : IsNADC.{u, v, w} q L n) : IsIntegral q L :=
  h.1

theorem represents
    (h : IsNADC.{u, v, w} q L n)
    {W : Type w} [AddCommGroup W] [Module K W]
    (r : QuadraticSpace K W) (M : Lattice K W)
    (hrank : finrank K W = n) (hM : IsIntegral r M)
    (hambient : q.Represents r) : Represents q r L M :=
  h.2 r M hrank hM hambient

end IsNADC

/-- Local `n`-universality implies local `n`-ADC-ness. -/
theorem IsNUniversal.isNADC
    (h : IsNUniversal.{u, v, w} q L n) : IsNADC.{u, v, w} q L n := by
  refine ⟨h.1, ?_⟩
  intro W _ _ r M hr hM _
  exact h.2 r M hr hM

/-- The restricted test family from He, Lemma 2.1: maximal rank-`n`
lattices whose ambient spaces are represented by the target ambient space. -/
def RepresentsAllRelevantOMaximalOfRank
    (q : QuadraticSpace K V) (L : Lattice K V) (n : Nat) : Prop :=
  ∀ {W : Type w} [AddCommGroup W] [Module K W]
    (r : QuadraticSpace K W) (M : Lattice K W),
    finrank K W = n → IsOMaximal r M → q.Represents r →
      Represents q r L M

/-- He (2025), Lemma 2.1: the local `n`-ADC condition can be tested only on
`O`-maximal rank-`n` lattices in ambient spaces represented by the target. -/
theorem isNADC_iff_representsAllRelevantOMaximal
    (q : QuadraticSpace K V) (L : Lattice K V) (n : Nat) :
    IsNADC.{u, v, w} q L n ↔
      IsIntegral q L ∧
        RepresentsAllRelevantOMaximalOfRank.{u, v, w} q L n := by
  constructor
  · rintro ⟨hintegral, hall⟩
    refine ⟨hintegral, ?_⟩
    intro W _ _ r M hr hmaximal hambient
    exact hall r M hr hmaximal.isIntegral hambient
  · rintro ⟨hintegral, hmaximal⟩
    refine ⟨hintegral, ?_⟩
    intro W _ _ r N hr hN hambient
    obtain ⟨M, hNM, hMmaximal⟩ :=
      exists_oMaximal_superlattice (q := r) (L := N) hN
    exact (hmaximal r M hr hMmaximal hambient).trans
      (represents_of_le r hNM)

/-! ## Maximal lattices and the equal-rank case -/

/-- He (2025), Lemma 4.14, over the repository's dyadic local-field
interface: an `O`-maximal lattice is `n`-ADC in every positive rank not
exceeding its ambient rank.  The rank bound is not needed in the proof; if
the source rank is too large, the ambient representation premise is simply
empty. -/
theorem IsOMaximal.isNADC
    {V : Type u} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    (hL : IsOMaximal q L) (n : Nat) :
    IsNADC.{u, u, u} q L n := by
  refine ⟨hL.isIntegral, ?_⟩
  intro W _ _ r N _ hN hspace
  obtain ⟨P, hNP, hPmaximal⟩ :=
    exists_oMaximal_superlattice (q := r) (L := N) hN
  exact (hL.represents_of_ambient hPmaximal hspace).trans
    (represents_of_le r hNP)

/-- The necessity direction of He (2025), Proposition 4.15: a local
`n`-ADC lattice whose ambient dimension is exactly `n` is `O`-maximal. -/
theorem IsNADC.isOMaximal_of_finrank_eq
    {V : Type u} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (hL : IsNADC.{u, u, u} q L n)
    (hrank : finrank K V = n) : IsOMaximal q L := by
  letI : Module.Finite K V := L.moduleFinite
  obtain ⟨M, hLM, hMmaximal⟩ :=
    exists_oMaximal_superlattice (q := q) (L := L) hL.isIntegral
  have hrep : Represents q q L M :=
    hL.represents q M hrank (hMmaximal.isIntegral)
      (QuadraticSpace.represents_refl q)
  rcases hrep with ⟨f⟩
  let e : QuadraticSpace.Isometry q q :=
    f.toQuadraticSpaceIsometryOfFinrankEq rfl
  let image : Lattice K V := map e.toLinearEquiv M
  let g : Isometry q q M image := Isometry.toMap q e M
  have himageMaximal : IsOMaximal q image :=
    hMmaximal.of_latticeIsometry g
  have himage_le : image ≤ L := by
    intro y hy
    change y ∈ image at hy
    change y ∈ L
    rw [show image = map e.toLinearEquiv M by rfl,
      mem_map_iff] at hy
    have hfy : f.toLinearMap (e.toLinearEquiv.symm y) ∈ L :=
      f.map_mem hy
    have heq : f.toLinearMap (e.toLinearEquiv.symm y) = y := by
      change e.toLinearEquiv (e.toLinearEquiv.symm y) = y
      exact e.toLinearEquiv.apply_symm_apply y
    rwa [heq] at hfy
  have himage_eq : L = image :=
    himageMaximal.eq_of_le L himage_le hL.isIntegral
  rw [himage_eq]
  exact himageMaximal

/-- He (2025), Proposition 4.15, for dyadic local fields: in equal rank,
`n`-ADC is equivalent to `O`-maximality. -/
theorem isNADC_iff_isOMaximal_of_finrank_eq
    {V : Type u} [AddCommGroup V] [Module K V]
    (q : QuadraticSpace K V) (L : Lattice K V) (n : Nat)
    (hrank : finrank K V = n) :
    IsNADC.{u, u, u} q L n ↔ IsOMaximal q L := by
  constructor
  · exact fun h => h.isOMaximal_of_finrank_eq hrank
  · exact fun h => IsOMaximal.isNADC h n

namespace QuadraticLatticeModel

/-- Ambient-space representability between bundled quadratic lattices. -/
def AmbientlyRepresents
    (X Y : QuadraticLatticeModel (K := K)) : Prop := by
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  letI : AddCommGroup Y.Carrier := Y.addCommGroup
  letI : Module K Y.Carrier := Y.module
  exact X.form.Represents Y.form

/-- `n`-ADC-ness of a bundled quadratic lattice. -/
def IsNADC (X : QuadraticLatticeModel (K := K)) (n : Nat) : Prop := by
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  exact Lattice.IsNADC.{u, u, u} X.form X.lattice n

/-- A bundled maximal lattice is locally `n`-ADC. -/
theorem IsOMaximal.isNADC
    {X : QuadraticLatticeModel (K := K)}
    (hX : X.IsOMaximal) (n : Nat) : X.IsNADC n := by
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  exact Lattice.IsOMaximal.isNADC hX n

/-- Elimination rule for bundled `n`-ADC-ness. -/
theorem IsNADC.represents
    {X Y : QuadraticLatticeModel (K := K)} {n : Nat}
    (hX : X.IsNADC n) (hRank : Y.rank = n)
    (hIntegral : Y.IsIntegral) (hAmbient : X.AmbientlyRepresents Y) :
    X.Represents Y := by
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  letI : AddCommGroup Y.Carrier := Y.addCommGroup
  letI : Module K Y.Carrier := Y.module
  exact hX.2 Y.form Y.lattice hRank hIntegral hAmbient

/-- Integral representation implies ambient-space representation. -/
theorem Represents.ambient
    {X Y : QuadraticLatticeModel (K := K)}
    (h : X.Represents Y) : X.AmbientlyRepresents Y := by
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  letI : AddCommGroup Y.Carrier := Y.addCommGroup
  letI : Module K Y.Carrier := Y.module
  exact Lattice.Represents.ambient h

end QuadraticLatticeModel

end Lattice

end Bong
