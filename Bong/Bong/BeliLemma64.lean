/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma63
import Bong.Bong.BeliLemma319
import Bong.Lattice.Jordan

/-!
# Beli (2003), Lemma 6.4

This file gives an intrinsic meaning to containment of `π^r A(0,0)` and
states the three orthogonal-splitting assertions of Lemma 6.4.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

namespace Lattice

/-- A lattice contains an integral copy of `π^r A(0,0)`. -/
def ContainsScaledHyperbolicPlane
    (q : QuadraticSpace K V) (L : Lattice K V) (r : Int) : Prop :=
  ∃ x y : V, x ∈ L ∧ y ∈ L ∧ BONG.IsScaledHyperbolicPair q x y r

namespace QuadraticSublattice

/-- A quadratic sublattice contains an ambient copy of `π^r A(0,0)`. -/
def ContainsScaledHyperbolicPlane (C : QuadraticSublattice q)
    (r : Int) : Prop :=
  ∃ x y : C.carrier, x ∈ C.lattice ∧ y ∈ C.lattice ∧
    BONG.IsScaledHyperbolicPair q (x : V) (y : V) r

end QuadraticSublattice

namespace OrthogonalDecomposition

variable {t : Nat} (D : OrthogonalDecomposition q L t)

/-- Every integral vector of a component belongs to the parent lattice. -/
theorem component_mem_parent (i : Fin t) (x : (D.component i).carrier)
    (hx : x ∈ (D.component i).lattice) : (x : V) ∈ L := by
  have hxComponent : (x : V) ∈ (D.component i).ambientSubmodule :=
    ⟨x, hx, rfl⟩
  have hle : (D.component i).ambientSubmodule ≤ L.toSubmodule := by
    rw [← D.sum_eq]
    exact le_iSup (fun j ↦ (D.component j).ambientSubmodule) i
  exact hle hxComponent

/-- Hyperbolic-plane containment in a component implies containment in the
parent orthogonal sum. -/
theorem containsScaledHyperbolicPlane_of_component
    (i : Fin t) (r : Int)
    (hH : (D.component i).ContainsScaledHyperbolicPlane r) :
    ContainsScaledHyperbolicPlane q L r := by
  rcases hH with ⟨x, y, hx, hy, hxy⟩
  exact ⟨(x : V), (y : V), D.component_mem_parent i x hx,
    D.component_mem_parent i y hy, hxy⟩

end OrthogonalDecomposition

/-- The unary-first orthogonal splitting in Lemma 6.4(i). -/
structure UnaryFirstSplitting (q : QuadraticSpace K V)
    (L : Lattice K V) (r : Int) extends OrthogonalDecomposition q L 2 where
  /-- The first component is unary. -/
  first_rank : Module.finrank K (component 0).carrier = 1
  /-- The complementary scale is contained in `𝖭^(r+1)`. -/
  tail_scale_le :
    scaleIdeal (component 1).space (component 1).lattice ≤
      powerIdeal (K := K) (r + 1)

/-- The binary-modular-first splitting in Lemma 6.4(ii). -/
structure BinaryFirstModularSplitting (q : QuadraticSpace K V)
    (L : Lattice K V) (r : Int) extends OrthogonalDecomposition q L 2 where
  /-- The first component is binary. -/
  first_rank : Module.finrank K (component 0).carrier = 2
  /-- The first component is `π^r`-modular. -/
  first_modular : IsModular (component 0).space (component 0).lattice
    (uniformizerPowerUnit K r)
  /-- Its scale is exactly `𝖭^r`. -/
  first_scale_eq :
    scaleIdeal (component 0).space (component 0).lattice =
      powerIdeal (K := K) r
  /-- The complementary scale is contained in `𝖭^(r+1)`. -/
  tail_scale_le :
    scaleIdeal (component 1).space (component 1).lattice ≤
      powerIdeal (K := K) (r + 1)
  /-- The complementary norm is properly contained in the first norm. -/
  tail_norm_lt :
    normIdeal (component 1).space (component 1).lattice <
      normIdeal (component 0).space (component 0).lattice

end Lattice

namespace BONG.PrefixWitness

variable {b : BONG V q L n} {length : Nat} {bound : length ≤ n}

/-- A prefix witness, viewed as an ambient quadratic sublattice. -/
def quadraticSublattice (w : PrefixWitness b length bound) :
    Lattice.QuadraticSublattice q where
  carrier := w.carrier
  nondegenerate := w.nondegenerate
  lattice := w.lattice

/-- A hyperbolic plane in a prefix is also contained in the parent lattice. -/
theorem containsScaledHyperbolicPlane_parent
    (w : PrefixWitness b length bound) (r : Int)
    (hH : w.quadraticSublattice.ContainsScaledHyperbolicPlane r) :
    Lattice.ContainsScaledHyperbolicPlane q L r := by
  rcases hH with ⟨x, y, hx, hy, hxy⟩
  exact ⟨(x : V), (y : V), w.contained x hx, w.contained y hy, hxy⟩

end BONG.PrefixWitness

/-- The nontrivial orthogonal-splitting implications in Beli (2003),
Lemma 6.4.  This interface has no default instance. -/
class BeliLemma64Laws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  unaryFirst_excludes_hyperbolic
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {r : Int}
    (S : Lattice.UnaryFirstSplitting q L r) :
    ¬Lattice.ContainsScaledHyperbolicPlane q L r
  full_implies_first
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {r : Int}
    (S : Lattice.BinaryFirstModularSplitting q L r) :
    Lattice.ContainsScaledHyperbolicPlane q L r →
      (S.component 0).ContainsScaledHyperbolicPlane r
  full_implies_binaryPrefix
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (b : BONG V q L (n + 3)) (hgood : b.IsGood)
    (h13 : b.order 0 < b.order 2) :
    Lattice.ContainsScaledHyperbolicPlane q L
        ((b.order 0 + b.order 1) / 2) →
      Lattice.QuadraticSublattice.ContainsScaledHyperbolicPlane
        (b.prefixWitness 2 (by omega)).quadraticSublattice
        ((b.order 0 + b.order 1) / 2)

namespace BONG

variable [BeliLemma64Laws.{u, v} K]

/-- Beli (2003), Lemma 6.4(i). -/
theorem beliLemma64_i {r : Int} (S : Lattice.UnaryFirstSplitting q L r) :
    ¬Lattice.ContainsScaledHyperbolicPlane q L r :=
  BeliLemma64Laws.unaryFirst_excludes_hyperbolic S

/-- Beli (2003), Lemma 6.4(ii). -/
theorem beliLemma64_ii {r : Int}
    (S : Lattice.BinaryFirstModularSplitting q L r) :
    Lattice.ContainsScaledHyperbolicPlane q L r ↔
      (S.component 0).ContainsScaledHyperbolicPlane r := by
  constructor
  · exact BeliLemma64Laws.full_implies_first S
  · exact S.toOrthogonalDecomposition.containsScaledHyperbolicPlane_of_component
      0 r

/-- Beli (2003), Lemma 6.4(iii). -/
theorem beliLemma64_iii (b : BONG V q L (n + 3)) (hgood : b.IsGood)
    (h13 : b.order 0 < b.order 2) :
    Lattice.ContainsScaledHyperbolicPlane q L
        ((b.order 0 + b.order 1) / 2) ↔
      Lattice.QuadraticSublattice.ContainsScaledHyperbolicPlane
        (b.prefixWitness 2 (by omega)).quadraticSublattice
        ((b.order 0 + b.order 1) / 2) := by
  constructor
  · exact BeliLemma64Laws.full_implies_binaryPrefix b hgood h13
  · exact (b.prefixWitness 2 (by omega)).containsScaledHyperbolicPlane_parent
      ((b.order 0 + b.order 1) / 2)

end BONG

end Bong
