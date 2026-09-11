/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Classification
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Representation of quadratic lattices by good BONGs

This file formalizes the data and conditions in Beli's representation theorem.
We first define quadratic-space and integral-lattice representations, then
Beli (2006), Definitions 4.1 and 4.3: the capped defects and the invariants
`A_i(M, N)`.  The four conditions of Theorem 4.5 are packaged at the end.

As with classification, the final equivalence depends on a deep local theorem
that is not available in mathlib.  It is isolated as an explicit typeclass and
is not introduced as a global axiom.
-/

namespace Bong

open Dyadic

universe u v w z

namespace QuadraticSpace

variable {K : Type u} [Field K]
  {U : Type z} [AddCommGroup U] [Module K U]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]

/-- An injective linear representation of one quadratic space by another. -/
structure Representation (source : QuadraticSpace K W) (target : QuadraticSpace K V) where
  toLinearMap : W →ₗ[K] V
  injective : Function.Injective toLinearMap
  map_bilin (x y : W) : target.bilin (toLinearMap x) (toLinearMap y) = source.bilin x y

@[simp]
theorem Representation.map_quadratic {source : QuadraticSpace K W}
    {target : QuadraticSpace K V} (f : Representation source target) (x : W) :
    target.quadratic (f.toLinearMap x) = source.quadratic x :=
  f.map_bilin x x

/-- `target.Represents source` means that `source → target`. -/
def Represents (target : QuadraticSpace K V) (source : QuadraticSpace K W) : Prop :=
  Nonempty (Representation source target)

/-- Every quadratic space represents itself. -/
def Representation.refl (q : QuadraticSpace K V) : Representation q q where
  toLinearMap := LinearMap.id
  injective := Function.injective_id
  map_bilin _ _ := rfl

theorem represents_refl (q : QuadraticSpace K V) : q.Represents q :=
  ⟨Representation.refl q⟩

/-- A quadratic-space isometry is, in particular, a representation. -/
def Isometry.toRepresentation {source : QuadraticSpace K W}
    {target : QuadraticSpace K V} (f : Isometry source target) :
    Representation source target where
  toLinearMap := f.toLinearEquiv
  injective := f.toLinearEquiv.injective
  map_bilin := f.map_bilin

/-- A quadratic-space representation between equal finite dimensions is an
isometry. -/
noncomputable def Representation.toIsometryOfFinrankEq
    {source : QuadraticSpace K W} {target : QuadraticSpace K V}
    [FiniteDimensional K W] [FiniteDimensional K V]
    (f : Representation source target)
    (hfinrank : Module.finrank K W = Module.finrank K V) :
    Isometry source target where
  toLinearEquiv :=
    f.toLinearMap.linearEquivOfInjective f.injective hfinrank
  map_bilin := f.map_bilin

@[simp]
theorem Representation.toIsometryOfFinrankEq_apply
    {source : QuadraticSpace K W} {target : QuadraticSpace K V}
    [FiniteDimensional K W] [FiniteDimensional K V]
    (f : Representation source target)
    (hfinrank : Module.finrank K W = Module.finrank K V) (x : W) :
    (f.toIsometryOfFinrankEq hfinrank).toLinearEquiv x = f.toLinearMap x :=
  rfl

theorem IsIsometric.represents {source : QuadraticSpace K W}
    {target : QuadraticSpace K V} (h : source.IsIsometric target) :
    target.Represents source := by
  rcases h with ⟨f⟩
  exact ⟨f.toRepresentation⟩

/-- Quadratic-space representations compose. -/
def Representation.trans {qU : QuadraticSpace K U} {qV : QuadraticSpace K V}
    {qW : QuadraticSpace K W} (g : Representation qV qU)
    (f : Representation qW qV) : Representation qW qU where
  toLinearMap := g.toLinearMap.comp f.toLinearMap
  injective := g.injective.comp f.injective
  map_bilin x y := by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, g.map_bilin, f.map_bilin]

theorem Represents.trans {qU : QuadraticSpace K U} {qV : QuadraticSpace K V}
    {qW : QuadraticSpace K W} (hUV : qU.Represents qV) (hVW : qV.Represents qW) :
    qU.Represents qW := by
  rcases hUV with ⟨g⟩
  rcases hVW with ⟨f⟩
  exact ⟨g.trans f⟩

end QuadraticSpace

namespace Lattice

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {U : Type z} [AddCommGroup U] [Module K U]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]

/-- An integral representation of a quadratic lattice by another lattice. -/
structure Representation
    (sourceQ : QuadraticSpace K W) (targetQ : QuadraticSpace K V)
    (source : Lattice K W) (target : Lattice K V) where
  toLinearMap : W →ₗ[K] V
  injective : Function.Injective toLinearMap
  map_bilin (x y : W) :
    targetQ.bilin (toLinearMap x) (toLinearMap y) = sourceQ.bilin x y
  map_mem {x : W} : x ∈ source → toLinearMap x ∈ target

@[simp]
theorem Representation.map_quadratic
    {sourceQ : QuadraticSpace K W} {targetQ : QuadraticSpace K V}
    {source : Lattice K W} {target : Lattice K V}
    (f : Representation sourceQ targetQ source target) (x : W) :
    targetQ.quadratic (f.toLinearMap x) = sourceQ.quadratic x :=
  f.map_bilin x x

/-- `target` represents `source` as integral quadratic lattices. -/
def Represents (targetQ : QuadraticSpace K V) (sourceQ : QuadraticSpace K W)
    (target : Lattice K V) (source : Lattice K W) : Prop :=
  Nonempty (Representation sourceQ targetQ source target)

/-- Forgetting integrality gives a representation of the ambient spaces. -/
def Representation.toQuadraticSpaceRepresentation
    {sourceQ : QuadraticSpace K W} {targetQ : QuadraticSpace K V}
    {source : Lattice K W} {target : Lattice K V}
    (f : Representation sourceQ targetQ source target) :
    QuadraticSpace.Representation sourceQ targetQ where
  toLinearMap := f.toLinearMap
  injective := f.injective
  map_bilin := f.map_bilin

/-- An integral representation between ambient spaces of equal finite
dimension is an ambient quadratic-space isometry. -/
noncomputable def Representation.toQuadraticSpaceIsometryOfFinrankEq
    {sourceQ : QuadraticSpace K W} {targetQ : QuadraticSpace K V}
    {source : Lattice K W} {target : Lattice K V}
    [FiniteDimensional K W] [FiniteDimensional K V]
    (f : Representation sourceQ targetQ source target)
    (hfinrank : Module.finrank K W = Module.finrank K V) :
    QuadraticSpace.Isometry sourceQ targetQ where
  toLinearEquiv :=
    f.toLinearMap.linearEquivOfInjective f.injective hfinrank
  map_bilin := f.map_bilin

@[simp]
theorem Representation.toQuadraticSpaceIsometryOfFinrankEq_apply
    {sourceQ : QuadraticSpace K W} {targetQ : QuadraticSpace K V}
    {source : Lattice K W} {target : Lattice K V}
    [FiniteDimensional K W] [FiniteDimensional K V]
    (f : Representation sourceQ targetQ source target)
    (hfinrank : Module.finrank K W = Module.finrank K V) (x : W) :
    (f.toQuadraticSpaceIsometryOfFinrankEq hfinrank).toLinearEquiv x =
      f.toLinearMap x :=
  rfl

/-- Every quadratic lattice represents itself. -/
def Representation.refl (q : QuadraticSpace K V) (L : Lattice K V) :
    Representation q q L L where
  toLinearMap := LinearMap.id
  injective := Function.injective_id
  map_bilin _ _ := rfl
  map_mem hx := hx

theorem represents_refl (q : QuadraticSpace K V) (L : Lattice K V) :
    Represents q q L L :=
  ⟨Representation.refl q L⟩

/-- A sublattice inclusion is an integral representation whose ambient map is
the identity.  This belongs to the common representation API because it is
used by universality and ADC arguments as well as by Beli's nested-lattice
arguments. -/
def Representation.ofLe (q : QuadraticSpace K V) {L M : Lattice K V}
    (hLM : L ≤ M) : Representation q q L M where
  toLinearMap := LinearMap.id
  injective := Function.injective_id
  map_bilin _ _ := rfl
  map_mem hx := hLM hx

/-- Every lattice represents each of its sublattices by inclusion. -/
theorem represents_of_le (q : QuadraticSpace K V) {L M : Lattice K V}
    (hLM : L ≤ M) : Represents q q M L :=
  ⟨Representation.ofLe q hLM⟩

/-- A lattice isometry is, in particular, an integral representation. -/
def Isometry.toRepresentation
    {sourceQ : QuadraticSpace K W} {targetQ : QuadraticSpace K V}
    {source : Lattice K W} {target : Lattice K V}
    (f : Isometry sourceQ targetQ source target) :
    Representation sourceQ targetQ source target where
  toLinearMap := f.toLinearEquiv
  injective := f.toLinearEquiv.injective
  map_bilin := f.map_bilin
  map_mem := (f.map_mem _).mp

theorem IsIsometric.represents
    {sourceQ : QuadraticSpace K W} {targetQ : QuadraticSpace K V}
    {source : Lattice K W} {target : Lattice K V}
    (h : IsIsometric sourceQ targetQ source target) :
    Represents targetQ sourceQ target source := by
  rcases h with ⟨f⟩
  exact ⟨f.toRepresentation⟩

/-- Integral lattice representations compose. -/
def Representation.trans
    {qU : QuadraticSpace K U} {qV : QuadraticSpace K V} {qW : QuadraticSpace K W}
    {LU : Lattice K U} {LV : Lattice K V} {LW : Lattice K W}
    (g : Representation qV qU LV LU) (f : Representation qW qV LW LV) :
    Representation qW qU LW LU where
  toLinearMap := g.toLinearMap.comp f.toLinearMap
  injective := g.injective.comp f.injective
  map_bilin x y := by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, g.map_bilin, f.map_bilin]
  map_mem hx := g.map_mem (f.map_mem hx)

theorem Represents.trans
    {qU : QuadraticSpace K U} {qV : QuadraticSpace K V} {qW : QuadraticSpace K W}
    {LU : Lattice K U} {LV : Lattice K V} {LW : Lattice K W}
    (hUV : Represents qU qV LU LV) (hVW : Represents qV qW LV LW) :
    Represents qU qW LU LW := by
  rcases hUV with ⟨g⟩
  rcases hVW with ⟨f⟩
  exact ⟨g.trans f⟩

theorem Represents.ambient
    {sourceQ : QuadraticSpace K W} {targetQ : QuadraticSpace K V}
    {source : Lattice K W} {target : Lattice K V}
    (h : Represents targetQ sourceQ target source) : targetQ.Represents sourceQ := by
  rcases h with ⟨f⟩
  exact ⟨f.toQuadraticSpaceRepresentation⟩

end Lattice

/--
An index `i` in the range `1 ≤ i ≤ min{largeRank - 1, smallRank}` used to
define Beli's representation invariant `A_i`.
-/
structure RepresentationIndex (largeRank smallRank : Nat) where
  val : Nat
  pos : 0 < val
  lt_large : val < largeRank
  le_small : val ≤ smallRank

namespace RepresentationIndex

/-- Representation indices are determined by their underlying natural
number; all remaining fields are propositions. -/
@[ext]
theorem ext {largeRank smallRank : Nat}
    {i j : RepresentationIndex largeRank smallRank}
    (h : i.val = j.val) : i = j := by
  cases i
  cases j
  cases h
  rfl

end RepresentationIndex

/-- An index used in condition (iii) of Beli's representation theorem. -/
structure CentralRepresentationIndex (largeRank smallRank : Nat) where
  val : Nat
  one_lt : 1 < val
  lt_large : val < largeRank
  le_small_succ : val ≤ smallRank + 1

namespace CentralRepresentationIndex

/-- The ordinary index `i - 1` associated with a central index `i`. -/
def previous {largeRank smallRank : Nat}
    (i : CentralRepresentationIndex largeRank smallRank) :
    RepresentationIndex largeRank smallRank where
  val := i.val - 1
  pos := by have := i.one_lt; omega
  lt_large := by have := i.one_lt; have := i.lt_large; omega
  le_small := by have := i.le_small_succ; omega

/-- A central index is ordinary when `i ≤ smallRank`. -/
def current {largeRank smallRank : Nat}
    (i : CentralRepresentationIndex largeRank smallRank) (hi : i.val ≤ smallRank) :
    RepresentationIndex largeRank smallRank where
  val := i.val
  pos := by have := i.one_lt; omega
  lt_large := i.lt_large
  le_small := hi

end CentralRepresentationIndex

/-- An index used in condition (iv) of Beli's representation theorem. -/
structure LongRepresentationIndex (largeRank smallRank : Nat) where
  val : Nat
  one_lt : 1 < val
  succ_lt_large : val + 1 < largeRank
  le_small_succ : val ≤ smallRank + 1

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {m n : Nat}

/--
The cap contributed by a prefix boundary.  For a prefix of length `i`, this is
`α_i` at an internal boundary and `∞` at either endpoint, implementing Beli's
instruction to omit nonexistent endpoint invariants.
-/
noncomputable def prefixAlphaCap (b : GoodBONG q L (n + 1)) (i : Nat) : WithTop ℚ :=
  if h : 0 < i ∧ i < n + 1 then
    (b.alphaValue ⟨i - 1, by omega⟩ : WithTop ℚ)
  else ⊤

@[simp]
theorem prefixAlphaCap_zero (b : GoodBONG q L (n + 1)) : b.prefixAlphaCap 0 = ⊤ := by
  simp [prefixAlphaCap]

@[simp]
theorem prefixAlphaCap_last (b : GoodBONG q L (n + 1)) :
    b.prefixAlphaCap (n + 1) = ⊤ := by
  simp [prefixAlphaCap]

theorem prefixAlphaCap_of_internal (b : GoodBONG q L (n + 1)) {i : Nat}
    (hi0 : 0 < i) (hin : i < n + 1) :
    b.prefixAlphaCap i = (b.alphaValue ⟨i - 1, by omega⟩ : WithTop ℚ) := by
  simp [prefixAlphaCap, hi0, hin]

/-- Beli (2006), Definition 4.1: the capped defect `d[ε a₁,ᵢ b₁,ⱼ]`. -/
noncomputable def truncatedPrefixDefect (a : GoodBONG q L (m + 1))
    (b : GoodBONG r M (n + 1)) (ε : Kˣ) (i j : Nat) : WithTop ℚ :=
  min
    (defectOrder (K := K) (ε * a.prefixProduct i * b.prefixProduct j))
    (min (a.prefixAlphaCap i) (b.prefixAlphaCap j))

theorem truncatedPrefixDefect_le_defect (a : GoodBONG q L (m + 1))
    (b : GoodBONG r M (n + 1)) (ε : Kˣ) (i j : Nat) :
    a.truncatedPrefixDefect b ε i j ≤
      defectOrder (K := K) (ε * a.prefixProduct i * b.prefixProduct j) :=
  min_le_left _ _

theorem truncatedPrefixDefect_le_leftCap (a : GoodBONG q L (m + 1))
    (b : GoodBONG r M (n + 1)) (ε : Kˣ) (i j : Nat) :
    a.truncatedPrefixDefect b ε i j ≤ a.prefixAlphaCap i :=
  (min_le_right _ _).trans (min_le_left _ _)

theorem truncatedPrefixDefect_le_rightCap (a : GoodBONG q L (m + 1))
    (b : GoodBONG r M (n + 1)) (ε : Kˣ) (i j : Nat) :
    a.truncatedPrefixDefect b ε i j ≤ b.prefixAlphaCap j :=
  (min_le_right _ _).trans (min_le_right _ _)

/-- Beli (2006), Definition 4.1: the segment notation `d[ε aᵢ,ⱼ]`. -/
noncomputable def truncatedSegmentDefect (a : GoodBONG q L (n + 1))
    (ε : Kˣ) (i j : Nat) : WithTop ℚ :=
  a.truncatedPrefixDefect a ε (i - 1) j

/-- The candidate `(R_{i+1} - S_i) / 2 + e` in Definition 4. -/
noncomputable def representationHalfGap (a : GoodBONG q L (m + 1))
    (b : GoodBONG r M (n + 1)) (i : RepresentationIndex (m + 1) (n + 1)) :
    WithTop ℚ :=
  ((((a.order ⟨i.val, i.lt_large⟩ -
      b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ) /
    2 + (ramificationIndex K : ℚ) : ℚ) : WithTop ℚ)

/-- The candidate `R_{i+1} - S_i + d[-a₁,ᵢ₊₁ b₁,ᵢ₋₁]`. -/
noncomputable def representationPrimaryDefect (a : GoodBONG q L (m + 1))
    (b : GoodBONG r M (n + 1)) (i : RepresentationIndex (m + 1) (n + 1)) :
    WithTop ℚ :=
  (((a.order ⟨i.val, i.lt_large⟩ -
      b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ) : WithTop ℚ) +
    a.truncatedPrefixDefect b (-1) (i.val + 1) (i.val - 1)

/--
The interior candidate
`R_{i+1} + R_{i+2} - S_{i-1} - S_i + d[a₁,ᵢ₊₂ b₁,ᵢ₋₂]`.
-/
noncomputable def representationSecondaryDefect (a : GoodBONG q L (m + 1))
    (b : GoodBONG r M (n + 1)) (i : RepresentationIndex (m + 1) (n + 1))
    (hi : 1 < i.val ∧ i.val + 1 < m + 1) : WithTop ℚ :=
  (((a.order ⟨i.val, i.lt_large⟩ + a.order ⟨i.val + 1, hi.2⟩ -
      b.order ⟨i.val - 2, by have := i.le_small; omega⟩ -
      b.order ⟨i.val - 1, by have := i.le_small; omega⟩ : Int) : ℚ) : WithTop ℚ) +
    a.truncatedPrefixDefect b 1 (i.val + 2) (i.val - 2)

/-- The nonempty candidate set defining `A_i(M, N)`. -/
noncomputable def representationAlphaCandidates (a : GoodBONG q L (m + 1))
    (b : GoodBONG r M (n + 1)) (i : RepresentationIndex (m + 1) (n + 1)) :
    Finset (WithTop ℚ) :=
  insert (a.representationHalfGap b i)
    (insert (a.representationPrimaryDefect b i)
      (if h : 1 < i.val ∧ i.val + 1 < m + 1 then
        {a.representationSecondaryDefect b i h}
      else ∅))

theorem representationHalfGap_mem_candidates (a : GoodBONG q L (m + 1))
    (b : GoodBONG r M (n + 1)) (i : RepresentationIndex (m + 1) (n + 1)) :
    a.representationHalfGap b i ∈ a.representationAlphaCandidates b i :=
  Finset.mem_insert_self _ _

theorem representationAlphaCandidates_nonempty (a : GoodBONG q L (m + 1))
    (b : GoodBONG r M (n + 1)) (i : RepresentationIndex (m + 1) (n + 1)) :
    (a.representationAlphaCandidates b i).Nonempty :=
  ⟨a.representationHalfGap b i, a.representationHalfGap_mem_candidates b i⟩

/-- Beli's representation invariant `A_i(M, N)` from Definition 4. -/
noncomputable def representationAlpha (a : GoodBONG q L (m + 1))
    (b : GoodBONG r M (n + 1)) (i : RepresentationIndex (m + 1) (n + 1)) :
    WithTop ℚ :=
  (a.representationAlphaCandidates b i).min'
    (a.representationAlphaCandidates_nonempty b i)

theorem representationAlpha_le_halfGap (a : GoodBONG q L (m + 1))
    (b : GoodBONG r M (n + 1)) (i : RepresentationIndex (m + 1) (n + 1)) :
    a.representationAlpha b i ≤ a.representationHalfGap b i :=
  Finset.min'_le _ _ (a.representationHalfGap_mem_candidates b i)

/-- `A_i(M, N)` is finite because its half-gap candidate is finite. -/
theorem representationAlpha_ne_top (a : GoodBONG q L (m + 1))
    (b : GoodBONG r M (n + 1)) (i : RepresentationIndex (m + 1) (n + 1)) :
    a.representationAlpha b i ≠ ⊤ := by
  intro htop
  have hle := a.representationAlpha_le_halfGap b i
  rw [htop] at hle
  simp [representationHalfGap] at hle

/-- The finite rational value of `A_i(M, N)`. -/
noncomputable def representationAlphaValue (a : GoodBONG q L (m + 1))
    (b : GoodBONG r M (n + 1)) (i : RepresentationIndex (m + 1) (n + 1)) : ℚ :=
  (a.representationAlpha b i).untop (a.representationAlpha_ne_top b i)

@[simp]
theorem coe_representationAlphaValue (a : GoodBONG q L (m + 1))
    (b : GoodBONG r M (n + 1)) (i : RepresentationIndex (m + 1) (n + 1)) :
    (a.representationAlphaValue b i : WithTop ℚ) = a.representationAlpha b i :=
  WithTop.coe_untop _ _

/-- The first candidate in the exceptional value `S_{N+1} + A_{N+1}`. -/
noncomputable def terminalAdjustedPrimary (a : GoodBONG q L (m + 1))
    (b : GoodBONG r M (n + 1)) (hgap : n + 2 < m + 1) : WithTop ℚ :=
  ((a.order ⟨n + 2, hgap⟩ : Int) : ℚ) +
    a.truncatedPrefixDefect b (-1) (n + 3) (n + 1)

/-- The optional second candidate in `S_{N+1} + A_{N+1}`. -/
noncomputable def terminalAdjustedSecondary (a : GoodBONG q L (m + 1))
    (b : GoodBONG r M (n + 1)) (hinner : n + 3 < m + 1) : WithTop ℚ :=
  (((a.order ⟨n + 2, by omega⟩ + a.order ⟨n + 3, hinner⟩ - b.order ⟨n, by omega⟩ :
      Int) : ℚ) : WithTop ℚ) +
    a.truncatedPrefixDefect b 1 (n + 4) n

/-- Candidate set for the exceptional boundary value `S_{N+1} + A_{N+1}`. -/
noncomputable def terminalAdjustedCandidates (a : GoodBONG q L (m + 1))
    (b : GoodBONG r M (n + 1)) (hgap : n + 2 < m + 1) : Finset (WithTop ℚ) :=
  insert (a.terminalAdjustedPrimary b hgap)
    (if hinner : n + 3 < m + 1 then {a.terminalAdjustedSecondary b hinner} else ∅)

theorem terminalAdjustedCandidates_nonempty (a : GoodBONG q L (m + 1))
    (b : GoodBONG r M (n + 1)) (hgap : n + 2 < m + 1) :
    (a.terminalAdjustedCandidates b hgap).Nonempty :=
  ⟨a.terminalAdjustedPrimary b hgap, Finset.mem_insert_self _ _⟩

/-- Definition 4's exceptional quantity `S_{N+1} + A_{N+1}`. -/
noncomputable def terminalAdjustedAlpha (a : GoodBONG q L (m + 1))
    (b : GoodBONG r M (n + 1)) (hgap : n + 2 < m + 1) : WithTop ℚ :=
  (a.terminalAdjustedCandidates b hgap).min'
    (a.terminalAdjustedCandidates_nonempty b hgap)

/--
The quantity `S_i + A_i`, extended at `i = N + 1` by Definition 4's exceptional
boundary formula.  This makes condition (iii) uniform at the last possible index.
-/
noncomputable def centralAdjustedAlpha (a : GoodBONG q L (m + 1))
    (b : GoodBONG r M (n + 1))
    (i : CentralRepresentationIndex (m + 1) (n + 1)) : WithTop ℚ :=
  if hi : i.val ≤ n + 1 then
    (((b.order ⟨i.val - 1, by have := i.one_lt; have := hi; omega⟩ : Int) : ℚ) :
        WithTop ℚ) +
      (a.representationAlphaValue b (i.current hi) : WithTop ℚ)
  else
    a.terminalAdjustedAlpha b (by
      have := i.le_small_succ
      have := i.lt_large
      omega)

/-- Condition (i) in Beli (2006), Theorem 4.5. -/
def RepresentationOrderCondition (a : GoodBONG q L (m + 1))
    (b : GoodBONG r M (n + 1)) (hRank : n ≤ m) : Prop :=
  ∀ i : Fin (n + 1),
    a.order ⟨i.val, by have := i.isLt; have := hRank; omega⟩ ≤ b.order i ∨
      ∃ (hi0 : 0 < i.val) (hiLarge : i.val + 1 < m + 1),
        a.order ⟨i.val, by have := i.isLt; have := hRank; omega⟩ +
            a.order ⟨i.val + 1, hiLarge⟩ ≤
          b.order ⟨i.val - 1, by have := i.isLt; omega⟩ + b.order i

/-- Condition (ii): `d[a₁,ᵢ b₁,ᵢ] ≥ A_i` at every ordinary boundary. -/
noncomputable def RepresentationDefectCondition (a : GoodBONG q L (m + 1))
    (b : GoodBONG r M (n + 1)) : Prop :=
  ∀ i : RepresentationIndex (m + 1) (n + 1),
    (a.representationAlphaValue b i : WithTop ℚ) ≤
      a.truncatedPrefixDefect b 1 i.val i.val

/-- Condition (iii): the required one-step prefix representations. -/
noncomputable def CentralRepresentationConditions (a : GoodBONG q L (m + 1))
    (b : GoodBONG r M (n + 1)) : Prop :=
  ∀ i : CentralRepresentationIndex (m + 1) (n + 1),
    (b.order ⟨i.val - 2, by have := i.one_lt; have := i.le_small_succ; omega⟩ <
        a.order ⟨i.val, by have := i.lt_large; omega⟩ ∧
      ((2 * (ramificationIndex K : ℚ) +
          (a.order ⟨i.val - 1, by
            have := i.one_lt
            have := i.lt_large
            omega⟩ : ℚ) : ℚ) : WithTop ℚ) <
        ((a.representationAlphaValue b i.previous : ℚ) : WithTop ℚ) +
          a.centralAdjustedAlpha b i) →
      DiagonalRepresents
        (b.prefixValues (i.val - 1) (by have := i.le_small_succ; omega))
        (a.prefixValues i.val (by have := i.lt_large; omega))

/-- Condition (iv): the required two-step prefix representations. -/
noncomputable def LongRepresentationConditions (a : GoodBONG q L (m + 1))
    (b : GoodBONG r M (n + 1)) : Prop :=
  ∀ i : LongRepresentationIndex (m + 1) (n + 1),
    ((if hi : i.val ≤ n + 1 then
        a.order ⟨i.val + 1, i.succ_lt_large⟩ ≤
          b.order ⟨i.val - 1, by have := i.one_lt; have := hi; omega⟩
      else True) ∧
      b.order ⟨i.val - 2, by have := i.one_lt; have := i.le_small_succ; omega⟩ +
          2 * (ramificationIndex K : Int) <
        a.order ⟨i.val + 1, i.succ_lt_large⟩ ∧
      a.order ⟨i.val, by have := i.succ_lt_large; omega⟩ +
          2 * (ramificationIndex K : Int) ≤
        b.order ⟨i.val - 2, by have := i.one_lt; have := i.le_small_succ; omega⟩ +
          2 * (ramificationIndex K : Int)) →
      DiagonalRepresents
        (b.prefixValues (i.val - 1) (by have := i.le_small_succ; omega))
        (a.prefixValues (i.val + 1) (by have := i.succ_lt_large; omega))

end BONG.GoodBONG

/-- The four explicit conditions in Beli (2006), Theorem 4.5. -/
structure RepresentationConditions
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type w} [AddCommGroup W] [Module K W]
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W} {m n : Nat}
    (a : BONG.GoodBONG q L (m + 1)) (b : BONG.GoodBONG r M (n + 1))
    (hRank : n ≤ m) : Prop where
  orderCondition : a.RepresentationOrderCondition b hRank
  defectCondition : a.RepresentationDefectCondition b
  centralRepresentations : a.CentralRepresentationConditions b
  longRepresentations : a.LongRepresentationConditions b

/-!
The final equivalence is an explicit local-field interface.  Its proof requires
the full dyadic representation theorem developed by Beli from O'Meara's and
Riehm's local results.
-/

/-- The deep local representation theorem required to complete Theorem 4.5. -/
class GoodBONGRepresentationLaws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  represents_iff
    {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type w} [AddCommGroup W] [Module K W]
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W} {m n : Nat}
    (hRank : n ≤ m) (ambient : q.Represents r)
    (a : BONG.GoodBONG q L (m + 1)) (b : BONG.GoodBONG r M (n + 1)) :
    Lattice.Represents q r L M ↔ RepresentationConditions a b hRank

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {m n : Nat}
  [GoodBONGRepresentationLaws.{u, v, w} K]

/-- Beli's representation theorem, assuming its isolated local-field laws. -/
theorem represents_iff_representationConditions
    (hRank : n ≤ m) (ambient : q.Represents r)
    (a : BONG.GoodBONG q L (m + 1)) (b : BONG.GoodBONG r M (n + 1)) :
    Lattice.Represents q r L M ↔ RepresentationConditions a b hRank :=
  GoodBONGRepresentationLaws.represents_iff (K := K) hRank ambient a b

end Bong
