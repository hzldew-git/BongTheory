/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaFundamentalIdeals
import Bong.Lattice.OrthogonalDecompositionPrefix
import Bong.Lattice.DeterminantIsometry
import Bong.Bong.Beli2009ClassificationPropagation
import Bong.Bong.Representation
import Bong.QuadraticSpace.OrthogonalSum

/-!
# The intrinsic conditions in O'Meara 93:28

This file gives the three conditions of O'Meara's dyadic classification
theorem using actual Jordan prefixes, determinant units, fundamental ideals,
fundamental weights, and quadratic-space representations.  In particular,
none of the conditions is an uninterpreted proposition supplied by a law
class.

The theorem itself is proved in the subsequent classification module.  The
separation is useful because the necessity proof and Beli's translation both
consume these semantic conditions independently of the sufficiency
induction.
-/

namespace Bong

open Dyadic Module

namespace QuadraticSpace

universe u v w

variable {K : Type u} [Field K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]

/-- The canonical embedding of the left summand into an orthogonal sum. -/
def Representation.orthogonalSumInl
    (q : QuadraticSpace K V) (r : QuadraticSpace K W) :
    Representation q (q.orthogonalSum r) where
  toLinearMap :=
    { toFun := fun x ↦ (x, 0)
      map_add' := by intro x y; simp
      map_smul' := by intro c x; simp }
  injective := by
    intro x y h
    exact congrArg Prod.fst h
  map_bilin := by
    intro x y
    simp

/-- Every quadratic space embeds into an orthogonal extension of itself. -/
theorem embedsInto_orthogonalSum_left
    (q : QuadraticSpace K V) (r : QuadraticSpace K W) :
    EmbedsInto q (q.orthogonalSum r) :=
  ⟨Representation.orthogonalSumInl q r⟩

/-- An isometry followed by the canonical inclusion gives an embedding into
an orthogonal extension of the target. -/
theorem Isometry.embedsInto_orthogonalSum_target
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    (f : Isometry q r) (s : QuadraticSpace K K) :
    EmbedsInto q (r.orthogonalSum s) := by
  exact ⟨(Representation.orthogonalSumInl r s).trans f.toRepresentation⟩

end QuadraticSpace

namespace Lattice

universe u v w z

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {Z : Type z} [AddCommGroup Z] [Module K Z]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {t : Nat}

/-- Equality in the refined determinant square-class group implies
congruence modulo every coefficient ideal: after dividing by the witnessing
valuation-unit square, the error is literally zero. -/
theorem unitsCongruentModulo_of_unitSquareClass_eq
    (x y : Kˣ) (I : CoefficientIdeal (K := K))
    (h : unitSquareClass K x = unitSquareClass K y) :
    BONG.GoodBONG.UnitsCongruentModulo x y I := by
  change QuotientGroup.mk' (valuationUnitSquareSubgroup K) x =
    QuotientGroup.mk' (valuationUnitSquareSubgroup K) y at h
  rw [QuotientGroup.mk'_eq_mk'] at h
  rcases h with ⟨z, hz, hxy⟩
  rw [mem_valuationUnitSquareSubgroup_iff] at hz
  rcases hz with ⟨s, _, rfl⟩
  refine ⟨s, ?_⟩
  have hxyK := congrArg (fun a : Kˣ ↦ (a : K)) hxy
  have hquotient : (y : K) / (x : K) / (s : K) ^ 2 = 1 := by
    rw [← hxyK]
    change ((x : K) * (s : K) ^ 2) / (x : K) / (s : K) ^ 2 = 1
    field_simp [Units.ne_zero x, Units.ne_zero s]
  rw [hquotient, sub_self]
  exact I.zero_mem

namespace QuadraticSublattice

/-- Package the determinant unit as an invariant of the whole quadratic
sublattice.  Keeping the dependent carrier hidden behind this interface makes
equality transport between definitionally equal prefix sublattices stable. -/
noncomputable def refinedDeterminantUnit
    {q : QuadraticSpace K V} (C : QuadraticSublattice q) : Kˣ :=
  determinantUnit C.space C.lattice

/-- A representation of one quadratic sublattice by an orthogonal extension
of another.  This whole-sublattice interface avoids exposing carrier-dependent
types when exact suffix decompositions are transported. -/
noncomputable def EmbedsIntoOrthogonalSum
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    (C : QuadraticSublattice q) (D : QuadraticSublattice r)
    (s : QuadraticSpace K Z) : Prop :=
  QuadraticSpace.EmbedsInto C.space (D.space.orthogonalSum s)

end QuadraticSublattice

namespace JordanDecomposition

/-- The actual quadratic space underlying the prefix ending immediately
before the cut `k`. -/
noncomputable abbrev prefixSpace
    (J : JordanDecomposition q L (t + 1)) (k : Nat) :=
  (J.toOrthogonalDecomposition.prefixQuadraticSublattice k).space

/-- The actual lattice underlying the prefix ending immediately before the
cut `k`. -/
noncomputable abbrev prefixIntegralLattice
    (J : JordanDecomposition q L (t + 1)) (k : Nat) :=
  (J.toOrthogonalDecomposition.prefixQuadraticSublattice k).lattice

/-- The determinant unit of the `i`th proper Jordan-chain prefix.  Here the
zero-based boundary `i` corresponds to O'Meara's one-based prefix `L_(i+1)`.
-/
noncomputable def prefixDeterminantUnit
    (J : JordanDecomposition q L (t + 1)) (i : Fin t) : Kˣ :=
  (J.toOrthogonalDecomposition.prefixQuadraticSublattice
    (i.val + 1)).refinedDeterminantUnit

/-- The fractional ideal `4 a_i w_i⁻¹`, represented by its valuation
order `2e + ord(a_i) - ord(w_i)`. -/
noncomputable def fourNormOverWeightIdeal
    (J : JordanDecomposition q L (t + 1)) (i : Fin (t + 1)) :
    CoefficientIdeal (K := K) :=
  powerIdeal (K := K)
    (2 * (ramificationIndex K : Int) +
      ordUnit K (J.fundamentalNormGenerator i) -
        J.fundamentalWeightOrder i)

namespace SameFundamentalType

/-- The threshold ideal `4 a_i w_i⁻¹` depends only on the fundamental
type. -/
theorem fourNormOverWeightIdeal_eq
    {J : JordanDecomposition q L (t + 1)}
    {H : JordanDecomposition r M (t + 1)}
    (F : SameFundamentalType J H) (i : Fin (t + 1)) :
    H.fourNormOverWeightIdeal i = J.fourNormOverWeightIdeal i := by
  unfold fourNormOverWeightIdeal
  have hnorm :=
    fundamentalNormGenerator_order_eq (K := K) F i
  have hweight :=
    fundamentalWeightOrder_eq (K := K) F i
  rw [F.indexEquiv_apply_eq_self] at hnorm hweight
  rw [hnorm, hweight]

end SameFundamentalType

/-- O'Meara 93:28(i): the determinant quotient of every two corresponding
proper Jordan prefixes is congruent to one modulo the actual fundamental
ideal `f_i`, up to a square multiplier. -/
noncomputable def Omeara9328ConditionI
    (J : JordanDecomposition q L (t + 1))
    (H : JordanDecomposition r M (t + 1)) : Prop :=
  ∀ i : Fin t,
    BONG.GoodBONG.UnitsCongruentModulo
      (H.prefixDeterminantUnit i) (J.prefixDeterminantUnit i)
      (J.fundamentalIdeal i)

/-- O'Meara 93:28(ii): when `f_i ⊊ 4 a_(i+1) w_(i+1)⁻¹`, the
source prefix embeds into the target prefix with the next fundamental line
adjoined. -/
noncomputable def Omeara9328ConditionII
    (J : JordanDecomposition q L (t + 1))
    (H : JordanDecomposition r M (t + 1)) : Prop :=
  ∀ i : Fin t,
    J.fundamentalIdeal i <
        J.fourNormOverWeightIdeal (boundaryRightIndex i) →
      QuadraticSublattice.EmbedsIntoOrthogonalSum
        (J.toOrthogonalDecomposition.prefixQuadraticSublattice (i.val + 1))
        (H.toOrthogonalDecomposition.prefixQuadraticSublattice (i.val + 1))
        (QuadraticSpace.scaledLine
          (J.fundamentalNormGenerator (boundaryRightIndex i)))

/-- O'Meara 93:28(iii): when `f_i ⊊ 4 a_i w_i⁻¹`, the source
prefix embeds into the target prefix with the current fundamental line
adjoined. -/
noncomputable def Omeara9328ConditionIII
    (J : JordanDecomposition q L (t + 1))
    (H : JordanDecomposition r M (t + 1)) : Prop :=
  ∀ i : Fin t,
    J.fundamentalIdeal i <
        J.fourNormOverWeightIdeal (boundaryLeftIndex i) →
      QuadraticSublattice.EmbedsIntoOrthogonalSum
        (J.toOrthogonalDecomposition.prefixQuadraticSublattice (i.val + 1))
        (H.toOrthogonalDecomposition.prefixQuadraticSublattice (i.val + 1))
        (QuadraticSpace.scaledLine
          (J.fundamentalNormGenerator (boundaryLeftIndex i)))

/-- The conjunction of the three semantic conditions in O'Meara 93:28.
Equality of fundamental type remains an explicit hypothesis of the theorem,
not a field of this definition. -/
noncomputable def Omeara9328Conditions
    (J : JordanDecomposition q L (t + 1))
    (H : JordanDecomposition r M (t + 1)) : Prop :=
  J.Omeara9328ConditionI H ∧ J.Omeara9328ConditionII H ∧
    J.Omeara9328ConditionIII H

/-- Corresponding prefixes of a transported Jordan decomposition satisfy
the determinant congruence in 93:28(i). -/
theorem omeara9328ConditionI_mapIsometry
    (J : JordanDecomposition q L (t + 1))
    (f : Lattice.Isometry q r L M) :
    J.Omeara9328ConditionI (J.mapIsometry f) := by
  intro i
  apply unitsCongruentModulo_of_unitSquareClass_eq
  change determinantClass
      ((J.mapIsometry f).prefixSpace (i.val + 1))
      ((J.mapIsometry f).prefixIntegralLattice (i.val + 1)) =
    determinantClass (J.prefixSpace (i.val + 1))
      (J.prefixIntegralLattice (i.val + 1))
  exact (determinantClass_eq_of_isometry
    (J.toOrthogonalDecomposition.prefixLatticeIsometry f
      (i.val + 1))).symm

/-- Corresponding prefixes of a transported Jordan decomposition satisfy
93:28(ii); the determinant/ideal trigger is not needed because the prefixes
are already isometric. -/
theorem omeara9328ConditionII_mapIsometry
    (J : JordanDecomposition q L (t + 1))
    (f : Lattice.Isometry q r L M) :
    J.Omeara9328ConditionII (J.mapIsometry f) := by
  intro i _
  let g := J.toOrthogonalDecomposition.prefixLatticeIsometry f
    (i.val + 1)
  exact g.toQuadraticSpaceIsometry.embedsInto_orthogonalSum_target
    (QuadraticSpace.scaledLine
      (J.fundamentalNormGenerator (boundaryRightIndex i)))

/-- Corresponding prefixes of a transported Jordan decomposition satisfy
93:28(iii). -/
theorem omeara9328ConditionIII_mapIsometry
    (J : JordanDecomposition q L (t + 1))
    (f : Lattice.Isometry q r L M) :
    J.Omeara9328ConditionIII (J.mapIsometry f) := by
  intro i _
  let g := J.toOrthogonalDecomposition.prefixLatticeIsometry f
    (i.val + 1)
  exact g.toQuadraticSpaceIsometry.embedsInto_orthogonalSum_target
    (QuadraticSpace.scaledLine
      (J.fundamentalNormGenerator (boundaryLeftIndex i)))

/-- The complete semantic 93:28 conditions hold for the Jordan splitting
obtained by transporting a splitting along an integral isometry.  This is the
easy, decomposition-matched part of the necessity proof; independence from
the chosen target Jordan splitting is established in the necessity module.
-/
theorem omeara9328Conditions_mapIsometry
    (J : JordanDecomposition q L (t + 1))
    (f : Lattice.Isometry q r L M) :
    J.Omeara9328Conditions (J.mapIsometry f) :=
  ⟨J.omeara9328ConditionI_mapIsometry f,
    J.omeara9328ConditionII_mapIsometry f,
    J.omeara9328ConditionIII_mapIsometry f⟩

end JordanDecomposition

end Lattice

end Bong
