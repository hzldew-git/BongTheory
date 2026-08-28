/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma96ProjectionModel
import Bong.Bong.PrefixIsometry
import Bong.Bong.SegmentTransport

/-!
# Beli (2019), Lemma 9.6: the ternary projected model

At rank three the initial ternary block is the whole target lattice.  Hence
the bad-BONG construction does not need the Corollary 4.4 split or a fourth
coordinate: the integral unary--binary normal form is already a normal form
of the complete lattice.  Projecting its matched unary coordinate leaves the
canonical binary model directly.
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG.Beli2019Lemma96MatchedNormalFormData

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}
  [laws : DyadicDiscriminantClassLaws K]
  {a : GoodBONG q L 3} {b : GoodBONG r M 3}

/-! The initial-three carrier is the whole ambient space at rank three. -/
theorem initialThreePrefix_carrier_eq_top_rankThree
    (a : GoodBONG q L 3) :
    a.lemma96InitialThreePrefix.carrier = (⊤ : Submodule K V) := by
  let whole := BONG.SegmentWitness.whole a.toBONG
  calc
    a.lemma96InitialThreePrefix.carrier =
        a.toBONG.segmentCarrier 0 3 (by omega) :=
      a.lemma96InitialThreePrefix.carrier_eq_segmentCarrier
    _ = whole.carrier := whole.carrier_eq_segmentCarrier.symm
    _ = ⊤ := rfl

set_option maxHeartbeats 300000 in
-- The whole-prefix isometry carries a large dependent restricted-space type.
/-- The full target lattice is exactly its canonical initial-three
restriction. -/
noncomputable def toInitialThreeIsometryRankThree
    (a : GoodBONG q L 3) :
    Lattice.Isometry q
      (q.restrict a.lemma96InitialThreePrefix.carrier
        a.lemma96InitialThreePrefix.nondegenerate)
      L a.lemma96InitialThreePrefix.lattice := by
  let hcarrier := initialThreePrefix_carrier_eq_top_rankThree a
  let e : V ≃ₗ[K] a.lemma96InitialThreePrefix.carrier :=
    Submodule.topEquiv.symm.trans
      (LinearEquiv.ofEq (⊤ : Submodule K V)
        a.lemma96InitialThreePrefix.carrier hcarrier.symm)
  refine
    { toLinearEquiv := e
      map_bilin := ?_
      map_mem := ?_ }
  · intro x y
    change q.bilin ((e x : a.lemma96InitialThreePrefix.carrier) : V)
        ((e y : a.lemma96InitialThreePrefix.carrier) : V) = q.bilin x y
    simp [e]
  · intro x
    change x ∈ L ↔ e x ∈ a.lemma96InitialThreePrefix.lattice
    rw [a.lemma96InitialThreePrefix.mem_lattice_iff_parent]
    change x ∈ L ↔ ((e x : a.lemma96InitialThreePrefix.carrier) : V) ∈ L
    simp [e]

/-- The complete ternary target lattice in the unary--binary coordinates
of Lemma 9.5. -/
noncomputable def fullModelIsometryRankThree
    (D : Beli2019Lemma96MatchedNormalFormData a b) :
    Lattice.Isometry q
      (unaryBinaryModelSpace D.normalForm.head D.normalForm.first
        D.normalForm.second D.normalForm.admissible)
      L (unaryBinaryModelLattice (K := K)) :=
  (toInitialThreeIsometryRankThree a).trans D.normalForm.toIsometry

set_option maxHeartbeats 1500000 in
-- Mapping a recursive BONG elaborates the induced projected tail type.
/-- Pull the complete exceptional ternary BONG back to the actual target
lattice.  Its recursive tail already lives on the required projected
lattice, so no separate dependent transport of orthogonal complements is
needed. -/
noncomputable def exceptionalBONGrankThree
    (D : Beli2019Lemma96MatchedNormalFormData a b) : BONG V q L 3 :=
  (exceptionalTernaryModelBONG (K := K) (a := a) (b := b) D).mapLatticeIsometry
    (fullModelIsometryRankThree (K := K) (a := a) (b := b) D).symm

/-- The actual bad-BONG head. -/
noncomputable def targetHeadRankThree
    (D : Beli2019Lemma96MatchedNormalFormData a b) : V :=
  D.exceptionalBONGrankThree.head

/-- Pullback along the whole-lattice isometry preserves the matched first
diagonal value. -/
@[simp]
theorem exceptionalBONGrankThree_value_zero
    (D : Beli2019Lemma96MatchedNormalFormData a b) :
    D.exceptionalBONGrankThree.value 0 = b.value 0 := by
  unfold exceptionalBONGrankThree
  rw [BONG.value_mapLatticeIsometry]
  exact D.exceptionalTernaryModelBONG_value_zero

/-- The bad-BONG head is a norm generator by construction. -/
theorem targetHeadRankThree_isNormGenerator
    (D : Beli2019Lemma96MatchedNormalFormData a b) :
    Lattice.IsNormGenerator q L D.targetHeadRankThree :=
  D.exceptionalBONGrankThree.head_isNormGenerator

/-- The bad-BONG head is anisotropic. -/
theorem targetHeadRankThree_anisotropic
    (D : Beli2019Lemma96MatchedNormalFormData a b) :
    q.IsAnisotropic D.targetHeadRankThree :=
  D.exceptionalBONGrankThree.head_isAnisotropic

/-- The recursive binary tail of the bad ternary BONG is automatically
good: the condition `R_i ≤ R_(i+2)` is vacuous in rank two. -/
noncomputable def projectedTailGoodBONGrankThree
    (D : Beli2019Lemma96MatchedNormalFormData a b) :
    GoodBONG
      (q.orthogonalSpace D.targetHeadRankThree
        D.targetHeadRankThree_anisotropic)
      (L.projectedLattice q D.targetHeadRankThree
        D.targetHeadRankThree_anisotropic) 2 where
  toBONG := D.exceptionalBONGrankThree.tail
  good := by
    intro i hi
    omega

@[simp]
theorem projectedTailGoodBONGrankThree_order_zero
    (D : Beli2019Lemma96MatchedNormalFormData a b) :
    D.projectedTailGoodBONGrankThree.order (0 : Fin 2) =
      a.order (0 : Fin 3) +
        (2 * (ramificationIndex K : Int) - 1) := by
  change D.exceptionalBONGrankThree.tail.order (0 : Fin 2) = _
  rw [BONG.order_tail]
  unfold exceptionalBONGrankThree
  rw [BONG.order_mapLatticeIsometry]
  rw [← D.exceptionalTernaryModelBONG.order_tail (0 : Fin 2)]
  change D.projectedUnaryBinaryBONG.order (0 : Fin 2) = _
  unfold projectedUnaryBinaryBONG
  rw [BONG.order_mapLatticeIsometry,
    binaryDiagonalModelBONG_order_zero, D.normalForm.first_order]

@[simp]
theorem projectedTailGoodBONGrankThree_order_one
    (D : Beli2019Lemma96MatchedNormalFormData a b) :
    D.projectedTailGoodBONGrankThree.order (1 : Fin 2) =
      a.order (0 : Fin 3) - 1 := by
  change D.exceptionalBONGrankThree.tail.order (1 : Fin 2) = _
  rw [BONG.order_tail]
  unfold exceptionalBONGrankThree
  rw [BONG.order_mapLatticeIsometry]
  rw [← D.exceptionalTernaryModelBONG.order_tail (1 : Fin 2)]
  change D.projectedUnaryBinaryBONG.order (1 : Fin 2) = _
  unfold projectedUnaryBinaryBONG
  rw [BONG.order_mapLatticeIsometry,
    binaryDiagonalModelBONG_order_one, D.normalForm.second_order]

end BONG.GoodBONG.Beli2019Lemma96MatchedNormalFormData

end Bong
