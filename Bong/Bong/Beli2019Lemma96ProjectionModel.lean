/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma96NormalForm
import Bong.Bong.Beli2019CanonicalApproximation
import Bong.Bong.BinaryDiagonalModelBONG
import Bong.Bong.DiagonalRepresentationCons
import Bong.Bong.GoodMap
import Bong.Bong.PrefixIsometry
import Bong.Bong.TwoBlockProductIsometry
import Bong.Bong.Beli2019Lemma710BONGProduct
import Bong.Bong.Beli2019Lemma710ProjectionProduct
import Bong.Bong.BeliCorollary44ThreeBlockProof
import Bong.Bong.Beli2019Lemma96TailRepresentation
import Bong.Lattice.OrthogonalProductIsometry
import Bong.Lattice.ProjectedIsometry

/-!
# Beli (2019), Lemma 9.6: the projected normal-form model

The matched unary vector lies in the first ternary block.  Once Corollary
4.4 splits that block from the remaining BONG segment, the whole target
lattice is isometric to

`(<head> ⊥ [first,second]) ⊥ suffix`.

The isometry below remembers the exact image of the matched head.  Projecting
along it deletes the unary factor and leaves the concrete product of the
binary normal-form lattice and the unchanged suffix lattice.
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG.Beli2019Lemma96MatchedNormalFormData

section InitialThreeGeometry

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {T : Nat}
  [laws : DyadicDiscriminantClassLaws K]
  {a : GoodBONG q L (T + 3)} {b : GoodBONG r M (T + 3)}

/-- Local high-level form of the fact that a lattice isometry transports a
norm generator.  It is kept here to avoid invalidating the foundational
lattice layer during the Lemma 9.6 development. -/
theorem isNormGenerator_mapLatticeIsometry
    {X : Type v} [AddCommGroup X] [Module K X]
    {Y : Type w} [AddCommGroup Y] [Module K Y]
    {qX : QuadraticSpace K X} {qY : QuadraticSpace K Y}
    {LX : Lattice K X} {LY : Lattice K Y} {x : X}
    (generator : Lattice.IsNormGenerator qX LX x)
    (f : Lattice.Isometry qX qY LX LY) :
    Lattice.IsNormGenerator qY LY (f.toLinearEquiv x) := by
  constructor
  · exact (f.map_mem x).mp generator.mem
  · calc
      Lattice.normIdeal qY LY =
          Lattice.normIdeal qY (Lattice.map f.toLinearEquiv LX) :=
        congrArg (Lattice.normIdeal qY) f.map_eq.symm
      _ = Lattice.normIdeal qX LX :=
        Lattice.normIdeal_map_isometry f.toQuadraticSpaceIsometry LX
      _ = Lattice.principalIdeal (K := K) (qX.quadratic x) :=
        generator.normIdeal_eq
      _ = Lattice.principalIdeal (K := K)
          (qY.quadratic (f.toLinearEquiv x)) :=
        congrArg (Lattice.principalIdeal (K := K))
          (f.map_quadratic x).symm

/-- Reindex a diagonal representation along equal source and target
dimensions.  The coefficient order is unchanged because `Fin.cast` preserves
the underlying natural-number index. -/
theorem diagonalRepresents_castLengths
    {m n m' n' : Nat} {source : Fin m → K} {target : Fin n → K}
    (hm : m = m') (hn : n = n')
    (h : DiagonalRepresents source target) :
    DiagonalRepresents
      (fun i : Fin m' => source (Fin.cast hm.symm i))
      (fun i : Fin n' => target (Fin.cast hn.symm i)) := by
  subst m'
  subst n'
  convert h using 1 <;> funext i <;> congr 1

/-- Identify the left block supplied by Corollary 4.4 with the canonical
prefix used by the normal-form theorem, then apply the normal-form
isometry. -/
noncomputable def splitPrefixIsometry
    (D : Beli2019Lemma96MatchedNormalFormData a b)
    (S : a.toBONG.TwoBlockSplitWitness 3 (by omega)) :
    Lattice.Isometry
      (q.restrict S.left.carrier S.left.nondegenerate)
      (unaryBinaryModelSpace D.normalForm.head D.normalForm.first
        D.normalForm.second D.normalForm.admissible)
      S.left.lattice (unaryBinaryModelLattice (K := K)) :=
  (S.leftPrefixWitness.latticeIsometry
      a.lemma96InitialThreePrefix).trans
    D.normalForm.toIsometry

/-- The full target lattice in unary--binary normal-form coordinates, with
the suffix block unchanged. -/
noncomputable def fullModelIsometry
    (D : Beli2019Lemma96MatchedNormalFormData a b)
    (S : a.toBONG.TwoBlockSplitWitness 3 (by omega)) :
    Lattice.Isometry q
      ((unaryBinaryModelSpace D.normalForm.head D.normalForm.first
          D.normalForm.second D.normalForm.admissible).orthogonalSum
        (q.restrict S.right.carrier S.right.nondegenerate))
      L
      (Lattice.product (unaryBinaryModelLattice (K := K))
        S.right.lattice) :=
  S.toProductLatticeIsometry.symm.trans
    ((D.splitPrefixIsometry S).orthogonalProductBasic
      (Lattice.Isometry.refl
        (q.restrict S.right.carrier S.right.nondegenerate)
        S.right.lattice))

/-- The unary normal-form vector, expressed in the left carrier selected by
the split witness. -/
noncomputable def splitLocalHead
    (D : Beli2019Lemma96MatchedNormalFormData a b)
    (S : a.toBONG.TwoBlockSplitWitness 3 (by omega)) :
    S.left.carrier :=
  (S.leftPrefixWitness.latticeIsometry
      a.lemma96InitialThreePrefix).toLinearEquiv.symm
    D.normalForm.localHead

/-- Changing between the two prefix witnesses does not change the ambient
unary vector. -/
theorem coe_splitLocalHead
    (D : Beli2019Lemma96MatchedNormalFormData a b)
    (S : a.toBONG.TwoBlockSplitWitness 3 (by omega)) :
    (D.splitLocalHead S : V) = D.normalForm.ambientHead := by
  let f := S.leftPrefixWitness.latticeIsometry
    a.lemma96InitialThreePrefix
  have h := BONG.PrefixWitness.coe_latticeIsometry_apply
    S.leftPrefixWitness a.lemma96InitialThreePrefix
      (f.toLinearEquiv.symm D.normalForm.localHead)
  rw [f.toLinearEquiv.apply_symm_apply] at h
  exact h.symm

/-- The matched head as an element of the split's left carrier. -/
noncomputable def splitMatchedHead
    (D : Beli2019Lemma96MatchedNormalFormData a b)
    (S : a.toBONG.TwoBlockSplitWitness 3 (by omega)) :
    S.left.carrier :=
  (D.matchedHead.scalar : K) • D.splitLocalHead S

@[simp]
theorem coe_splitMatchedHead
    (D : Beli2019Lemma96MatchedNormalFormData a b)
    (S : a.toBONG.TwoBlockSplitWitness 3 (by omega)) :
    (D.splitMatchedHead S : V) = D.matchedHead.vector := by
  rw [D.matchedHead.vector_eq]
  change (D.matchedHead.scalar : K) • (D.splitLocalHead S : V) =
    (D.matchedHead.scalar : K) • D.normalForm.ambientHead
  rw [D.coe_splitLocalHead S]

/-- In full normal-form coordinates the exact matched head is the scalar
multiple of the unary coordinate, with zero suffix component. -/
@[simp]
theorem fullModelIsometry_matchedHead
    (D : Beli2019Lemma96MatchedNormalFormData a b)
    (S : a.toBONG.TwoBlockSplitWitness 3 (by omega)) :
    (D.fullModelIsometry S).toLinearEquiv D.matchedHead.vector =
      (((D.matchedHead.scalar : K), (0 : Fin 2 → K)),
        (0 : S.right.carrier)) := by
  rw [← D.coe_splitMatchedHead S]
  change
    (((D.splitPrefixIsometry S).toLinearEquiv
        ((S.toAmbientLinearEquiv).symm
          (D.splitMatchedHead S : V)).1),
      ((S.toAmbientLinearEquiv).symm
        (D.splitMatchedHead S : V)).2) = _
  have hsplit :
      (S.toAmbientLinearEquiv).symm (D.splitMatchedHead S : V) =
        (D.splitMatchedHead S, 0) := by
    apply S.toAmbientLinearEquiv.injective
    rw [LinearEquiv.apply_symm_apply]
    change (D.splitMatchedHead S : V) =
      (D.splitMatchedHead S : V) + 0
    simp
  rw [hsplit]
  change
    (((D.splitPrefixIsometry S).toLinearEquiv
        ((D.matchedHead.scalar : K) • D.splitLocalHead S)), 0) = _
  rw [map_smul]
  change
    ((D.matchedHead.scalar : K) •
        D.normalForm.toIsometry.toLinearEquiv
          ((S.leftPrefixWitness.latticeIsometry
            a.lemma96InitialThreePrefix).toLinearEquiv
              (D.splitLocalHead S)), 0) = _
  rw [show
      (S.leftPrefixWitness.latticeIsometry
          a.lemma96InitialThreePrefix).toLinearEquiv
          (D.splitLocalHead S) = D.normalForm.localHead by
        exact LinearEquiv.apply_symm_apply _ _]
  change
    ((D.matchedHead.scalar : K) •
        D.normalForm.toIsometry.toLinearEquiv
          (D.normalForm.toIsometry.toLinearEquiv.symm
            ((1 : K), (0 : Fin 2 → K))), 0) = _
  rw [LinearEquiv.apply_symm_apply]
  ext <;> simp

/-- The scalar multiple of the unary basis vector is anisotropic.  This is
the one-dimensional input used to delete the unary factor after projection. -/
theorem unaryScalar_anisotropic
    (D : Beli2019Lemma96MatchedNormalFormData a b) :
    (QuadraticSpace.rescaleUnit D.normalForm.head
        (QuadraticSpace.line K)).IsAnisotropic
      (D.matchedHead.scalar : K) := by
  simp [QuadraticSpace.IsAnisotropic]

/-- The orthogonal complement of a nonzero vector in the unary factor is
zero-dimensional. -/
theorem unaryScalar_orthogonal_subsingleton
    (D : Beli2019Lemma96MatchedNormalFormData a b) :
    Subsingleton
      ((QuadraticSpace.rescaleUnit D.normalForm.head
          (QuadraticSpace.line K)).vectorOrthogonal
        (D.matchedHead.scalar : K)) := by
  let qHead := QuadraticSpace.rescaleUnit D.normalForm.head
    (QuadraticSpace.line K)
  have hdim := qHead.finrank_vectorOrthogonal D.unaryScalar_anisotropic
  have hzero : Module.finrank K
      (qHead.vectorOrthogonal (D.matchedHead.scalar : K)) = 0 := by
    simp only [Module.finrank_self] at hdim
    omega
  change Subsingleton
    (qHead.vectorOrthogonal (D.matchedHead.scalar : K))
  exact Module.finrank_zero_iff.mp hzero

/-- Projecting the unary--binary normal-form lattice along the matched unary
vector leaves exactly the concrete binary diagonal lattice. -/
noncomputable def projectedUnaryBinaryToBinary
    (D : Beli2019Lemma96MatchedNormalFormData a b) :
    Lattice.Isometry
      ((unaryBinaryModelSpace D.normalForm.head D.normalForm.first
          D.normalForm.second D.normalForm.admissible).orthogonalSpace
        ((D.matchedHead.scalar : K), (0 : Fin 2 → K))
        D.unaryScalar_anisotropic.orthogonalSum_inl)
      (binaryDiagonalModelSpace D.normalForm.first D.normalForm.second
        D.normalForm.admissible)
      ((unaryBinaryModelLattice (K := K)).projectedLattice
        (unaryBinaryModelSpace D.normalForm.head D.normalForm.first
          D.normalForm.second D.normalForm.admissible)
        ((D.matchedHead.scalar : K), (0 : Fin 2 → K))
        D.unaryScalar_anisotropic.orthogonalSum_inl)
      (binaryDiagonalModelLattice (K := K)) :=
  (Lattice.projectedOrthogonalProductIsometry
      (q := QuadraticSpace.rescaleUnit D.normalForm.head
        (QuadraticSpace.line K))
      (r := binaryDiagonalModelSpace D.normalForm.first D.normalForm.second
        D.normalForm.admissible)
      (L := unaryModelLattice (K := K))
      (M := binaryDiagonalModelLattice (K := K))
      D.unaryScalar_anisotropic).trans
    (Lattice.orthogonalProductSndIsometryOfSubsingleton
      ((QuadraticSpace.rescaleUnit D.normalForm.head
        (QuadraticSpace.line K)).orthogonalSpace
          (D.matchedHead.scalar : K) D.unaryScalar_anisotropic)
      (binaryDiagonalModelSpace D.normalForm.first D.normalForm.second
        D.normalForm.admissible)
      ((unaryModelLattice (K := K)).projectedLattice
        (QuadraticSpace.rescaleUnit D.normalForm.head
          (QuadraticSpace.line K))
        (D.matchedHead.scalar : K) D.unaryScalar_anisotropic)
      (binaryDiagonalModelLattice (K := K))
      D.unaryScalar_orthogonal_subsingleton)

/-- The matched coordinate is anisotropic in the unary--binary factor. -/
theorem unaryBinaryMatchedHead_anisotropic
    (D : Beli2019Lemma96MatchedNormalFormData a b) :
    (unaryBinaryModelSpace D.normalForm.head D.normalForm.first
        D.normalForm.second D.normalForm.admissible).IsAnisotropic
      ((D.matchedHead.scalar : K), (0 : Fin 2 → K)) :=
  D.unaryScalar_anisotropic.orthogonalSum_inl

/-- The literal scalar unary coordinate is a norm generator of the concrete
unary--binary normal-form lattice. -/
theorem unaryBinaryMatchedHead_isNormGenerator
    (D : Beli2019Lemma96MatchedNormalFormData a b) :
    Lattice.IsNormGenerator
      (unaryBinaryModelSpace D.normalForm.head D.normalForm.first
        D.normalForm.second D.normalForm.admissible)
      (unaryBinaryModelLattice (K := K))
      ((D.matchedHead.scalar : K), (0 : Fin 2 → K)) := by
  let f := D.normalForm.toIsometry
  have hscaled := D.normalForm.localHead_isNormGenerator.smul_valuationUnit
    D.matchedHead.scalar D.matchedHead.scalar_isValuationUnit
  have hmapped := isNormGenerator_mapLatticeIsometry hscaled f
  have hcoordinate :
      f.toLinearEquiv
          ((D.matchedHead.scalar : K) • D.normalForm.localHead) =
        ((D.matchedHead.scalar : K), (0 : Fin 2 → K)) := by
    change f.toLinearEquiv
        ((D.matchedHead.scalar : K) •
          f.toLinearEquiv.symm ((1 : K), (0 : Fin 2 → K))) = _
    rw [map_smul, LinearEquiv.apply_symm_apply]
    ext <;> simp
  rw [hcoordinate] at hmapped
  exact hmapped

/-- The canonical binary BONG, pulled back to the projected unary--binary
lattice along the explicit projection isometry. -/
noncomputable def projectedUnaryBinaryBONG
    (D : Beli2019Lemma96MatchedNormalFormData a b) :
    BONG
      ((unaryBinaryModelSpace D.normalForm.head D.normalForm.first
        D.normalForm.second D.normalForm.admissible).vectorOrthogonal
          ((D.matchedHead.scalar : K), (0 : Fin 2 → K)))
      ((unaryBinaryModelSpace D.normalForm.head D.normalForm.first
        D.normalForm.second D.normalForm.admissible).orthogonalSpace
          ((D.matchedHead.scalar : K), (0 : Fin 2 → K))
          D.unaryBinaryMatchedHead_anisotropic)
      ((unaryBinaryModelLattice (K := K)).projectedLattice
        (unaryBinaryModelSpace D.normalForm.head D.normalForm.first
          D.normalForm.second D.normalForm.admissible)
        ((D.matchedHead.scalar : K), (0 : Fin 2 → K))
        D.unaryBinaryMatchedHead_anisotropic) 2 :=
  (binaryDiagonalModelBONG D.normalForm.first D.normalForm.second
    D.normalForm.admissible).mapLatticeIsometry
      D.projectedUnaryBinaryToBinary.symm

/-- The rank-three BONG in normal-form coordinates whose head is the exact
source value and whose tail is the canonical binary projected block. -/
noncomputable def exceptionalTernaryModelBONG
    (D : Beli2019Lemma96MatchedNormalFormData a b) :
    BONG (K × (Fin 2 → K))
      (unaryBinaryModelSpace D.normalForm.head D.normalForm.first
        D.normalForm.second D.normalForm.admissible)
      (unaryBinaryModelLattice (K := K)) 3 :=
  BONG.cons
    ((D.matchedHead.scalar : K), (0 : Fin 2 → K))
    D.unaryBinaryMatchedHead_isNormGenerator
    D.unaryBinaryMatchedHead_anisotropic
    D.projectedUnaryBinaryBONG

/-- The original first-three BONG transported to the same normal-form
coordinates. -/
noncomputable def originalTernaryModelBONG
    (D : Beli2019Lemma96MatchedNormalFormData a b) :
    BONG (K × (Fin 2 → K))
      (unaryBinaryModelSpace D.normalForm.head D.normalForm.first
        D.normalForm.second D.normalForm.admissible)
      (unaryBinaryModelLattice (K := K)) 3 :=
  a.lemma96InitialThree.toBONG.mapLatticeIsometry D.normalForm.toIsometry

/-- The exceptional ternary model head has exactly the source head value. -/
@[simp]
theorem exceptionalTernaryModelBONG_value_zero
    (D : Beli2019Lemma96MatchedNormalFormData a b) :
    D.exceptionalTernaryModelBONG.value 0 = b.value 0 := by
  rw [D.exceptionalTernaryModelBONG.value_zero_eq_quadratic_head]
  have hcoordinate :
      D.normalForm.toIsometry.toLinearEquiv
          ((D.matchedHead.scalar : K) • D.normalForm.localHead) =
        ((D.matchedHead.scalar : K), (0 : Fin 2 → K)) := by
    change D.normalForm.toIsometry.toLinearEquiv
        ((D.matchedHead.scalar : K) •
          D.normalForm.toIsometry.toLinearEquiv.symm
            ((1 : K), (0 : Fin 2 → K))) = _
    rw [map_smul, LinearEquiv.apply_symm_apply]
    ext <;> simp
  have hquadratic := D.normalForm.toIsometry.map_quadratic
    ((D.matchedHead.scalar : K) • D.normalForm.localHead)
  rw [hcoordinate] at hquadratic
  change
    (unaryBinaryModelSpace D.normalForm.head D.normalForm.first
      D.normalForm.second D.normalForm.admissible).quadratic
        ((D.matchedHead.scalar : K), (0 : Fin 2 → K)) = b.value 0
  rw [hquadratic]
  change q.quadratic
      ((D.matchedHead.scalar : K) • D.normalForm.ambientHead) = b.value 0
  rw [← D.matchedHead.vector_eq]
  exact D.matchedHead.quadratic_eq

/-- The two tail values of the exceptional ternary model are the canonical
binary diagonal-model values. -/
@[simp]
theorem exceptionalTernaryModelBONG_value_succ
    (D : Beli2019Lemma96MatchedNormalFormData a b) (i : Fin 2) :
    D.exceptionalTernaryModelBONG.value i.succ =
      (binaryDiagonalModelBONG D.normalForm.first D.normalForm.second
        D.normalForm.admissible).value i := by
  simp only [exceptionalTernaryModelBONG, BONG.value_cons_succ,
    projectedUnaryBinaryBONG, BONG.value_mapLatticeIsometry]

/-- The original ternary diagonal form is represented by the exceptional
matched-head ternary form. -/
theorem initialThree_diagonalRepresents_exceptional
    (D : Beli2019Lemma96MatchedNormalFormData a b) :
    DiagonalRepresents a.lemma96InitialThree.toBONG.value
      (Fin.cons (b.value 0)
        (binaryDiagonalModelBONG D.normalForm.first D.normalForm.second
          D.normalForm.admissible).value) := by
  have h := D.originalTernaryModelBONG.diagonalRepresents_values
    D.exceptionalTernaryModelBONG
  convert h using 1
  · funext i
    simp only [originalTernaryModelBONG, BONG.value_mapLatticeIsometry]
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using D.exceptionalTernaryModelBONG_value_zero
    · simpa using D.exceptionalTernaryModelBONG_value_succ j

/-- The exact matched coordinate is anisotropic in the complete normal-form
product. -/
theorem fullModelMatchedHead_anisotropic
    (D : Beli2019Lemma96MatchedNormalFormData a b)
    (S : a.toBONG.TwoBlockSplitWitness 3 (by omega)) :
    ((unaryBinaryModelSpace D.normalForm.head D.normalForm.first
        D.normalForm.second D.normalForm.admissible).orthogonalSum
      (q.restrict S.right.carrier S.right.nondegenerate)).IsAnisotropic
      (((D.matchedHead.scalar : K), (0 : Fin 2 → K)),
        (0 : S.right.carrier)) :=
  D.unaryBinaryMatchedHead_anisotropic.orthogonalSum_inl

/-- Project the full target lattice through its normal-form isometry.  The
target axis is stated using the literal unary coordinate, rather than an
opaque isometric image. -/
noncomputable def projectedFullModelIsometry
    (D : Beli2019Lemma96MatchedNormalFormData a b)
    (S : a.toBONG.TwoBlockSplitWitness 3 (by omega)) :
    Lattice.Isometry
      (q.orthogonalSpace D.matchedHead.vector D.matchedHead.anisotropic)
      (((unaryBinaryModelSpace D.normalForm.head D.normalForm.first
          D.normalForm.second D.normalForm.admissible).orthogonalSum
        (q.restrict S.right.carrier S.right.nondegenerate)).orthogonalSpace
        (((D.matchedHead.scalar : K), (0 : Fin 2 → K)),
          (0 : S.right.carrier)) (D.fullModelMatchedHead_anisotropic S))
      (L.projectedLattice q D.matchedHead.vector D.matchedHead.anisotropic)
      ((Lattice.product (unaryBinaryModelLattice (K := K))
          S.right.lattice).projectedLattice
        ((unaryBinaryModelSpace D.normalForm.head D.normalForm.first
          D.normalForm.second D.normalForm.admissible).orthogonalSum
          (q.restrict S.right.carrier S.right.nondegenerate))
        (((D.matchedHead.scalar : K), (0 : Fin 2 → K)),
          (0 : S.right.carrier)) (D.fullModelMatchedHead_anisotropic S)) := by
  exact (D.fullModelIsometry S).projectedAlongImageEq
    D.matchedHead.vector D.matchedHead.anisotropic
    (((D.matchedHead.scalar : K), (0 : Fin 2 → K)),
      (0 : S.right.carrier))
    (D.fullModelMatchedHead_anisotropic S)
    (D.fullModelIsometry_matchedHead S)

/-- The projected target lattice is concretely the product of the explicit
binary normal-form lattice and the unchanged suffix lattice. -/
noncomputable def projectedToBinarySuffix
    (D : Beli2019Lemma96MatchedNormalFormData a b)
    (S : a.toBONG.TwoBlockSplitWitness 3 (by omega)) :
    Lattice.Isometry
      (q.orthogonalSpace D.matchedHead.vector D.matchedHead.anisotropic)
      ((binaryDiagonalModelSpace D.normalForm.first D.normalForm.second
          D.normalForm.admissible).orthogonalSum
        (q.restrict S.right.carrier S.right.nondegenerate))
      (L.projectedLattice q D.matchedHead.vector D.matchedHead.anisotropic)
      (Lattice.product (binaryDiagonalModelLattice (K := K))
        S.right.lattice) :=
  (D.projectedFullModelIsometry S).trans
    ((Lattice.projectedOrthogonalProductIsometry
        (q := unaryBinaryModelSpace D.normalForm.head D.normalForm.first
          D.normalForm.second D.normalForm.admissible)
        (r := q.restrict S.right.carrier S.right.nondegenerate)
        (L := unaryBinaryModelLattice (K := K))
        (M := S.right.lattice)
        D.unaryBinaryMatchedHead_anisotropic).trans
      (D.projectedUnaryBinaryToBinary.orthogonalProductBasic
        (Lattice.Isometry.refl
          (q.restrict S.right.carrier S.right.nondegenerate)
          S.right.lattice)))

end InitialThreeGeometry

section HigherRank

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {N : Nat}
  [laws : DyadicDiscriminantClassLaws K]
  {a : GoodBONG q L (N + 4)} {b : GoodBONG r M (N + 4)}

/-- The concrete binary normal-form BONG concatenated with the unchanged
suffix.  The fourth-order lower bound is precisely what makes the first
binary entry a valid norm generator after adjoining that suffix. -/
noncomputable def binarySuffixGoodBONG
    (D : Beli2019Lemma96MatchedNormalFormData a b)
    (S : a.toBONG.TwoBlockSplitWitness 3 (by omega))
    (houter : a.order (0 : Fin (N + 4)) =
      a.order (2 : Fin (N + 4)))
    (hfourth : a.order (0 : Fin (N + 4)) +
        2 * (ramificationIndex K : Int) ≤
      a.order (3 : Fin (N + 4))) :
    GoodBONG
      ((binaryDiagonalModelSpace D.normalForm.first D.normalForm.second
          D.normalForm.admissible).orthogonalSum
        (q.restrict S.right.carrier S.right.nondegenerate))
      (Lattice.product (binaryDiagonalModelLattice (K := K))
        S.right.lattice) (N + 3) := by
  let binary := binaryDiagonalModelGoodBONG D.normalForm.first
    D.normalForm.second D.normalForm.admissible
  have hlength : N + 4 - 3 = N + 1 := by omega
  let suffix := (S.right.toGoodBONG a.good).castLength
    hlength
  exact binary.orthogonalProductRight_of_endpointBounds suffix (by omega)
    (by
      change binary.order (0 : Fin 2) ≤
        suffix.order (0 : Fin (N + 1))
      rw [binaryDiagonalModelGoodBONG_order_zero,
        D.normalForm.first_order, GoodBONG.order_castLength]
      change a.order 0 + (2 * (ramificationIndex K : Int) - 1) ≤
        S.right.bong.order (⟨0, by omega⟩ : Fin (N + 4 - 3))
      rw [S.right.order_eq]
      change a.order 0 + (2 * (ramificationIndex K : Int) - 1) ≤
        a.order (3 : Fin (N + 4))
      omega)
    (by
      change binary.order (1 : Fin 2) ≤
        suffix.order (0 : Fin (N + 1))
      rw [binaryDiagonalModelGoodBONG_order_one,
        D.normalForm.second_order, GoodBONG.order_castLength]
      change a.order 0 - 1 ≤
        S.right.bong.order (⟨0, by omega⟩ : Fin (N + 4 - 3))
      rw [S.right.order_eq]
      change a.order 0 - 1 ≤ a.order (3 : Fin (N + 4))
      calc
        a.order 0 - 1 ≤ a.order 0 := sub_le_self _ (by norm_num)
        _ ≤ a.order 0 + 2 * (ramificationIndex K : Int) := by
          apply le_add_of_nonneg_right
          positivity
        _ ≤ a.order (3 : Fin (N + 4)) := hfourth)
    (by
      intro hm
      have hN : 0 < N := by
        by_contra hnot
        have hzero : N = 0 := Nat.eq_zero_of_not_pos hnot
        subst N
        simp at hm
      have h4lt : 4 < N + 4 := by
        simpa only [zero_add] using Nat.add_lt_add_right hN 4
      have h2lt : 2 < N + 4 := (by decide : 2 < 4).trans h4lt
      let i₂ : Fin (N + 4) := ⟨2, h2lt⟩
      let i₄ : Fin (N + 4) := ⟨4, h4lt⟩
      let j : Fin (N + 1) := ⟨1, hm⟩
      let j' : Fin (N + 4 - 3) := Fin.cast hlength.symm j
      rw [show (⟨2 - 1, by decide⟩ : Fin 2) = 1 by decide,
        binaryDiagonalModelGoodBONG_order_one,
        D.normalForm.second_order, GoodBONG.order_castLength]
      change a.order 0 - 1 ≤ S.right.bong.order j'
      rw [S.right.order_eq]
      have hsourceIndex :
          S.right.sourceIndex j' = i₄ := by
        apply Fin.ext
        change 3 + j'.val = i₄.val
        rfl
      rw [hsourceIndex]
      have hbound : i₂.val + 2 < N + 4 := by
        change 4 < N + 4
        exact h4lt
      have hgood := a.good i₂ hbound
      have hnext : (⟨i₂.val + 2, hbound⟩ : Fin (N + 4)) = i₄ := by
        apply Fin.ext
        rfl
      rw [hnext] at hgood
      change a.order i₂ ≤ a.order i₄ at hgood
      have hi₂ : (2 : Fin (N + 4)) = i₂ := by
        apply Fin.ext
        change 2 % (N + 4) = 2
        rw [Nat.mod_eq_of_lt h2lt]
      rw [hi₂] at houter
      change a.order 0 - 1 ≤ a.order i₄
      calc
        a.order 0 - 1 ≤ a.order i₂ := by
          rw [← houter]
          exact sub_le_self _ (by norm_num)
        _ ≤ a.order i₄ := hgood)

/-- Transport the explicit product BONG back to the actual projected target
lattice.  This is the geometric projected tail required in Lemma 9.6. -/
noncomputable def projectedTailGoodBONG
    (D : Beli2019Lemma96MatchedNormalFormData a b)
    (S : a.toBONG.TwoBlockSplitWitness 3 (by omega))
    (houter : a.order (0 : Fin (N + 4)) =
      a.order (2 : Fin (N + 4)))
    (hfourth : a.order (0 : Fin (N + 4)) +
        2 * (ramificationIndex K : Int) ≤
      a.order (3 : Fin (N + 4))) :
    GoodBONG
      (q.orthogonalSpace D.matchedHead.vector D.matchedHead.anisotropic)
      (L.projectedLattice q D.matchedHead.vector D.matchedHead.anisotropic)
      (N + 3) :=
  (D.binarySuffixGoodBONG S houter hfourth).mapLatticeIsometry
    (D.projectedToBinarySuffix S).symm

/-- The first order of the concrete binary--suffix BONG. -/
@[simp]
theorem binarySuffixGoodBONG_order_zero
    (D : Beli2019Lemma96MatchedNormalFormData a b)
    (S : a.toBONG.TwoBlockSplitWitness 3 (by omega))
    (houter : a.order (0 : Fin (N + 4)) =
      a.order (2 : Fin (N + 4)))
    (hfourth : a.order (0 : Fin (N + 4)) +
        2 * (ramificationIndex K : Int) ≤
      a.order (3 : Fin (N + 4))) :
    (D.binarySuffixGoodBONG S houter hfourth).order 0 =
      ordUnit K D.normalForm.first := by
  unfold binarySuffixGoodBONG
  rw [show (0 : Fin (N + 3)) =
      BONG.orthogonalProductLeftIndex (N + 1) (0 : Fin 2) by
        apply Fin.ext
        rfl]
  simp only [GoodBONG.orthogonalProductRight_of_endpointBounds,
    GoodBONG.orthogonalProductRight_of_orderBounds,
    GoodBONG.orthogonalProductRight, GoodBONG.order]
  rw [BONG.order_orthogonalProductRight_left]
  change (binaryDiagonalModelBONG D.normalForm.first D.normalForm.second
    D.normalForm.admissible).order 0 = ordUnit K D.normalForm.first
  exact binaryDiagonalModelBONG_order_zero _ _ _

/-- The first value of the concrete product BONG is the first binary-model
value. -/
@[simp]
theorem binarySuffixGoodBONG_value_zero
    (D : Beli2019Lemma96MatchedNormalFormData a b)
    (S : a.toBONG.TwoBlockSplitWitness 3 (by omega))
    (houter : a.order (0 : Fin (N + 4)) =
      a.order (2 : Fin (N + 4)))
    (hfourth : a.order (0 : Fin (N + 4)) +
        2 * (ramificationIndex K : Int) ≤
      a.order (3 : Fin (N + 4))) :
    (D.binarySuffixGoodBONG S houter hfourth).value 0 =
      (binaryDiagonalModelBONG D.normalForm.first D.normalForm.second
        D.normalForm.admissible).value 0 := by
  unfold binarySuffixGoodBONG
  rw [show (0 : Fin (N + 3)) =
      BONG.orthogonalProductLeftIndex (N + 1) (0 : Fin 2) by
        apply Fin.ext
        rfl]
  simp only [GoodBONG.orthogonalProductRight_of_endpointBounds,
    GoodBONG.orthogonalProductRight_of_orderBounds,
    GoodBONG.orthogonalProductRight, GoodBONG.value]
  rw [BONG.value_orthogonalProductRight_left]
  rfl

/-- The second order of the concrete binary--suffix BONG. -/
@[simp]
theorem binarySuffixGoodBONG_order_one
    (D : Beli2019Lemma96MatchedNormalFormData a b)
    (S : a.toBONG.TwoBlockSplitWitness 3 (by omega))
    (houter : a.order (0 : Fin (N + 4)) =
      a.order (2 : Fin (N + 4)))
    (hfourth : a.order (0 : Fin (N + 4)) +
        2 * (ramificationIndex K : Int) ≤
      a.order (3 : Fin (N + 4))) :
    (D.binarySuffixGoodBONG S houter hfourth).order
        (1 : Fin (N + 3)) =
      ordUnit K D.normalForm.second := by
  unfold binarySuffixGoodBONG
  rw [show (1 : Fin (N + 3)) =
      BONG.orthogonalProductLeftIndex (N + 1) (1 : Fin 2) by
        apply Fin.ext
        change 1 % (N + 3) = 1 % 2
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by decide)]]
  simp only [GoodBONG.orthogonalProductRight_of_endpointBounds,
    GoodBONG.orthogonalProductRight_of_orderBounds,
    GoodBONG.orthogonalProductRight, GoodBONG.order]
  rw [BONG.order_orthogonalProductRight_left]
  change (binaryDiagonalModelBONG D.normalForm.first D.normalForm.second
    D.normalForm.admissible).order 1 = ordUnit K D.normalForm.second
  exact binaryDiagonalModelBONG_order_one _ _ _

/-- The second value of the concrete product BONG is the second
binary-model value. -/
@[simp]
theorem binarySuffixGoodBONG_value_one
    (D : Beli2019Lemma96MatchedNormalFormData a b)
    (S : a.toBONG.TwoBlockSplitWitness 3 (by omega))
    (houter : a.order (0 : Fin (N + 4)) =
      a.order (2 : Fin (N + 4)))
    (hfourth : a.order (0 : Fin (N + 4)) +
        2 * (ramificationIndex K : Int) ≤
      a.order (3 : Fin (N + 4))) :
    (D.binarySuffixGoodBONG S houter hfourth).value
        (1 : Fin (N + 3)) =
      (binaryDiagonalModelBONG D.normalForm.first D.normalForm.second
        D.normalForm.admissible).value 1 := by
  unfold binarySuffixGoodBONG
  rw [show (1 : Fin (N + 3)) =
      BONG.orthogonalProductLeftIndex (N + 1) (1 : Fin 2) by
        apply Fin.ext
        change 1 % (N + 3) = 1 % 2
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by decide)]]
  simp only [GoodBONG.orthogonalProductRight_of_endpointBounds,
    GoodBONG.orthogonalProductRight_of_orderBounds,
    GoodBONG.orthogonalProductRight, GoodBONG.value]
  rw [BONG.value_orthogonalProductRight_left]
  rfl

/-- Mapping the product BONG back to the projected lattice preserves its
first order. -/
@[simp]
theorem projectedTailGoodBONG_order_zero
    (D : Beli2019Lemma96MatchedNormalFormData a b)
    (S : a.toBONG.TwoBlockSplitWitness 3 (by omega))
    (houter : a.order (0 : Fin (N + 4)) =
      a.order (2 : Fin (N + 4)))
    (hfourth : a.order (0 : Fin (N + 4)) +
        2 * (ramificationIndex K : Int) ≤
      a.order (3 : Fin (N + 4))) :
    (D.projectedTailGoodBONG S houter hfourth).order 0 =
      ordUnit K D.normalForm.first := by
  unfold projectedTailGoodBONG
  rw [GoodBONG.order_mapLatticeIsometry,
    D.binarySuffixGoodBONG_order_zero S houter hfourth]

/-- Mapping the product BONG back to the projected lattice preserves its
second order. -/
@[simp]
theorem projectedTailGoodBONG_order_one
    (D : Beli2019Lemma96MatchedNormalFormData a b)
    (S : a.toBONG.TwoBlockSplitWitness 3 (by omega))
    (houter : a.order (0 : Fin (N + 4)) =
      a.order (2 : Fin (N + 4)))
    (hfourth : a.order (0 : Fin (N + 4)) +
        2 * (ramificationIndex K : Int) ≤
      a.order (3 : Fin (N + 4))) :
    (D.projectedTailGoodBONG S houter hfourth).order
        (1 : Fin (N + 3)) =
      ordUnit K D.normalForm.second := by
  unfold projectedTailGoodBONG
  rw [GoodBONG.order_mapLatticeIsometry,
    D.binarySuffixGoodBONG_order_one S houter hfourth]

/-- Every order after the explicit binary block is the corresponding order
of the unchanged original suffix. -/
theorem binarySuffixGoodBONG_order_later
    (D : Beli2019Lemma96MatchedNormalFormData a b)
    (S : a.toBONG.TwoBlockSplitWitness 3 (by omega))
    (houter : a.order (0 : Fin (N + 4)) =
      a.order (2 : Fin (N + 4)))
    (hfourth : a.order (0 : Fin (N + 4)) +
        2 * (ramificationIndex K : Int) ≤
      a.order (3 : Fin (N + 4)))
    (i : Fin (N + 3)) (hi : 2 ≤ i.val) :
    (D.binarySuffixGoodBONG S houter hfourth).order i =
      a.order i.succ := by
  let j : Fin (N + 1) := ⟨i.val - 2, by omega⟩
  have hindex : i = BONG.orthogonalProductRightIndex 2 j := by
    apply Fin.ext
    simp only [BONG.orthogonalProductRightIndex_val]
    dsimp only [j]
    omega
  unfold binarySuffixGoodBONG
  rw [hindex]
  simp only [GoodBONG.orthogonalProductRight_of_endpointBounds,
    GoodBONG.orthogonalProductRight_of_orderBounds,
    GoodBONG.orthogonalProductRight, GoodBONG.order]
  rw [BONG.order_orthogonalProductRight_right]
  change ((S.right.toGoodBONG a.good).castLength _).order j =
    a.order (BONG.orthogonalProductRightIndex 2 j).succ
  rw [GoodBONG.order_castLength]
  simp only [GoodBONG.order, BONG.SegmentWitness.toGoodBONG]
  change S.right.bong.order (⟨j.val, by omega⟩ : Fin (N + 4 - 3)) =
    a.toBONG.order (BONG.orthogonalProductRightIndex 2 j).succ
  rw [S.right.order_eq]
  congr 1
  apply Fin.ext
  simp only [BONG.SegmentWitness.sourceIndex_val, Fin.val_succ,
    BONG.orthogonalProductRightIndex_val]
  omega

/-- Every value after the binary block is the corresponding unchanged
original suffix value. -/
theorem binarySuffixGoodBONG_value_later
    (D : Beli2019Lemma96MatchedNormalFormData a b)
    (S : a.toBONG.TwoBlockSplitWitness 3 (by omega))
    (houter : a.order (0 : Fin (N + 4)) =
      a.order (2 : Fin (N + 4)))
    (hfourth : a.order (0 : Fin (N + 4)) +
        2 * (ramificationIndex K : Int) ≤
      a.order (3 : Fin (N + 4)))
    (i : Fin (N + 3)) (hi : 2 ≤ i.val) :
    (D.binarySuffixGoodBONG S houter hfourth).value i =
      a.value i.succ := by
  let j : Fin (N + 1) := ⟨i.val - 2, by omega⟩
  have hindex : i = BONG.orthogonalProductRightIndex 2 j := by
    apply Fin.ext
    simp only [BONG.orthogonalProductRightIndex_val]
    dsimp only [j]
    omega
  unfold binarySuffixGoodBONG
  rw [hindex]
  simp only [GoodBONG.orthogonalProductRight_of_endpointBounds,
    GoodBONG.orthogonalProductRight_of_orderBounds,
    GoodBONG.orthogonalProductRight, GoodBONG.value]
  rw [BONG.value_orthogonalProductRight_right]
  change ((S.right.toGoodBONG a.good).castLength _).value j =
    a.value (BONG.orthogonalProductRightIndex 2 j).succ
  change ((S.right.toGoodBONG a.good).castLength _).toBONG.value j =
    a.toBONG.value (BONG.orthogonalProductRightIndex 2 j).succ
  simp only [GoodBONG.castLength, BONG.SegmentWitness.toGoodBONG]
  change S.right.bong.value (⟨j.val, by omega⟩ : Fin (N + 4 - 3)) =
    a.toBONG.value (BONG.orthogonalProductRightIndex 2 j).succ
  rw [S.right.value_eq]
  congr 1
  apply Fin.ext
  simp only [BONG.SegmentWitness.sourceIndex_val, Fin.val_succ,
    BONG.orthogonalProductRightIndex_val]
  omega

/-- The later-order formula survives transport back to the actual projected
lattice. -/
theorem projectedTailGoodBONG_order_later
    (D : Beli2019Lemma96MatchedNormalFormData a b)
    (S : a.toBONG.TwoBlockSplitWitness 3 (by omega))
    (houter : a.order (0 : Fin (N + 4)) =
      a.order (2 : Fin (N + 4)))
    (hfourth : a.order (0 : Fin (N + 4)) +
        2 * (ramificationIndex K : Int) ≤
      a.order (3 : Fin (N + 4)))
    (i : Fin (N + 3)) (hi : 2 ≤ i.val) :
    (D.projectedTailGoodBONG S houter hfourth).order i =
      a.order i.succ := by
  unfold projectedTailGoodBONG
  rw [GoodBONG.order_mapLatticeIsometry]
  exact D.binarySuffixGoodBONG_order_later S houter hfourth i hi

/-- All projected-tail values are the product values transported through the
projection isometry. -/
theorem projectedTailGoodBONG_value_zero
    (D : Beli2019Lemma96MatchedNormalFormData a b)
    (S : a.toBONG.TwoBlockSplitWitness 3 (by omega))
    (houter : a.order (0 : Fin (N + 4)) =
      a.order (2 : Fin (N + 4)))
    (hfourth : a.order (0 : Fin (N + 4)) +
        2 * (ramificationIndex K : Int) ≤
      a.order (3 : Fin (N + 4))) :
    (D.projectedTailGoodBONG S houter hfourth).value 0 =
      (binaryDiagonalModelBONG D.normalForm.first D.normalForm.second
        D.normalForm.admissible).value 0 := by
  unfold projectedTailGoodBONG GoodBONG.value GoodBONG.mapLatticeIsometry
  rw [BONG.value_mapLatticeIsometry]
  change (D.binarySuffixGoodBONG S houter hfourth).value 0 = _
  exact D.binarySuffixGoodBONG_value_zero S houter hfourth

theorem projectedTailGoodBONG_value_one
    (D : Beli2019Lemma96MatchedNormalFormData a b)
    (S : a.toBONG.TwoBlockSplitWitness 3 (by omega))
    (houter : a.order (0 : Fin (N + 4)) =
      a.order (2 : Fin (N + 4)))
    (hfourth : a.order (0 : Fin (N + 4)) +
        2 * (ramificationIndex K : Int) ≤
      a.order (3 : Fin (N + 4))) :
    (D.projectedTailGoodBONG S houter hfourth).value
        (1 : Fin (N + 3)) =
      (binaryDiagonalModelBONG D.normalForm.first D.normalForm.second
        D.normalForm.admissible).value 1 := by
  unfold projectedTailGoodBONG GoodBONG.value GoodBONG.mapLatticeIsometry
  rw [BONG.value_mapLatticeIsometry]
  change (D.binarySuffixGoodBONG S houter hfourth).value 1 = _
  exact D.binarySuffixGoodBONG_value_one S houter hfourth

theorem projectedTailGoodBONG_value_later
    (D : Beli2019Lemma96MatchedNormalFormData a b)
    (S : a.toBONG.TwoBlockSplitWitness 3 (by omega))
    (houter : a.order (0 : Fin (N + 4)) =
      a.order (2 : Fin (N + 4)))
    (hfourth : a.order (0 : Fin (N + 4)) +
        2 * (ramificationIndex K : Int) ≤
      a.order (3 : Fin (N + 4)))
    (i : Fin (N + 3)) (hi : 2 ≤ i.val) :
    (D.projectedTailGoodBONG S houter hfourth).value i =
      a.value i.succ := by
  unfold projectedTailGoodBONG GoodBONG.value GoodBONG.mapLatticeIsometry
  rw [BONG.value_mapLatticeIsometry]
  exact D.binarySuffixGoodBONG_value_later S houter hfourth i hi

/-- The first two values of the projected tail are exactly the canonical
binary-model values, uniformly over a binary index. -/
theorem projectedTailGoodBONG_value_binary
    (D : Beli2019Lemma96MatchedNormalFormData a b)
    (S : a.toBONG.TwoBlockSplitWitness 3 (by omega))
    (houter : a.order (0 : Fin (N + 4)) =
      a.order (2 : Fin (N + 4)))
    (hfourth : a.order (0 : Fin (N + 4)) +
        2 * (ramificationIndex K : Int) ≤
      a.order (3 : Fin (N + 4))) (i : Fin 2) :
    (D.projectedTailGoodBONG S houter hfourth).value
        ⟨i.val, by omega⟩ =
      (binaryDiagonalModelBONG D.normalForm.first D.normalForm.second
        D.normalForm.admissible).value i := by
  fin_cases i
  · simpa using D.projectedTailGoodBONG_value_zero S houter hfourth
  · simpa using D.projectedTailGoodBONG_value_one S houter hfourth

/-- The geometrically constructed projected tail has exactly the three order
identities displayed in Beli's proof of Lemma 9.6. -/
theorem projectedTail_orderProfile
    (D : Beli2019Lemma96MatchedNormalFormData a b)
    (S : a.toBONG.TwoBlockSplitWitness 3 (by omega))
    (houter : a.order (0 : Fin (N + 4)) =
      a.order (2 : Fin (N + 4)))
    (hfirstGap : a.order (1 : Fin (N + 4)) -
        a.order (0 : Fin (N + 4)) =
      2 * (ramificationIndex K : Int) - 2)
    (hfourth : a.order (0 : Fin (N + 4)) +
        2 * (ramificationIndex K : Int) ≤
      a.order (3 : Fin (N + 4))) :
    Beli2019Lemma96TailOrderProfile a
      (D.projectedTailGoodBONG S houter hfourth) where
  firstOrder := by
    rw [D.projectedTailGoodBONG_order_zero S houter hfourth,
      D.normalForm.first_order]
    omega
  secondOrder := by
    rw [D.projectedTailGoodBONG_order_one S houter hfourth,
      D.normalForm.second_order, houter]
  laterOrders := D.projectedTailGoodBONG_order_later S houter hfourth

/-- Every prefix of the exceptional BONG is obtained from the represented
initial ternary block by appending the unchanged original suffix. -/
theorem projectedTail_prefixTransport
    (D : Beli2019Lemma96MatchedNormalFormData a b)
    (S : a.toBONG.TwoBlockSplitWitness 3 (by omega))
    (houter : a.order (0 : Fin (N + 4)) =
      a.order (2 : Fin (N + 4)))
    (hfourth : a.order (0 : Fin (N + 4)) +
        2 * (ramificationIndex K : Int) ≤
      a.order (3 : Fin (N + 4))) :
    Beli2019Lemma96PrefixTransport a b
      (D.projectedTailGoodBONG S houter hfourth) where
  targetPrefix := by
    intro tailLength hkTwo hk
    obtain ⟨rest, rfl⟩ : ∃ rest, tailLength = rest + 2 := by
      exact ⟨tailLength - 2, by omega⟩
    let common : Fin rest → K := fun j =>
      a.value ⟨j.val + 3, by omega⟩
    have hbase := D.initialThree_diagonalRepresents_exceptional
    have hbase' : DiagonalRepresents
        (a.prefixValues 3 (by omega))
        (Fin.cons (b.value 0)
          (binaryDiagonalModelBONG D.normalForm.first D.normalForm.second
            D.normalForm.admissible).value) := by
      convert hbase using 1
      change a.lemma814FirstThreeValues =
        a.lemma96InitialThree.lemma814FirstThreeValues
      exact a.lemma96InitialThree_firstThreeValues_eq.symm
    have happ := diagonalRepresents_append hbase' common
    have hlength : 3 + rest = rest + 2 + 1 := by omega
    have hcast := diagonalRepresents_castLengths hlength hlength happ
    convert hcast using 1
    · funext i
      let x := Fin.cast hlength.symm i
      change a.value ⟨x.val, by omega⟩ =
        Fin.append (a.prefixValues 3 (by omega)) common x
      by_cases hx : x.val < 3
      · let j : Fin 3 := ⟨x.val, hx⟩
        have hindex : x = Fin.castAdd rest j := by
          apply Fin.ext
          rfl
        conv_rhs => rw [hindex]
        rw [Fin.append_left]
        congr 1
      · let j : Fin rest := ⟨x.val - 3, by omega⟩
        have hindex : x = Fin.natAdd 3 j := by
          apply Fin.ext
          change x.val = 3 + (x.val - 3)
          omega
        conv_rhs => rw [hindex]
        rw [Fin.append_right]
        dsimp only [common]
        congr 1
        apply Fin.ext
        change x.val = j.val + 3
        dsimp only [j]
        omega
    · funext i
      refine Fin.cases ?_ (fun tailIndex => ?_) i
      · rw [Fin.cons_zero]
        have hindex : Fin.cast hlength.symm
            (0 : Fin (rest + 2 + 1)) =
          Fin.castAdd rest (0 : Fin 3) := by
          apply Fin.ext
          rfl
        rw [hindex, Fin.append_left, Fin.cons_zero]
      · rw [Fin.cons_succ]
        by_cases hsmall : tailIndex.val < 2
        · let j : Fin 2 := ⟨tailIndex.val, hsmall⟩
          have hindex : Fin.cast hlength.symm tailIndex.succ =
              Fin.castAdd rest j.succ := by
            apply Fin.ext
            rfl
          conv_rhs => rw [hindex]
          rw [Fin.append_left, Fin.cons_succ]
          change (D.projectedTailGoodBONG S houter hfourth).value
              ⟨j.val, by omega⟩ =
            (binaryDiagonalModelBONG D.normalForm.first
              D.normalForm.second D.normalForm.admissible).value j
          exact D.projectedTailGoodBONG_value_binary S houter hfourth j
        · let j : Fin rest := ⟨tailIndex.val - 2, by omega⟩
          have hindex : Fin.cast hlength.symm tailIndex.succ =
              Fin.natAdd 3 j := by
            apply Fin.ext
            change tailIndex.val + 1 = 3 + (tailIndex.val - 2)
            omega
          conv_rhs => rw [hindex]
          rw [Fin.append_right]
          dsimp only [common]
          have htailBound : tailIndex.val < N + 3 :=
            tailIndex.isLt.trans_le hk
          have htailTwo : 2 ≤ tailIndex.val := Nat.le_of_not_gt hsmall
          let ambientIndex : Fin (N + 3) :=
            ⟨tailIndex.val, htailBound⟩
          let suffixIndex : Fin (N + 4) :=
            ⟨j.val + 3, by dsimp only [j]; omega⟩
          change (D.projectedTailGoodBONG S houter hfourth).value
              ambientIndex = a.value suffixIndex
          have hv := D.projectedTailGoodBONG_value_later
            S houter hfourth ambientIndex (by
              dsimp only [ambientIndex]
              exact htailTwo)
          have hindex' : ambientIndex.succ = suffixIndex := by
            apply Fin.ext
            change tailIndex.val + 1 = (tailIndex.val - 2) + 3
            omega
          simpa only [hindex'] using hv

/-- The fourth-order lower bound puts an orthogonal cut immediately after
the initial ternary block by Beli's Corollary 4.4(i). -/
theorem exists_initialThreeSplit
    [BeliCorollary44Laws.{u, v} K]
    (D : Beli2019Lemma96MatchedNormalFormData a b)
    (houter : a.order (0 : Fin (N + 4)) =
      a.order (2 : Fin (N + 4)))
    (hfourth : a.order (0 : Fin (N + 4)) +
        2 * (ramificationIndex K : Int) ≤
      a.order (3 : Fin (N + 4))) :
    Nonempty (a.toBONG.TwoBlockSplitWitness 3 (by omega)) := by
  let i : Fin (N + 4) := ⟨2, by omega⟩
  have hi : i.val + 1 < N + 4 := by
    dsimp only [i]
    omega
  have hiTwo : (2 : Fin (N + 4)) = i := by
    apply Fin.ext
    change 2 % (N + 4) = 2
    rw [Nat.mod_eq_of_lt (by omega)]
  have hthree : (⟨i.val + 1, hi⟩ : Fin (N + 4)) =
      (3 : Fin (N + 4)) := by
    apply Fin.ext
    dsimp only [i]
    change 3 = 3 % (N + 4)
    rw [Nat.mod_eq_of_lt (by omega)]
  have horder : a.order i ≤ a.order ⟨i.val + 1, hi⟩ := by
    calc
      a.order i = a.order (2 : Fin (N + 4)) :=
        congrArg a.order hiTwo.symm
      _ = a.order 0 := houter.symm
      _ ≤ a.order 0 + 2 * (ramificationIndex K : Int) := by
        apply le_add_of_nonneg_right
        positivity
      _ ≤ a.order (3 : Fin (N + 4)) := hfourth
      _ = a.order ⟨i.val + 1, hi⟩ := congrArg a.order hthree.symm
  have hsplit := a.toBONG.beliCorollary44_i_unconditional a.good i hi horder
  simpa only [BONG.HasTwoBlockSplit, i] using hsplit

/-- The complete geometric output of the exceptional head construction:
the Corollary 4.4 split, the actual projected-lattice Good BONG, and its
verified order profile. -/
structure ProjectedTailData
    (D : Beli2019Lemma96MatchedNormalFormData a b) where
  split : a.toBONG.TwoBlockSplitWitness 3 (by omega)
  targetTail : GoodBONG
    (q.orthogonalSpace D.matchedHead.vector D.matchedHead.anisotropic)
    (L.projectedLattice q D.matchedHead.vector D.matchedHead.anisotropic)
    (N + 3)
  orderProfile : Beli2019Lemma96TailOrderProfile a targetTail
  prefixTransport : Beli2019Lemma96PrefixTransport a b targetTail

/-- Construct the complete projected-tail data directly from the numerical
hypotheses of Lemma 9.6. -/
theorem exists_projectedTailData
    [BeliCorollary44Laws.{u, v} K]
    (D : Beli2019Lemma96MatchedNormalFormData a b)
    (houter : a.order (0 : Fin (N + 4)) =
      a.order (2 : Fin (N + 4)))
    (hfirstGap : a.order (1 : Fin (N + 4)) -
        a.order (0 : Fin (N + 4)) =
      2 * (ramificationIndex K : Int) - 2)
    (hfourth : a.order (0 : Fin (N + 4)) +
        2 * (ramificationIndex K : Int) ≤
      a.order (3 : Fin (N + 4))) :
    Nonempty (ProjectedTailData D) := by
  rcases D.exists_initialThreeSplit houter hfourth with ⟨S⟩
  let tail := D.projectedTailGoodBONG S houter hfourth
  exact ⟨{
    split := S
    targetTail := tail
    orderProfile := D.projectedTail_orderProfile S houter hfirstGap hfourth
    prefixTransport := D.projectedTail_prefixTransport S houter hfourth
  }⟩

end HigherRank

end BONG.GoodBONG.Beli2019Lemma96MatchedNormalFormData

end Bong
