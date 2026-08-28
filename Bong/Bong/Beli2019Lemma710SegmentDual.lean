/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma710SegmentModel
import Bong.Bong.MaximalNormSplittingDual

/-!
# Beli (2019), Lemma 7.10: dualizing a consecutive replacement

The general case of Lemma 7.10 uses the equality of the original replacement
block once more after integral duality and reversal.  This file isolates the
lattice-theoretic core: dualizing an isometry from a replacement lattice to
an orthogonal product, identifying the dual product componentwise, and then
exchanging the two factors.
-/

namespace Bong

open Dyadic

namespace BONG.SegmentWitness

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}
  {n m start dualStart length : Nat}
  {bound : start + length ≤ n}
  {dualBound : dualStart + length ≤ m}
  {b : BONG V q L n} {c : BONG W r M m}

/-- Passing to a consecutive segment commutes with normalized dual vectors,
after the evident inclusion of the segment carrier into the parent space. -/
@[simp]
theorem coe_dualVector_eq
    (w : SegmentWitness b start length bound) (i : Fin length) :
    (w.bong.dualVector i : V) = b.dualVector (w.sourceIndex i) := by
  rw [BONG.dualVector, BONG.dualVector, w.valueUnit_eq]
  change ((b.valueUnit (w.sourceIndex i))⁻¹ : K) •
      (w.bong.ambientVector i : V) =
    ((b.valueUnit (w.sourceIndex i))⁻¹ : K) •
      b.ambientVector (w.sourceIndex i)
  rw [w.ambientVector_eq]
  congr 1

/-- The reverse-dual vector of a segment is the parent dual vector at the
reversed local segment index. -/
@[simp]
theorem coe_reverseDualVector_eq
    (w : SegmentWitness b start length bound) (i : Fin length) :
    (w.bong.reverseDualVector i : V) =
      b.dualVector (w.sourceIndex (Fin.rev i)) := by
  rw [BONG.reverseDualVector, w.coe_dualVector_eq]

/-- For a prefix segment, reversing inside the segment agrees with taking
the suffix of the reversed parent sequence. -/
theorem coe_reverseDualVector_prefix_eq
    {prefixBound : 0 + length ≤ n}
    (w : SegmentWitness b 0 length prefixBound) (i : Fin length) :
    (w.bong.reverseDualVector i : V) =
      b.reverseDualVector
        ⟨n - length + i.val, by omega⟩ := by
  rw [w.coe_reverseDualVector_eq, BONG.reverseDualVector]
  congr 1
  apply Fin.ext
  simp only [sourceIndex_val, Nat.zero_add, Fin.rev]
  omega

/-- A consecutive segment in a reverse-dual BONG is the integral dual of
the corresponding original segment.  The statement deliberately records
the ambient isometry and the literal vector formula: later uses in Lemma
7.10 must agree with the canonical stopping-space map, not merely exhibit
an abstract isometric lattice. -/
noncomputable def reverseDualLatticeIsometry
    [BONGReverseDualLaws.{u, v} K]
    (original : SegmentWitness b start length bound)
    (originalGood : b.IsGood)
    (dual : SegmentWitness c dualStart length dualBound)
    (ambient : q.Isometry r)
    (dualVectors : ∀ i : Fin length,
      (dual.bong.ambientVector i : W) =
        ambient.toLinearEquiv
          (original.bong.reverseDualVector i : V)) :
    Lattice.Isometry
      (q.restrict original.carrier original.nondegenerate)
      (r.restrict dual.carrier dual.nondegenerate)
      (Lattice.dualLattice
        (q.restrict original.carrier original.nondegenerate)
        original.lattice)
      dual.lattice := by
  let originalSegment := original.toGoodBONG originalGood
  choose reverseDual reverseDualVectors using
    originalSegment.exists_reverseDual
  let f : original.carrier ≃ₗ[K] dual.carrier :=
    reverseDual.toBONG.basis.equiv dual.bong.basis (Equiv.refl (Fin length))
  have hgram : ∀ i j : Fin length,
      (r.restrict dual.carrier dual.nondegenerate).bilin
          (dual.bong.basis i) (dual.bong.basis j) =
        (q.restrict original.carrier original.nondegenerate).bilin
          (reverseDual.toBONG.basis i) (reverseDual.toBONG.basis j) := by
    intro i j
    change r.bilin (dual.bong.ambientVector i : W)
        (dual.bong.ambientVector j : W) =
      q.bilin (reverseDual.toBONG.ambientVector i : original.carrier)
        (reverseDual.toBONG.ambientVector j : original.carrier)
    rw [dualVectors i, dualVectors j, ambient.map_bilin,
      reverseDualVectors i, reverseDualVectors j]
    change q.bilin (original.bong.reverseDualVector i : V)
        (original.bong.reverseDualVector j : V) =
      q.bilin (original.bong.reverseDualVector i : V)
        (original.bong.reverseDualVector j : V)
    rfl
  let restricted :
      (q.restrict original.carrier original.nondegenerate).Isometry
        (r.restrict dual.carrier dual.nondegenerate) :=
    { toLinearEquiv := f
      map_bilin := by
        intro x y
        have hforms :
            (r.restrict dual.carrier dual.nondegenerate).bilin.comp
                f.toLinearMap f.toLinearMap =
              (q.restrict original.carrier original.nondegenerate).bilin := by
          apply LinearMap.BilinForm.ext_basis reverseDual.toBONG.basis
          intro i j
          rw [LinearMap.BilinForm.comp_apply]
          simpa [f, Module.Basis.equiv] using hgram i j
        exact DFunLike.congr_fun (DFunLike.congr_fun hforms x) y }
  let mapped := reverseDual.toBONG.map restricted
  have mappedVectors : ∀ i : Fin length,
      mapped.ambientVector i = dual.bong.ambientVector i := by
    intro i
    rw [BONG.ambientVector_map]
    change f (reverseDual.toBONG.basis i) = dual.bong.basis i
    simp [f, Module.Basis.equiv]
  have hmap :
      Lattice.map restricted.toLinearEquiv
          (Lattice.dualLattice
            (q.restrict original.carrier original.nondegenerate)
            original.lattice) =
        dual.lattice :=
    mapped.lattice_eq_of_ambientVector_eq dual.bong mappedVectors
  exact
    { toLinearEquiv := restricted.toLinearEquiv
      map_bilin := restricted.map_bilin
      map_mem := by
        intro x
        rw [← hmap, Lattice.map_mem_map_iff] }

/-- The segment reverse-dual isometry is the canonical basis map on every
normalized reversed dual vector. -/
@[simp]
theorem reverseDualLatticeIsometry_apply_reverseDualVector
    [BONGReverseDualLaws.{u, v} K]
    (original : SegmentWitness b start length bound)
    (originalGood : b.IsGood)
    (dual : SegmentWitness c dualStart length dualBound)
    (ambient : q.Isometry r)
    (dualVectors : ∀ i : Fin length,
      (dual.bong.ambientVector i : W) =
        ambient.toLinearEquiv
          (original.bong.reverseDualVector i : V))
    (i : Fin length) :
    (reverseDualLatticeIsometry original originalGood dual ambient
      dualVectors).toLinearEquiv (original.bong.reverseDualVector i) =
      dual.bong.ambientVector i := by
  let originalSegment := original.toGoodBONG originalGood
  let reverseDual :=
    Classical.choose originalSegment.exists_reverseDual
  have reverseDualVectors :=
    Classical.choose_spec originalSegment.exists_reverseDual
  change (reverseDual.toBONG.basis.equiv dual.bong.basis
      (Equiv.refl (Fin length))) (original.bong.reverseDualVector i) =
    dual.bong.ambientVector i
  have hreverse := reverseDualVectors i
  change reverseDual.toBONG.ambientVector i =
    original.bong.reverseDualVector i at hreverse
  rw [← hreverse]
  change (reverseDual.toBONG.basis.equiv dual.bong.basis
      (Equiv.refl (Fin length))) (reverseDual.toBONG.basis i) =
    dual.bong.basis i
  simp [Module.Basis.equiv]

end BONG.SegmentWitness

namespace BONG.OrthogonalPrefixRawSeed

universe u v w z

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}
  {n steps baseLength : Nat}

/-- A BONG on the orthogonal product required at the hidden stopping node.
The ambient type changes along the extracted prefix, so the family follows
the same dependent recursion as `StopSegmentIsometry`. -/
def StopProductBONG
    {b : BONG V q L n}
    (S : OrthogonalPrefixRawSeed r M baseLength (steps := steps) b) :
    Type (max (u + 1) (v + 1) (w + 1)) := by
  induction S with
  | @stop V _ _ q L n N source base =>
      exact BONG (V × W) (q.orthogonalSum r)
        (Lattice.product L M) baseLength
  | cons _ _ _ _ tailProduct =>
      exact tailProduct

/-- Exact vector compatibility between a stopping-product BONG and the
canonical map from the hidden stopping space to the literal target segment.
This is the strengthened datum needed by Lemma 7.10: it determines the
image lattice, whereas an arbitrary abstract lattice isometry would not. -/
def StopProductVectorEq
    {U : Type z} [AddCommGroup U] [Module K U]
    {s : QuadraticSpace K U} {P : Lattice K U}
    {targetLength start : Nat} {bound : start + baseLength ≤ targetLength}
    {target : BONG U s P targetLength}
    {b : BONG V q L n}
    (S : OrthogonalPrefixRawSeed r M baseLength (steps := steps) b)
    (segment : SegmentWitness target start baseLength bound)
    (stopToSegment : S.StopSegmentIsometry segment)
    (product : S.StopProductBONG) : Prop := by
  induction S with
  | stop =>
      exact ∀ i : Fin baseLength,
        stopToSegment.toLinearEquiv (product.ambientVector i) =
          segment.bong.ambientVector i
  | cons _ _ _ _ tailEq =>
      exact tailEq stopToSegment product

/-- Compatibility of a segment-to-product isometry with the canonical
stopping BONG.  At the unique stopping node it says that the isometry sends
each literal dual replacement vector to the corresponding hidden product
vector. -/
def StopSegmentProductVectorEq
    {U : Type z} [AddCommGroup U] [Module K U]
    {s : QuadraticSpace K U} {P : Lattice K U}
    {targetLength start : Nat} {bound : start + baseLength ≤ targetLength}
    {target : BONG U s P targetLength}
    {b : BONG V q L n}
    (S : OrthogonalPrefixRawSeed r M baseLength (steps := steps) b)
    (segment : SegmentWitness target start baseLength bound)
    (segmentToProduct : S.StopSegmentProductIsometry segment) : Prop := by
  induction S with
  | @stop V _ _ q L n N source base =>
      exact ∀ i : Fin baseLength,
        segmentToProduct.toLinearEquiv (segment.bong.ambientVector i) =
          base.ambientVector i
  | cons _ _ _ _ tailEq =>
      exact tailEq segmentToProduct

/-- Literal agreement of the mapped product BONG with the target segment
proves the precise segment-product equality consumed by M603. -/
theorem stopSegmentProductEq_of_productVectors
    {U : Type z} [AddCommGroup U] [Module K U]
    {s : QuadraticSpace K U} {P : Lattice K U}
    {targetLength start : Nat} {bound : start + baseLength ≤ targetLength}
    {target : BONG U s P targetLength}
    {b : BONG V q L n}
    (S : OrthogonalPrefixRawSeed r M baseLength (steps := steps) b)
    (segment : SegmentWitness target start baseLength bound)
    (stopToSegment : S.StopSegmentIsometry segment)
    (product : S.StopProductBONG)
    (vectors : S.StopProductVectorEq segment stopToSegment product) :
    S.StopSegmentProductEq segment stopToSegment := by
  induction S with
  | stop =>
      let mapped := product.map stopToSegment.toQuadraticSpaceIsometry
      have hvector : ∀ i : Fin baseLength,
          segment.bong.ambientVector i = mapped.ambientVector i := by
        intro i
        rw [BONG.ambientVector_map]
        exact (vectors i).symm
      exact segment.bong.lattice_eq_of_ambientVector_eq mapped hvector
  | cons _ _ _ _ ih =>
      exact ih stopToSegment product vectors

/-- A dualized replacement-block isometry proves the exact stopping product
identity as soon as its action on the replacement BONG vectors is the
canonical one.  This is the commutative-diagram form used by M604. -/
theorem stopSegmentProductEq_of_segmentProductIsometry
    {U : Type z} [AddCommGroup U] [Module K U]
    {s : QuadraticSpace K U} {P : Lattice K U}
    {targetLength start : Nat} {bound : start + baseLength ≤ targetLength}
    {target : BONG U s P targetLength}
    {b : BONG V q L n}
    (S : OrthogonalPrefixRawSeed r M baseLength (steps := steps) b)
    (segment : SegmentWitness target start baseLength bound)
    (stopToSegment : S.StopSegmentIsometry segment)
    (segmentToProduct : S.StopSegmentProductIsometry segment)
    (stopVectors : S.StopBaseVectorEq segment stopToSegment)
    (productVectors :
      S.StopSegmentProductVectorEq segment segmentToProduct) :
    S.StopSegmentProductEq segment stopToSegment := by
  induction S with
  | @stop V _ _ q L n N source base =>
      let product := segment.bong.mapLatticeIsometry segmentToProduct
      apply stopSegmentProductEq_of_productVectors
        (OrthogonalPrefixRawSeed.stop (M := M) source base)
        segment stopToSegment product
      intro i
      change stopToSegment.toLinearEquiv
          ((segment.bong.mapLatticeIsometry segmentToProduct).ambientVector i) =
        segment.bong.ambientVector i
      rw [BONG.ambientVector_mapLatticeIsometry, productVectors i]
      exact stopVectors i
  | cons _ _ _ _ ih =>
      exact ih stopToSegment segmentToProduct stopVectors productVectors

/-- The concrete commutative diagram attached to an automatically extracted
target prefix.  Unlike `TargetPrefixSegmentProductEq`, this stores the actual
dualized lattice isometry together with its action on the BONG basis. -/
structure TargetPrefixSegmentProductIsometryData
    (source : BONG V q L n) (hsteps : steps ≤ n)
    {P : Lattice K (V × W)}
    (target : BONG (V × W) (q.orthogonalSum r) P
      (baseLength + steps))
    (leftVectors : ∀ i : Fin steps,
      target.ambientVector (orthogonalProductLeftIndex baseLength i) =
        (source.ambientVector (prefixSourceIndex hsteps i), 0)) where
  segmentToProduct :
    let model := extractTargetPrefixSegment (M := M) source hsteps target
      leftVectors
    model.extraction.seed.StopSegmentProductIsometry model.segment
  productVectors :
    let model := extractTargetPrefixSegment (M := M) source hsteps target
      leftVectors
    model.extraction.seed.StopSegmentProductVectorEq model.segment
      segmentToProduct

/-- The commutative-diagram form implies the equality form consumed by the
existing certificate constructor. -/
theorem TargetPrefixSegmentProductIsometryData.segmentProductEq
    (source : BONG V q L n) (hsteps : steps ≤ n)
    {P : Lattice K (V × W)}
    (target : BONG (V × W) (q.orthogonalSum r) P
      (baseLength + steps))
    (leftVectors : ∀ i : Fin steps,
      target.ambientVector (orthogonalProductLeftIndex baseLength i) =
        (source.ambientVector (prefixSourceIndex hsteps i), 0))
    (D : TargetPrefixSegmentProductIsometryData (M := M) source hsteps
      target leftVectors) :
    TargetPrefixSegmentProductEq (M := M) source hsteps target
      leftVectors := by
  let model := extractTargetPrefixSegment (M := M) source hsteps target
    leftVectors
  exact model.extraction.seed.stopSegmentProductEq_of_segmentProductIsometry
    model.segment model.stopToSegment D.segmentToProduct model.stopVectors
    D.productVectors

end BONG.OrthogonalPrefixRawSeed

namespace Lattice

universe u v w z z' v' w'

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {U : Type z} [AddCommGroup U] [Module K U]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {s : QuadraticSpace K U}
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {N : Lattice K U} {L : Lattice K V} {M : Lattice K W}

/-- A lattice isometry which agrees on the vectors of two BONGs also agrees
on their normalized reversed dual vectors. -/
theorem Isometry.map_reverseDualVector_of_ambientVector_eq
    {length : Nat} (f : Isometry s q N L)
    (b : BONG U s N length) (c : BONG V q L length)
    (vectors : ∀ i : Fin length,
      f.toLinearEquiv (b.ambientVector i) = c.ambientVector i)
    (i : Fin length) :
    f.toLinearEquiv (b.reverseDualVector i) = c.reverseDualVector i := by
  let j := Fin.rev i
  have hvalue : b.value j = c.value j := by
    calc
      b.value j = s.quadratic (b.ambientVector j) :=
        (b.quadratic_ambientVector j).symm
      _ = q.quadratic (f.toLinearEquiv (b.ambientVector j)) :=
        (f.map_quadratic (b.ambientVector j)).symm
      _ = q.quadratic (c.ambientVector j) := by rw [vectors j]
      _ = c.value j := c.quadratic_ambientVector j
  have hunit : b.valueUnit j = c.valueUnit j := by
    apply Units.ext
    simpa only [BONG.coe_valueUnit] using hvalue
  simp only [BONG.reverseDualVector, BONG.dualVector,
    LinearEquiv.map_smul]
  rw [hunit, vectors]

section OrthogonalProductIsometry

variable {V' : Type v'} [AddCommGroup V'] [Module K V']
  {W' : Type w'} [AddCommGroup W'] [Module K W']
  {q' : QuadraticSpace K V'} {r' : QuadraticSpace K W'}
  {L' : Lattice K V'} {M' : Lattice K W'}

/-- Take the orthogonal product of two lattice isometries.  The underlying
map acts componentwise and carries the concrete product lattice exactly onto
the product of the two target lattices. -/
noncomputable def Isometry.orthogonalProduct
    (f : Isometry q q' L L') (g : Isometry r r' M M') :
    Isometry (q.orthogonalSum r) (q'.orthogonalSum r')
      (product L M) (product L' M') where
  toLinearEquiv := f.toLinearEquiv.prodCongr g.toLinearEquiv
  map_bilin := by
    intro x y
    simp only [QuadraticSpace.orthogonalSum_bilin_apply,
      LinearEquiv.prodCongr_apply]
    rw [f.map_bilin, g.map_bilin]
  map_mem := by
    intro x
    rw [mem_product_iff, mem_product_iff]
    simp only [LinearEquiv.prodCongr_apply]
    exact and_congr (f.map_mem x.1) (g.map_mem x.2)

@[simp]
theorem Isometry.orthogonalProduct_apply
    (f : Isometry q q' L L') (g : Isometry r r' M M') (x : V × W) :
    (f.orthogonalProduct g).toLinearEquiv x =
      (f.toLinearEquiv x.1, g.toLinearEquiv x.2) :=
  rfl

end OrthogonalProductIsometry

/-- Dualize a replacement-block isometry and reverse the order of its two
orthogonal factors, exactly as in the duality paragraph of Lemma 7.10. -/
noncomputable def Isometry.swappedDualOrthogonalProduct
    (f : Isometry s (q.orthogonalSum r) N (product L M)) :
    Isometry s (r.orthogonalSum q)
      (dualLattice s N)
      (product (dualLattice r M) (dualLattice q L)) := by
  let dualProduct := dualOrthogonalProductIsometry
    (q := q) (r := r) (L := L) (M := M)
  let swapProduct := orthogonalSumSwapLatticeIsometry q r
    (product (dualLattice q L) (dualLattice r M))
  let identifySwap : Isometry (r.orthogonalSum q) (r.orthogonalSum q)
      (swapLattice (product (dualLattice q L) (dualLattice r M)))
      (product (dualLattice r M) (dualLattice q L)) :=
    Isometry.ofLatticeEq (r.orthogonalSum q) swapLattice_product
  exact f.dual.trans dualProduct |>.trans swapProduct |>.trans identifySwap

@[simp]
theorem Isometry.swappedDualOrthogonalProduct_apply
    (f : Isometry s (q.orthogonalSum r) N (product L M)) (x : U) :
    f.swappedDualOrthogonalProduct.toLinearEquiv x =
      ((f.toLinearEquiv x).2, (f.toLinearEquiv x).1) := by
  simp [Isometry.swappedDualOrthogonalProduct, Isometry.trans,
    dualOrthogonalProductIsometry]

/-- Equality form of the preceding construction when the replacement and
the product already live in the same orthogonal-sum space. -/
theorem dualLattice_swap_eq_product_of_eq_product
    {N : Lattice K (V × W)} (h : N = product L M) :
    dualLattice (r.orthogonalSum q) (swapLattice N) =
      product (dualLattice r M) (dualLattice q L) := by
  rw [h, swapLattice_product, dualLattice_orthogonalProduct]

/-- The equality form bundled as the identity lattice isometry used by
subsequent consecutive-segment transport. -/
noncomputable def swappedDualOrthogonalProductIsometryOfEq
    {N : Lattice K (V × W)} (h : N = product L M) :
    Isometry (r.orthogonalSum q) (r.orthogonalSum q)
      (dualLattice (r.orthogonalSum q) (swapLattice N))
      (product (dualLattice r M) (dualLattice q L)) :=
  Isometry.ofLatticeEq (r.orthogonalSum q)
    (dualLattice_swap_eq_product_of_eq_product h)

/-- Compose the three geometric identifications used in the middle line of
Beli's general-case duality argument: identify the reverse dual of the
replacement block, dualize and swap its original product decomposition, and
identify the two reverse-dual factors. -/
noncomputable def Isometry.dualReplacementOrthogonalProduct
    {U' : Type z'} [AddCommGroup U'] [Module K U']
    {s' : QuadraticSpace K U'} {N' : Lattice K U'}
    {V' : Type v'} [AddCommGroup V'] [Module K V']
    {W' : Type w'} [AddCommGroup W'] [Module K W']
    {q' : QuadraticSpace K V'} {r' : QuadraticSpace K W'}
    {L' : Lattice K V'} {M' : Lattice K W'}
    (replacement : Isometry s (q.orthogonalSum r) N (product L M))
    (replacementDual : Isometry s s'
      (dualLattice s N) N')
    (rightDual : Isometry r r'
      (dualLattice r M) M')
    (leftDual : Isometry q q'
      (dualLattice q L) L') :
    Isometry s' (r'.orthogonalSum q') N' (product M' L') :=
  replacementDual.symm |>.trans
    replacement.swappedDualOrthogonalProduct |>.trans
    (rightDual.orthogonalProduct leftDual)

@[simp]
theorem Isometry.dualReplacementOrthogonalProduct_apply
    {U' : Type z'} [AddCommGroup U'] [Module K U']
    {s' : QuadraticSpace K U'} {N' : Lattice K U'}
    {V' : Type v'} [AddCommGroup V'] [Module K V']
    {W' : Type w'} [AddCommGroup W'] [Module K W']
    {q' : QuadraticSpace K V'} {r' : QuadraticSpace K W'}
    {L' : Lattice K V'} {M' : Lattice K W'}
    (replacement : Isometry s (q.orthogonalSum r) N (product L M))
    (replacementDual : Isometry s s'
      (dualLattice s N) N')
    (rightDual : Isometry r r'
      (dualLattice r M) M')
    (leftDual : Isometry q q'
      (dualLattice q L) L') (x : U') :
    (replacement.dualReplacementOrthogonalProduct replacementDual
      rightDual leftDual).toLinearEquiv x =
      (rightDual.toLinearEquiv
          (replacement.toLinearEquiv
            (replacementDual.symm.toLinearEquiv x)).2,
        leftDual.toLinearEquiv
          (replacement.toLinearEquiv
            (replacementDual.symm.toLinearEquiv x)).1) := by
  simp [Isometry.dualReplacementOrthogonalProduct, Isometry.trans]

end Lattice

namespace BONG.OrthogonalPrefixRawSeed

universe u v w z

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}
  {n steps baseLength : Nat}

/-- Original replacement data at the unique stopping node.  It is the exact
formal counterpart of
`[x_s,...,x_t] ⊥ [x_{t+1},...,x_u] = [y_s,...,y_u]`:
`replacement` is that equality as a lattice isometry, while the other three
isometries identify the reversed integral duals with the concrete segments
used by the second endpoint argument. -/
structure DualReplacementAtStop
    {U : Type z} [AddCommGroup U] [Module K U]
    {s : QuadraticSpace K U} {P : Lattice K U}
    {targetLength start : Nat} {bound : start + baseLength ≤ targetLength}
    {target : BONG U s P targetLength}
    {N : Lattice K (V × W)}
    (source : BONG V q L n)
    (base : BONG (V × W) (q.orthogonalSum r) N baseLength)
    (segment : SegmentWitness target start baseLength bound) where
  LeftOriginal : Type w
  [leftOriginalAddCommGroup : AddCommGroup LeftOriginal]
  [leftOriginalModule : Module K LeftOriginal]
  leftOriginalForm : QuadraticSpace K LeftOriginal
  leftOriginalLattice : Lattice K LeftOriginal
  RightOriginal : Type v
  [rightOriginalAddCommGroup : AddCommGroup RightOriginal]
  [rightOriginalModule : Module K RightOriginal]
  rightOriginalForm : QuadraticSpace K RightOriginal
  rightOriginalLattice : Lattice K RightOriginal
  ReplacementOriginal : Type (max v w)
  [replacementOriginalAddCommGroup : AddCommGroup ReplacementOriginal]
  [replacementOriginalModule : Module K ReplacementOriginal]
  replacementOriginalForm : QuadraticSpace K ReplacementOriginal
  replacementOriginalLattice : Lattice K ReplacementOriginal
  replacement : Lattice.Isometry replacementOriginalForm
    (leftOriginalForm.orthogonalSum rightOriginalForm)
    replacementOriginalLattice
    (Lattice.product leftOriginalLattice rightOriginalLattice)
  replacementDual : Lattice.Isometry replacementOriginalForm
    (s.restrict segment.carrier segment.nondegenerate)
    (Lattice.dualLattice replacementOriginalForm replacementOriginalLattice)
    segment.lattice
  rightDual : Lattice.Isometry rightOriginalForm q
    (Lattice.dualLattice rightOriginalForm rightOriginalLattice) L
  leftDual : Lattice.Isometry leftOriginalForm r
    (Lattice.dualLattice leftOriginalForm leftOriginalLattice) M
  productVectors : ∀ i : Fin baseLength,
    (replacement.dualReplacementOrthogonalProduct replacementDual
      rightDual leftDual).toLinearEquiv (segment.bong.ambientVector i) =
      base.ambientVector i

/-- A left-first orthogonal BONG becomes a right-first orthogonal BONG after
reverse duality and exchange of the two factors.  The four vector hypotheses
are the literal consecutive-block formulas from the paper; the conclusion is
exactly the last commuting square required by `DualReplacementAtStop`.

The common rank is written `leftLength + rightLength`.  Indices are built
directly in that common finite type, avoiding any definitional dependence on
the order in which natural-number addition happens to be displayed. -/
theorem factorVectors_of_consecutiveBONGs
    {leftLength rightLength : Nat}
    {LeftOriginal : Type w} [AddCommGroup LeftOriginal]
    [Module K LeftOriginal]
    (leftOriginalForm : QuadraticSpace K LeftOriginal)
    (leftOriginalLattice : Lattice K LeftOriginal)
    {RightOriginal : Type v} [AddCommGroup RightOriginal]
    [Module K RightOriginal]
    (rightOriginalForm : QuadraticSpace K RightOriginal)
    (rightOriginalLattice : Lattice K RightOriginal)
    (leftBONG : BONG LeftOriginal leftOriginalForm leftOriginalLattice
      leftLength)
    (rightBONG : BONG RightOriginal rightOriginalForm rightOriginalLattice
      rightLength)
    (productBONG : BONG (LeftOriginal × RightOriginal)
      (leftOriginalForm.orthogonalSum rightOriginalForm)
      (Lattice.product leftOriginalLattice rightOriginalLattice)
      (leftLength + rightLength))
    (productLeftVectors : ∀ i : Fin leftLength,
      productBONG.ambientVector
          ⟨i.val, by omega⟩ =
        (leftBONG.ambientVector i, 0))
    (productRightVectors : ∀ j : Fin rightLength,
      productBONG.ambientVector
          ⟨leftLength + j.val, by omega⟩ =
        (0, rightBONG.ambientVector j))
    (rightDual : Lattice.Isometry rightOriginalForm q
      (Lattice.dualLattice rightOriginalForm rightOriginalLattice) L)
    (leftDual : Lattice.Isometry leftOriginalForm r
      (Lattice.dualLattice leftOriginalForm leftOriginalLattice) M)
    {N : Lattice K (V × W)}
    (base : BONG (V × W) (q.orthogonalSum r) N
      (leftLength + rightLength))
    (baseRightVectors : ∀ j : Fin rightLength,
      base.ambientVector
          ⟨j.val, by omega⟩ =
        (rightDual.toLinearEquiv (rightBONG.reverseDualVector j), 0))
    (baseLeftVectors : ∀ i : Fin leftLength,
      base.ambientVector
          ⟨rightLength + i.val, by omega⟩ =
        (0, leftDual.toLinearEquiv (leftBONG.reverseDualVector i))) :
    ∀ k : Fin (leftLength + rightLength),
      (rightDual.orthogonalProduct leftDual).toLinearEquiv
          ((productBONG.reverseDualVector k).2,
            (productBONG.reverseDualVector k).1) =
        base.ambientVector k := by
  intro k
  by_cases hk : k.val < rightLength
  · let j : Fin rightLength := ⟨k.val, hk⟩
    let originalIndex : Fin (leftLength + rightLength) :=
      ⟨leftLength + (Fin.rev j).val, by omega⟩
    have hrev : Fin.rev k = originalIndex := by
      apply Fin.ext
      simp only [Fin.rev, originalIndex, j]
      omega
    have hvalue : productBONG.value (Fin.rev k) =
        rightBONG.value (Fin.rev j) := by
      calc
        productBONG.value (Fin.rev k) =
            (leftOriginalForm.orthogonalSum rightOriginalForm).quadratic
              (productBONG.ambientVector (Fin.rev k)) :=
          (productBONG.quadratic_ambientVector (Fin.rev k)).symm
        _ = (leftOriginalForm.orthogonalSum rightOriginalForm).quadratic
              (0, rightBONG.ambientVector (Fin.rev j)) := by
          rw [hrev]
          exact congrArg
            (leftOriginalForm.orthogonalSum rightOriginalForm).quadratic
            (productRightVectors (Fin.rev j))
        _ = rightOriginalForm.quadratic
              (rightBONG.ambientVector (Fin.rev j)) := by
          simp [QuadraticSpace.orthogonalSum_quadratic_apply]
        _ = rightBONG.value (Fin.rev j) :=
          rightBONG.quadratic_ambientVector (Fin.rev j)
    have hunit : productBONG.valueUnit (Fin.rev k) =
        rightBONG.valueUnit (Fin.rev j) := by
      apply Units.ext
      simpa only [BONG.coe_valueUnit] using hvalue
    have hunitOriginal : productBONG.valueUnit originalIndex =
        rightBONG.valueUnit (Fin.rev j) := by
      rw [← hrev]
      exact hunit
    have hproduct : productBONG.reverseDualVector k =
        (0, rightBONG.reverseDualVector j) := by
      simp only [BONG.reverseDualVector, BONG.dualVector]
      rw [hrev, productRightVectors, hunitOriginal]
      simp [j]
    have hkIndex : k =
        (⟨j.val, by omega⟩ : Fin (leftLength + rightLength)) := by
      apply Fin.ext
      rfl
    rw [hproduct, Lattice.Isometry.orthogonalProduct_apply, hkIndex,
      baseRightVectors]
    simp
  · have hright : rightLength ≤ k.val := by omega
    let i : Fin leftLength := ⟨k.val - rightLength, by omega⟩
    let originalIndex : Fin (leftLength + rightLength) :=
      ⟨(Fin.rev i).val, by omega⟩
    have hrev : Fin.rev k = originalIndex := by
      apply Fin.ext
      simp only [Fin.rev, originalIndex, i]
      omega
    have hvalue : productBONG.value (Fin.rev k) =
        leftBONG.value (Fin.rev i) := by
      calc
        productBONG.value (Fin.rev k) =
            (leftOriginalForm.orthogonalSum rightOriginalForm).quadratic
              (productBONG.ambientVector (Fin.rev k)) :=
          (productBONG.quadratic_ambientVector (Fin.rev k)).symm
        _ = (leftOriginalForm.orthogonalSum rightOriginalForm).quadratic
              (leftBONG.ambientVector (Fin.rev i), 0) := by
          rw [hrev]
          exact congrArg
            (leftOriginalForm.orthogonalSum rightOriginalForm).quadratic
            (productLeftVectors (Fin.rev i))
        _ = leftOriginalForm.quadratic
              (leftBONG.ambientVector (Fin.rev i)) := by
          simp [QuadraticSpace.orthogonalSum_quadratic_apply]
        _ = leftBONG.value (Fin.rev i) :=
          leftBONG.quadratic_ambientVector (Fin.rev i)
    have hunit : productBONG.valueUnit (Fin.rev k) =
        leftBONG.valueUnit (Fin.rev i) := by
      apply Units.ext
      simpa only [BONG.coe_valueUnit] using hvalue
    have hunitOriginal : productBONG.valueUnit originalIndex =
        leftBONG.valueUnit (Fin.rev i) := by
      rw [← hrev]
      exact hunit
    have hproduct : productBONG.reverseDualVector k =
        (leftBONG.reverseDualVector i, 0) := by
      simp only [BONG.reverseDualVector, BONG.dualVector]
      rw [hrev, productLeftVectors, hunitOriginal]
      simp [i]
    have hkIndex : k =
        (⟨rightLength + i.val, by omega⟩ :
          Fin (leftLength + rightLength)) := by
      apply Fin.ext
      simp only [i]
      omega
    rw [hproduct, Lattice.Isometry.orthogonalProduct_apply, hkIndex,
      baseLeftVectors]
    simp

/-- Construct the stopping replacement diagram from BONG-level data.  The
commuting equation is now a consequence of: the original replacement map on
its BONG, the reverse-dual realization of the replacement segment, and the
componentwise realization of the swapped product dual. -/
noncomputable def DualReplacementAtStop.ofBONGDiagram
    {U : Type z} [AddCommGroup U] [Module K U]
    {s : QuadraticSpace K U} {P : Lattice K U}
    {targetLength start : Nat} {bound : start + baseLength ≤ targetLength}
    {target : BONG U s P targetLength}
    {N : Lattice K (V × W)}
    (source : BONG V q L n)
    (base : BONG (V × W) (q.orthogonalSum r) N baseLength)
    (segment : SegmentWitness target start baseLength bound)
    {LeftOriginal : Type w} [AddCommGroup LeftOriginal]
    [Module K LeftOriginal]
    (leftOriginalForm : QuadraticSpace K LeftOriginal)
    (leftOriginalLattice : Lattice K LeftOriginal)
    {RightOriginal : Type v} [AddCommGroup RightOriginal]
    [Module K RightOriginal]
    (rightOriginalForm : QuadraticSpace K RightOriginal)
    (rightOriginalLattice : Lattice K RightOriginal)
    {ReplacementOriginal : Type (max v w)}
    [AddCommGroup ReplacementOriginal] [Module K ReplacementOriginal]
    (replacementOriginalForm : QuadraticSpace K ReplacementOriginal)
    (replacementOriginalLattice : Lattice K ReplacementOriginal)
    (replacementBONG : BONG ReplacementOriginal replacementOriginalForm
      replacementOriginalLattice baseLength)
    (productBONG : BONG (LeftOriginal × RightOriginal)
      (leftOriginalForm.orthogonalSum rightOriginalForm)
      (Lattice.product leftOriginalLattice rightOriginalLattice) baseLength)
    (replacement : Lattice.Isometry replacementOriginalForm
      (leftOriginalForm.orthogonalSum rightOriginalForm)
      replacementOriginalLattice
      (Lattice.product leftOriginalLattice rightOriginalLattice))
    (replacementVectors : ∀ i : Fin baseLength,
      replacement.toLinearEquiv (replacementBONG.ambientVector i) =
        productBONG.ambientVector i)
    (replacementDual : Lattice.Isometry replacementOriginalForm
      (s.restrict segment.carrier segment.nondegenerate)
      (Lattice.dualLattice replacementOriginalForm
        replacementOriginalLattice)
      segment.lattice)
    (replacementDualVectors : ∀ i : Fin baseLength,
      replacementDual.toLinearEquiv (replacementBONG.reverseDualVector i) =
        segment.bong.ambientVector i)
    (rightDual : Lattice.Isometry rightOriginalForm q
      (Lattice.dualLattice rightOriginalForm rightOriginalLattice) L)
    (leftDual : Lattice.Isometry leftOriginalForm r
      (Lattice.dualLattice leftOriginalForm leftOriginalLattice) M)
    (factorVectors : ∀ i : Fin baseLength,
      (rightDual.orthogonalProduct leftDual).toLinearEquiv
          ((productBONG.reverseDualVector i).2,
            (productBONG.reverseDualVector i).1) =
        base.ambientVector i) :
    DualReplacementAtStop (M := M) source base segment where
  LeftOriginal := LeftOriginal
  leftOriginalForm := leftOriginalForm
  leftOriginalLattice := leftOriginalLattice
  RightOriginal := RightOriginal
  rightOriginalForm := rightOriginalForm
  rightOriginalLattice := rightOriginalLattice
  ReplacementOriginal := ReplacementOriginal
  replacementOriginalForm := replacementOriginalForm
  replacementOriginalLattice := replacementOriginalLattice
  replacement := replacement
  replacementDual := replacementDual
  rightDual := rightDual
  leftDual := leftDual
  productVectors := by
    intro i
    rw [Lattice.Isometry.dualReplacementOrthogonalProduct_apply]
    have hinverse :
        replacementDual.symm.toLinearEquiv
            (segment.bong.ambientVector i) =
          replacementBONG.reverseDualVector i := by
      apply replacementDual.toLinearEquiv.injective
      rw [replacementDualVectors i]
      exact replacementDual.toLinearEquiv.apply_symm_apply _
    rw [hinverse]
    rw [replacement.map_reverseDualVector_of_ambientVector_eq
      replacementBONG productBONG replacementVectors i]
    exact factorVectors i

/-- Paper-facing constructor for the general stopping replacement in Lemma
7.10.  The product BONG is given by its literal left and right consecutive
blocks, while the stopping BONG is given by the reversed right and left dual
blocks.  Therefore no final whole-product commuting equation is required from
the caller. -/
noncomputable def DualReplacementAtStop.ofConsecutiveBONGDiagram
    {leftLength rightLength : Nat}
    {U : Type z} [AddCommGroup U] [Module K U]
    {s : QuadraticSpace K U} {P : Lattice K U}
    {targetLength start : Nat}
    {bound : start + (leftLength + rightLength) ≤ targetLength}
    {target : BONG U s P targetLength}
    {N : Lattice K (V × W)}
    (source : BONG V q L n)
    (base : BONG (V × W) (q.orthogonalSum r) N
      (leftLength + rightLength))
    (segment : SegmentWitness target start (leftLength + rightLength) bound)
    {LeftOriginal : Type w} [AddCommGroup LeftOriginal]
    [Module K LeftOriginal]
    (leftOriginalForm : QuadraticSpace K LeftOriginal)
    (leftOriginalLattice : Lattice K LeftOriginal)
    {RightOriginal : Type v} [AddCommGroup RightOriginal]
    [Module K RightOriginal]
    (rightOriginalForm : QuadraticSpace K RightOriginal)
    (rightOriginalLattice : Lattice K RightOriginal)
    (leftBONG : BONG LeftOriginal leftOriginalForm leftOriginalLattice
      leftLength)
    (rightBONG : BONG RightOriginal rightOriginalForm rightOriginalLattice
      rightLength)
    {ReplacementOriginal : Type (max v w)}
    [AddCommGroup ReplacementOriginal] [Module K ReplacementOriginal]
    (replacementOriginalForm : QuadraticSpace K ReplacementOriginal)
    (replacementOriginalLattice : Lattice K ReplacementOriginal)
    (replacementBONG : BONG ReplacementOriginal replacementOriginalForm
      replacementOriginalLattice (leftLength + rightLength))
    (productBONG : BONG (LeftOriginal × RightOriginal)
      (leftOriginalForm.orthogonalSum rightOriginalForm)
      (Lattice.product leftOriginalLattice rightOriginalLattice)
      (leftLength + rightLength))
    (productLeftVectors : ∀ i : Fin leftLength,
      productBONG.ambientVector
          ⟨i.val, by omega⟩ =
        (leftBONG.ambientVector i, 0))
    (productRightVectors : ∀ j : Fin rightLength,
      productBONG.ambientVector
          ⟨leftLength + j.val, by omega⟩ =
        (0, rightBONG.ambientVector j))
    (replacement : Lattice.Isometry replacementOriginalForm
      (leftOriginalForm.orthogonalSum rightOriginalForm)
      replacementOriginalLattice
      (Lattice.product leftOriginalLattice rightOriginalLattice))
    (replacementVectors : ∀ i : Fin (leftLength + rightLength),
      replacement.toLinearEquiv (replacementBONG.ambientVector i) =
        productBONG.ambientVector i)
    (replacementDual : Lattice.Isometry replacementOriginalForm
      (s.restrict segment.carrier segment.nondegenerate)
      (Lattice.dualLattice replacementOriginalForm
        replacementOriginalLattice)
      segment.lattice)
    (replacementDualVectors : ∀ i : Fin (leftLength + rightLength),
      replacementDual.toLinearEquiv (replacementBONG.reverseDualVector i) =
        segment.bong.ambientVector i)
    (rightDual : Lattice.Isometry rightOriginalForm q
      (Lattice.dualLattice rightOriginalForm rightOriginalLattice) L)
    (leftDual : Lattice.Isometry leftOriginalForm r
      (Lattice.dualLattice leftOriginalForm leftOriginalLattice) M)
    (baseRightVectors : ∀ j : Fin rightLength,
      base.ambientVector
          ⟨j.val, by omega⟩ =
        (rightDual.toLinearEquiv (rightBONG.reverseDualVector j), 0))
    (baseLeftVectors : ∀ i : Fin leftLength,
      base.ambientVector
          ⟨rightLength + i.val, by omega⟩ =
        (0, leftDual.toLinearEquiv (leftBONG.reverseDualVector i))) :
    DualReplacementAtStop (M := M) source base segment :=
  DualReplacementAtStop.ofBONGDiagram (M := M) source base segment
    leftOriginalForm leftOriginalLattice rightOriginalForm
    rightOriginalLattice replacementOriginalForm replacementOriginalLattice
    replacementBONG productBONG replacement replacementVectors
    replacementDual replacementDualVectors rightDual leftDual
    (factorVectors_of_consecutiveBONGs leftOriginalForm leftOriginalLattice
      rightOriginalForm rightOriginalLattice leftBONG rightBONG productBONG
      productLeftVectors productRightVectors rightDual leftDual base
      baseRightVectors baseLeftVectors)

/-- Dependent propagation of original replacement data through the unchanged
prefix constructors of a raw seed. -/
def StopDualReplacementData
    {U : Type z} [AddCommGroup U] [Module K U]
    {s : QuadraticSpace K U} {P : Lattice K U}
    {targetLength start : Nat} {bound : start + baseLength ≤ targetLength}
    {target : BONG U s P targetLength}
    {b : BONG V q L n}
    (S : OrthogonalPrefixRawSeed r M baseLength (steps := steps) b)
    (segment : SegmentWitness target start baseLength bound) : Type _ := by
  induction S with
  | @stop V _ _ q L n N source base =>
      exact DualReplacementAtStop (M := M) source base segment
  | cons _ _ _ _ tailData =>
      exact tailData

/-- The isometry and basis-compatibility pair at an arbitrary raw stopping
node. -/
def StopSegmentProductIsometryData
    {U : Type z} [AddCommGroup U] [Module K U]
    {s : QuadraticSpace K U} {P : Lattice K U}
    {targetLength start : Nat} {bound : start + baseLength ≤ targetLength}
    {target : BONG U s P targetLength}
    {b : BONG V q L n}
    (S : OrthogonalPrefixRawSeed r M baseLength (steps := steps) b)
    (segment : SegmentWitness target start baseLength bound) : Type _ :=
  { segmentToProduct : S.StopSegmentProductIsometry segment //
    S.StopSegmentProductVectorEq segment segmentToProduct
  }

/-- Forget the original block models after their dualized composite has been
formed. -/
noncomputable def StopDualReplacementData.toSegmentProductIsometryData
    {U : Type z} [AddCommGroup U] [Module K U]
    {s : QuadraticSpace K U} {P : Lattice K U}
    {targetLength start : Nat} {bound : start + baseLength ≤ targetLength}
    {target : BONG U s P targetLength}
    {b : BONG V q L n}
    (S : OrthogonalPrefixRawSeed r M baseLength (steps := steps) b)
    (segment : SegmentWitness target start baseLength bound)
    (D : S.StopDualReplacementData segment) :
    S.StopSegmentProductIsometryData segment := by
  induction S with
  | stop source base =>
      letI := D.leftOriginalAddCommGroup
      letI := D.leftOriginalModule
      letI := D.rightOriginalAddCommGroup
      letI := D.rightOriginalModule
      letI := D.replacementOriginalAddCommGroup
      letI := D.replacementOriginalModule
      exact ⟨
        D.replacement.dualReplacementOrthogonalProduct
          D.replacementDual D.rightDual D.leftDual,
        D.productVectors
      ⟩
  | cons generator anisotropic tail tailSeed ih =>
      exact ih D

/-- Dualizing the original consecutive-block equality constructs the complete
commutative diagram required by M603. -/
noncomputable def targetPrefixSegmentProductIsometryDataOfDualReplacement
    (source : BONG V q L n) (hsteps : steps ≤ n)
    {P : Lattice K (V × W)}
    (target : BONG (V × W) (q.orthogonalSum r) P
      (baseLength + steps))
    (leftVectors : ∀ i : Fin steps,
      target.ambientVector (orthogonalProductLeftIndex baseLength i) =
        (source.ambientVector (prefixSourceIndex hsteps i), 0))
    (D :
      let model := extractTargetPrefixSegment (M := M) source hsteps target
        leftVectors
      model.extraction.seed.StopDualReplacementData model.segment) :
    TargetPrefixSegmentProductIsometryData (M := M) source hsteps target
      leftVectors := by
  let model := extractTargetPrefixSegment (M := M) source hsteps target
    leftVectors
  let E := StopDualReplacementData.toSegmentProductIsometryData
    model.extraction.seed model.segment D
  exact
    { segmentToProduct := E.1
      productVectors := E.2 }

end BONG.OrthogonalPrefixRawSeed

namespace BONG.GoodBONG

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}
  {n rightLength : Nat}

/-- Lemma 7.10 with the replacement identity supplied as the dualized
commutative diagram rather than as a pre-established equality of the hidden
stopping lattice. -/
theorem beli2019Lemma710General_of_targetPrefixSegmentProductIsometryData
    {baseTail steps : Nat} {N : Lattice K (V × W)}
    (b : GoodBONG q L n) (hsteps : steps ≤ n)
    (right : BONG W r M (rightLength + 1))
    (target : GoodBONG (q.orthogonalSum r) N
      ((baseTail + 1) + steps))
    (leftVectors : ∀ i : Fin steps,
      target.toBONG.ambientVector
          (orthogonalProductLeftIndex (baseTail + 1) i) =
        (b.toBONG.ambientVector
          (OrthogonalPrefixRawSeed.prefixSourceIndex hsteps i), 0))
    (D : OrthogonalPrefixRawSeed.TargetPrefixSegmentProductIsometryData
      (M := M) b.toBONG hsteps target.toBONG leftVectors)
    (hlast : ∀ hpos : 0 < steps,
      b.order ⟨steps - 1, by omega⟩ ≤ right.order 0) :
    N = Lattice.product L M :=
  b.beli2019Lemma710General_of_targetPrefixSegmentProductEq hsteps right
    target leftVectors (D.segmentProductEq _ _ _ _) hlast

end BONG.GoodBONG

end Bong
