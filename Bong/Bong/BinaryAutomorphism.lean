/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryUniqueness
import Bong.Bong.Existence
import Bong.Bong.Map
import Bong.Lattice.Automorphism

/-!
# Orthogonal-group inclusion for nested binary lattices

This file completes the second assertion of Beli (2003), Lemma 3.2(i).  If two
binary lattices have a common norm generator and `L ≤ M`, every integral
orthogonal automorphism of `L` stabilizes `M`; this gives an injective group
homomorphism `O(L) → O(M)`.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V}

namespace BONG

/-- Mapping a binary BONG by an ambient isometry preserves its relative order. -/
@[simp]
theorem binaryOrderGap_map (f : QuadraticSpace.Isometry q q)
    (b : BONG V q L 2) :
    (b.map f).binaryOrderGap = b.binaryOrderGap := by
  rw [binaryOrderGap, binaryOrderGap, order_map, order_map]

/-- An automorphism of the smaller binary lattice also stabilizes the larger
lattice when the two BONGs have a common head norm generator. -/
theorem map_eq_of_le_of_head_eq
    (b : BONG V q L 2) (c : BONG V q M 2)
    (hhead : b.head = c.head) (hLM : L ≤ M)
    (f : Lattice.IntegralOrthogonalGroup q L) :
    Lattice.map f.toLinearEquiv M = M := by
  let x := f.toLinearEquiv b.head
  have hxL : x ∈ L := by
    exact (f.map_mem b.head).1 b.head_isNormGenerator.mem
  have hxM : x ∈ M := hLM hxL
  have generatorM : Lattice.IsNormGenerator q M x := by
    constructor
    · exact hxM
    · calc
        Lattice.normIdeal q M =
            Lattice.principalIdeal (K := K) (q.quadratic c.head) :=
          c.head_isNormGenerator.normIdeal_eq
        _ = Lattice.principalIdeal (K := K) (q.quadratic b.head) := by
          rw [hhead]
        _ = Lattice.principalIdeal (K := K) (q.quadratic x) := by
          rw [f.map_quadratic]
  have anisotropicM : q.IsAnisotropic x :=
    f.toQuadraticSpaceIsometry.map_isAnisotropic
      b.head_isAnisotropic
  have hfin : Module.finrank K V = 2 := b.length_eq_finrank.symm
  let d : BONG V q M 2 :=
    BONG.ofNormGeneratorBinary q M x generatorM anisotropicM hfin
  let mapped : BONG V q (Lattice.map f.toLinearEquiv M) 2 :=
    c.map f.toQuadraticSpaceIsometry
  have hmappedHead : mapped.head = x := by
    calc
      mapped.head = mapped.ambientVector 0 :=
        mapped.ambientVector_zero_eq_head.symm
      _ = f.toLinearEquiv (c.ambientVector 0) := by
        exact ambientVector_map f.toQuadraticSpaceIsometry c 0
      _ = f.toLinearEquiv c.head :=
        congrArg f.toLinearEquiv c.ambientVector_zero_eq_head
      _ = x := by rw [← hhead]
  have hdHead : d.head = x := by
    exact head_ofNormGeneratorBinary q M x generatorM anisotropicM hfin
  have hgap : mapped.binaryOrderGap = d.binaryOrderGap := by
    calc
      mapped.binaryOrderGap = c.binaryOrderGap :=
        binaryOrderGap_map f.toQuadraticSpaceIsometry c
      _ = d.binaryOrderGap := c.binaryOrderGap_eq d
  exact mapped.lattice_eq_of_head_eq_of_binaryOrderGap_eq d
    (hmappedHead.trans hdHead.symm) hgap

end BONG

namespace Lattice

namespace IntegralOrthogonalGroup

/-- Restrict the same ambient automorphism to the larger binary lattice. -/
noncomputable def ofBinaryCommonHead
    (b : BONG V q L 2) (c : BONG V q M 2)
    (hhead : b.head = c.head) (hLM : L ≤ M)
    (f : IntegralOrthogonalGroup q L) :
    IntegralOrthogonalGroup q M where
  toLinearEquiv := f.toLinearEquiv
  map_bilin := f.map_bilin
  map_mem x := by
    have hx := Lattice.map_mem_map_iff f.toLinearEquiv M x
    rw [b.map_eq_of_le_of_head_eq c hhead hLM f] at hx
    exact hx.symm

/-- Beli (2003), Lemma 3.2(i): the induced orthogonal-group homomorphism. -/
noncomputable def binaryInclusionHom
    (b : BONG V q L 2) (c : BONG V q M 2)
    (hhead : b.head = c.head) (hLM : L ≤ M) :
    IntegralOrthogonalGroup q L →* IntegralOrthogonalGroup q M where
  toFun := ofBinaryCommonHead b c hhead hLM
  map_one' := by
    apply Isometry.ext
    intro x
    rfl
  map_mul' f g := by
    apply Isometry.ext
    intro x
    rfl

/-- The orthogonal-group homomorphism is injective. -/
theorem binaryInclusionHom_injective
    (b : BONG V q L 2) (c : BONG V q M 2)
    (hhead : b.head = c.head) (hLM : L ≤ M) :
    Function.Injective (binaryInclusionHom b c hhead hLM) := by
  intro f g hfg
  apply Isometry.ext
  intro x
  exact congrArg
    (fun h : IntegralOrthogonalGroup q M => h.toLinearEquiv x) hfg

end IntegralOrthogonalGroup

end Lattice

end Bong
