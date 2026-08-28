/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.SectionTwo

/-!
# Beli (2019), Lemma 7.10: the prefix-extension kernel

The proof of Lemma 7.10 first treats the case in which the replaced block
reaches the right endpoint.  Starting from equality of the two remaining
tail lattices, it adjoins the common vectors `x_(s-1), ..., x_1` one at a
time.  At every step the common vector is a norm generator, so equality of
the projected lattices reconstructs equality of the parent lattices.

`BONG.PrefixLatticeExtension` records exactly this dependent chain.  Unlike
an equality of flattened lists, its recursive constructor keeps every tail
in the correct orthogonal-complement space.  The theorem
`PrefixLatticeExtension.lattice_eq` is the decreasing induction in the
paper.  Later files only need to build this chain from the order estimates
and the orthogonal-sum data of Lemma 7.10.
-/

namespace Bong

open Dyadic

universe u v

namespace Lattice

/--
A chain obtained by adjoining the same anisotropic norm generator to two
equal projected suffix lattices.  This is the lattice-level form of the
decreasing induction in Lemma 7.10 and does not presuppose a flattened BONG
for either parent lattice.
-/
inductive CommonNormGeneratorExtension
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] :
    {V : Type v} -> [AddCommGroup V] -> [Module K V] ->
    {q : QuadraticSpace K V} -> {L M : Lattice K V} -> Prop
  | suffix
      {V : Type v} [AddCommGroup V] [Module K V]
      {q : QuadraticSpace K V} {L M : Lattice K V}
      (lattice_eq : L = M) :
      CommonNormGeneratorExtension (q := q) (L := L) (M := M)
  | cons
      {V : Type v} [AddCommGroup V] [Module K V]
      {q : QuadraticSpace K V} {L M : Lattice K V} {x : V}
      (generatorL : IsNormGenerator q L x)
      (generatorM : IsNormGenerator q M x)
      (anisotropic : q.IsAnisotropic x)
      (tail : CommonNormGeneratorExtension
        (q := q.orthogonalSpace x anisotropic)
        (L := L.projectedLattice q x anisotropic)
        (M := M.projectedLattice q x anisotropic)) :
      CommonNormGeneratorExtension (q := q) (L := L) (M := M)

namespace CommonNormGeneratorExtension

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- Equality propagates through every common norm-generator step. -/
theorem lattice_eq
    [BONGReconstructionLaws.{u, v} K]
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L M : Lattice K V}
    (h : CommonNormGeneratorExtension (q := q) (L := L) (M := M)) :
    L = M := by
  induction h with
  | suffix hLM =>
      exact hLM
  | @cons V _ _ q L M x generatorL generatorM anisotropic _ ih =>
      apply Lattice.eq_of_normIdeal_eq_of_projectedLattice_eq
        q L M x generatorL generatorM anisotropic
      · rw [generatorL.normIdeal_eq, generatorM.normIdeal_eq]
      · exact ih

end CommonNormGeneratorExtension

end Lattice

namespace BONG

/--
A certificate that two BONG lattices have equal projected suffix lattices
after deleting a common prefix of norm generators.

The `suffix` constructor supplies the equality at the end of the common
prefix.  The `cons` constructor adjoins one common anisotropic norm
generator on both sides.  Its tail certificate lives in the common
orthogonal complement, so no non-dependent flattening of BONGs is needed.
-/
inductive PrefixLatticeExtension
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] :
    {V : Type v} -> [AddCommGroup V] -> [Module K V] ->
    {q : QuadraticSpace K V} -> {L M : Lattice K V} -> {n : Nat} ->
    BONG V q L n -> BONG V q M n -> Prop
  | suffix
      {V : Type v} [AddCommGroup V] [Module K V]
      {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}
      (b : BONG V q L n) (c : BONG V q M n) (lattice_eq : L = M) :
      PrefixLatticeExtension b c
  | cons
      {V : Type v} [AddCommGroup V] [Module K V]
      {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat} {x : V}
      (generatorL : Lattice.IsNormGenerator q L x)
      (generatorM : Lattice.IsNormGenerator q M x)
      (anisotropic : q.IsAnisotropic x)
      (tailL : BONG (q.vectorOrthogonal x)
        (q.orthogonalSpace x anisotropic)
        (L.projectedLattice q x anisotropic) n)
      (tailM : BONG (q.vectorOrthogonal x)
        (q.orthogonalSpace x anisotropic)
        (M.projectedLattice q x anisotropic) n)
      (tail : PrefixLatticeExtension tailL tailM) :
      PrefixLatticeExtension
        (BONG.cons x generatorL anisotropic tailL)
        (BONG.cons x generatorM anisotropic tailM)

namespace PrefixLatticeExtension

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/--
The decreasing reconstruction induction used in the right-end case of
Beli (2019), Lemma 7.10.
-/
theorem lattice_eq
    [BONGReconstructionLaws.{u, v} K]
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}
    {b : BONG V q L n} {c : BONG V q M n}
    (h : PrefixLatticeExtension b c) : L = M := by
  induction h with
  | suffix _ _ hLM =>
      exact hLM
  | @cons V _ _ q L M n x generatorL generatorM anisotropic
      tailL tailM _ ih =>
      apply Lattice.eq_of_normIdeal_eq_of_projectedLattice_eq
        q L M x generatorL generatorM anisotropic
      · rw [generatorL.normIdeal_eq, generatorM.normIdeal_eq]
      · exact ih

/-- One common norm-generator step, exposed for direct use. -/
theorem cons_lattice_eq
    [BONGReconstructionLaws.{u, v} K]
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat} {x : V}
    (generatorL : Lattice.IsNormGenerator q L x)
    (generatorM : Lattice.IsNormGenerator q M x)
    (anisotropic : q.IsAnisotropic x)
    (tailL : BONG (q.vectorOrthogonal x)
      (q.orthogonalSpace x anisotropic)
      (L.projectedLattice q x anisotropic) n)
    (tailM : BONG (q.vectorOrthogonal x)
      (q.orthogonalSpace x anisotropic)
      (M.projectedLattice q x anisotropic) n)
    (tail : PrefixLatticeExtension tailL tailM) :
    L = M :=
  (PrefixLatticeExtension.cons generatorL generatorM anisotropic
    tailL tailM tail).lattice_eq

end PrefixLatticeExtension

end BONG

end Bong
