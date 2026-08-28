/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma411Proof
import Bong.QuadraticSpace.OrthogonalMap

/-!
# Beli (2003), Theorem 1: the reverse inclusion

The recursive Section 6 group starts with the binary group of Lemma 3.7 and,
at every new head, adjoins the first adjacent group and the corresponding
two-step principal-unit group.  This is the inductive presentation used in
the paper's reverse-inclusion proof.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

namespace Lattice

variable {x : V} {anisotropic : q.IsAnisotropic x}

/-- The linear equivalence induced on `x^⊥` by an integral orthogonal map
which fixes `x`. -/
def fixingVectorOrthogonalLinearEquiv
    (g : IntegralOrthogonalGroup q L)
    (hfix : g.toLinearEquiv x = x) :
    q.vectorOrthogonal x ≃ₗ[K] q.vectorOrthogonal x where
  toFun y := ⟨g.toLinearEquiv y, by
    rw [q.mem_vectorOrthogonal_iff]
    calc
      q.bilin x (g.toLinearEquiv y) =
          q.bilin (g.toLinearEquiv x) (g.toLinearEquiv y) :=
        congrArg (fun z : V => q.bilin z (g.toLinearEquiv y)) hfix.symm
      _ = q.bilin x y := g.map_bilin x y
      _ = 0 := (q.mem_vectorOrthogonal_iff x y).1 y.property⟩
  invFun y := ⟨g.toLinearEquiv.symm y, by
    rw [q.mem_vectorOrthogonal_iff]
    have hmap := g.map_bilin x (g.toLinearEquiv.symm y)
    have hmap' :
        q.bilin (g.toLinearEquiv x) y =
          q.bilin x (g.toLinearEquiv.symm y) := by
      simpa only [g.toLinearEquiv.apply_symm_apply] using hmap
    calc
      q.bilin x (g.toLinearEquiv.symm y) =
          q.bilin (g.toLinearEquiv x) y := hmap'.symm
      _ = q.bilin x y :=
        congrArg (fun z : V => q.bilin z y) hfix
      _ = 0 := (q.mem_vectorOrthogonal_iff x y).1 y.property⟩
  left_inv y := by
    apply Subtype.ext
    exact g.toLinearEquiv.symm_apply_apply y
  right_inv y := by
    apply Subtype.ext
    exact g.toLinearEquiv.apply_symm_apply y
  map_add' y z := by
    apply Subtype.ext
    exact g.toLinearEquiv.map_add y z
  map_smul' a y := by
    apply Subtype.ext
    exact g.toLinearEquiv.map_smul a y

@[simp]
theorem fixingVectorOrthogonalLinearEquiv_coe
    (g : IntegralOrthogonalGroup q L)
    (hfix : g.toLinearEquiv x = x) (y : q.vectorOrthogonal x) :
    (fixingVectorOrthogonalLinearEquiv g hfix y : V) =
      g.toLinearEquiv y :=
  rfl

/-- Orthogonal projection commutes with an integral orthogonal map fixing the
distinguished vector. -/
theorem projectionToOrthogonal_apply_of_fix
    (g : IntegralOrthogonalGroup q L)
    (hfix : g.toLinearEquiv x = x) (y : V) :
    q.projectionToOrthogonal x anisotropic (g.toLinearEquiv y) =
      fixingVectorOrthogonalLinearEquiv g hfix
        (q.projectionToOrthogonal x anisotropic y) := by
  apply Subtype.ext
  have hmap := g.toQuadraticSpaceIsometry.map_orthogonalProjection x y
  change q.orthogonalProjection (g.toLinearEquiv x)
      (g.toLinearEquiv y) =
    g.toLinearEquiv (q.orthogonalProjection x y) at hmap
  rw [hfix] at hmap
  exact hmap

/-- Beli (2003), Lemma 2.3: an integral orthogonal map fixing a norm
generator restricts to the projected lattice. -/
noncomputable def restrictFixingVector
    (g : IntegralOrthogonalGroup q L)
    (hfix : g.toLinearEquiv x = x) :
    IntegralOrthogonalGroup (q.orthogonalSpace x anisotropic)
      (projectedLattice q L x anisotropic) where
  toLinearEquiv := fixingVectorOrthogonalLinearEquiv g hfix
  map_bilin y z := g.map_bilin y z
  map_mem y := by
    constructor
    · intro hy
      rcases (mem_projectedLattice_iff q L x anisotropic y).1 hy with
        ⟨z, hz, hprojection⟩
      apply (mem_projectedLattice_iff q L x anisotropic _).2
      refine ⟨g.toLinearEquiv z, (g.map_mem z).1 hz, ?_⟩
      rw [projectionToOrthogonal_apply_of_fix g hfix, hprojection]
    · intro hy
      rcases (mem_projectedLattice_iff q L x anisotropic _).1 hy with
        ⟨z, hz, hprojection⟩
      have hfixInv : g.toLinearEquiv.symm x = x := by
        apply g.toLinearEquiv.injective
        rw [g.toLinearEquiv.apply_symm_apply, hfix]
      apply (mem_projectedLattice_iff q L x anisotropic y).2
      refine ⟨g.toLinearEquiv.symm z, (g.symm.map_mem z).1 hz, ?_⟩
      have hinvProjection := projectionToOrthogonal_apply_of_fix
        (anisotropic := anisotropic) g.symm hfixInv z
      change q.projectionToOrthogonal x anisotropic
          (g.toLinearEquiv.symm z) =
        fixingVectorOrthogonalLinearEquiv g.symm hfixInv
          (q.projectionToOrthogonal x anisotropic z) at hinvProjection
      rw [hinvProjection, hprojection]
      apply Subtype.ext
      exact g.toLinearEquiv.symm_apply_apply y

@[simp]
theorem restrictFixingVector_toLinearEquiv_coe
    (g : IntegralOrthogonalGroup q L)
    (hfix : g.toLinearEquiv x = x) (y : q.vectorOrthogonal x) :
    ((restrictFixingVector (anisotropic := anisotropic) g hfix).toLinearEquiv
      y : V) = g.toLinearEquiv y :=
  rfl

/-- Extending the restriction from Lemma 2.3 recovers the original map. -/
theorem projectedAutomorphismHom_restrictFixingVector
    (generator : IsNormGenerator q L x)
    (g : IntegralOrthogonalGroup q L)
    (hfix : g.toLinearEquiv x = x) :
    projectedAutomorphismHom generator
      (restrictFixingVector (anisotropic := anisotropic) g hfix) = g := by
  apply Isometry.ext
  intro y
  rw [projectedAutomorphismHom_apply]
  change QuadraticSpace.orthogonalExtensionLinearEquiv
      (restrictFixingVector (anisotropic := anisotropic) g hfix).toQuadraticSpaceIsometry
        y = g.toLinearEquiv y
  rw [QuadraticSpace.orthogonalExtensionLinearEquiv_apply,
    QuadraticSpace.orthogonalExtensionLinearMap_apply]
  change (q.bilin x y / q.quadratic x) • x +
      ((restrictFixingVector (anisotropic := anisotropic) g hfix).toLinearEquiv
        (q.projectionToOrthogonal x anisotropic y) : V) =
    g.toLinearEquiv y
  rw [restrictFixingVector_toLinearEquiv_coe]
  have hdecomposition := congrArg g.toLinearEquiv
    (q.lineProjection_add_orthogonalProjection x y)
  simpa only [map_add, QuadraticSpace.lineProjection_apply,
    map_smul, hfix, QuadraticSpace.projectionToOrthogonal_coe] using
      hdecomposition

/-- Restriction in Lemma 2.3 preserves the integral spinor norm. -/
theorem integralSpinorNorm_restrictFixingVector
    (generator : IsNormGenerator q L x)
    (g : IntegralOrthogonalGroup q L)
    (hfix : g.toLinearEquiv x = x) :
    integralSpinorNorm
        (restrictFixingVector (anisotropic := anisotropic) g hfix) =
      integralSpinorNorm g := by
  calc
    integralSpinorNorm
        (restrictFixingVector (anisotropic := anisotropic) g hfix) =
        integralSpinorNorm
          (projectedAutomorphismHom generator
            (restrictFixingVector (anisotropic := anisotropic) g hfix)) :=
      (integralSpinorNorm_extendProjectedAutomorphism generator _).symm
    _ = integralSpinorNorm g := by
      rw [projectedAutomorphismHom_restrictFixingVector generator g hfix]

namespace IntegralRotation

/-- Restricting a proper integral rotation which fixes a norm generator to
the projected lattice again gives a proper integral rotation.  Properness is
the determinant part of Beli's Lemma 2.3: extension by the identity on the
norm-generator line preserves determinant. -/
noncomputable def restrictFixingVector
    (generator : IsNormGenerator q L x)
    (g : IntegralRotation q L)
    (hfix : g.toIntegralOrthogonalGroup.toLinearEquiv x = x) :
    IntegralRotation (q.orthogonalSpace x anisotropic)
      (projectedLattice q L x anisotropic) where
  toIntegralOrthogonalGroup :=
    Lattice.restrictFixingVector (anisotropic := anisotropic)
      g.toIntegralOrthogonalGroup hfix
  det_eq_one := by
    letI : Module.Finite K V := L.moduleFinite
    calc
      LinearEquiv.det
          (Lattice.restrictFixingVector (anisotropic := anisotropic)
            g.toIntegralOrthogonalGroup hfix).toLinearEquiv =
          LinearEquiv.det
            (QuadraticSpace.orthogonalExtensionLinearEquiv
              (Lattice.restrictFixingVector (anisotropic := anisotropic)
                g.toIntegralOrthogonalGroup hfix).toQuadraticSpaceIsometry) :=
        by simpa only [Lattice.Isometry.toQuadraticSpaceIsometry] using
          (QuadraticSpace.det_orthogonalExtensionLinearEquiv
            (Lattice.restrictFixingVector (anisotropic := anisotropic)
              g.toIntegralOrthogonalGroup hfix).toQuadraticSpaceIsometry).symm
      _ = LinearEquiv.det g.toIntegralOrthogonalGroup.toLinearEquiv := by
        exact congrArg
          (fun h : IntegralOrthogonalGroup q L =>
            LinearEquiv.det h.toLinearEquiv)
          (projectedAutomorphismHom_restrictFixingVector
            (anisotropic := anisotropic) generator
            g.toIntegralOrthogonalGroup hfix)
      _ = 1 := g.det_eq_one

@[simp]
theorem restrictFixingVector_toIntegralOrthogonalGroup
    (generator : IsNormGenerator q L x)
    (g : IntegralRotation q L)
    (hfix : g.toIntegralOrthogonalGroup.toLinearEquiv x = x) :
    IntegralRotation.toIntegralOrthogonalGroup
        (g.restrictFixingVector (anisotropic := anisotropic) generator hfix) =
      Lattice.restrictFixingVector (anisotropic := anisotropic)
        g.toIntegralOrthogonalGroup hfix :=
  rfl

end IntegralRotation

end Lattice

namespace BONG

/-- A two-step principal-unit depth in the expanded Section 6 presentation. -/
noncomputable def sectionSixTwoStepDepth
    (b : BONG V q L (n + 2)) (i : Fin n) : Nat :=
  Int.toNat ((b.order ⟨i.1 + 2, by omega⟩ -
    b.order ⟨i.1, by omega⟩) / 2)

/-- The join of all adjacent binary factors for a BONG of rank at least two. -/
noncomputable def sectionSixAdjacentFactor
    (b : BONG V q L (n + 2)) : Subgroup (SquareClass K) :=
  ⨆ i : Fin (n + 1),
    beliSpinorGroup K
      (b.adjacentUnitSquareClass i.castSucc (by
        simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
          Nat.succ_lt_succ i.isLt))

/-- The join of the principal-unit groups attached to all two-step gaps. -/
noncomputable def sectionSixCongruenceFactor
    (b : BONG V q L (n + 2)) : Subgroup (SquareClass K) :=
  ⨆ i : Fin n,
    beliCongruenceSquareClassSubgroup K (b.sectionSixTwoStepDepth i)

/-- The expanded Section 6 right-hand side, valid from rank two onward. -/
noncomputable def sectionSixRHS
    (b : BONG V q L (n + 2)) : Subgroup (SquareClass K) :=
  b.sectionSixAdjacentFactor ⊔ b.sectionSixCongruenceFactor

@[simp]
theorem sectionSixRHS_rankTwo (b : BONG V q L 2) :
    b.sectionSixRHS = beliSpinorGroup K b.binaryUnitSquareClass := by
  simp [sectionSixRHS, sectionSixAdjacentFactor,
    sectionSixCongruenceFactor, adjacentUnitSquareClass,
    adjacentParameter, binaryUnitSquareClass, binaryParameter]

/-- The expanded two-step depth is the depth used in Theorem 1. -/
theorem sectionSixTwoStepDepth_eq_theoremOneTwoStepDepth
    (b : BONG V q L (n + 3)) (i : Fin (n + 1)) :
    b.sectionSixTwoStepDepth i = b.theoremOneTwoStepDepth i :=
  rfl

/-- The expanded adjacent factor is definitionally the adjacent factor in
Theorem 1. -/
theorem sectionSixAdjacentFactor_eq_theoremOneAdjacentFactor
    (b : BONG V q L (n + 3)) :
    b.sectionSixAdjacentFactor = b.theoremOneAdjacentFactor :=
  rfl

/-- Joining all two-step principal-unit groups is the same as taking the one
at their minimum depth. -/
theorem sectionSixCongruenceFactor_eq_theoremOneCongruenceFactor
    (b : BONG V q L (n + 3)) :
    b.sectionSixCongruenceFactor = b.theoremOneCongruenceFactor := by
  apply le_antisymm
  · unfold sectionSixCongruenceFactor theoremOneCongruenceFactor
    apply iSup_le
    intro i
    apply beliCongruenceSquareClassSubgroup_anti K
    rw [b.sectionSixTwoStepDepth_eq_theoremOneTwoStepDepth i]
    exact b.theoremOneAlpha_le_twoStepDepth i
  · have hmem := b.theoremOneAlpha_mem_candidates
    rw [theoremOneAlphaCandidates, Finset.mem_image] at hmem
    rcases hmem with ⟨i, _hi, hidepth⟩
    unfold sectionSixCongruenceFactor theoremOneCongruenceFactor
    rw [← hidepth,
      ← b.sectionSixTwoStepDepth_eq_theoremOneTwoStepDepth i]
    exact le_iSup (fun j : Fin (n + 1) =>
      beliCongruenceSquareClassSubgroup K
        (b.sectionSixTwoStepDepth j)) i

/-- The expanded Section 6 presentation is exactly the right-hand side of
Theorem 1. -/
theorem sectionSixRHS_eq_theoremOneRHS
    (b : BONG V q L (n + 3)) :
    b.sectionSixRHS = b.theoremOneRHS := by
  unfold sectionSixRHS theoremOneRHS
  rw [b.sectionSixAdjacentFactor_eq_theoremOneAdjacentFactor,
    b.sectionSixCongruenceFactor_eq_theoremOneCongruenceFactor]

/-- Adjacent parameters commute with removing the BONG head, after shifting
the index by one. -/
theorem adjacentUnitSquareClass_tail
    (b : BONG V q L (n + 3)) (i : Fin (n + 1)) :
    b.tail.adjacentUnitSquareClass i.castSucc (by
      simpa [Nat.succ_eq_add_one] using Nat.succ_lt_succ i.isLt) =
      b.adjacentUnitSquareClass i.succ.castSucc (by
        simpa [Nat.succ_eq_add_one] using
          Nat.succ_lt_succ i.succ.isLt) := by
  unfold adjacentUnitSquareClass adjacentParameter
  congr 1
  apply Units.ext
  simp

/-- Two-step depths commute with removing the BONG head, after shifting the
index by one. -/
theorem sectionSixTwoStepDepth_tail
    (b : BONG V q L (n + 3)) (i : Fin n) :
    b.tail.sectionSixTwoStepDepth i =
      b.sectionSixTwoStepDepth i.succ := by
  unfold sectionSixTwoStepDepth
  rw [b.order_tail, b.order_tail]
  congr 3 <;> apply Fin.ext <;> simp

/-- The head factor in the Lemma 6.6 remark occurs in the expanded Section 6
right-hand side. -/
theorem lemma66FlooredHeadFactor_le_sectionSixRHS
    (b : BONG V q L (n + 3)) :
    b.lemma66FlooredHeadFactor ≤ b.sectionSixRHS := by
  unfold lemma66FlooredHeadFactor sectionSixRHS
  apply sup_le
  · apply le_trans _ le_sup_left
    unfold sectionSixAdjacentFactor
    exact le_iSup (fun i : Fin (n + 2) =>
      beliSpinorGroup K
        (b.adjacentUnitSquareClass i.castSucc (by
          simpa [Nat.succ_eq_add_one] using
            Nat.succ_lt_succ i.isLt))) 0
  · apply le_trans _ le_sup_right
    unfold lemma66FlooredCongruenceFactor lemma66FlooredDepth
      sectionSixCongruenceFactor
    apply le_trans
      (principalUnitSquareClassSubgroup_le_beliCongruence K
        (b.theoremOneTwoStepDepth 0))
    exact le_iSup (fun i : Fin (n + 1) =>
      beliCongruenceSquareClassSubgroup K
        (b.sectionSixTwoStepDepth i)) 0

/-- The expanded adjacent factor of the tail embeds in that of the full
BONG. -/
theorem sectionSixAdjacentFactor_tail_le
    (b : BONG V q L (n + 3)) :
    b.tail.sectionSixAdjacentFactor ≤ b.sectionSixAdjacentFactor := by
  unfold sectionSixAdjacentFactor
  apply iSup_le
  intro i
  rw [b.adjacentUnitSquareClass_tail i]
  exact le_iSup (fun j : Fin (n + 2) =>
    beliSpinorGroup K
      (b.adjacentUnitSquareClass j.castSucc (by
        simpa [Nat.succ_eq_add_one] using
          Nat.succ_lt_succ j.isLt))) i.succ

/-- The expanded congruence factor of the tail embeds in that of the full
BONG. -/
theorem sectionSixCongruenceFactor_tail_le
    (b : BONG V q L (n + 3)) :
    b.tail.sectionSixCongruenceFactor ≤
      b.sectionSixCongruenceFactor := by
  unfold sectionSixCongruenceFactor
  apply iSup_le
  intro i
  rw [b.sectionSixTwoStepDepth_tail i]
  exact le_iSup (fun j : Fin (n + 1) =>
    beliCongruenceSquareClassSubgroup K
      (b.sectionSixTwoStepDepth j)) i.succ

/-- The complete expanded right-hand side for the tail embeds in that of the
full BONG. -/
theorem sectionSixRHS_tail_le (b : BONG V q L (n + 3)) :
    b.tail.sectionSixRHS ≤ b.sectionSixRHS := by
  unfold sectionSixRHS
  exact sup_le_sup b.sectionSixAdjacentFactor_tail_le
    b.sectionSixCongruenceFactor_tail_le

/-- The obstruction group `H'` from the Lemma 6.6 remark also occurs in the
expanded Section 6 right-hand side. -/
theorem lemma66FlooredTailFactor_le_sectionSixRHS
    (b : BONG V q L (n + 3)) :
    b.lemma66FlooredTailFactor ≤ b.sectionSixRHS := by
  unfold lemma66FlooredTailFactor sectionSixRHS
  apply sup_le
  · apply le_trans _ le_sup_left
    unfold sectionSixAdjacentFactor
    exact le_iSup (fun i : Fin (n + 2) =>
      beliSpinorGroup K
        (b.adjacentUnitSquareClass i.castSucc (by
          simpa [Nat.succ_eq_add_one] using
            Nat.succ_lt_succ i.isLt))) 1
  · apply le_trans _ le_sup_right
    unfold lemma66FlooredCongruenceFactor lemma66FlooredDepth
      sectionSixCongruenceFactor
    apply le_trans
      (principalUnitSquareClassSubgroup_le_beliCongruence K
        (b.theoremOneTwoStepDepth 0))
    exact le_iSup (fun i : Fin (n + 1) =>
      beliCongruenceSquareClassSubgroup K
        (b.sectionSixTwoStepDepth i)) 0

variable [BinarySpinorLocalLaws.{u, v} K]

/-- The rank-two base case of the reverse-inclusion induction. -/
theorem spinorNormImageSubgroup_eq_sectionSixRHS_rankTwo
    (b : BONG V q L 2) :
    Lattice.spinorNormImageSubgroup (q := q) (L := L) =
      b.sectionSixRHS := by
  apply SetLike.coe_injective
  rw [Lattice.coe_spinorNormImageSubgroup,
    b.spinorNormImage_eq_beliSpinorGroup, b.sectionSixRHS_rankTwo]

variable [BeliLemma66Laws.{u, v} K]

/-- Property B gives the reverse inclusion into the expanded Section 6
right-hand side.  This is the induction in the proof of Theorem 1. -/
theorem spinorNormImageSubgroup_le_sectionSixRHS_of_propertyB
    (b : BONG V q L (n + 2)) (hB : b.HasPropertyB) :
    Lattice.spinorNormImageSubgroup (q := q) (L := L) ≤
      b.sectionSixRHS := by
  induction n generalizing V with
  | zero =>
      exact le_of_eq b.spinorNormImageSubgroup_eq_sectionSixRHS_rankTwo
  | succ n ih =>
      intro z hz
      rcases hz with ⟨s, rfl⟩
      by_cases htailTop : b.lemma66FlooredTailFactor = ⊤
      · have hsectionTop : b.sectionSixRHS = ⊤ := by
          apply top_unique
          rw [← htailTop]
          exact b.lemma66FlooredTailFactor_le_sectionSixRHS
        rw [hsectionTop]
        exact Subgroup.mem_top _
      · have hx : s.toIntegralOrthogonalGroup.toLinearEquiv b.head ∈ L :=
          (s.toIntegralOrthogonalGroup.map_mem b.head).1
            b.head_isNormGenerator.mem
        have heq :
            q.quadratic (s.toIntegralOrthogonalGroup.toLinearEquiv b.head) =
              q.quadratic b.head :=
          s.toIntegralOrthogonalGroup.map_quadratic b.head
        rcases b.beliLemma66_floored hB
          (s.toIntegralOrthogonalGroup.toLinearEquiv b.head) hx
          heq htailTop with ⟨f, hfapply, hfspinor⟩
        let g : Lattice.IntegralRotation q L := f⁻¹ * s
        have hgfix : g.toIntegralOrthogonalGroup.toLinearEquiv b.head =
            b.head := by
          change f.toIntegralOrthogonalGroup.toLinearEquiv.symm
              (s.toIntegralOrthogonalGroup.toLinearEquiv b.head) = b.head
          rw [← hfapply]
          exact f.toIntegralOrthogonalGroup.toLinearEquiv.symm_apply_apply
            b.head
        let t := g.restrictFixingVector
          (anisotropic := b.head_isAnisotropic)
          b.head_isNormGenerator hgfix
        have htImage : t.spinorNorm ∈
            Lattice.spinorNormImageSubgroup
              (q := q.orthogonalSpace b.head b.head_isAnisotropic)
              (L := L.projectedLattice q b.head b.head_isAnisotropic) :=
          ⟨t, rfl⟩
        have htTail : t.spinorNorm ∈
            b.tail.sectionSixRHS :=
          ih b.tail hB.tail htImage
        have htFull : t.spinorNorm ∈ b.sectionSixRHS :=
          b.sectionSixRHS_tail_le htTail
        have hfFull : f.spinorNorm ∈ b.sectionSixRHS :=
          b.lemma66FlooredHeadFactor_le_sectionSixRHS hfspinor
        have hproduct :
            f.spinorNorm * t.spinorNorm ∈
              b.sectionSixRHS :=
          b.sectionSixRHS.mul_mem hfFull htFull
        have hrestrict : t.spinorNorm = g.spinorNorm :=
          Lattice.integralSpinorNorm_restrictFixingVector
            b.head_isNormGenerator g.toIntegralOrthogonalGroup hgfix
        have hsdecomp : f * g = s := by
          simp [g]
        have hspinor : s.spinorNorm =
            f.spinorNorm * t.spinorNorm := by
          rw [← hsdecomp, Lattice.IntegralRotation.spinorNorm_mul,
            hrestrict]
        change s.spinorNorm ∈ b.sectionSixRHS
        rw [hspinor]
        exact hproduct

variable [BeliLemma67Laws.{u, v} K]
  [BeliLemma411Laws.{u, v} K]

/-- In the non-property-B branch, Lemma 4.11 makes the spinor image subgroup
full. -/
theorem spinorNormImageSubgroup_eq_top_of_not_propertyB
    (b : BONG V q L (n + 3))
    (hA : b.HasPropertyA) (hnotB : ¬b.HasPropertyB) :
    Lattice.spinorNormImageSubgroup (q := q) (L := L) = ⊤ := by
  apply SetLike.coe_injective
  rw [Lattice.coe_spinorNormImageSubgroup, b.beliLemma411 hA hnotB]
  rfl

/-- Beli (2003), Section 6: the reverse inclusion in Theorem 1. -/
theorem spinorNormImageSubgroup_le_theoremOneRHS
    (b : BONG V q L (n + 3)) (hA : b.HasPropertyA) :
    Lattice.spinorNormImageSubgroup (q := q) (L := L) ≤
      b.theoremOneRHS := by
  by_cases hB : b.HasPropertyB
  · rw [← b.sectionSixRHS_eq_theoremOneRHS]
    exact b.spinorNormImageSubgroup_le_sectionSixRHS_of_propertyB hB
  · rw [b.spinorNormImageSubgroup_eq_top_of_not_propertyB hA hB,
      b.theoremOneRHS_eq_top_of_not_propertyB hA hB]

variable [BeliLemma49Laws.{u, v} K]
  [BeliTheoremOneTernaryLaws.{u, v} K]

/-- Beli (2003), Theorem 1, in subgroup form. -/
theorem beliTheoremOne (b : BONG V q L (n + 3))
    (hA : b.HasPropertyA) :
    Lattice.spinorNormImageSubgroup (q := q) (L := L) =
      b.theoremOneRHS :=
  le_antisymm (b.spinorNormImageSubgroup_le_theoremOneRHS hA)
    (b.theoremOneRHS_le_spinorNormImage hA)

/-- Beli (2003), Theorem 1, in the original set-valued notation. -/
theorem beliTheoremOne_set (b : BONG V q L (n + 3))
    (hA : b.HasPropertyA) :
    Lattice.spinorNormImage (q := q) (L := L) =
      (b.theoremOneRHS : Set (SquareClass K)) := by
  rw [← Lattice.coe_spinorNormImageSubgroup, b.beliTheoremOne hA]

end BONG

end Bong
