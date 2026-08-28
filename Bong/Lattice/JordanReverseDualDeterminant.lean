/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.JordanReverseDualPrefixes
import Bong.Lattice.OrthogonalDecompositionPrefixSuffix
import Bong.Lattice.OrthogonalDecompositionPrefixVolume
import Bong.Lattice.UnimodularDeterminantRigidity

/-!
# Determinants of reverse-dual prefixes

At a Jordan boundary, the reverse-dual prefix is the integral dual of the
complementary suffix at the level of volume and refined determinant class.
The proof computes volumes componentwise, using reversal only to reindex the
finite sum.  This is the determinant part of O'Meara 93:24.
-/

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {t : Nat}

/-- The volume of the suffix after a proper boundary is the sum of the
volumes of precisely the components after that boundary. -/
theorem boundarySuffixVolume_eq_sum_components
    (J : JordanDecomposition q L (t + 1)) (j : Fin t) :
    let a := j.val + 1
    let b := t - j.val
    let eTotal : Fin (a + b) ≃ Fin (t + 1) :=
      finCongr (by omega)
    volumeOrder
        (J.toOrthogonalDecomposition.suffixQuadraticSublattice a).space
        (J.toOrthogonalDecomposition.suffixQuadraticSublattice a).lattice =
      ∑ i : Fin b,
        volumeOrder
          (J.component (eTotal (Fin.natAdd a i))).space
          (J.component (eTotal (Fin.natAdd a i))).lattice := by
  dsimp only
  let a := j.val + 1
  let b := t - j.val
  have hb : 0 < b := by dsimp [b]; omega
  have hlen : a + b = t + 1 := by dsimp [a, b]; omega
  let eTotal : Fin (a + b) ≃ Fin (t + 1) := finCongr hlen
  let v : Fin (t + 1) → Int := fun i ↦
    volumeOrder (J.component i).space (J.component i).lattice
  have hfull :=
    J.toOrthogonalDecomposition.volumeOrder_eq_sum_components
  have hprefix :=
    J.toOrthogonalDecomposition
      |>.volumeOrder_prefixQuadraticSublattice_eq_sum
        (n := j.val) (by omega : j.val + 1 ≤ t + 1)
  have hprefix' :
      volumeOrder
          (J.toOrthogonalDecomposition.prefixQuadraticSublattice a).space
          (J.toOrthogonalDecomposition.prefixQuadraticSublattice a).lattice =
        ∑ i : Fin a, v (eTotal (Fin.castAdd b i)) := by
    dsimp only [a]
    rw [hprefix]
    apply Finset.sum_congr rfl
    intro i _
    congr 2
  have hsplit :=
    (J.toOrthogonalDecomposition.prefixSuffixDecomposition a)
      |>.volumeOrder_eq_add_components
  rw [OrthogonalDecomposition.prefixSuffixDecomposition_zero,
    OrthogonalDecomposition.prefixSuffixDecomposition_one] at hsplit
  have hsum :
      (∑ i : Fin (t + 1), v i) =
        (∑ i : Fin a, v (eTotal (Fin.castAdd b i))) +
          ∑ i : Fin b, v (eTotal (Fin.natAdd a i)) := by
    calc
      (∑ i : Fin (t + 1), v i) =
          ∑ i : Fin (a + b), v (eTotal i) :=
        (Equiv.sum_comp eTotal v).symm
      _ = _ := Fin.sum_univ_add (fun i : Fin (a + b) ↦ v (eTotal i))
  change volumeOrder
      (J.toOrthogonalDecomposition.suffixQuadraticSublattice a).space
      (J.toOrthogonalDecomposition.suffixQuadraticSublattice a).lattice = _
  change _ = ∑ i : Fin b, v (eTotal (Fin.natAdd a i))
  rw [hfull, hsum, hprefix'] at hsplit
  omega

set_option maxHeartbeats 0 in
-- Dependent finite reindexing across a reversed Jordan boundary is expensive.
/-- The reverse-dual prefix and the complementary original suffix have
opposite volume orders. -/
theorem reverseDualBoundaryPrefix_volumeOrder
    (J : JordanDecomposition q L (t + 1)) (j : Fin t) :
    volumeOrder
        (J.reverseDual.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice ((Fin.rev j).val + 1)).space
        (J.reverseDual.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice ((Fin.rev j).val + 1)).lattice =
      -volumeOrder
        (J.toOrthogonalDecomposition
          |>.suffixQuadraticSublattice (j.val + 1)).space
        (J.toOrthogonalDecomposition
          |>.suffixQuadraticSublattice (j.val + 1)).lattice := by
  classical
  let a := j.val + 1
  let b := t - j.val
  have hb : 0 < b := by dsimp [b]; omega
  have hlen : a + b = t + 1 := by dsimp [a, b]; omega
  have hrevLen : (Fin.rev j).val + 1 = b := by
    rw [Fin.val_rev]
    dsimp [b]
    omega
  let eTotal : Fin (a + b) ≃ Fin (t + 1) := finCongr hlen
  let eB : Fin b ≃ Fin ((Fin.rev j).val + 1) := finCongr hrevLen.symm
  let v : Fin (t + 1) → Int := fun i ↦
    volumeOrder (J.component i).space (J.component i).lattice
  have hsuffix := J.boundarySuffixVolume_eq_sum_components j
  dsimp only at hsuffix
  have hrev :=
    J.reverseDual.toOrthogonalDecomposition
      |>.volumeOrder_prefixQuadraticSublattice_eq_sum
        (n := (Fin.rev j).val) (by omega)
  have hcomponent (i : Fin b) :
      volumeOrder
          (J.reverseDual.toOrthogonalDecomposition.prefixBlockSpace
            (by omega : (Fin.rev j).val + 1 ≤ t + 1) (eB i))
          (J.reverseDual.toOrthogonalDecomposition.prefixBlockLattice
            (by omega : (Fin.rev j).val + 1 ≤ t + 1) (eB i)) =
        -v (eTotal (Fin.natAdd a (Fin.rev i))) := by
    let idx : Fin (t + 1) :=
      (J.reverseDual.toOrthogonalDecomposition.prefixIndexEquiv
        ((Fin.rev j).val + 1) (by omega) (eB i)).1
    change volumeOrder (J.component (Fin.rev idx)).space
        (dualLattice (J.component (Fin.rev idx)).space
          (J.component (Fin.rev idx)).lattice) = _
    rw [volumeOrder_dualLattice]
    have hidxVal : idx.val = i.val := by rfl
    have hidx : Fin.rev idx =
        eTotal (Fin.natAdd a (Fin.rev i)) := by
      apply Fin.ext
      rw [Fin.val_rev, hidxVal]
      simp only [eTotal, finCongr_apply]
      dsimp [a, b]
      omega
    rw [hidx]
  have hrev' :
      volumeOrder
          (J.reverseDual.toOrthogonalDecomposition
            |>.prefixQuadraticSublattice ((Fin.rev j).val + 1)).space
          (J.reverseDual.toOrthogonalDecomposition
            |>.prefixQuadraticSublattice ((Fin.rev j).val + 1)).lattice =
        ∑ i : Fin b, -v (eTotal (Fin.natAdd a (Fin.rev i))) := by
    calc
      _ = ∑ i : Fin ((Fin.rev j).val + 1),
          volumeOrder
            (J.reverseDual.toOrthogonalDecomposition.prefixBlockSpace
              (by omega : (Fin.rev j).val + 1 ≤ t + 1) i)
            (J.reverseDual.toOrthogonalDecomposition.prefixBlockLattice
              (by omega : (Fin.rev j).val + 1 ≤ t + 1) i) := hrev
      _ = ∑ i : Fin b,
          volumeOrder
            (J.reverseDual.toOrthogonalDecomposition.prefixBlockSpace
              (by omega : (Fin.rev j).val + 1 ≤ t + 1) (eB i))
            (J.reverseDual.toOrthogonalDecomposition.prefixBlockLattice
              (by omega : (Fin.rev j).val + 1 ≤ t + 1) (eB i)) := by
        exact (Equiv.sum_comp eB fun i : Fin ((Fin.rev j).val + 1) ↦
          volumeOrder
            (J.reverseDual.toOrthogonalDecomposition.prefixBlockSpace
              (by omega : (Fin.rev j).val + 1 ≤ t + 1) i)
            (J.reverseDual.toOrthogonalDecomposition.prefixBlockLattice
              (by omega : (Fin.rev j).val + 1 ≤ t + 1) i)).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        exact hcomponent i
  rw [hrev']
  have hreverse :
      (∑ i : Fin b, v (eTotal (Fin.natAdd a (Fin.rev i)))) =
        ∑ i : Fin b, v (eTotal (Fin.natAdd a i)) := by
    exact Equiv.sum_comp Fin.revPerm
      (fun i : Fin b ↦ v (eTotal (Fin.natAdd a i)))
  rw [Finset.sum_neg_distrib, hreverse]
  simpa only [a, b, eTotal] using (congrArg Neg.neg hsuffix).symm

/-- The refined determinant class of a reverse-dual boundary prefix is the
inverse class of the complementary original suffix. -/
theorem reverseDualBoundaryPrefix_determinantClass
    (J : JordanDecomposition q L (t + 1)) (j : Fin t) :
    determinantClass
        (J.reverseDual.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice ((Fin.rev j).val + 1)).space
        (J.reverseDual.toOrthogonalDecomposition
          |>.prefixQuadraticSublattice ((Fin.rev j).val + 1)).lattice =
      (determinantClass
        (J.toOrthogonalDecomposition
          |>.suffixQuadraticSublattice (j.val + 1)).space
        (J.toOrthogonalDecomposition
          |>.suffixQuadraticSublattice (j.val + 1)).lattice)⁻¹ := by
  let RP := J.reverseDual.toOrthogonalDecomposition
    |>.prefixQuadraticSublattice ((Fin.rev j).val + 1)
  let S := J.toOrthogonalDecomposition
    |>.suffixQuadraticSublattice (j.val + 1)
  have hvolume : volumeOrder RP.space RP.lattice =
      volumeOrder S.space (dualLattice S.space S.lattice) :=
    (J.reverseDualBoundaryPrefix_volumeOrder j).trans
      (volumeOrder_dualLattice S.space S.lattice).symm
  have hclass := determinantClass_eq_of_volumeOrder_eq_spaceIsometry
    hvolume (J.reverseDualBoundaryPrefixSpaceIsometry j)
  exact hclass.trans (determinantClass_dualLattice S.space S.lattice)

end Lattice.JordanDecomposition

end Bong
