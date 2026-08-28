/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaScaledHyperbolicTowerSpace
import Bong.Lattice.HyperbolicLatticeModular
import Bong.Lattice.HyperbolicLatticeInvariants
import Bong.Lattice.OrthogonalDecompositionDeterminant
import Bong.Lattice.UnimodularDeterminantRigidity

/-!
# Integral invariants of the scaled zero-coefficient tower

The standard coordinate lattice on a tower of `s A(0,0)` planes is
`s`-modular.  For two planes, normalization by `s⁻¹` has refined
determinant class one.  This supplies the determinant-one comparison model
for the hyperbolic source head in O'Meara 93:28.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- Standard integral lattice on the recursively parenthesized scaled
zero-coefficient tower. -/
noncomputable abbrev scaledZeroOmearaTowerLattice (n : Nat) :
    Lattice K (HyperbolicExtension K (Fin 0 → K) n) :=
  hyperbolicExtensionLattice
    (QuadraticSpace.zeroCoordinateBasisLattice (K := K)) n

/-- The standard tower lattice is modular at the displayed common scale. -/
theorem scaledZeroOmearaTowerLattice_isModular (s : Kˣ) :
    ∀ n : Nat,
      IsModular (QuadraticSpace.scaledZeroOmearaTowerForm s n)
        (scaledZeroOmearaTowerLattice (K := K) n) s
  | 0 => by
      unfold IsModular
      apply Lattice.ext
      ext x
      have hx : x = 0 := by
        funext i
        exact Fin.elim0 i
      subst x
      simp
  | n + 1 => by
      have hhead : IsModular
          ((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit s)
          (hyperbolicPlaneLattice (K := K)) s :=
        (hyperbolicPlaneLattice_isModular (K := K) s).mapLatticeIsometry
          (scaledZeroOmearaPlaneLatticeIsometry s).symm
      exact hhead.orthogonalProduct
        (scaledZeroOmearaTowerLattice_isModular s n)

/-- Two unimodular zero-coefficient planes have determinant class one. -/
theorem determinantClass_scaledZeroOmearaTower_one_two :
    determinantClass
        (QuadraticSpace.scaledZeroOmearaTowerForm (1 : Kˣ) 2)
        (scaledZeroOmearaTowerLattice (K := K) 2) = 1 := by
  have hzeroSubsingleton : Subsingleton (Fin 0 → K) :=
    ⟨by
      intro x y
      funext i
      exact Fin.elim0 i⟩
  have hbase : determinantClass
      (zeroCoordinateQuadraticSpace (K := K))
      (QuadraticSpace.zeroCoordinateBasisLattice (K := K)) = 1 :=
    determinantClass_eq_one_of_subsingleton _ _ hzeroSubsingleton
  change determinantClass
      (((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit (1 : Kˣ)).orthogonalSum
        (((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit (1 : Kˣ)).orthogonalSum
          (zeroCoordinateQuadraticSpace (K := K))))
      (product (hyperbolicPlaneLattice (K := K))
        (product (hyperbolicPlaneLattice (K := K))
          (QuadraticSpace.zeroCoordinateBasisLattice (K := K)))) = 1
  rw [determinantClass_orthogonalProduct,
    determinantClass_orthogonalProduct,
    determinantClass_eq_of_isometry
      (scaledZeroOmearaPlaneLatticeIsometry (1 : Kˣ)),
    determinantClass_hyperbolicPlaneLattice,
    hbase]
  simp only [one_pow, mul_one]
  rw [← unitSquareClass_one K]
  rw [← unitSquareClass_mul]
  norm_num

/-- After normalizing a two-plane tower by the inverse of its scale, its
standard lattice is unimodular and has determinant class one. -/
theorem determinantClass_normalized_scaledZeroOmearaTower_two (s : Kˣ) :
    determinantClass
        ((QuadraticSpace.scaledZeroOmearaTowerForm s 2).rescaleUnit s⁻¹)
        (scaledZeroOmearaTowerLattice (K := K) 2) = 1 := by
  have hsource : IsUnimodular
      ((QuadraticSpace.scaledZeroOmearaTowerForm s 2).rescaleUnit s⁻¹)
      (scaledZeroOmearaTowerLattice (K := K) 2) :=
    (scaledZeroOmearaTowerLattice_isModular (K := K) s 2)
      |>.isUnimodular_rescaleQuadraticInverse
  have htarget : IsUnimodular
      (QuadraticSpace.scaledZeroOmearaTowerForm (1 : Kˣ) 2)
      (scaledZeroOmearaTowerLattice (K := K) 2) := by
    exact scaledZeroOmearaTowerLattice_isModular (K := K) (1 : Kˣ) 2
  let fRaw := QuadraticSpace.scaledZeroOmearaTowerRescaleSpaceIsometry
    s s⁻¹ 2
  have hscale : s⁻¹ * s = (1 : Kˣ) := by simp
  let f : QuadraticSpace.Isometry
      ((QuadraticSpace.scaledZeroOmearaTowerForm s 2).rescaleUnit s⁻¹)
      (QuadraticSpace.scaledZeroOmearaTowerForm (1 : Kˣ) 2) := by
    simpa only [hscale] using fRaw
  exact (determinantClass_eq_of_unimodular_spaceIsometry
    hsource htarget f).trans
      (determinantClass_scaledZeroOmearaTower_one_two (K := K))

end Lattice

end Bong
