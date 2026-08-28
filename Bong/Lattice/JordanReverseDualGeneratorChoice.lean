/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.JordanReverseDualSaturation
import Bong.Lattice.Omeara9328GeneratorChoice

/-!
# Coherent norm-generator choices under reverse duality

O'Meara's duality argument must retain the actual chosen norm generators,
not merely their valuations.  At the reversed index the coherent choice is
`s⁻² a`, where `s` is the old scale generator and `a` is the old
fundamental norm generator.
-/

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {t : Nat}

namespace FundamentalNormGeneratorChoice

/-- The coherent inverse-square norm-generator choice on the reverse-dual
Jordan chain. -/
noncomputable def reverseDual
    {J : JordanDecomposition q L t}
    (A : FundamentalNormGeneratorChoice J) :
    FundamentalNormGeneratorChoice J.reverseDual where
  value := fun i ↦
    (J.scaleGenerator (Fin.rev i))⁻¹ ^ 2 * A.value (Fin.rev i)
  spec := by
    intro i
    rw [J.reverseDual_fundamentalLattice i]
    let c : Kˣ := (J.scaleGenerator (Fin.rev i))⁻¹
    let a : Kˣ := A.value (Fin.rev i)
    have ha := A.spec (Fin.rev i)
    constructor
    · change (((c ^ 2 * a : Kˣ) : K)) ∈
        Lattice.normGroupSet q
          (Lattice.rescale c (J.fundamentalLattice (Fin.rev i)))
      simpa only [Units.val_mul] using
        (Lattice.sq_mul_mem_normGroupSet_rescale c ha.1)
    · change Lattice.normIdeal q
          (Lattice.rescale c (J.fundamentalLattice (Fin.rev i))) =
        Lattice.principalIdeal (K := K) ((c ^ 2 * a : Kˣ) : K)
      exact Lattice.normIdeal_rescale_eq_principal_of_finrank_pos
        (J.ambient_finrank_pos_of_index (Fin.rev i)) c a ha.2

@[simp]
theorem reverseDual_value
    {J : JordanDecomposition q L t}
    (A : FundamentalNormGeneratorChoice J) (i : Fin t) :
    A.reverseDual.value i =
      (J.scaleGenerator (Fin.rev i))⁻¹ ^ 2 * A.value (Fin.rev i) :=
  rfl

end FundamentalNormGeneratorChoice

/-- The explicit threshold `4aw⁻¹` is invariant under reverse duality
when the coherent inverse-square generator choice is used. -/
@[simp]
theorem reverseDual_fourNormOverWeightIdealWith
    (J : JordanDecomposition q L (t + 1))
    (A : FundamentalNormGeneratorChoice J) (i : Fin (t + 1)) :
    J.reverseDual.fourNormOverWeightIdealWith A.reverseDual i =
      J.fourNormOverWeightIdealWith A (Fin.rev i) := by
  unfold fourNormOverWeightIdealWith
  rw [FundamentalNormGeneratorChoice.reverseDual_value,
    ordUnit_mul, ordUnit_pow, ordUnit_inv,
    J.reverseDual_fundamentalWeightOrder]
  congr 1
  unfold fundamentalScaleOrder
  ring

/-- The scalar coordinate change used to identify a reverse-dual generator
line with its original line. -/
noncomputable def reverseDualGeneratorLineLinearEquiv
    (J : JordanDecomposition q L t)
    (A : FundamentalNormGeneratorChoice J) (i : Fin t) :
    K ≃ₗ[K] K :=
    { toFun := fun x ↦
        (((J.scaleGenerator (Fin.rev i))⁻¹ : Kˣ) : K) * x
      invFun := fun x ↦ (J.scaleGenerator (Fin.rev i) : K) * x
      left_inv := by intro x; simp
      right_inv := by intro x; simp
      map_add' := by intro x y; ring
      map_smul' := by
        intro c x
        simp only [smul_eq_mul, RingHom.id_apply]
        ring }

@[simp]
theorem reverseDualGeneratorLineLinearEquiv_apply
    (J : JordanDecomposition q L t)
    (A : FundamentalNormGeneratorChoice J) (i : Fin t) (x : K) :
    J.reverseDualGeneratorLineLinearEquiv A i x =
      (((J.scaleGenerator (Fin.rev i))⁻¹ : Kˣ) : K) * x :=
  rfl

/-- The line belonging to a reverse-dual coherent generator is isometric to
the line belonging to the corresponding original generator. -/
noncomputable def reverseDualGeneratorLineIsometry
    (J : JordanDecomposition q L t)
    (A : FundamentalNormGeneratorChoice J) (i : Fin t) :
    QuadraticSpace.Isometry
      (QuadraticSpace.scaledLine (A.reverseDual.value i))
      (QuadraticSpace.scaledLine (A.value (Fin.rev i))) where
  toLinearEquiv := J.reverseDualGeneratorLineLinearEquiv A i
  map_bilin := by
    intro x y
    simp only [QuadraticSpace.scaledLine_bilin_apply,
      reverseDualGeneratorLineLinearEquiv_apply,
      FundamentalNormGeneratorChoice.reverseDual_value,
      Units.val_mul, Units.val_pow_eq_pow_val]
    ring

end Lattice.JordanDecomposition

end Bong
