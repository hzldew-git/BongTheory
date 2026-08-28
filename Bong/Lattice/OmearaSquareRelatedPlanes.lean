/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinarySpinorMonotonicity
import Bong.Dyadic.BeliGroups
import Bong.Lattice.OmearaHighRankModularSplitting

/-!
# Square-related planes in O'Meara 93:18(v)

The last calculation in O'Meara 93:18(v) displays two modular binary
planes whose first coefficients differ by an integral square.  After
orienting the planes so that `alpha = gamma * c^2`, the 93:12 change of
complement replaces their first coefficient by

`alpha + gamma * c^2 = 2 * alpha`.

The resulting even plane is hyperbolic.  This file packages that exact
calculation as a constructor for `Omeara9318vData`; it introduces no law
class and leaves only the low-rank production of the square-related
coefficients to be proved.
-/

namespace Bong

open Dyadic

namespace Lattice

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {a : Kˣ}

/-- Two nonzero coefficients with the same normalized unit part and an
ordered, parity-compatible valuation differ by the square of an integral
uniformizer power.  This is the coordinate-free scalar form of the
`bπ^(2r), bπ^(2t)` calculation in 93:18(v). -/
theorem exists_integralSquareMultiplier_of_normalizedUnitPart_eq
    (gamma alpha : Kˣ)
    (hle : ordUnit K gamma ≤ ordUnit K alpha)
    (hmod : Int.ModEq 2 (ordUnit K alpha) (ordUnit K gamma))
    (hnormalized : normalizedUnitPart K gamma =
      normalizedUnitPart K alpha) :
    ∃ c : Kˣ, (c : K) ∈ IntegerRing K ∧ gamma * c ^ 2 = alpha := by
  rcases exists_nat_eq_add_two_mul_of_le_modEq_two hle hmod with
    ⟨k, hk⟩
  let c : Kˣ := uniformizerPowerUnit K (k : Int)
  have hgamma :
      uniformizerPowerUnit K (ordUnit K gamma) *
          normalizedUnitPart K gamma = gamma :=
    uniformizerPower_mul_normalizedUnitPart K gamma
  have halpha :
      uniformizerPowerUnit K (ordUnit K alpha) *
          normalizedUnitPart K alpha = alpha :=
    uniformizerPower_mul_normalizedUnitPart K alpha
  refine ⟨c, uniformizerPowerUnit_nat_mem_integerRing k, ?_⟩
  calc
    gamma * c ^ 2 =
        (uniformizerPowerUnit K (ordUnit K gamma) *
          normalizedUnitPart K gamma) *
            uniformizerPowerUnit K (k : Int) ^ 2 := by rw [hgamma]
    _ = uniformizerPowerUnit K
          (ordUnit K gamma + 2 * (k : Int)) *
            normalizedUnitPart K gamma :=
      uniformizerParameter_mul_square
        (normalizedUnitPart K gamma) (ordUnit K gamma) k
    _ = uniformizerPowerUnit K (ordUnit K alpha) *
          normalizedUnitPart K alpha := by rw [← hk, hnormalized]
    _ = alpha := halpha

/-- Two displayed modular O'Meara planes yield a scaled hyperbolic
summand when the first coefficient is an integral-square multiple of the
second.  This is the final coefficient calculation in 93:18(v). -/
noncomputable def Omeara9318vData.ofTwoPlaneDisplayedIsometryOfSquareRelated
    {W : Type w} [AddCommGroup W] [Module K W]
    (hmodular : IsModular q L a)
    (alpha gamma c : K)
    (halpha : alpha ∈ IntegerRing K)
    (hgamma : gamma ∈ IntegerRing K)
    (hc : c ∈ IntegerRing K)
    (hrelated : alpha = gamma * c ^ 2)
    (r : QuadraticSpace K W) (M : Lattice K W)
    (displayed : Isometry q
      (((QuadraticSpace.omearaPlane alpha).rescaleUnit a).orthogonalSum
        (((QuadraticSpace.omearaPlane gamma).rescaleUnit a).orthogonalSum r))
      L
      (product (hyperbolicPlaneLattice (K := K))
        (product (hyperbolicPlaneLattice (K := K)) M))) :
    Omeara9318vData q L a := by
  have hsum : alpha + gamma * c ^ 2 = 2 * alpha := by
    rw [← hrelated]
    ring
  exact
    OmearaHighRankModularPlaneData.Omeara9318vData.ofTwoPlaneDisplayedIsometryOfSquare
      (q := q) (L := L) (a := a) hmodular alpha gamma c alpha
        hgamma hc hsum halpha r M displayed

/-- Invariant form of the preceding constructor.  It is enough that the
two nonzero first coefficients have equal normalized unit part, that their
orders have the same parity, and that the coefficient of the first
displayed plane has no smaller order. -/
noncomputable def Omeara9318vData.ofTwoPlaneDisplayedIsometryOfNormalizedCoefficients
    {W : Type w} [AddCommGroup W] [Module K W]
    (hmodular : IsModular q L a)
    (alpha gamma : Kˣ)
    (halpha : (alpha : K) ∈ IntegerRing K)
    (hgamma : (gamma : K) ∈ IntegerRing K)
    (hle : ordUnit K gamma ≤ ordUnit K alpha)
    (hmod : Int.ModEq 2 (ordUnit K alpha) (ordUnit K gamma))
    (hnormalized : normalizedUnitPart K gamma =
      normalizedUnitPart K alpha)
    (r : QuadraticSpace K W) (M : Lattice K W)
    (displayed : Isometry q
      (((QuadraticSpace.omearaPlane (alpha : K)).rescaleUnit a)
          |>.orthogonalSum
        (((QuadraticSpace.omearaPlane (gamma : K)).rescaleUnit a)
          |>.orthogonalSum r))
      L
      (product (hyperbolicPlaneLattice (K := K))
        (product (hyperbolicPlaneLattice (K := K)) M))) :
    Omeara9318vData q L a := by
  let hexists := exists_integralSquareMultiplier_of_normalizedUnitPart_eq
    gamma alpha hle hmod hnormalized
  let c : Kˣ := Classical.choose hexists
  have hc : (c : K) ∈ IntegerRing K :=
    (Classical.choose_spec hexists).1
  have hrelated : (alpha : K) = (gamma : K) * (c : K) ^ 2 := by
    have h := congrArg (fun z : Kˣ ↦ (z : K))
      (Classical.choose_spec hexists).2
    simpa only [Units.val_mul, Units.val_pow_eq_pow_val] using h.symm
  exact Omeara9318vData.ofTwoPlaneDisplayedIsometryOfSquareRelated
    (q := q) (L := L) (a := a) hmodular
      (alpha : K) (gamma : K) (c : K) halpha hgamma hc hrelated
        r M displayed

/-- A factorization through one common coefficient is the form in which
the square relation occurs in O'Meara's notation
`bπ^(2r), bπ^(2t)`. -/
noncomputable def Omeara9318vData.ofTwoPlaneDisplayedIsometryOfCommonSquare
    {W : Type w} [AddCommGroup W] [Module K W]
    (hmodular : IsModular q L a)
    (b c : K)
    (hb : b ∈ IntegerRing K)
    (hc : c ∈ IntegerRing K)
    (r : QuadraticSpace K W) (M : Lattice K W)
    (displayed : Isometry q
      (((QuadraticSpace.omearaPlane (b * c ^ 2)).rescaleUnit a)
          |>.orthogonalSum
        (((QuadraticSpace.omearaPlane b).rescaleUnit a).orthogonalSum r))
      L
      (product (hyperbolicPlaneLattice (K := K))
        (product (hyperbolicPlaneLattice (K := K)) M))) :
    Omeara9318vData q L a := by
  have halpha : b * c ^ 2 ∈ IntegerRing K :=
    (IntegerRing K).toSubring.mul_mem hb
      ((IntegerRing K).toSubring.pow_mem hc 2)
  exact Omeara9318vData.ofTwoPlaneDisplayedIsometryOfSquareRelated
    (q := q) (L := L) (a := a) hmodular
      (b * c ^ 2) b c halpha hb hc rfl r M displayed

end Lattice

end Bong
