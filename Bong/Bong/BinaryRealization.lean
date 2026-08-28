/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryInvariant
import Bong.Bong.Existence
import Bong.Bong.BinaryStrictModular
import Bong.Lattice.BasisUnits
import Bong.Lattice.DeterminantBasis
import Bong.QuadraticSpace.BinaryModel

/-!
# Realizing admissible binary BONG parameters

The scalar parameter `a` is operationally admissible when some `c` satisfies
`2c ∈ 𝒪` and `c² + a ∈ 𝒪`.  The integral standard lattice in the
binary Gram model then has its first basis vector as a norm generator.
-/

namespace Bong

open Dyadic
open Module

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

namespace Dyadic

variable [QuadraticDefectLaws K]

/-- If a nonsquare differs from a square by an integral element, twice the
square root is integral.  Otherwise that root would give an approximation of
depth `2e + 1`, contradicting the universal defect bound for nonsquares. -/
theorem two_mul_mem_integerRing_of_not_isSquare_of_sub_sq_mem
    {a : Kˣ} {x : K} (ha : ¬IsSquare a)
    (hdiff : (a : K) - x ^ 2 ∈ IntegerRing K) :
    (2 : K) * x ∈ IntegerRing K := by
  by_contra htwo
  have htwoOrd : ord K ((2 : K) * x) < 0 := by
    exact lt_of_not_ge (fun h => htwo ((mem_integerRing_iff K).2 h))
  have hx : x ≠ 0 := by
    intro hx
    subst x
    simp at htwo
  let xu : Kˣ := Units.mk0 x hx
  have hxOrd : ord K x =
      ((ordUnit K xu : Int) : WithTop Int) := by
    exact (coe_ordUnit K xu).symm
  have htwoInt :
      (ramificationIndex K : Int) + ordUnit K xu < 0 := by
    apply WithTop.coe_lt_coe.mp
    rw [WithTop.coe_add, ramificationIndex_spec,
      coe_ordUnit]
    simpa [xu, ord_mul] using htwoOrd
  have hxSqNeg : ord K (x ^ 2) < 0 := by
    rw [ord_pow, hxOrd]
    norm_cast
    simp only [nsmul_eq_mul]
    have hepos := ramificationIndex_pos K
    omega
  have hdiffOrd : 0 ≤ ord K ((a : K) - x ^ 2) :=
    (mem_integerRing_iff K).1 hdiff
  have heqOrder : ord K (a : K) = ord K (x ^ 2) := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hsum := (ord K).map_sub_eq_of_lt_left hlt
      rw [hsum] at hdiffOrd
      exact (not_lt_of_ge hdiffOrd) (hlt.trans hxSqNeg)
    · have hsum := (ord K).map_sub_eq_of_lt_right hgt
      rw [hsum] at hdiffOrd
      exact (not_lt_of_ge hdiffOrd) hxSqNeg
  have haOrder : ordUnit K a = 2 * ordUnit K xu := by
    apply WithTop.coe_injective
    rw [coe_ordUnit, heqOrder, ord_pow, hxOrd]
    norm_cast
  have hdepth :
      2 * ramificationIndex K + 1 ≤ -ordUnit K a := by
    rw [haOrder]
    have hepos := ramificationIndex_pos K
    omega
  have happ : IsQuadraticApproximation K a
      (2 * ramificationIndex K + 1) := by
    refine ⟨x, ?_⟩
    have herror :
        1 - x ^ 2 / (a : K) = ((a : K) - x ^ 2) / (a : K) := by
      field_simp [Units.ne_zero a]
    rw [herror, div_eq_mul_inv, ord_mul,
      AddValuation.map_inv, ← coe_ordUnit]
    calc
      ((2 * ramificationIndex K + 1 : Nat) : WithTop Int) ≤
          ((-ordUnit K a : Int) : WithTop Int) := by
        apply WithTop.coe_le_coe.mpr
        exact_mod_cast hdepth
      _ = 0 + ((-ordUnit K a : Int) : WithTop Int) := by simp
      _ ≤ ord K ((a : K) - x ^ 2) +
          ((-ordUnit K a : Int) : WithTop Int) :=
        by simpa [add_comm] using
          add_le_add_right hdiffOrd
            ((-ordUnit K a : Int) : WithTop Int)
  have hlower := natCast_le_quadraticDefect K happ
  have hupper := quadraticDefect_le_two_mul_e_of_not_isSquare
    (K := K) ha
  have himpossible :
      ((2 * ramificationIndex K + 1 : Nat) : ℕ∞) ≤
        ((2 * ramificationIndex K : Nat) : ℕ∞) :=
    hlower.trans hupper
  have hfalse : ¬(2 * ramificationIndex K + 1 ≤
      2 * ramificationIndex K) := by omega
  apply hfalse
  exact_mod_cast himpossible

end Dyadic

namespace BONG

/-- The standard field basis of the explicit binary model. -/
noncomputable def binaryModelBasis :
    Basis (Fin 2) K (Fin 2 → K) :=
  Pi.basisFun K (Fin 2)

/-- The standard integral lattice in the explicit binary model. -/
noncomputable def binaryModelLattice : Lattice K (Fin 2 → K) :=
  Lattice.basisLattice (binaryModelBasis (K := K))

@[simp]
theorem binaryModelBasis_zero :
    binaryModelBasis (K := K) 0 = QuadraticSpace.binaryModelFirst := by
  rw [binaryModelBasis, Pi.basisFun_apply]
  rfl

@[simp]
theorem binaryModelBasis_one :
    binaryModelBasis (K := K) 1 = QuadraticSpace.binaryModelSecond := by
  rw [binaryModelBasis, Pi.basisFun_apply]
  rfl

/-- Membership in the standard binary-model lattice is coordinatewise
integrality. -/
theorem mem_binaryModelLattice_iff (z : Fin 2 → K) :
    z ∈ binaryModelLattice (K := K) ↔
      ∀ i, z i ∈ IntegerRing K := by
  rw [binaryModelLattice,
    Lattice.mem_basisLattice_iff_repr_mem_integerRing]
  simp [binaryModelBasis]

/-- The standard model basis, with its index expressed by the ambient
finrank expected by the determinant API. -/
noncomputable def binaryModelIndexEquiv :
    Fin 2 ≃ Fin (finrank K (Fin 2 → K)) :=
  finCongr (by simp)

noncomputable def binaryModelFinrankBasis :
    Basis (Fin (finrank K (Fin 2 → K))) K (Fin 2 → K) :=
  (binaryModelBasis (K := K)).reindex
    (binaryModelIndexEquiv (K := K))

/-- Reindexing the standard model basis does not change its lattice. -/
theorem basisLattice_binaryModelFinrankBasis :
    Lattice.basisLattice (binaryModelFinrankBasis (K := K)) =
      binaryModelLattice (K := K) := by
  exact Lattice.basisLattice_reindex
    (binaryModelBasis (K := K))
      (binaryModelIndexEquiv (K := K))

/-- The Gram determinant in the finrank-indexed standard basis is `a`. -/
theorem binaryModel_basisGramDeterminant (a : Kˣ) (c : K) :
    Lattice.basisGramDeterminant (QuadraticSpace.binaryModel a c)
      (binaryModelFinrankBasis (K := K)) = (a : K) := by
  let e := binaryModelIndexEquiv (K := K)
  have hmatrix :
      Lattice.basisGramMatrix (QuadraticSpace.binaryModel a c)
          (binaryModelFinrankBasis (K := K)) =
        Matrix.reindex e e
          (QuadraticSpace.binaryModelMatrix a c) := by
    ext i j
    simp [Lattice.basisGramMatrix, binaryModelFinrankBasis,
      binaryModelBasis, e, QuadraticSpace.binaryModel,
      LinearMap.BilinForm.toMatrix_apply, Pi.basisFun_apply,
      Matrix.toBilin'_single, Matrix.reindex_apply]
  rw [Lattice.basisGramDeterminant, hmatrix,
    Matrix.det_reindex_self,
    QuadraticSpace.binaryModelMatrix_det]

/-- The Gram determinant unit of the standard binary model is `a`. -/
theorem binaryModel_basisGramUnit (a : Kˣ) (c : K) :
    Lattice.basisGramUnit (QuadraticSpace.binaryModel a c)
      (binaryModelFinrankBasis (K := K)) = a := by
  apply Units.ext
  exact binaryModel_basisGramDeterminant a c

/-- The refined determinant class of the standard model lattice is the
class represented by `a`. -/
theorem binaryModel_determinantClass (a : Kˣ) (c : K) :
    Lattice.determinantClass (QuadraticSpace.binaryModel a c)
      (binaryModelLattice (K := K)) = unitSquareClass K a := by
  rw [← basisLattice_binaryModelFinrankBasis]
  rw [← Lattice.unitSquareClass_basisGramUnit_eq_determinantClass
    (QuadraticSpace.binaryModel a c)
      (binaryModelFinrankBasis (K := K)),
    binaryModel_basisGramUnit]

/-- Beli's elementary integrality condition for a binary BONG parameter. -/
def IsBinaryParameterAdmissible (a : Kˣ) : Prop :=
  ∃ c : K,
    (2 : K) * c ∈ IntegerRing K ∧
      c ^ 2 + (a : K) ∈ IntegerRing K

/-- A refined binary class is admissible when one representative satisfies
the elementary integrality condition. -/
def IsBinaryInvariantClassAdmissible (A : UnitSquareClass K) : Prop :=
  ∃ a : Kˣ,
    unitSquareClass K a = A ∧ IsBinaryParameterAdmissible a

/-- The first standard vector belongs to the binary model lattice. -/
theorem binaryModelFirst_mem (a : Kˣ) (c : K) :
    QuadraticSpace.binaryModelFirst ∈
      binaryModelLattice (K := K) := by
  change QuadraticSpace.binaryModelFirst ∈
    Submodule.span (IntegerRing K)
      (Set.range (binaryModelBasis (K := K)))
  apply Submodule.subset_span
  exact ⟨0, binaryModelBasis_zero⟩

/-- The second standard vector belongs to the binary model lattice. -/
theorem binaryModelSecond_mem (a : Kˣ) (c : K) :
    QuadraticSpace.binaryModelSecond ∈
      binaryModelLattice (K := K) := by
  change QuadraticSpace.binaryModelSecond ∈
    Submodule.span (IntegerRing K)
      (Set.range (binaryModelBasis (K := K)))
  apply Submodule.subset_span
  exact ⟨1, binaryModelBasis_one⟩

/-- Under the two integrality conditions, the first standard vector is a
norm generator of the model lattice. -/
theorem binaryModelFirst_isNormGenerator
    (a : Kˣ) (c : K)
    (htwo : (2 : K) * c ∈ IntegerRing K)
    (hdiag : c ^ 2 + (a : K) ∈ IntegerRing K) :
    Lattice.IsNormGenerator (QuadraticSpace.binaryModel a c)
      (binaryModelLattice (K := K))
      QuadraticSpace.binaryModelFirst := by
  constructor
  · exact binaryModelFirst_mem a c
  · rw [QuadraticSpace.binaryModel_quadratic_first]
    change Lattice.normIdeal (QuadraticSpace.binaryModel a c)
      (binaryModelLattice (K := K)) = Lattice.unitIdeal (K := K)
    apply le_antisymm
    · rw [Lattice.normIdeal, Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      change (QuadraticSpace.binaryModel a c).quadratic
        (x : Fin 2 → K) ∈ Lattice.unitIdeal (K := K)
      rw [Lattice.mem_unitIdeal_iff]
      have hx :=
        (Lattice.mem_basisLattice_iff_repr_mem_integerRing
          (binaryModelBasis (K := K)) (x : Fin 2 → K)).1 x.property
      have hx0 : (x : Fin 2 → K) 0 ∈ IntegerRing K := by
        simpa [binaryModelBasis] using hx 0
      have hx1 : (x : Fin 2 → K) 1 ∈ IntegerRing K := by
        simpa [binaryModelBasis] using hx 1
      rw [QuadraticSpace.binaryModel_quadratic_apply]
      apply (IntegerRing K).add_mem
      · apply (IntegerRing K).add_mem
        · exact (IntegerRing K).pow_mem hx0 2
        · exact (IntegerRing K).mul_mem _ _ htwo
            ((IntegerRing K).mul_mem _ _ hx0 hx1)
      · exact (IntegerRing K).mul_mem _ _ hdiag
          ((IntegerRing K).pow_mem hx1 2)
    · rw [Lattice.unitIdeal, Lattice.principalIdeal,
        Submodule.span_le]
      rintro _ h
      rw [Set.mem_singleton_iff] at h
      subst h
      rw [← QuadraticSpace.binaryModel_quadratic_first a c]
      exact Lattice.quadratic_mem_normIdeal_of_mem
        (QuadraticSpace.binaryModel a c)
        (binaryModelLattice (K := K))
        (binaryModelFirst_mem a c)

/-- The first standard vector is anisotropic in every binary model. -/
theorem binaryModelFirst_isAnisotropic (a : Kˣ) (c : K) :
    (QuadraticSpace.binaryModel a c).IsAnisotropic
      QuadraticSpace.binaryModelFirst := by
  simp [QuadraticSpace.IsAnisotropic]

/-- Every operationally admissible parameter gives a concrete binary BONG. -/
noncomputable def binaryModelBONG
    (a : Kˣ) (c : K)
    (htwo : (2 : K) * c ∈ IntegerRing K)
    (hdiag : c ^ 2 + (a : K) ∈ IntegerRing K) :
    BONG (Fin 2 → K) (QuadraticSpace.binaryModel a c)
      (binaryModelLattice (K := K)) 2 :=
  ofNormGeneratorBinary
    (QuadraticSpace.binaryModel a c)
    (binaryModelLattice (K := K))
    QuadraticSpace.binaryModelFirst
    (binaryModelFirst_isNormGenerator a c htwo hdiag)
    (binaryModelFirst_isAnisotropic a c) (by simp)

@[simp]
theorem binaryModelBONG_head
    (a : Kˣ) (c : K)
    (htwo : (2 : K) * c ∈ IntegerRing K)
    (hdiag : c ^ 2 + (a : K) ∈ IntegerRing K) :
    (binaryModelBONG a c htwo hdiag).head =
      QuadraticSpace.binaryModelFirst :=
  head_ofNormGeneratorBinary _ _ _ _ _ _

@[simp]
theorem binaryModelBONG_value_zero
    (a : Kˣ) (c : K)
    (htwo : (2 : K) * c ∈ IntegerRing K)
    (hdiag : c ^ 2 + (a : K) ∈ IntegerRing K) :
    (binaryModelBONG a c htwo hdiag).value 0 = 1 := by
  rw [(binaryModelBONG a c htwo hdiag).value_zero_eq_quadratic_head,
    binaryModelBONG_head]
  simp

/-- The concrete BONG realizes the prescribed refined binary parameter. -/
theorem binaryModelBONG_binaryUnitSquareClass
    (a : Kˣ) (c : K)
    (htwo : (2 : K) * c ∈ IntegerRing K)
    (hdiag : c ^ 2 + (a : K) ∈ IntegerRing K) :
    (binaryModelBONG a c htwo hdiag).binaryUnitSquareClass =
      unitSquareClass K a := by
  let b := binaryModelBONG a c htwo hdiag
  have hvalueUnit : b.valueUnit 0 = 1 := by
    apply Units.ext
    exact binaryModelBONG_value_zero a c htwo hdiag
  rw [← b.binaryDeterminantInvariant_eq_parameter,
    binaryDeterminantInvariant,
    binaryModel_determinantClass, hvalueUnit]
  simp

/-- The parameter of every binary BONG satisfies the elementary integrality
condition.  The witness is the mixed projection coefficient in an adapted
integral basis. -/
theorem binaryParameter_isBinaryParameterAdmissible
    {V : Type*} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    (b : BONG V q L 2) :
    IsBinaryParameterAdmissible b.binaryParameter := by
  let c : K := b.binaryMixedPairing / b.value 0
  refine ⟨c, ?_, ?_⟩
  · simpa [c, binaryMixedPairing,
      b.value_zero_eq_quadratic_head] using
        (Lattice.two_projectionCoefficient_mem_integerRing
          q L b.head b.binarySecondVector b.head_isNormGenerator
          b.head_isAnisotropic b.binarySecondVector_mem)
  · have hvalueMem :=
      b.quadratic_binarySecondVector_mem_principal_value_zero
    have hquotient :
        q.quadratic b.binarySecondVector / b.value 0 ∈
          IntegerRing K := by
      apply Lattice.mem_integerRing_of_mul_mem_principalIdeal
        (b.value_ne_zero 0)
      convert hvalueMem using 1
      field_simp [b.value_ne_zero 0]
    have hformula :
        c ^ 2 + (b.binaryParameter : K) =
          q.quadratic b.binarySecondVector / b.value 0 := by
      rw [b.coe_binaryParameter, b.quadratic_binarySecondVector_eq]
      dsimp [c]
      field_simp [b.value_ne_zero 0]
    rw [hformula]
    exact hquotient

/-- Every binary BONG therefore determines an admissible refined invariant
class. -/
theorem binaryUnitSquareClass_isAdmissible
    {V : Type*} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    (b : BONG V q L 2) :
    IsBinaryInvariantClassAdmissible b.binaryUnitSquareClass :=
  ⟨b.binaryParameter, rfl,
    b.binaryParameter_isBinaryParameterAdmissible⟩

/-- Operational admissibility is sufficient for realization by a concrete
binary BONG. -/
theorem IsBinaryParameterAdmissible.exists_modelBONG
    {a : Kˣ} (ha : IsBinaryParameterAdmissible a) :
    ∃ (c : K)
      (htwo : (2 : K) * c ∈ IntegerRing K)
      (hdiag : c ^ 2 + (a : K) ∈ IntegerRing K),
      (binaryModelBONG a c htwo hdiag).binaryUnitSquareClass =
        unitSquareClass K a := by
  rcases ha with ⟨c, htwo, hdiag⟩
  exact ⟨c, htwo, hdiag,
    binaryModelBONG_binaryUnitSquareClass a c htwo hdiag⟩

/-- An admissible refined class is realized by one of the explicit binary
model BONGs. -/
theorem IsBinaryInvariantClassAdmissible.exists_modelBONG
    {A : UnitSquareClass K}
    (hA : IsBinaryInvariantClassAdmissible A) :
    ∃ (a : Kˣ) (c : K)
      (htwo : (2 : K) * c ∈ IntegerRing K)
      (hdiag : c ^ 2 + (a : K) ∈ IntegerRing K),
      (binaryModelBONG a c htwo hdiag).binaryUnitSquareClass = A := by
  rcases hA with ⟨a, haClass, c, htwo, hdiag⟩
  exact ⟨a, c, htwo, hdiag,
    (binaryModelBONG_binaryUnitSquareClass a c htwo hdiag).trans
      haClass⟩

end BONG

end Bong
