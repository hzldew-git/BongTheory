/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliCorollary315
import Bong.Bong.BinaryModelIsometry
import Bong.Bong.QuadraticApproximationExact
import Bong.Bong.ResidueFieldSize
import Bong.Lattice.FormRescale
import Bong.Lattice.NormGeneratorIsometry

/-!
# Beli 2003, Lemma 3.17

This file starts the coordinate-free proof of Lemma 3.17 with its normalized
binary-model core.  For the Gram matrix `[[1,c],[c,c²+a]]`, a second vector
`αe₀+βe₁` has the same value as `e₀` and completes it to an integral basis
exactly when the equation below holds with `α ∈ 𝓞` and `β ∈ 𝓞ˣ`.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

namespace BONG

/-- The normalized coordinate witness that `e₀` has an equal-value integral
basis companion in the binary model with parameter `a` and shear `c`. -/
def HasEqualNormGeneratorBasisWitness (a : Kˣ) (c : K) : Prop :=
  ∃ α β : K,
    α ∈ IntegerRing K ∧
      IsValuationUnit K β ∧
        α ^ 2 + (2 * c) * (α * β) +
            (c ^ 2 + (a : K)) * β ^ 2 = 1

/-- The companion vector represented by the two normalized coordinates. -/
def binaryModelEqualCompanion (α β : K) : Fin 2 → K :=
  α • QuadraticSpace.binaryModelFirst +
    β • QuadraticSpace.binaryModelSecond

@[simp]
theorem binaryModelEqualCompanion_zero (α β : K) :
    binaryModelEqualCompanion α β 0 = α := by
  simp [binaryModelEqualCompanion, QuadraticSpace.binaryModelFirst,
    QuadraticSpace.binaryModelSecond]

@[simp]
theorem binaryModelEqualCompanion_one (α β : K) :
    binaryModelEqualCompanion α β 1 = β := by
  simp [binaryModelEqualCompanion, QuadraticSpace.binaryModelFirst,
    QuadraticSpace.binaryModelSecond]

theorem binaryModelEqualCompanion_quadratic
    (a : Kˣ) (c α β : K) :
    (QuadraticSpace.binaryModel a c).quadratic
        (binaryModelEqualCompanion α β) =
      α ^ 2 + (2 * c) * (α * β) +
        (c ^ 2 + (a : K)) * β ^ 2 := by
  rw [QuadraticSpace.binaryModel_quadratic_apply]
  simp

/-- Integral coordinates place the companion in the standard model lattice. -/
theorem binaryModelEqualCompanion_mem
    (α β : K) (hα : α ∈ IntegerRing K)
    (hβ : β ∈ IntegerRing K) :
    binaryModelEqualCompanion α β ∈
      binaryModelLattice (K := K) := by
  change binaryModelEqualCompanion α β ∈
    Lattice.basisLattice (binaryModelBasis (K := K))
  rw [Lattice.mem_basisLattice_iff_repr_mem_integerRing]
  intro i
  fin_cases i
  · simpa [binaryModelBasis] using hα
  · simpa [binaryModelBasis] using hβ

/-- The second standard vector belongs to the underlying submodule of the
standard model lattice. -/
theorem binaryModelSecond_mem_toSubmodule :
    QuadraticSpace.binaryModelSecond (K := K) ∈
      binaryModelLattice (K := K) := by
  change QuadraticSpace.binaryModelSecond ∈
    Submodule.span (IntegerRing K)
      (Set.range (binaryModelBasis (K := K)))
  apply Submodule.subset_span
  exact ⟨1, binaryModelBasis_one⟩

/-- A unit second coordinate is exactly what makes the first vector and its
companion span the standard integral lattice. -/
theorem span_binaryModelFirst_equalCompanion
    (α β : K) (hα : α ∈ IntegerRing K)
    (hβ : IsValuationUnit K β) :
    Submodule.span (IntegerRing K)
        {QuadraticSpace.binaryModelFirst,
          binaryModelEqualCompanion α β} =
      (binaryModelLattice (K := K)).toSubmodule := by
  have hβIntegral : β ∈ IntegerRing K := by
    apply (mem_integerRing_iff K).2
    rw [Dyadic.IsIntegral, hβ]
  apply le_antisymm
  · rw [Submodule.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact binaryModelFirst_mem (K := K) 1 0
    · exact binaryModelEqualCompanion_mem α β hα hβIntegral
  · intro z hz
    let S := Submodule.span (IntegerRing K)
      {QuadraticSpace.binaryModelFirst,
        binaryModelEqualCompanion α β}
    change z ∈ S
    have hfirst : QuadraticSpace.binaryModelFirst ∈ S :=
      Submodule.subset_span (by simp [S])
    have hcompanion : binaryModelEqualCompanion α β ∈ S :=
      Submodule.subset_span (by simp [S])
    have hscaledFirst : α • QuadraticSpace.binaryModelFirst ∈ S := by
      exact S.smul_mem ⟨α, hα⟩ hfirst
    have hdifference :
        binaryModelEqualCompanion α β -
            α • QuadraticSpace.binaryModelFirst ∈ S :=
      S.sub_mem hcompanion hscaledFirst
    have hβinvIntegral : β⁻¹ ∈ IntegerRing K := by
      apply (mem_integerRing_iff K).2
      rw [Dyadic.IsIntegral, AddValuation.map_inv, hβ]
      simp
    have hinvScaled := S.smul_mem ⟨β⁻¹, hβinvIntegral⟩ hdifference
    have hβne : β ≠ 0 := by
      intro hzero
      rw [hzero, IsValuationUnit] at hβ
      simpa using hβ
    change
      (β⁻¹ : K) •
          (binaryModelEqualCompanion α β -
            α • QuadraticSpace.binaryModelFirst) ∈ S at hinvScaled
    have heq :
        (β⁻¹ : K) •
            (binaryModelEqualCompanion α β -
              α • QuadraticSpace.binaryModelFirst) =
          QuadraticSpace.binaryModelSecond := by
      ext i
      fin_cases i <;> simp [binaryModelEqualCompanion, hβne]
    have hsecond : QuadraticSpace.binaryModelSecond ∈ S := by
      rwa [heq] at hinvScaled
    have hzcoords :=
      (Lattice.mem_basisLattice_iff_repr_mem_integerRing
        (binaryModelBasis (K := K)) z).1 hz
    have hz0 : z 0 ∈ IntegerRing K := by
      simpa [binaryModelBasis] using hzcoords 0
    have hz1 : z 1 ∈ IntegerRing K := by
      simpa [binaryModelBasis] using hzcoords 1
    have hz0mem : z 0 • QuadraticSpace.binaryModelFirst ∈ S :=
      S.smul_mem ⟨z 0, hz0⟩ hfirst
    have hz1mem : z 1 • QuadraticSpace.binaryModelSecond ∈ S :=
      S.smul_mem ⟨z 1, hz1⟩ hsecond
    have hzdecomp :
        z = z 0 • QuadraticSpace.binaryModelFirst +
          z 1 • QuadraticSpace.binaryModelSecond := by
      ext i
      fin_cases i <;>
        simp [QuadraticSpace.binaryModelFirst,
          QuadraticSpace.binaryModelSecond]
    rw [hzdecomp]
    exact S.add_mem hz0mem hz1mem

/-- The literal geometric assertion in the standard binary model. -/
def HasEqualNormGeneratorBasisInModel (a : Kˣ) (c : K) : Prop :=
  ∃ x : Fin 2 → K,
    Lattice.IsNormGenerator (QuadraticSpace.binaryModel a c)
        (binaryModelLattice (K := K)) x ∧
      (QuadraticSpace.binaryModel a c).quadratic x =
        (QuadraticSpace.binaryModel a c).quadratic
          QuadraticSpace.binaryModelFirst ∧
      Submodule.span (IntegerRing K)
          {QuadraticSpace.binaryModelFirst, x} =
        (binaryModelLattice (K := K)).toSubmodule

/-- The coordinate equation is equivalent to the actual equal-value
norm-generator basis assertion in the standard binary model. -/
theorem hasEqualNormGeneratorBasisWitness_iff_inModel
    (a : Kˣ) (c : K)
    (htwo : (2 : K) * c ∈ IntegerRing K)
    (hdiag : c ^ 2 + (a : K) ∈ IntegerRing K) :
    HasEqualNormGeneratorBasisWitness a c ↔
      HasEqualNormGeneratorBasisInModel a c := by
  constructor
  · rintro ⟨α, β, hα, hβ, heq⟩
    have hβIntegral : β ∈ IntegerRing K := by
      apply (mem_integerRing_iff K).2
      rw [Dyadic.IsIntegral, hβ]
    let x := binaryModelEqualCompanion α β
    have hxmem : x ∈ binaryModelLattice (K := K) :=
      binaryModelEqualCompanion_mem α β hα hβIntegral
    have hxvalue :
        (QuadraticSpace.binaryModel a c).quadratic x = 1 := by
      dsimp [x]
      rw [binaryModelEqualCompanion_quadratic]
      exact heq
    have hhead := binaryModelFirst_isNormGenerator a c htwo hdiag
    have hxgenerator :
        Lattice.IsNormGenerator (QuadraticSpace.binaryModel a c)
          (binaryModelLattice (K := K)) x := by
      constructor
      · exact hxmem
      · calc
          Lattice.normIdeal (QuadraticSpace.binaryModel a c)
                (binaryModelLattice (K := K)) =
              Lattice.principalIdeal (K := K)
                ((QuadraticSpace.binaryModel a c).quadratic
                  QuadraticSpace.binaryModelFirst) :=
            hhead.normIdeal_eq
          _ = Lattice.principalIdeal (K := K)
                ((QuadraticSpace.binaryModel a c).quadratic x) := by
            rw [QuadraticSpace.binaryModel_quadratic_first, hxvalue]
    refine ⟨x, hxgenerator, ?_, ?_⟩
    · rw [hxvalue, QuadraticSpace.binaryModel_quadratic_first]
    · exact span_binaryModelFirst_equalCompanion α β hα hβ
  · rintro ⟨x, hxgenerator, hxvalue, hxspan⟩
    let α : K := x 0
    let β : K := x 1
    have hxcoords :=
      (Lattice.mem_basisLattice_iff_repr_mem_integerRing
        (binaryModelBasis (K := K)) x).1 hxgenerator.mem
    have hα : α ∈ IntegerRing K := by
      dsimp [α]
      simpa [binaryModelBasis] using hxcoords 0
    have hβIntegral : β ∈ IntegerRing K := by
      dsimp [β]
      simpa [binaryModelBasis] using hxcoords 1
    have hsecondSpan :
        QuadraticSpace.binaryModelSecond ∈
          Submodule.span (IntegerRing K)
            {QuadraticSpace.binaryModelFirst, x} := by
      rw [hxspan]
      exact binaryModelSecond_mem_toSubmodule (K := K)
    rw [Submodule.mem_span_pair] at hsecondSpan
    rcases hsecondSpan with ⟨A, B, hlinear⟩
    have hBβ : (B : K) * β = 1 := by
      have hcoord := congrFun hlinear 1
      simp [QuadraticSpace.binaryModelFirst,
        QuadraticSpace.binaryModelSecond] at hcoord
      simp only [Algebra.smul_def] at hcoord
      rw [ValuationSubring.algebraMap_apply (IntegerRing K) B] at hcoord
      change (B : K) * β = 1 at hcoord
      exact hcoord
    have hβne : β ≠ 0 := by
      intro hzero
      rw [hzero, mul_zero] at hBβ
      norm_num at hBβ
    have hβinv : β⁻¹ = (B : K) := by
      calc
        β⁻¹ = ((B : K) * β) * β⁻¹ := by rw [hBβ]; simp
        _ = (B : K) := by simp [mul_assoc, hβne]
    let βUnit : Kˣ := Units.mk0 β hβne
    have hβOrderNonneg :=
      Lattice.ordUnit_nonneg_of_mem_integerRing βUnit hβIntegral
    have hβInvIntegral : ((βUnit⁻¹ : Kˣ) : K) ∈ IntegerRing K := by
      change β⁻¹ ∈ IntegerRing K
      rw [hβinv]
      exact B.property
    have hβInvOrderNonneg :=
      Lattice.ordUnit_nonneg_of_mem_integerRing βUnit⁻¹ hβInvIntegral
    rw [ordUnit_inv] at hβInvOrderNonneg
    have hβOrder : ordUnit K βUnit = 0 := by omega
    have hβ : IsValuationUnit K β := by
      simpa [βUnit] using
        (isValuationUnit_iff_ordUnit_eq_zero K βUnit).2 hβOrder
    refine ⟨α, β, hα, hβ, ?_⟩
    have hxone :
        (QuadraticSpace.binaryModel a c).quadratic x = 1 := by
      simpa using hxvalue
    rw [QuadraticSpace.binaryModel_quadratic_apply] at hxone
    simpa [α, β] using hxone

/-- The existential assertion (1) of Lemma 3.17 in normalized binary-model
coordinates. -/
def HasSomeEqualNormGeneratorBasis (a : Kˣ) : Prop :=
  ∃ c : K,
    (2 : K) * c ∈ IntegerRing K ∧
      c ^ 2 + (a : K) ∈ IntegerRing K ∧
        HasEqualNormGeneratorBasisWitness a c

/-- The assertion (2) of Lemma 3.17 in normalized coordinates: every shear
representing a binary lattice with chosen first norm generator has an
equal-value basis companion. -/
def HasEveryEqualNormGeneratorBasis (a : Kˣ) : Prop :=
  ∀ c : K,
    (2 : K) * c ∈ IntegerRing K →
      c ^ 2 + (a : K) ∈ IntegerRing K →
        HasEqualNormGeneratorBasisWitness a c

/-- The four alternatives in Beli (2003), Lemma 3.17(3), for a presentation
`a = πʳ ε` with `ε` a valuation unit.  At infinite defect the strict
lower bound in case (iii) is automatic; case (ii), being an equality with a
finite integer, remains a finite-defect branch.  The exceptional `-1/4`
branch is expressed in the refined unit-square-class quotient. -/
noncomputable def BeliLemma317ParameterCases (R : Int) (ε : Kˣ) : Prop :=
  let d := quadraticDefect K (-ε)
  2 * (ramificationIndex K : Int) < R ∨
    (d ≠ ⊤ ∧
      R = 2 * (ramificationIndex K : Int) - 2 * (d.toNat : Int)) ∨
    ((d = ⊤ ∨
        (d ≠ ⊤ ∧
          2 * (ramificationIndex K : Int) - 2 * (d.toNat : Int) < R)) ∧
      R < 2 * (ramificationIndex K : Int) ∧
      Even R ∧
      Even (R / 2 + (ramificationIndex K : Int)) ∧
      unitSquareClass K (uniformizerPowerUnit K R * ε) ≠
        unitSquareClass K (negativeQuarterUnit K)) ∨
    ((R = 2 * (ramificationIndex K : Int) ∨
        unitSquareClass K (uniformizerPowerUnit K R * ε) =
          unitSquareClass K (negativeQuarterUnit K)) ∧
      HasResidueFieldMoreThanTwoElements (K := K))


/-- If `ord(a)>2e`, then `1-a` is a valuation unit. -/
theorem ord_one_sub_eq_zero_of_two_e_lt_order
    (a : Kˣ)
    (hR : 2 * (ramificationIndex K : Int) < ordUnit K a) :
    ord K (1 - (a : K)) = 0 := by
  have hePos : (0 : Int) < (ramificationIndex K : Int) := by
    exact_mod_cast ramificationIndex_pos K
  have hRPos : (0 : Int) < ordUnit K a := by omega
  have hlt : ord K (1 : K) < ord K (a : K) := by
    rw [ord_one, ← coe_ordUnit]
    exact_mod_cast hRPos
  simpa using (ord K).map_sub_eq_of_lt_left hlt

/-- In particular, the near-one element occurring in Lemma 3.17(i) is
nonzero. -/
theorem one_sub_ne_zero_of_two_e_lt_order
    (a : Kˣ)
    (hR : 2 * (ramificationIndex K : Int) < ordUnit K a) :
    1 - (a : K) ≠ 0 := by
  intro hzero
  have horder := ord_one_sub_eq_zero_of_two_e_lt_order a hR
  rw [hzero, ord_zero] at horder
  exact WithTop.top_ne_coe horder

/-- A quadratic approximation one step beyond `2e` forces the represented
unit to be a square. -/
theorem isSquare_of_quadraticApproximation_two_e_add_one
    [QuadraticDefectLaws K]
    (u : Kˣ)
    (happrox : IsQuadraticApproximation K u
      (2 * ramificationIndex K + 1)) :
    IsSquare u := by
  by_contra hnonsquare
  have hlower := natCast_le_quadraticDefect K happrox
  have hupper := quadraticDefect_le_two_mul_e_of_not_isSquare
    (K := K) hnonsquare
  have himpossible :
      ((2 * ramificationIndex K + 1 : Nat) : ℕ∞) ≤
        ((2 * ramificationIndex K : Nat) : ℕ∞) :=
    hlower.trans hupper
  have : 2 * ramificationIndex K + 1 ≤
      2 * ramificationIndex K := by
    exact_mod_cast himpossible
  omega

/-- A unit sufficiently close to one is a square.  This is the precise
Hensel consequence needed for Lemma 3.17(i), derived from the quadratic-defect
square criterion and its universal `2e` bound. -/
theorem isSquare_one_sub_of_two_e_lt_order
    [QuadraticDefectLaws K]
    (a : Kˣ)
    (hR : 2 * (ramificationIndex K : Int) < ordUnit K a) :
    IsSquare (Units.mk0 (1 - (a : K))
      (one_sub_ne_zero_of_two_e_lt_order a hR)) := by
  let b : Kˣ := Units.mk0 (1 - (a : K))
    (one_sub_ne_zero_of_two_e_lt_order a hR)
  have hbOrder : ord K (b : K) = 0 := by
    change ord K (1 - (a : K)) = 0
    exact ord_one_sub_eq_zero_of_two_e_lt_order a hR
  have happrox : IsQuadraticApproximation K b
      (2 * ramificationIndex K + 1) := by
    refine ⟨1, ?_⟩
    have herror :
        1 - (1 : K) ^ 2 / (b : K) =
          -(a : K) / (b : K) := by
      calc
        1 - (1 : K) ^ 2 / (b : K) =
            ((b : K) - 1) / (b : K) := by
              field_simp [Units.ne_zero b]
        _ = -(a : K) / (b : K) := by
          congr 1
          change 1 - (a : K) - 1 = -(a : K)
          ring
    rw [herror, div_eq_mul_inv, ord_mul, ord_neg,
      AddValuation.map_inv, hbOrder]
    simp only [neg_zero, add_zero]
    rw [← coe_ordUnit]
    apply WithTop.coe_le_coe.mpr
    exact_mod_cast (show
      2 * (ramificationIndex K : Int) + 1 ≤ ordUnit K a by omega)
  have hsquare : IsSquare b := by
    by_contra hnonsquare
    have hlower := natCast_le_quadraticDefect K happrox
    have hupper := quadraticDefect_le_two_mul_e_of_not_isSquare
      (K := K) hnonsquare
    have himpossible :
        ((2 * ramificationIndex K + 1 : Nat) : ℕ∞) ≤
          ((2 * ramificationIndex K : Nat) : ℕ∞) :=
      hlower.trans hupper
    have : 2 * ramificationIndex K + 1 ≤
        2 * ramificationIndex K := by
      exact_mod_cast himpossible
    omega
  exact hsquare

/-- Beli (2003), Lemma 3.17(3)(i): if `R>2e`, the standard orthogonal
model admits an equal-value norm-generator basis. -/
theorem hasSomeEqualNormGeneratorBasis_of_two_e_lt_order
    [QuadraticDefectLaws K]
    (a : Kˣ)
    (hR : 2 * (ramificationIndex K : Int) < ordUnit K a) :
    HasSomeEqualNormGeneratorBasis a := by
  let b : Kˣ := Units.mk0 (1 - (a : K))
    (one_sub_ne_zero_of_two_e_lt_order a hR)
  have hsquare : IsSquare b := by
    exact isSquare_one_sub_of_two_e_lt_order a hR
  rcases hsquare with ⟨s, hs⟩
  have hbOrder : ordUnit K b = 0 := by
    apply WithTop.coe_injective
    rw [coe_ordUnit]
    change ord K (1 - (a : K)) = 0
    exact ord_one_sub_eq_zero_of_two_e_lt_order a hR
  have hsOrder : ordUnit K s = 0 := by
    rw [hs, ordUnit_mul] at hbOrder
    omega
  have hsIntegral : (s : K) ∈ IntegerRing K := by
    apply (mem_integerRing_iff K).2
    rw [Dyadic.IsIntegral, ← coe_ordUnit, hsOrder]
    simp
  have haIntegral : (a : K) ∈ IntegerRing K := by
    apply (mem_integerRing_iff K).2
    rw [Dyadic.IsIntegral, ← coe_ordUnit]
    exact_mod_cast (show (0 : Int) ≤ ordUnit K a by omega)
  refine ⟨0, by simp, by simpa using haIntegral, (s : K), 1,
    hsIntegral, by simp [IsValuationUnit], ?_⟩
  have hsval : (b : K) = (s : K) ^ 2 := by
    simpa [pow_two] using congrArg Units.val hs
  change 1 - (a : K) = (s : K) ^ 2 at hsval
  have hmain : (s : K) ^ 2 + (a : K) = 1 := by
    rw [← hsval]
    ring
  simpa using hmain

/-- Beli (2003), Lemma 3.17(3)(ii).  At
`R = 2e - 2d(-ε)`, an exact defect approximation gives the shear and the
unit second coordinate used in Beli's displayed construction. -/
theorem hasSomeEqualNormGeneratorBasis_of_order_eq_two_e_sub_two_defect
    [QuadraticDefectLaws K] [UnitQuadraticDefectParityLaws K]
    (R : Int) (ε : Kˣ) (hε : IsValuationUnit K (ε : K))
    (hfinite : quadraticDefect K (-ε) ≠ ⊤)
    (hR : R = 2 * (ramificationIndex K : Int) -
      2 * ((quadraticDefect K (-ε)).toNat : Int)) :
    HasSomeEqualNormGeneratorBasis
      (uniformizerPowerUnit K R * ε) := by
  let q : Kˣ := -ε
  let d : Nat := (quadraticDefect K q).toNat
  have hfiniteQ : quadraticDefect K q ≠ ⊤ := by
    simpa [q] using hfinite
  have hRQ : R = 2 * (ramificationIndex K : Int) - 2 * (d : Int) := by
    simpa [d, q] using hR
  have hqUnit : IsValuationUnit K (q : K) := by
    change ord K (-((ε : K))) = 0
    change ord K (ε : K) = 0 at hε
    simpa only [ord_neg] using hε
  have hdPos : 0 < d := by
    exact quadraticDefect_toNat_pos_of_unit_of_ne_top
      q hqUnit hfiniteQ
  rcases exists_quadraticApproximation_exact_order q hfiniteQ with
    ⟨x, hxError⟩
  let err : K := 1 - x ^ 2 / (q : K)
  have herrOrder : ord K err = ((d : Int) : WithTop Int) := by
    simpa [err, d] using hxError
  have herrPos : 0 < ord K err := by
    rw [herrOrder]
    exact_mod_cast hdPos
  have hquotOrder : ord K (x ^ 2 / (q : K)) = 0 := by
    have hlt : ord K (1 : K) < ord K err := by
      simpa only [ord_one] using herrPos
    have hsub := (ord K).map_sub_eq_of_lt_left hlt
    have heq : 1 - err = x ^ 2 / (q : K) := by
      dsimp [err]
      ring
    rw [heq] at hsub
    simpa using hsub
  have hxne : x ≠ 0 := by
    intro hzero
    rw [hzero] at hquotOrder
    simp at hquotOrder
  let xu : Kˣ := Units.mk0 x hxne
  have hquotUnitOrder : ordUnit K (xu ^ 2 * q⁻¹) = 0 := by
    apply (isValuationUnit_iff_ordUnit_eq_zero K (xu ^ 2 * q⁻¹)).1
    rw [IsValuationUnit]
    have hval : ((xu ^ 2 * q⁻¹ : Kˣ) : K) =
        x ^ 2 / (q : K) := by
      simp [xu, div_eq_mul_inv]
    rw [hval]
    exact hquotOrder
  have hqOrder : ordUnit K q = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K q).1 hqUnit
  have hxuOrder : ordUnit K xu = 0 := by
    rw [ordUnit_mul, ordUnit_pow, ordUnit_inv, hqOrder] at hquotUnitOrder
    omega
  have hxUnit : IsValuationUnit K x := by
    simpa [xu] using
      (isValuationUnit_iff_ordUnit_eq_zero K xu).2 hxuOrder
  have hbaseEq :
      x ^ 2 + (ε : K) = (ε : K) * err := by
    dsimp [err, q]
    field_simp [Units.ne_zero ε]
    ring
  have hbaseOrder :
      ord K (x ^ 2 + (ε : K)) =
        ((d : Int) : WithTop Int) := by
    rw [hbaseEq, ord_mul, hε, herrOrder]
    simp
  have hREven : R = 2 * (R / 2) := by
    omega
  let p : Kˣ := uniformizerPowerUnit K (R / 2)
  have hpSq : p ^ 2 = uniformizerPowerUnit K R := by
    dsimp [p]
    unfold uniformizerPowerUnit
    rw [pow_two, ← zpow_add]
    congr 1
    omega
  let a : Kˣ := uniformizerPowerUnit K R * ε
  let c : K := (p : K) * x
  let D : K := c ^ 2 + (a : K)
  have hDEq :
      D = (uniformizerPowerUnit K R : K) *
        (x ^ 2 + (ε : K)) := by
    have hpSqVal : (p : K) ^ 2 =
        (uniformizerPowerUnit K R : K) := by
      simpa using congrArg Units.val hpSq
    dsimp [D, c, a]
    change ((p : K) * x) ^ 2 +
        (uniformizerPowerUnit K R : K) * (ε : K) =
      (uniformizerPowerUnit K R : K) * (x ^ 2 + (ε : K))
    rw [mul_pow, hpSqVal]
    ring
  have hDOrder : ord K D =
      ((R + (d : Int) : Int) : WithTop Int) := by
    rw [hDEq, ord_mul, ← coe_ordUnit,
      ordUnit_uniformizerPowerUnit, hbaseOrder]
    norm_cast
  have hcOrder : ord K c = ((R / 2 : Int) : WithTop Int) := by
    dsimp [c]
    rw [ord_mul, ← coe_ordUnit,
      ordUnit_uniformizerPowerUnit, hxUnit]
    simp
  have htwoCOrder : ord K ((2 : K) * c) =
      (((ramificationIndex K : Int) + R / 2 : Int) : WithTop Int) := by
    rw [ord_mul, ← ramificationIndex_spec, hcOrder]
    norm_cast
  have hDne : D ≠ 0 := by
    intro hzero
    rw [hzero, ord_zero] at hDOrder
    exact WithTop.top_ne_coe hDOrder
  let β : K := -(((2 : K) * c) / D)
  have hβOrder : ord K β = 0 := by
    dsimp [β]
    rw [ord_neg, div_eq_mul_inv, ord_mul,
      AddValuation.map_inv, htwoCOrder, hDOrder]
    norm_cast
    omega
  have hβUnit : IsValuationUnit K β := hβOrder
  have hnonsquare : ¬IsSquare q := by
    intro hsquare
    exact hfiniteQ
      ((quadraticDefect_eq_top_iff_isSquare (K := K) q).2 hsquare)
  have hdBound := quadraticDefect_le_two_mul_e_of_not_isSquare
    (K := K) hnonsquare
  have hdLe : d ≤ 2 * ramificationIndex K := by
    rw [← ENat.coe_toNat hfiniteQ] at hdBound
    simpa [d] using ENat.coe_le_coe.mp hdBound
  have hdLeInt : (d : Int) ≤ 2 * (ramificationIndex K : Int) := by
    exact_mod_cast hdLe
  have hDNonneg : 0 ≤ R + (d : Int) := by
    omega
  have htwoCNonneg :
      0 ≤ (ramificationIndex K : Int) + R / 2 := by
    omega
  have htwoCIntegral : (2 : K) * c ∈ IntegerRing K := by
    apply (mem_integerRing_iff K).2
    rw [Dyadic.IsIntegral, htwoCOrder]
    exact_mod_cast htwoCNonneg
  have hDIntegral : D ∈ IntegerRing K := by
    apply (mem_integerRing_iff K).2
    rw [Dyadic.IsIntegral, hDOrder]
    exact_mod_cast hDNonneg
  refine ⟨c, htwoCIntegral, by simpa [D, a] using hDIntegral,
    1, β, by simp, hβUnit, ?_⟩
  have hβEq : D * β = -((2 : K) * c) := by
    dsimp [β]
    field_simp [hDne]
  have heq :
      (1 : K) ^ 2 + (2 * c) * ((1 : K) * β) + D * β ^ 2 = 1 := by
    calc
      (1 : K) ^ 2 + (2 * c) * ((1 : K) * β) + D * β ^ 2 =
          1 + β * ((2 : K) * c + D * β) := by ring
      _ = 1 := by rw [hβEq]; ring
  simpa [D, a] using heq

/-- In Lemma 3.17(iii), shifting the parameter order by two does not change
the norm-generator group.  This is the even-step collapse in the high-defect
branch of Definition 6. -/
theorem beliNormGeneratorGroup_eq_shift_two_of_caseIII
    [QuadraticDefectLaws K]
    [PrincipalUnitSquareClassFiltrationLaws K]
    (R : Int) (ε : Kˣ) (hε : IsValuationUnit K (ε : K))
    (hfinite : quadraticDefect K (-ε) ≠ ⊤)
    (hlower : 2 * (ramificationIndex K : Int) -
      2 * ((quadraticDefect K (-ε)).toNat : Int) < R)
    (hupper : R < 2 * (ramificationIndex K : Int))
    (hEvenR : Even R)
    (hEvenHigh : Even (R / 2 + (ramificationIndex K : Int))) :
    beliNormGeneratorGroup K (uniformizerPowerUnit K R * ε) =
      beliNormGeneratorGroup K
        (uniformizerPowerUnit K (R + 2) * ε) := by
  let d : Nat := (quadraticDefect K (-ε)).toNat
  let n : Nat := Int.toNat
    (R / 2 + (ramificationIndex K : Int))
  let a : Kˣ := uniformizerPowerUnit K R * ε
  let a' : Kˣ := uniformizerPowerUnit K (R + 2) * ε
  have hnonsquare : ¬IsSquare (-ε) := by
    intro hsquare
    exact hfinite
      ((quadraticDefect_eq_top_iff_isSquare (K := K) (-ε)).2 hsquare)
  have hdBound := quadraticDefect_le_two_mul_e_of_not_isSquare
    (K := K) hnonsquare
  have hdLe : d ≤ 2 * ramificationIndex K := by
    rw [← ENat.coe_toNat hfinite] at hdBound
    simpa [d] using ENat.coe_le_coe.mp hdBound
  have hdLeInt : (d : Int) ≤
      2 * (ramificationIndex K : Int) := by
    exact_mod_cast hdLe
  have hRlower : -(2 * (ramificationIndex K : Int)) < R := by
    have hlower' : 2 * (ramificationIndex K : Int) -
        2 * (d : Int) < R := by
      simpa [d] using hlower
    omega
  have hRDouble : R = 2 * (R / 2) := by
    rcases hEvenR with ⟨r, hr⟩
    omega
  have hRnextUpper : R + 2 ≤
      2 * (ramificationIndex K : Int) := by
    rcases hEvenR with ⟨r, hr⟩
    omega
  have hEvenR' : Even R := hEvenR
  have hEvenNext : Even (R + 2) := hEvenR.add (by norm_num)
  have haOrder : ordUnit K a = R :=
    ordUnit_uniformizerPower_mul_valuationUnit ε hε R
  have ha'Order : ordUnit K a' = R + 2 :=
    ordUnit_uniformizerPower_mul_valuationUnit ε hε (R + 2)
  have hdefectA : beliParameterDefect K a = quadraticDefect K (-ε) :=
    beliParameterDefect_uniformizerPower_mul_valuationUnit_of_even
      (K := K) R ε hε hEvenR'
  have hdefectA' : beliParameterDefect K a' = quadraticDefect K (-ε) :=
    beliParameterDefect_uniformizerPower_mul_valuationUnit_of_even
      (K := K) (R + 2) ε hε hEvenNext
  have hnotOrderA :
      ¬2 * (ramificationIndex K : Int) < ordUnit K a := by
    rw [haOrder]
    omega
  have hnotOrderA' :
      ¬2 * (ramificationIndex K : Int) < ordUnit K a' := by
    rw [ha'Order]
    omega
  have hhighA :
      ¬2 * beliParameterDefect K a ≤
        (beliDefectCutoff K a : ℕ∞) := by
    intro hlow
    unfold beliDefectCutoff at hlow
    rw [haOrder, hdefectA, ← ENat.coe_toNat hfinite] at hlow
    norm_cast at hlow
    norm_num at hlow
    have hcut : 0 ≤ 2 * (ramificationIndex K : Int) - R := by omega
    have hlowInt : 2 * (d : Int) ≤
        (Int.toNat
          (2 * (ramificationIndex K : Int) - R) : Int) := by
      exact_mod_cast hlow
    rw [Int.toNat_of_nonneg hcut] at hlowInt
    have hlower' : 2 * (ramificationIndex K : Int) -
        2 * (d : Int) < R := by
      simpa [d] using hlower
    omega
  have hhighA' :
      ¬2 * beliParameterDefect K a' ≤
        (beliDefectCutoff K a' : ℕ∞) := by
    intro hlow
    unfold beliDefectCutoff at hlow
    rw [ha'Order, hdefectA', ← ENat.coe_toNat hfinite] at hlow
    norm_cast at hlow
    norm_num at hlow
    have hcut : 0 ≤
        2 * (ramificationIndex K : Int) - (R + 2) := by omega
    have hlowInt : 2 * (d : Int) ≤
        (Int.toNat
          (2 * (ramificationIndex K : Int) - (R + 2)) : Int) := by
      exact_mod_cast hlow
    rw [Int.toNat_of_nonneg hcut] at hlowInt
    have hlower' : 2 * (ramificationIndex K : Int) -
        2 * (d : Int) < R := by
      simpa [d] using hlower
    omega
  have hnIntPos : 0 < R / 2 + (ramificationIndex K : Int) := by
    omega
  have hnIntLt : R / 2 + (ramificationIndex K : Int) <
      2 * (ramificationIndex K : Int) := by
    omega
  have hnCast : (n : Int) =
      R / 2 + (ramificationIndex K : Int) := by
    dsimp [n]
    rw [Int.toNat_of_nonneg hnIntPos.le]
  have hnPosCast : (0 : Int) < (n : Int) := by
    rw [hnCast]
    exact hnIntPos
  have hnPos : 0 < n := by exact_mod_cast hnPosCast
  have hnLtCast : (n : Int) <
      (2 * ramificationIndex K : Nat) := by
    rw [hnCast]
    norm_cast
  have hnLt : n < 2 * ramificationIndex K := by
    exact_mod_cast hnLtCast
  have hnEven : Even n := by
    rw [← hnCast] at hEvenHigh
    exact_mod_cast hEvenHigh
  have hnextExponent :
      Int.toNat ((R + 2) / 2 + (ramificationIndex K : Int)) =
        n + 1 := by
    have hhalf : (R + 2) / 2 = R / 2 + 1 := by
      rcases hEvenR' with ⟨r, hr⟩
      omega
    rw [hhalf]
    have hnonneg : 0 ≤ R / 2 + 1 +
        (ramificationIndex K : Int) := by omega
    have hleftCast := Int.toNat_of_nonneg hnonneg
    omega
  have hgA : beliNormGeneratorGroup K a =
      principalUnitValuationClassSubgroup K n := by
    rw [beliNormGeneratorGroup_of_high_defect K a hnotOrderA hhighA]
    unfold beliHighDefectExponent
    rw [haOrder]
    simp [n, add_comm]
  have hgA' : beliNormGeneratorGroup K a' =
      principalUnitValuationClassSubgroup K (n + 1) := by
    rw [beliNormGeneratorGroup_of_high_defect K a' hnotOrderA' hhighA']
    unfold beliHighDefectExponent
    rw [ha'Order]
    simpa [add_comm] using congrArg
      (principalUnitValuationClassSubgroup K) hnextExponent
  change beliNormGeneratorGroup K a = beliNormGeneratorGroup K a'
  rw [hgA, hgA']
  exact principalUnitValuationClassSubgroup_eq_succ_of_even
    K n hnPos hnLt hnEven

/-- The same two-step equality in the square-unit branch `d(-ε)=∞` of
case (iii).  Here the high-defect branch is automatic. -/
theorem beliNormGeneratorGroup_eq_shift_two_of_caseIII_top
    [PrincipalUnitSquareClassFiltrationLaws K]
    (R : Int) (ε : Kˣ) (hε : IsValuationUnit K (ε : K))
    (hdefect : quadraticDefect K (-ε) = ⊤)
    (hlower : -(2 * (ramificationIndex K : Int)) < R)
    (hupper : R < 2 * (ramificationIndex K : Int))
    (hEvenR : Even R)
    (hEvenHigh : Even (R / 2 + (ramificationIndex K : Int))) :
    beliNormGeneratorGroup K (uniformizerPowerUnit K R * ε) =
      beliNormGeneratorGroup K
        (uniformizerPowerUnit K (R + 2) * ε) := by
  let n : Nat := Int.toNat
    (R / 2 + (ramificationIndex K : Int))
  let a : Kˣ := uniformizerPowerUnit K R * ε
  let a' : Kˣ := uniformizerPowerUnit K (R + 2) * ε
  have hRnextUpper : R + 2 ≤
      2 * (ramificationIndex K : Int) := by
    rcases hEvenR with ⟨r, hr⟩
    omega
  have hRDouble : R = 2 * (R / 2) := by
    rcases hEvenR with ⟨r, hr⟩
    omega
  have hEvenNext : Even (R + 2) := hEvenR.add (by norm_num)
  have haOrder : ordUnit K a = R :=
    ordUnit_uniformizerPower_mul_valuationUnit ε hε R
  have ha'Order : ordUnit K a' = R + 2 :=
    ordUnit_uniformizerPower_mul_valuationUnit ε hε (R + 2)
  have hdefectA : beliParameterDefect K a = ⊤ := by
    rw [beliParameterDefect_uniformizerPower_mul_valuationUnit_of_even
      (K := K) R ε hε hEvenR, hdefect]
  have hdefectA' : beliParameterDefect K a' = ⊤ := by
    rw [beliParameterDefect_uniformizerPower_mul_valuationUnit_of_even
      (K := K) (R + 2) ε hε hEvenNext, hdefect]
  have hnotOrderA :
      ¬2 * (ramificationIndex K : Int) < ordUnit K a := by
    rw [haOrder]
    omega
  have hnotOrderA' :
      ¬2 * (ramificationIndex K : Int) < ordUnit K a' := by
    rw [ha'Order]
    omega
  have hhighA :
      ¬2 * beliParameterDefect K a ≤
        (beliDefectCutoff K a : ℕ∞) := by
    rw [hdefectA]
    simp
  have hhighA' :
      ¬2 * beliParameterDefect K a' ≤
        (beliDefectCutoff K a' : ℕ∞) := by
    rw [hdefectA']
    simp
  have hnIntPos : 0 < R / 2 + (ramificationIndex K : Int) := by
    omega
  have hnIntLt : R / 2 + (ramificationIndex K : Int) <
      2 * (ramificationIndex K : Int) := by
    omega
  have hnCast : (n : Int) =
      R / 2 + (ramificationIndex K : Int) := by
    dsimp [n]
    rw [Int.toNat_of_nonneg hnIntPos.le]
  have hnPos : 0 < n := by
    exact_mod_cast (show (0 : Int) < (n : Int) by
      rw [hnCast]
      exact hnIntPos)
  have hnLt : n < 2 * ramificationIndex K := by
    exact_mod_cast (show (n : Int) <
      (2 * ramificationIndex K : Nat) by
        rw [hnCast]
        norm_cast)
  have hnEven : Even n := by
    rw [← hnCast] at hEvenHigh
    exact_mod_cast hEvenHigh
  have hnextExponent :
      Int.toNat ((R + 2) / 2 + (ramificationIndex K : Int)) =
        n + 1 := by
    have hhalf : (R + 2) / 2 = R / 2 + 1 := by
      rcases hEvenR with ⟨r, hr⟩
      omega
    rw [hhalf]
    have hnonneg : 0 ≤ R / 2 + 1 +
        (ramificationIndex K : Int) := by omega
    have hleftCast := Int.toNat_of_nonneg hnonneg
    omega
  have hgA : beliNormGeneratorGroup K a =
      principalUnitValuationClassSubgroup K n := by
    rw [beliNormGeneratorGroup_of_high_defect K a hnotOrderA hhighA]
    unfold beliHighDefectExponent
    rw [haOrder]
    simp [n, add_comm]
  have hgA' : beliNormGeneratorGroup K a' =
      principalUnitValuationClassSubgroup K (n + 1) := by
    rw [beliNormGeneratorGroup_of_high_defect K a' hnotOrderA' hhighA']
    unfold beliHighDefectExponent
    rw [ha'Order]
    simpa [add_comm] using congrArg
      (principalUnitValuationClassSubgroup K) hnextExponent
  change beliNormGeneratorGroup K a = beliNormGeneratorGroup K a'
  rw [hgA, hgA']
  exact principalUnitValuationClassSubgroup_eq_succ_of_even
    K n hnPos hnLt hnEven

/-- Equal-basis witnesses transport under multiplication of the parameter by
the square of a valuation unit. -/
theorem HasSomeEqualNormGeneratorBasis.mul_valuationUnit_square
    {a s : Kˣ} (ha : HasSomeEqualNormGeneratorBasis a)
    (hs : IsValuationUnit K (s : K)) :
    HasSomeEqualNormGeneratorBasis (a * s ^ 2) := by
  rcases ha with ⟨c, htwo, hdiag, α, β, hα, hβ, heq⟩
  have hsIntegral := (valuationUnit_mem_integerRing_and_inv s hs).1
  let c' : K := c * (s : K)
  let β' : K := β / (s : K)
  have htwo' : (2 : K) * c' ∈ IntegerRing K := by
    have hmem := (IntegerRing K).mul_mem _ _ htwo hsIntegral
    convert hmem using 1
    dsimp [c']
    ring
  have hdiag' : c' ^ 2 + ((a * s ^ 2 : Kˣ) : K) ∈
      IntegerRing K := by
    have hmem := (IntegerRing K).mul_mem _ _ hdiag
      ((IntegerRing K).pow_mem hsIntegral 2)
    convert hmem using 1
    dsimp [c']
    change (c * (s : K)) ^ 2 + (a : K) * (s : K) ^ 2 =
      (c ^ 2 + (a : K)) * (s : K) ^ 2
    ring
  have hβ' : IsValuationUnit K β' := by
    dsimp [β']
    rw [IsValuationUnit, div_eq_mul_inv, ord_mul,
      AddValuation.map_inv, hβ, hs]
    simp
  refine ⟨c', htwo', hdiag', α, β', hα, hβ', ?_⟩
  have hsne : (s : K) ≠ 0 := Units.ne_zero s
  dsimp [c', β']
  change
    α ^ 2 + (2 * (c * (s : K))) * (α * (β / (s : K))) +
        ((c * (s : K)) ^ 2 + (a : K) * (s : K) ^ 2) *
          (β / (s : K)) ^ 2 = 1
  calc
    α ^ 2 + (2 * (c * (s : K))) * (α * (β / (s : K))) +
          ((c * (s : K)) ^ 2 + (a : K) * (s : K) ^ 2) *
            (β / (s : K)) ^ 2 =
        α ^ 2 + (2 * c) * (α * β) +
          (c ^ 2 + (a : K)) * β ^ 2 := by
            field_simp [hsne]
    _ = 1 := heq

/-- The existential assertion of Lemma 3.17 depends only on the refined
unit-square class of its parameter. -/
theorem hasSomeEqualNormGeneratorBasis_mul_valuationUnit_square_iff
    (a s : Kˣ) (hs : IsValuationUnit K (s : K)) :
    HasSomeEqualNormGeneratorBasis (a * s ^ 2) ↔
      HasSomeEqualNormGeneratorBasis a := by
  constructor
  · intro hscaled
    have hsInv : IsValuationUnit K ((s⁻¹ : Kˣ) : K) := by
      rw [IsValuationUnit, Units.val_inv_eq_inv_val,
        AddValuation.map_inv, hs]
      simp
    have h := hscaled.mul_valuationUnit_square hsInv
    convert h using 1
    group
  · intro ha
    exact ha.mul_valuationUnit_square hs

/-- Equal refined unit-square classes have equivalent equal-basis
assertions. -/
theorem hasSomeEqualNormGeneratorBasis_iff_of_unitSquareClass_eq
    {a b : Kˣ} (hclass : unitSquareClass K a = unitSquareClass K b) :
    HasSomeEqualNormGeneratorBasis a ↔
      HasSomeEqualNormGeneratorBasis b := by
  rcases exists_valuationUnit_mul_square_eq_of_unitSquareClass_eq
      K hclass with ⟨s, hs, hab⟩
  rw [← hab]
  exact
    (hasSomeEqualNormGeneratorBasis_mul_valuationUnit_square_iff
      a s hs).symm

/-- The determinant identity for two vectors in a normalized binary model. -/
theorem binaryModel_pair_determinant_identity
    (a : Kˣ) (c x₀ x₁ y₀ y₁ : K) :
    (x₀ ^ 2 + (2 * c) * (x₀ * x₁) +
          (c ^ 2 + (a : K)) * x₁ ^ 2) *
        (y₀ ^ 2 + (2 * c) * (y₀ * y₁) +
          (c ^ 2 + (a : K)) * y₁ ^ 2) -
      (x₀ * y₀ + c * (x₀ * y₁ + x₁ * y₀) +
          (c ^ 2 + (a : K)) * x₁ * y₁) ^ 2 =
        (a : K) * (x₀ * y₁ - x₁ * y₀) ^ 2 := by
  ring

/-- Two integral vectors of the same unit value and with unit determinant
produce the existential equal-basis assertion.  The normalized Gram parameter
in their basis differs from the original parameter by a valuation-unit
square. -/
theorem hasSomeEqualNormGeneratorBasis_of_equal_value_integral_pair
    (a : Kˣ) (c x₀ x₁ y₀ y₁ u : K)
    (htwo : (2 : K) * c ∈ IntegerRing K)
    (hdiag : c ^ 2 + (a : K) ∈ IntegerRing K)
    (hx₀ : x₀ ∈ IntegerRing K) (hx₁ : x₁ ∈ IntegerRing K)
    (hy₀ : y₀ ∈ IntegerRing K) (hy₁ : y₁ ∈ IntegerRing K)
    (hdet : IsValuationUnit K (x₀ * y₁ - x₁ * y₀))
    (hu : IsValuationUnit K u)
    (hxvalue :
      x₀ ^ 2 + (2 * c) * (x₀ * x₁) +
        (c ^ 2 + (a : K)) * x₁ ^ 2 = u)
    (hyvalue :
      y₀ ^ 2 + (2 * c) * (y₀ * y₁) +
        (c ^ 2 + (a : K)) * y₁ ^ 2 = u) :
    HasSomeEqualNormGeneratorBasis a := by
  let δ : K := x₀ * y₁ - x₁ * y₀
  let Bxy : K := x₀ * y₀ + c * (x₀ * y₁ + x₁ * y₀) +
    (c ^ 2 + (a : K)) * x₁ * y₁
  let t : K := Bxy / u
  have huNe : u ≠ 0 := by
    intro hzero
    rw [hzero, IsValuationUnit, ord_zero] at hu
    exact WithTop.top_ne_coe hu
  have hδNe : δ ≠ 0 := by
    intro hzero
    change x₀ * y₁ - x₁ * y₀ = 0 at hzero
    rw [hzero, IsValuationUnit, ord_zero] at hdet
    exact WithTop.top_ne_coe hdet
  have htwoMem : (2 : K) ∈ IntegerRing K := by norm_num
  have htwoBxy : (2 : K) * Bxy ∈ IntegerRing K := by
    have hfirst := (IntegerRing K).mul_mem _ _
      ((IntegerRing K).mul_mem _ _ htwoMem hx₀) hy₀
    have hcrossSum := (IntegerRing K).add_mem _ _
      ((IntegerRing K).mul_mem _ _ hx₀ hy₁)
      ((IntegerRing K).mul_mem _ _ hx₁ hy₀)
    have hcross := (IntegerRing K).mul_mem _ _ htwo hcrossSum
    have hlast := (IntegerRing K).mul_mem _ _
      ((IntegerRing K).mul_mem _ _ htwoMem hdiag)
      ((IntegerRing K).mul_mem _ _ hx₁ hy₁)
    have hsum := (IntegerRing K).add_mem _ _
      ((IntegerRing K).add_mem _ _ hfirst hcross) hlast
    convert hsum using 1
    dsimp [Bxy]
    ring
  let uU : Kˣ := Units.mk0 u huNe
  have huInvIntegral : u⁻¹ ∈ IntegerRing K := by
    change ((uU⁻¹ : Kˣ) : K) ∈ IntegerRing K
    exact (valuationUnit_mem_integerRing_and_inv uU hu).2
  have htwoT : (2 : K) * t ∈ IntegerRing K := by
    have hmem := (IntegerRing K).mul_mem _ _ htwoBxy huInvIntegral
    convert hmem using 1
    dsimp [t]
    field_simp [huNe]
  have hgram := binaryModel_pair_determinant_identity
    a c x₀ x₁ y₀ y₁
  rw [hxvalue, hyvalue] at hgram
  have hparameter :
      1 - t ^ 2 = (a : K) * δ ^ 2 / u ^ 2 := by
    dsimp [t, Bxy, δ]
    field_simp [huNe]
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hgram
  have hparameterNe : 1 - t ^ 2 ≠ 0 := by
    rw [hparameter]
    exact div_ne_zero
      (mul_ne_zero (Units.ne_zero a) (pow_ne_zero 2 hδNe))
      (pow_ne_zero 2 huNe)
  let a' : Kˣ := Units.mk0 (1 - t ^ 2) hparameterNe
  have hdiag' : t ^ 2 + (a' : K) ∈ IntegerRing K := by
    have hone : (1 : K) ∈ IntegerRing K := (IntegerRing K).one_mem
    convert hone using 1
    dsimp [a']
    ring
  have hsome' : HasSomeEqualNormGeneratorBasis a' := by
    refine ⟨t, htwoT, hdiag', 0, 1, by simp,
      by simp [IsValuationUnit], ?_⟩
    dsimp [a']
    ring
  let δU : Kˣ := Units.mk0 δ hδNe
  let s : Kˣ := δU / uU
  have hs : IsValuationUnit K (s : K) := by
    rw [isValuationUnit_iff_ordUnit_eq_zero]
    dsimp [s]
    rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv]
    have hδOrder : ordUnit K δU = 0 :=
      (isValuationUnit_iff_ordUnit_eq_zero K δU).1 hdet
    have huOrder : ordUnit K uU = 0 :=
      (isValuationUnit_iff_ordUnit_eq_zero K uU).1 hu
    omega
  have ha' : a' = a * s ^ 2 := by
    apply Units.ext
    change 1 - t ^ 2 = (a : K) * ((s : K) ^ 2)
    rw [hparameter]
    dsimp [s, δU, uU]
    simp only [Units.val_div_eq_div_val, Units.val_mk0,
      Units.val_pow_eq_pow_val]
    field_simp [huNe]
  have hclass : unitSquareClass K a' = unitSquareClass K a := by
    rw [ha']
    exact unitSquareClass_mul_unit_square K a s hs
  exact
    (hasSomeEqualNormGeneratorBasis_iff_of_unitSquareClass_eq
      hclass).1 hsome'

/-- Beli's claim in the proof of Lemma 3.17: if a normalized binary model is
spanned by two norm generators and `g(a)=g(π²a)`, Lemma 3.11 produces two
equal-value generators.  The proof is carried out in coordinates for the
index-`π` sublattice. -/
theorem hasSomeEqualNormGeneratorBasis_of_normGeneratorGroup_shift
    [BinaryNormGeneratorLocalLaws.{u, u} K]
    (a : Kˣ) (c : K)
    (htwo : (2 : K) * c ∈ IntegerRing K)
    (hdiag : c ^ 2 + (a : K) ∈ IntegerRing K)
    (hu : IsValuationUnit K
      (1 + (2 : K) * c + (c ^ 2 + (a : K))))
    (hgroup : beliNormGeneratorGroup K a =
      beliNormGeneratorGroup K
        (a * uniformizerPowerUnit K 1 ^ 2)) :
    HasSomeEqualNormGeneratorBasis a := by
  let u₀ : K := 1 + (2 : K) * c + (c ^ 2 + (a : K))
  have huNe : u₀ ≠ 0 := by
    intro hzero
    change IsValuationUnit K u₀ at hu
    rw [hzero, IsValuationUnit, ord_zero] at hu
    exact WithTop.top_ne_coe hu
  let x : Fin 2 → K := binaryModelEqualCompanion 1 1
  have hxMem : x ∈ binaryModelLattice (K := K) := by
    exact binaryModelEqualCompanion_mem 1 1 (by norm_num) (by norm_num)
  have hxValue :
      (QuadraticSpace.binaryModel a c).quadratic x = u₀ := by
    dsimp [x, u₀]
    rw [binaryModelEqualCompanion_quadratic]
    ring
  have hxAnisotropic :
      (QuadraticSpace.binaryModel a c).IsAnisotropic x := by
    rw [QuadraticSpace.IsAnisotropic, hxValue]
    exact huNe
  let b := binaryExactModelBONG a c htwo hdiag
  have hxGenerator :
      Lattice.IsNormGenerator (QuadraticSpace.binaryModel a c)
        (binaryModelLattice (K := K)) x := by
    have hhead := binaryModelFirst_isNormGenerator a c htwo hdiag
    apply (hhead.iff_isValuationUnit_quadratic_of_value_one
      (binaryModelFirst_isAnisotropic a c)
      (QuadraticSpace.binaryModel_quadratic_first a c)
      hxMem hxAnisotropic).2
    change IsValuationUnit K u₀ at hu
    simpa [hxValue] using hu
  let uU : Kˣ := Units.mk0 u₀ huNe
  let uClass : valuationUnitSubgroup K := ⟨uU, by
    change IsValuationUnit K u₀
    simpa [u₀] using hu⟩
  have hratioX : b.normGeneratorValueRatioUnit x hxGenerator = uU := by
    apply Units.ext
    simp [b, normGeneratorValueRatioUnit, hxValue, uU,
      binaryExactModelBONG_value_zero]
  have hclassX : b.normGeneratorValueRatioClass x hxGenerator =
      valuationUnitClassHom K uClass := by
    unfold normGeneratorValueRatioClass
      normGeneratorValueRatioValuationUnit
    congr 1
    apply Subtype.ext
    exact hratioX
  have hxClassMem : b.normGeneratorValueRatioClass x hxGenerator ∈
      beliNormGeneratorGroup K b.binaryParameter := by
    change b.normGeneratorValueRatioClass x hxGenerator ∈
      (beliNormGeneratorGroup K b.binaryParameter :
        Set (ValuationUnitClass K))
    rw [← b.normGeneratorValueRatioClassSet_eq_beliNormGeneratorGroup]
    exact ⟨x, hxGenerator, rfl⟩
  have huMemA : valuationUnitClassHom K uClass ∈
      beliNormGeneratorGroup K a := by
    rw [← hclassX]
    simpa [b] using hxClassMem
  let pU : Kˣ := uniformizerPowerUnit K 1
  let p : K := (pU : K)
  let a' : Kˣ := a * pU ^ 2
  let c' : K := p * (1 + c)
  have hpOrder : ord K p = (1 : WithTop Int) := by
    change ord K (uniformizerPowerUnit K 1 : K) =
      (1 : WithTop Int)
    rw [← coe_ordUnit, ordUnit_uniformizerPowerUnit]
    norm_num
  have hpIntegral : p ∈ IntegerRing K := by
    apply (mem_integerRing_iff K).2
    rw [Dyadic.IsIntegral, hpOrder]
    norm_num
  have hpMaximal : IsInMaximalIdeal K p := by
    rw [IsInMaximalIdeal, hpOrder]
    norm_num
  have htwoMem : (2 : K) ∈ IntegerRing K := by norm_num
  have htwoOneAddC : (2 : K) * (1 + c) ∈ IntegerRing K := by
    have hmem := (IntegerRing K).add_mem _ _ htwoMem htwo
    convert hmem using 1 <;> ring
  have htwo' : (2 : K) * c' ∈ IntegerRing K := by
    have hmem := (IntegerRing K).mul_mem _ _ hpIntegral htwoOneAddC
    convert hmem using 1
    dsimp [c']
    ring
  have huIntegral : u₀ ∈ IntegerRing K := by
    apply (mem_integerRing_iff K).2
    change 0 ≤ ord K u₀
    change IsValuationUnit K u₀ at hu
    rw [hu]
  have hdiagEq : c' ^ 2 + (a' : K) = p ^ 2 * u₀ := by
    dsimp [c', a', p, pU, u₀]
    ring
  have hdiag' : c' ^ 2 + (a' : K) ∈ IntegerRing K := by
    rw [hdiagEq]
    exact (IntegerRing K).mul_mem _ _
      ((IntegerRing K).pow_mem hpIntegral 2) huIntegral
  let b' := binaryExactModelBONG a' c' htwo' hdiag'
  have huMemA' : valuationUnitClassHom K uClass ∈
      beliNormGeneratorGroup K a' := by
    change beliNormGeneratorGroup K a =
        beliNormGeneratorGroup K a' at hgroup
    rwa [← hgroup]
  have huMemB' : valuationUnitClassHom K uClass ∈
      beliNormGeneratorGroup K b'.binaryParameter := by
    simpa [b'] using huMemA'
  rcases b'.exists_normGeneratorValueRatioUnit_eq_of_mem_beliNormGeneratorGroup
      uClass huMemB' with ⟨y, hyGenerator, hratioY⟩
  have hyCoords :=
    (Lattice.mem_basisLattice_iff_repr_mem_integerRing
      (binaryModelBasis (K := K)) y).1 hyGenerator.mem
  have hy₀Integral : y 0 ∈ IntegerRing K := by
    simpa [binaryModelBasis] using hyCoords 0
  have hy₁Integral : y 1 ∈ IntegerRing K := by
    simpa [binaryModelBasis] using hyCoords 1
  have hyValue :
      (QuadraticSpace.binaryModel a' c').quadratic y = u₀ := by
    have hval := congrArg Units.val hratioY
    simp only [normGeneratorValueRatioUnit, Units.val_div_eq_div_val,
      Units.val_mk0, coe_valueUnit] at hval
    dsimp [uClass, uU] at hval
    change
      (QuadraticSpace.binaryModel a' c').quadratic y /
          b'.value 0 = u₀ at hval
    have hb'Zero : b'.value 0 = 1 := by
      exact binaryExactModelBONG_value_zero a' c' htwo' hdiag'
    rwa [hb'Zero, div_one] at hval
  have hyFormula :
      y 0 ^ 2 + (2 * c') * (y 0 * y 1) +
          (c' ^ 2 + (a' : K)) * y 1 ^ 2 = u₀ := by
    rw [← hyValue]
    exact (QuadraticSpace.binaryModel_quadratic_apply a' c' y).symm
  have htwo'Maximal : IsInMaximalIdeal K ((2 : K) * c') := by
    have hbaseIntegral : Dyadic.IsIntegral K ((2 : K) * (1 + c)) :=
      (mem_integerRing_iff K).1 htwoOneAddC
    have hprod := isInMaximalIdeal_mul_isIntegral K hpMaximal hbaseIntegral
    convert hprod using 1
    dsimp [c']
    ring
  have hdiag'Maximal : IsInMaximalIdeal K (c' ^ 2 + (a' : K)) := by
    rw [hdiagEq]
    have hpSqMaximal : IsInMaximalIdeal K (p ^ 2) := by
      rw [pow_two]
      exact isInMaximalIdeal_mul_isIntegral K hpMaximal
        ((mem_integerRing_iff K).1 hpIntegral)
    exact isInMaximalIdeal_mul_isIntegral K hpSqMaximal
      ((mem_integerRing_iff K).1 huIntegral)
  have hy₀Unit : IsValuationUnit K (y 0) := by
    rw [IsValuationUnit]
    by_contra hnotZero
    have hy₀Nonneg : 0 ≤ ord K (y 0) :=
      (mem_integerRing_iff K).1 hy₀Integral
    have hy₀Pos : IsInMaximalIdeal K (y 0) :=
      lt_of_le_of_ne hy₀Nonneg (Ne.symm hnotZero)
    have hy₁Nonneg : Dyadic.IsIntegral K (y 1) :=
      (mem_integerRing_iff K).1 hy₁Integral
    have hfirst : IsInMaximalIdeal K (y 0 ^ 2) := by
      rw [pow_two]
      exact isInMaximalIdeal_mul_isIntegral K hy₀Pos hy₀Nonneg
    have hcross :
        IsInMaximalIdeal K ((2 * c') * (y 0 * y 1)) := by
      exact isInMaximalIdeal_mul_isIntegral K htwo'Maximal
        ((mem_integerRing_iff K).1
          ((IntegerRing K).mul_mem _ _ hy₀Integral hy₁Integral))
    have hlast :
        IsInMaximalIdeal K ((c' ^ 2 + (a' : K)) * y 1 ^ 2) := by
      exact isInMaximalIdeal_mul_isIntegral K hdiag'Maximal
        ((mem_integerRing_iff K).1
          ((IntegerRing K).pow_mem hy₁Integral 2))
    have hsum := isInMaximalIdeal_add K
      (isInMaximalIdeal_add K hfirst hcross) hlast
    rw [hyFormula] at hsum
    change ord K u₀ = 0 at hu
    change 0 < ord K u₀ at hsum
    rw [hu] at hsum
    exact (lt_irrefl 0) hsum
  let Y₀ : K := y 0 + p * y 1
  let Y₁ : K := p * y 1
  have hY₀Integral : Y₀ ∈ IntegerRing K := by
    exact (IntegerRing K).add_mem _ _ hy₀Integral
      ((IntegerRing K).mul_mem _ _ hpIntegral hy₁Integral)
  have hY₁Integral : Y₁ ∈ IntegerRing K := by
    exact (IntegerRing K).mul_mem _ _ hpIntegral hy₁Integral
  have hdetUnit : IsValuationUnit K
      ((1 : K) * Y₁ - (1 : K) * Y₀) := by
    have heq : (1 : K) * Y₁ - (1 : K) * Y₀ = -(y 0) := by
      dsimp [Y₀, Y₁]
      ring
    rw [heq, IsValuationUnit, ord_neg]
    exact hy₀Unit
  have hYValue :
      Y₀ ^ 2 + (2 * c) * (Y₀ * Y₁) +
          (c ^ 2 + (a : K)) * Y₁ ^ 2 = u₀ := by
    rw [← hyFormula]
    dsimp [Y₀, Y₁, c', a', p, pU]
    ring
  apply hasSomeEqualNormGeneratorBasis_of_equal_value_integral_pair
    a c 1 1 Y₀ Y₁ u₀ htwo hdiag
    (by norm_num) (by norm_num) hY₀Integral hY₁Integral hdetUnit
    (by
      change IsValuationUnit K u₀
      simpa [u₀] using hu)
  · dsimp [u₀]
    ring
  · exact hYValue

/-- Beli (2003), Lemma 3.17(3)(iii).  The defect-adapted model is spanned by
the norm generators `e₀` and `e₀+e₁`; the preceding index-`π` claim and the
even-step equality `g(πᴿε)=g(πᴿ⁺²ε)` then produce equal-value generators. -/
theorem hasSomeEqualNormGeneratorBasis_of_caseIII
    [QuadraticDefectLaws K]
    [UnitQuadraticDefectParityLaws K]
    [PrincipalUnitSquareClassFiltrationLaws K]
    [BinaryNormGeneratorLocalLaws.{u, u} K]
    (R : Int) (ε : Kˣ) (hε : IsValuationUnit K (ε : K))
    (hfinite : quadraticDefect K (-ε) ≠ ⊤)
    (hlower : 2 * (ramificationIndex K : Int) -
      2 * ((quadraticDefect K (-ε)).toNat : Int) < R)
    (hupper : R < 2 * (ramificationIndex K : Int))
    (hEvenR : Even R)
    (hEvenHigh : Even (R / 2 + (ramificationIndex K : Int))) :
    HasSomeEqualNormGeneratorBasis
      (uniformizerPowerUnit K R * ε) := by
  let q : Kˣ := -ε
  let d : Nat := (quadraticDefect K q).toNat
  have hfiniteQ : quadraticDefect K q ≠ ⊤ := by
    simpa [q] using hfinite
  have hqUnit : IsValuationUnit K (q : K) := by
    change ord K (-((ε : K))) = 0
    change ord K (ε : K) = 0 at hε
    simpa only [ord_neg] using hε
  have hdPos : 0 < d :=
    quadraticDefect_toNat_pos_of_unit_of_ne_top q hqUnit hfiniteQ
  have hnonsquare : ¬IsSquare q := by
    intro hsquare
    exact hfiniteQ
      ((quadraticDefect_eq_top_iff_isSquare (K := K) q).2 hsquare)
  have hdBound := quadraticDefect_le_two_mul_e_of_not_isSquare
    (K := K) hnonsquare
  have hdLe : d ≤ 2 * ramificationIndex K := by
    rw [← ENat.coe_toNat hfiniteQ] at hdBound
    simpa [d] using ENat.coe_le_coe.mp hdBound
  have hdLeInt : (d : Int) ≤
      2 * (ramificationIndex K : Int) := by
    exact_mod_cast hdLe
  have hlowerD : 2 * (ramificationIndex K : Int) -
      2 * (d : Int) < R := by
    simpa [d, q] using hlower
  have hRDouble : R = 2 * (R / 2) := by
    rcases hEvenR with ⟨r, hr⟩
    omega
  have hhighPos : 0 <
      (ramificationIndex K : Int) + R / 2 := by
    omega
  have hdiagPos : 0 < R + (d : Int) := by omega
  rcases exists_quadraticApproximation_exact_order q hfiniteQ with
    ⟨x, hxError⟩
  let err : K := 1 - x ^ 2 / (q : K)
  have herrOrder : ord K err = ((d : Int) : WithTop Int) := by
    simpa [err, d] using hxError
  have herrPos : 0 < ord K err := by
    rw [herrOrder]
    exact_mod_cast hdPos
  have hquotOrder : ord K (x ^ 2 / (q : K)) = 0 := by
    have hlt : ord K (1 : K) < ord K err := by
      simpa only [ord_one] using herrPos
    have hsub := (ord K).map_sub_eq_of_lt_left hlt
    have heq : 1 - err = x ^ 2 / (q : K) := by
      dsimp [err]
      ring
    rw [heq] at hsub
    simpa using hsub
  have hxNe : x ≠ 0 := by
    intro hzero
    rw [hzero] at hquotOrder
    simp at hquotOrder
  let xu : Kˣ := Units.mk0 x hxNe
  have hqOrder : ordUnit K q = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K q).1 hqUnit
  have hquotUnitOrder : ordUnit K (xu ^ 2 * q⁻¹) = 0 := by
    apply (isValuationUnit_iff_ordUnit_eq_zero K (xu ^ 2 * q⁻¹)).1
    rw [IsValuationUnit]
    have hval : ((xu ^ 2 * q⁻¹ : Kˣ) : K) =
        x ^ 2 / (q : K) := by
      simp [xu, div_eq_mul_inv]
    rw [hval]
    exact hquotOrder
  have hxuOrder : ordUnit K xu = 0 := by
    rw [ordUnit_mul, ordUnit_pow, ordUnit_inv, hqOrder]
      at hquotUnitOrder
    omega
  have hxUnit : IsValuationUnit K x := by
    simpa [xu] using
      (isValuationUnit_iff_ordUnit_eq_zero K xu).2 hxuOrder
  have hbaseEq : x ^ 2 + (ε : K) = (ε : K) * err := by
    dsimp [err, q]
    field_simp [Units.ne_zero ε]
    ring
  have hbaseOrder : ord K (x ^ 2 + (ε : K)) =
      ((d : Int) : WithTop Int) := by
    rw [hbaseEq, ord_mul, hε, herrOrder]
    simp
  let p : Kˣ := uniformizerPowerUnit K (R / 2)
  have hpSq : p ^ 2 = uniformizerPowerUnit K R := by
    dsimp [p]
    unfold uniformizerPowerUnit
    rw [pow_two, ← zpow_add]
    congr 1
    omega
  let a : Kˣ := uniformizerPowerUnit K R * ε
  let c : K := (p : K) * x
  let D : K := c ^ 2 + (a : K)
  have hDEq : D = (uniformizerPowerUnit K R : K) *
      (x ^ 2 + (ε : K)) := by
    have hpSqVal : (p : K) ^ 2 =
        (uniformizerPowerUnit K R : K) := by
      simpa using congrArg Units.val hpSq
    dsimp [D, c, a]
    change ((p : K) * x) ^ 2 +
        (uniformizerPowerUnit K R : K) * (ε : K) =
      (uniformizerPowerUnit K R : K) * (x ^ 2 + (ε : K))
    rw [mul_pow, hpSqVal]
    ring
  have hDOrder : ord K D =
      ((R + (d : Int) : Int) : WithTop Int) := by
    rw [hDEq, ord_mul, ← coe_ordUnit,
      ordUnit_uniformizerPowerUnit, hbaseOrder]
    norm_cast
  have hcOrder : ord K c = ((R / 2 : Int) : WithTop Int) := by
    dsimp [c]
    rw [ord_mul, ← coe_ordUnit,
      ordUnit_uniformizerPowerUnit, hxUnit]
    simp
  have htwoCOrder : ord K ((2 : K) * c) =
      (((ramificationIndex K : Int) + R / 2 : Int) : WithTop Int) := by
    rw [ord_mul, ← ramificationIndex_spec, hcOrder]
    norm_cast
  have htwoCIntegral : (2 : K) * c ∈ IntegerRing K := by
    apply (mem_integerRing_iff K).2
    rw [Dyadic.IsIntegral, htwoCOrder]
    exact_mod_cast hhighPos.le
  have hDIntegral : D ∈ IntegerRing K := by
    apply (mem_integerRing_iff K).2
    rw [Dyadic.IsIntegral, hDOrder]
    exact_mod_cast hdiagPos.le
  have htwoCMaximal : IsInMaximalIdeal K ((2 : K) * c) := by
    rw [IsInMaximalIdeal, htwoCOrder]
    exact_mod_cast hhighPos
  have hDMaximal : IsInMaximalIdeal K D := by
    rw [IsInMaximalIdeal, hDOrder]
    exact_mod_cast hdiagPos
  have hu : IsValuationUnit K
      (1 + (2 : K) * c + (c ^ 2 + (a : K))) := by
    have hcorrection : IsInMaximalIdeal K ((2 : K) * c + D) :=
      isInMaximalIdeal_add K htwoCMaximal hDMaximal
    have hlt : ord K (1 : K) < ord K ((2 : K) * c + D) := by
      change 0 < ord K ((2 : K) * c + D) at hcorrection
      simpa only [ord_one] using hcorrection
    have horder := (ord K).map_add_eq_of_lt_left hlt
    change ord K (1 + (2 : K) * c + D) = 0
    simpa [add_assoc] using horder
  have hgroups := beliNormGeneratorGroup_eq_shift_two_of_caseIII
    R ε hε hfinite hlower hupper hEvenR hEvenHigh
  have hpowerShift :
      uniformizerPowerUnit K (R + 2) =
        uniformizerPowerUnit K R * uniformizerPowerUnit K 1 ^ 2 := by
    unfold uniformizerPowerUnit
    rw [pow_two, ← zpow_add, ← zpow_add]
    congr 1
  have hparameterShift :
      a * uniformizerPowerUnit K 1 ^ 2 =
        uniformizerPowerUnit K (R + 2) * ε := by
    dsimp [a]
    rw [hpowerShift]
    ac_rfl
  have hgroupExact : beliNormGeneratorGroup K a =
      beliNormGeneratorGroup K
        (a * uniformizerPowerUnit K 1 ^ 2) := by
    change beliNormGeneratorGroup K
        (uniformizerPowerUnit K R * ε) = _
    rw [hparameterShift]
    exact hgroups
  apply hasSomeEqualNormGeneratorBasis_of_normGeneratorGroup_shift
    a c htwoCIntegral
  · simpa [D, a] using hDIntegral
  · exact hu
  · exact hgroupExact

/-- At order `-2e`, a square normalized negative unit gives exactly the
exceptional refined class `-1/4`. -/
theorem unitSquareClass_uniformizerPower_mul_eq_negativeQuarter
    (R : Int) (ε : Kˣ) (hε : IsValuationUnit K (ε : K))
    (hR : R = -(2 * (ramificationIndex K : Int)))
    (hsquare : IsSquare (-ε)) :
    unitSquareClass K (uniformizerPowerUnit K R * ε) =
      unitSquareClass K (negativeQuarterUnit K) := by
  rcases hsquare with ⟨s, hs⟩
  let twoU : Kˣ := Units.mk0 (2 : K) (by norm_num)
  let pInvE : Kˣ :=
    uniformizerPowerUnit K (-(ramificationIndex K : Int))
  let v : Kˣ := twoU * pInvE
  let t : Kˣ := v * s
  have htwoOrder : ordUnit K twoU = (ramificationIndex K : Int) := by
    apply WithTop.coe_injective
    rw [coe_ordUnit]
    change ord K (2 : K) =
      (((ramificationIndex K : Nat) : Int) : WithTop Int)
    exact (ramificationIndex_spec K).symm
  have hvOrder : ordUnit K v = 0 := by
    dsimp [v, pInvE]
    rw [ordUnit_mul, ordUnit_uniformizerPowerUnit, htwoOrder]
    omega
  have hnegUnit : IsValuationUnit K ((-ε : Kˣ) : K) := by
    change ord K (-((ε : K))) = 0
    change ord K (ε : K) = 0 at hε
    simpa only [ord_neg] using hε
  have hnegOrder : ordUnit K (-ε) = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K (-ε)).1 hnegUnit
  have hsOrder : ordUnit K s = 0 := by
    rw [hs, ordUnit_mul] at hnegOrder
    omega
  have htOrder : ordUnit K t = 0 := by
    dsimp [t]
    rw [ordUnit_mul, hvOrder, hsOrder]
    omega
  have htUnit : IsValuationUnit K (t : K) :=
    (isValuationUnit_iff_ordUnit_eq_zero K t).2 htOrder
  have hpSq : pInvE ^ 2 = uniformizerPowerUnit K
      (-(2 * (ramificationIndex K : Int))) := by
    dsimp [pInvE]
    unfold uniformizerPowerUnit
    rw [pow_two, ← zpow_add]
    congr 1
    omega
  have hquarterTwo : negativeQuarterUnit K * twoU ^ 2 = -1 := by
    apply Units.ext
    dsimp [negativeQuarterUnit, twoU]
    norm_num [show (4 : K) = 2 * 2 by norm_num]
  have hfactor :
      negativeQuarterUnit K * t ^ 2 =
        uniformizerPowerUnit K R * ε := by
    calc
      negativeQuarterUnit K * t ^ 2 =
          (negativeQuarterUnit K * twoU ^ 2) * pInvE ^ 2 * s ^ 2 := by
            dsimp [t, v]
            simp only [mul_pow]
            ac_rfl
      _ = (-1) * uniformizerPowerUnit K
            (-(2 * (ramificationIndex K : Int))) * (-ε) := by
          rw [hquarterTwo, hpSq, pow_two, ← hs]
      _ = uniformizerPowerUnit K
            (-(2 * (ramificationIndex K : Int))) * ε := by
          apply Units.ext
          simp
      _ = uniformizerPowerUnit K R * ε := by rw [hR]
  calc
    unitSquareClass K (uniformizerPowerUnit K R * ε) =
        unitSquareClass K (negativeQuarterUnit K * t ^ 2) := by
          rw [hfactor]
    _ = unitSquareClass K (negativeQuarterUnit K) :=
      unitSquareClass_mul_unit_square K (negativeQuarterUnit K) t htUnit

/-- The infinite-defect branch of Beli (2003), Lemma 3.17(iii).  A square
root of `-ε` makes the adapted second diagonal coefficient zero. -/
theorem hasSomeEqualNormGeneratorBasis_of_caseIII_top
    [QuadraticDefectLaws K]
    [PrincipalUnitSquareClassFiltrationLaws K]
    [BinaryNormGeneratorLocalLaws.{u, u} K]
    (R : Int) (ε : Kˣ) (hε : IsValuationUnit K (ε : K))
    (ha : IsBinaryParameterAdmissible
      (uniformizerPowerUnit K R * ε))
    (hdefect : quadraticDefect K (-ε) = ⊤)
    (hupper : R < 2 * (ramificationIndex K : Int))
    (hEvenR : Even R)
    (hEvenHigh : Even (R / 2 + (ramificationIndex K : Int)))
    (hquarter : unitSquareClass K (uniformizerPowerUnit K R * ε) ≠
      unitSquareClass K (negativeQuarterUnit K)) :
    HasSomeEqualNormGeneratorBasis
      (uniformizerPowerUnit K R * ε) := by
  have hsquare : IsSquare (-ε) :=
    (quadraticDefect_eq_top_iff_isSquare (K := K) (-ε)).1 hdefect
  have haOrder : ordUnit K (uniformizerPowerUnit K R * ε) = R :=
    ordUnit_uniformizerPower_mul_valuationUnit ε hε R
  have hRge : -(2 * (ramificationIndex K : Int)) ≤ R := by
    rw [← haOrder]
    exact ha.ordUnit_ge_neg_two_mul_e
  have hRne : R ≠ -(2 * (ramificationIndex K : Int)) := by
    intro hR
    exact hquarter
      (unitSquareClass_uniformizerPower_mul_eq_negativeQuarter
        R ε hε hR hsquare)
  have hRlower : -(2 * (ramificationIndex K : Int)) < R := by omega
  rcases hsquare with ⟨s, hs⟩
  have hnegUnit : IsValuationUnit K ((-ε : Kˣ) : K) := by
    change ord K (-((ε : K))) = 0
    change ord K (ε : K) = 0 at hε
    simpa only [ord_neg] using hε
  have hsOrder : ordUnit K s = 0 := by
    have hnegOrder : ordUnit K (-ε) = 0 :=
      (isValuationUnit_iff_ordUnit_eq_zero K (-ε)).1 hnegUnit
    rw [hs, ordUnit_mul] at hnegOrder
    omega
  have hsUnit : IsValuationUnit K (s : K) :=
    (isValuationUnit_iff_ordUnit_eq_zero K s).2 hsOrder
  have hRDouble : R = 2 * (R / 2) := by
    rcases hEvenR with ⟨r, hr⟩
    omega
  have hhighPos : 0 <
      (ramificationIndex K : Int) + R / 2 := by omega
  let p : Kˣ := uniformizerPowerUnit K (R / 2)
  have hpSq : p ^ 2 = uniformizerPowerUnit K R := by
    dsimp [p]
    unfold uniformizerPowerUnit
    rw [pow_two, ← zpow_add]
    congr 1
    omega
  let a : Kˣ := uniformizerPowerUnit K R * ε
  let c : K := (p : K) * (s : K)
  have hdiagEq : c ^ 2 + (a : K) = 0 := by
    have hpSqVal : (p : K) ^ 2 =
        (uniformizerPowerUnit K R : K) := by
      simpa using congrArg Units.val hpSq
    have hsVal : -(ε : K) = (s : K) ^ 2 := by
      simpa [pow_two] using congrArg Units.val hs
    dsimp [c, a]
    rw [mul_pow, hpSqVal]
    change (uniformizerPowerUnit K R : K) * (s : K) ^ 2 +
      (uniformizerPowerUnit K R : K) * (ε : K) = 0
    rw [← hsVal]
    ring
  have hcOrder : ord K c = ((R / 2 : Int) : WithTop Int) := by
    dsimp [c]
    rw [ord_mul, ← coe_ordUnit,
      ordUnit_uniformizerPowerUnit, hsUnit]
    simp
  have htwoCOrder : ord K ((2 : K) * c) =
      (((ramificationIndex K : Int) + R / 2 : Int) : WithTop Int) := by
    rw [ord_mul, ← ramificationIndex_spec, hcOrder]
    norm_cast
  have htwoCIntegral : (2 : K) * c ∈ IntegerRing K := by
    apply (mem_integerRing_iff K).2
    rw [Dyadic.IsIntegral, htwoCOrder]
    exact_mod_cast hhighPos.le
  have hdiagIntegral : c ^ 2 + (a : K) ∈ IntegerRing K := by
    rw [hdiagEq]
    exact (IntegerRing K).zero_mem
  have htwoCMaximal : IsInMaximalIdeal K ((2 : K) * c) := by
    rw [IsInMaximalIdeal, htwoCOrder]
    exact_mod_cast hhighPos
  have hu : IsValuationUnit K
      (1 + (2 : K) * c + (c ^ 2 + (a : K))) := by
    rw [hdiagEq, add_zero, IsValuationUnit]
    have hlt : ord K (1 : K) < ord K ((2 : K) * c) := by
      change 0 < ord K ((2 : K) * c) at htwoCMaximal
      simpa only [ord_one] using htwoCMaximal
    simpa using (ord K).map_add_eq_of_lt_left hlt
  have hgroups := beliNormGeneratorGroup_eq_shift_two_of_caseIII_top
    R ε hε hdefect hRlower hupper hEvenR hEvenHigh
  have hpowerShift :
      uniformizerPowerUnit K (R + 2) =
        uniformizerPowerUnit K R * uniformizerPowerUnit K 1 ^ 2 := by
    unfold uniformizerPowerUnit
    rw [pow_two, ← zpow_add, ← zpow_add]
    congr 1
  have hparameterShift :
      a * uniformizerPowerUnit K 1 ^ 2 =
        uniformizerPowerUnit K (R + 2) * ε := by
    dsimp [a]
    rw [hpowerShift]
    ac_rfl
  have hgroupExact : beliNormGeneratorGroup K a =
      beliNormGeneratorGroup K
        (a * uniformizerPowerUnit K 1 ^ 2) := by
    change beliNormGeneratorGroup K
        (uniformizerPowerUnit K R * ε) = _
    rw [hparameterShift]
    exact hgroups
  apply hasSomeEqualNormGeneratorBasis_of_normGeneratorGroup_shift
    a c htwoCIntegral hdiagIntegral hu hgroupExact

/-- The exceptional hyperbolic class in Lemma 3.17(iv), constructed directly
from a residue class different from `0` and `1`. -/
theorem hasSomeEqualNormGeneratorBasis_negativeQuarter
    (hres : HasResidueFieldMoreThanTwoElements (K := K)) :
    HasSomeEqualNormGeneratorBasis (negativeQuarterUnit K) := by
  rcases hres with ⟨ζ, hζ, hζneOne⟩
  change ord K ζ = 0 at hζ
  have hζSubNonneg : 0 ≤ ord K (ζ - 1) := by
    have hmin := min_ord_le_ord_add K ζ (-(1 : K))
    simpa [sub_eq_add_neg, hζ] using hmin
  have hζSubOrder : ord K (ζ - 1) = 0 := by
    apply le_antisymm
    · exact not_lt.mp hζneOne
    · exact hζSubNonneg
  have hζPlusOrder : ord K (ζ + 1) = 0 := by
    have htwoPos := ord_two_pos K
    have heq : ζ + 1 = (ζ - 1) + (2 : K) := by ring
    rw [heq]
    have hlt : ord K (ζ - 1) < ord K (2 : K) := by
      rw [hζSubOrder]
      exact htwoPos
    simpa [hζSubOrder] using (ord K).map_add_eq_of_lt_left hlt
  have hOneSubOrder : ord K (1 - ζ) = 0 := by
    have heq : 1 - ζ = -(ζ - 1) := by ring
    rw [heq, ord_neg, hζSubOrder]
  have hNumeratorOrder : ord K (1 - ζ ^ 2) = 0 := by
    have heq : 1 - ζ ^ 2 = (1 - ζ) * (1 + ζ) := by ring
    rw [heq, ord_mul, hOneSubOrder]
    have hplus : ord K (1 + ζ) = 0 := by
      simpa [add_comm] using hζPlusOrder
    rw [hplus]
    simp
  have hζne : ζ ≠ 0 := by
    intro hzero
    rw [hzero, ord_zero] at hζ
    exact WithTop.top_ne_coe hζ
  let c : K := (2 : K)⁻¹
  let β : K := (1 - ζ ^ 2) / ζ
  have htwoC : (2 : K) * c ∈ IntegerRing K := by
    have heq : (2 : K) * c = 1 := by
      dsimp [c]
      field_simp
    rw [heq]
    exact (IntegerRing K).one_mem
  have hdiag : c ^ 2 + (negativeQuarterUnit K : K) ∈
      IntegerRing K := by
    have heq : c ^ 2 + (negativeQuarterUnit K : K) = 0 := by
      dsimp [c, negativeQuarterUnit]
      change (2 : K)⁻¹ ^ 2 + -(4 : K)⁻¹ = 0
      norm_num [show (4 : K) = 2 * 2 by norm_num]
    rw [heq]
    exact (IntegerRing K).zero_mem
  have hζIntegral : ζ ∈ IntegerRing K := by
    apply (mem_integerRing_iff K).2
    rw [Dyadic.IsIntegral, hζ]
  have hβUnit : IsValuationUnit K β := by
    rw [IsValuationUnit]
    dsimp [β]
    rw [div_eq_mul_inv, ord_mul, AddValuation.map_inv,
      hNumeratorOrder, hζ]
    simp
  refine ⟨c, htwoC, hdiag, ζ, β, hζIntegral, hβUnit, ?_⟩
  have htwoCEq : (2 : K) * c = 1 := by
    dsimp [c]
    field_simp
  have hdiagEq : c ^ 2 + (negativeQuarterUnit K : K) = 0 := by
    dsimp [c, negativeQuarterUnit]
    change (2 : K)⁻¹ ^ 2 + -(4 : K)⁻¹ = 0
    norm_num [show (4 : K) = 2 * 2 by norm_num]
  rw [htwoCEq, hdiagEq]
  dsimp [β]
  field_simp [hζne]
  ring

/-- The exceptional-class half of Lemma 3.17(iv), transported from the
explicit `-1/4` model. -/
theorem hasSomeEqualNormGeneratorBasis_of_negativeQuarterClass
    (a : Kˣ)
    (hclass : unitSquareClass K a =
      unitSquareClass K (negativeQuarterUnit K))
    (hres : HasResidueFieldMoreThanTwoElements (K := K)) :
    HasSomeEqualNormGeneratorBasis a := by
  exact
    (hasSomeEqualNormGeneratorBasis_iff_of_unitSquareClass_eq
      hclass).2
        (hasSomeEqualNormGeneratorBasis_negativeQuarter hres)

/-- The `R=2e` half of Lemma 3.17(iv).  The proof follows Beli's residue
construction and then applies the quadratic-defect square criterion to the
resulting approximation beyond depth `2e`. -/
theorem hasSomeEqualNormGeneratorBasis_of_order_eq_two_e
    [QuadraticDefectLaws K] [PerfectResidueFieldLaws K]
    (ε : Kˣ) (hε : IsValuationUnit K (ε : K))
    (hres : HasResidueFieldMoreThanTwoElements (K := K)) :
    HasSomeEqualNormGeneratorBasis
      (uniformizerPowerUnit K
        (2 * (ramificationIndex K : Int)) * ε) := by
  let twoU : Kˣ := Units.mk0 (2 : K) (by norm_num)
  let pE : Kˣ :=
    uniformizerPowerUnit K (ramificationIndex K : Int)
  let v : Kˣ := pE / twoU
  have htwoOrder : ordUnit K twoU = (ramificationIndex K : Int) := by
    apply WithTop.coe_injective
    rw [coe_ordUnit]
    change ord K (2 : K) =
      (((ramificationIndex K : Nat) : Int) : WithTop Int)
    exact (ramificationIndex_spec K).symm
  have hvOrder : ordUnit K v = 0 := by
    dsimp [v]
    rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv,
      ordUnit_uniformizerPowerUnit, htwoOrder]
    omega
  have hvUnit : IsValuationUnit K (v : K) :=
    (isValuationUnit_iff_ordUnit_eq_zero K v).2 hvOrder
  let η : Kˣ := v ^ 2 * ε
  have hηOrder : ordUnit K η = 0 := by
    dsimp [η]
    rw [ordUnit_mul, ordUnit_pow, hvOrder,
      (isValuationUnit_iff_ordUnit_eq_zero K ε).1 hε]
    omega
  have hηUnit : IsValuationUnit K (η : K) :=
    (isValuationUnit_iff_ordUnit_eq_zero K η).2 hηOrder
  have hpESq :
      uniformizerPowerUnit K (2 * (ramificationIndex K : Int)) =
        pE ^ 2 := by
    dsimp [pE]
    unfold uniformizerPowerUnit
    rw [pow_two, ← zpow_add]
    congr 1
    omega
  have htwoMulV : twoU * v = pE := by
    dsimp [v]
    simp [div_eq_mul_inv, mul_comm]
  have haEq :
      uniformizerPowerUnit K (2 * (ramificationIndex K : Int)) * ε =
        twoU ^ 2 * η := by
    rw [hpESq, ← htwoMulV, mul_pow]
    dsimp [η]
    ac_rfl
  rcases hres.exists_unit_add_one_unit with ⟨ζ, hζ, hζPlus⟩
  change ord K ζ = 0 at hζ
  change ord K (ζ + 1) = 0 at hζPlus
  let r : K := ζ ^ 2 + ζ
  have hrOrder : ord K r = 0 := by
    have heq : r = ζ * (ζ + 1) := by
      dsimp [r]
      ring
    rw [heq, ord_mul, hζ, hζPlus]
    simp
  have hrne : r ≠ 0 := by
    intro hzero
    rw [hzero, ord_zero] at hrOrder
    exact WithTop.top_ne_coe hrOrder
  let u : Kˣ := Units.mk0 (r / (η : K))
    (div_ne_zero hrne (Units.ne_zero η))
  have huUnit : IsValuationUnit K (u : K) := by
    rw [IsValuationUnit]
    dsimp [u]
    rw [div_eq_mul_inv, ord_mul, AddValuation.map_inv,
      hrOrder, hηUnit]
    simp
  rcases exists_unit_squareRoot_mod_maximal (K := K) u huUnit with
    ⟨A, hA, hAApprox⟩
  change ord K A = 0 at hA
  change 0 < ord K (A ^ 2 - (u : K)) at hAApprox
  have hdiffEq :
      A ^ 2 * (η : K) - r =
        (A ^ 2 - (u : K)) * (η : K) := by
    dsimp [u]
    field_simp [Units.ne_zero η]
  have hdiffPos : 0 < ord K (A ^ 2 * (η : K) - r) := by
    rw [hdiffEq, ord_mul, hηUnit]
    simpa using hAApprox
  have hdiffOne : (1 : WithTop Int) ≤
      ord K (A ^ 2 * (η : K) - r) := by
    by_cases htop : ord K (A ^ 2 * (η : K) - r) = ⊤
    · rw [htop]
      exact le_top
    · obtain ⟨z, hz⟩ := WithTop.ne_top_iff_exists.mp htop
      have hzPos : (0 : Int) < z := by
        apply WithTop.coe_lt_coe.mp
        simpa [hz] using hdiffPos
      rw [← hz]
      exact_mod_cast (show (1 : Int) ≤ z by omega)
  let B : K := 1 + (2 : K) ^ 2 * A ^ 2 * (η : K)
  have hfourOrder : ord K ((2 : K) ^ 2) =
      ((2 * (ramificationIndex K : Int) : Int) : WithTop Int) := by
    rw [ord_pow, ← ramificationIndex_spec]
    norm_cast
  have htermOrder : ord K ((2 : K) ^ 2 * A ^ 2 * (η : K)) =
      ((2 * (ramificationIndex K : Int) : Int) : WithTop Int) := by
    rw [ord_mul, ord_mul, hfourOrder, ord_pow, hA, hηUnit]
    simp
  have htermPos : 0 < ord K ((2 : K) ^ 2 * A ^ 2 * (η : K)) := by
    rw [htermOrder]
    have hePos := ramificationIndex_pos K
    exact_mod_cast (show (0 : Int) <
      2 * (ramificationIndex K : Int) by omega)
  have hBOrder : ord K B = 0 := by
    dsimp [B]
    have hlt : ord K (1 : K) <
        ord K ((2 : K) ^ 2 * A ^ 2 * (η : K)) := by
      simpa only [ord_one] using htermPos
    simpa using (ord K).map_add_eq_of_lt_left hlt
  have hBne : B ≠ 0 := by
    intro hzero
    rw [hzero, ord_zero] at hBOrder
    exact WithTop.top_ne_coe hBOrder
  let Bu : Kˣ := Units.mk0 B hBne
  let x₀ : K := 1 + (2 : K) * ζ
  have hdifference :
      B - x₀ ^ 2 =
        (2 : K) ^ 2 * (A ^ 2 * (η : K) - r) := by
    dsimp [B, x₀, r]
    ring
  have hdiffDepth :
      ((2 * ramificationIndex K + 1 : Nat) : WithTop Int) ≤
        ord K (B - x₀ ^ 2) := by
    rw [hdifference, ord_mul, hfourOrder]
    have hadd := add_le_add_left hdiffOne
      ((2 * (ramificationIndex K : Int) : Int) : WithTop Int)
    norm_cast at hadd ⊢
    simpa [add_comm] using hadd
  have happrox : IsQuadraticApproximation K Bu
      (2 * ramificationIndex K + 1) := by
    refine ⟨x₀, ?_⟩
    have hnormalized :
        1 - x₀ ^ 2 / (Bu : K) = (B - x₀ ^ 2) / B := by
      change 1 - x₀ ^ 2 / B = (B - x₀ ^ 2) / B
      field_simp [hBne]
    rw [hnormalized, div_eq_mul_inv, ord_mul,
      AddValuation.map_inv, hBOrder]
    simpa using hdiffDepth
  have hBSquare : IsSquare Bu :=
    isSquare_of_quadraticApproximation_two_e_add_one Bu happrox
  rcases hBSquare with ⟨b, hb⟩
  have hBuOrder : ordUnit K Bu = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K Bu).1 hBOrder
  have hbOrder : ordUnit K b = 0 := by
    rw [hb, ordUnit_mul] at hBuOrder
    omega
  have hbUnit : IsValuationUnit K (b : K) :=
    (isValuationUnit_iff_ordUnit_eq_zero K b).2 hbOrder
  have hbInvIntegral : ((b⁻¹ : Kˣ) : K) ∈ IntegerRing K := by
    exact (valuationUnit_mem_integerRing_and_inv b hbUnit).2
  let a : Kˣ :=
    uniformizerPowerUnit K (2 * (ramificationIndex K : Int)) * ε
  have haOrder : ordUnit K a = 2 * (ramificationIndex K : Int) := by
    dsimp [a]
    rw [ordUnit_mul, ordUnit_uniformizerPowerUnit,
      (isValuationUnit_iff_ordUnit_eq_zero K ε).1 hε]
    omega
  have haIntegral : (a : K) ∈ IntegerRing K := by
    apply (mem_integerRing_iff K).2
    rw [Dyadic.IsIntegral, ← coe_ordUnit, haOrder]
    exact_mod_cast (show (0 : Int) ≤
      2 * (ramificationIndex K : Int) by positivity)
  let α : K := ((b⁻¹ : Kˣ) : K)
  let β : K := A * α
  have hβUnit : IsValuationUnit K β := by
    rw [IsValuationUnit]
    dsimp [β, α]
    rw [ord_mul, hA, ← coe_ordUnit, ordUnit_inv, hbOrder]
    simp
  refine ⟨0, by simp, by simpa [a] using haIntegral,
    α, β, by simpa [α] using hbInvIntegral, hβUnit, ?_⟩
  have haVal : (a : K) = (2 : K) ^ 2 * (η : K) := by
    exact congrArg Units.val haEq
  have hbVal : B = (b : K) ^ 2 := by
    simpa [Bu, pow_two] using congrArg Units.val hb
  have hnumerator : 1 + (a : K) * A ^ 2 = B := by
    rw [haVal]
    dsimp [B]
    ring
  have hmain : α ^ 2 + (a : K) * β ^ 2 = 1 := by
    calc
      α ^ 2 + (a : K) * β ^ 2 =
          (1 + (a : K) * A ^ 2) / (b : K) ^ 2 := by
            dsimp [α, β]
            simp only [Units.val_inv_eq_inv_val]
            field_simp [Units.ne_zero b]
      _ = 1 := by
        rw [hnumerator, hbVal]
        field_simp [Units.ne_zero b]
  simpa [a] using hmain

/-- Two integral shears for the same normalized binary parameter differ by an
integer.  This is the scalar form of binary uniqueness with a common norm
generator. -/
theorem binaryShear_sub_mem_integerRing
    (a : Kˣ) (c c' : K)
    (htwo : (2 : K) * c ∈ IntegerRing K)
    (hdiag : c ^ 2 + (a : K) ∈ IntegerRing K)
    (htwo' : (2 : K) * c' ∈ IntegerRing K)
    (hdiag' : c' ^ 2 + (a : K) ∈ IntegerRing K) :
    c - c' ∈ IntegerRing K := by
  by_contra hnotIntegral
  have hnotNonneg : ¬0 ≤ ord K (c - c') := by
    intro hnonneg
    exact hnotIntegral ((mem_integerRing_iff K).2 hnonneg)
  have hdeltaNeg : ord K (c - c') < 0 := lt_of_not_ge hnotNonneg
  have htwoNonneg : 0 ≤ ord K ((2 : K) * c') :=
    (mem_integerRing_iff K).1 htwo'
  have hdeltaLt : ord K (c - c') < ord K ((2 : K) * c') :=
    hdeltaNeg.trans_le htwoNonneg
  have hsum : c + c' = (c - c') + (2 : K) * c' := by ring
  have hsumOrder : ord K (c + c') = ord K (c - c') := by
    rw [hsum]
    exact (ord K).map_add_eq_of_lt_left hdeltaLt
  have hsquares :
      (c ^ 2 + (a : K)) - (c' ^ 2 + (a : K)) ∈
        IntegerRing K :=
    (IntegerRing K).sub_mem hdiag hdiag'
  have hfactor :
      (c ^ 2 + (a : K)) - (c' ^ 2 + (a : K)) =
        (c - c') * (c + c') := by ring
  rw [hfactor] at hsquares
  have hproductNonneg :
      0 ≤ ord K ((c - c') * (c + c')) :=
    (mem_integerRing_iff K).1 hsquares
  rw [ord_mul, hsumOrder] at hproductNonneg
  have hdeltaNeTop : ord K (c - c') ≠ ⊤ := by
    intro htop
    rw [htop] at hdeltaNeg
    exact (not_lt_of_ge le_top) hdeltaNeg
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hdeltaNeTop
  rw [← hn] at hdeltaNeg hproductNonneg
  norm_cast at hdeltaNeg hproductNonneg
  omega

/-- An equal-value companion transports between any two integral shears for
the same parameter. -/
theorem hasEqualNormGeneratorBasisWitness_iff_of_shears
    (a : Kˣ) (c c' : K)
    (htwo : (2 : K) * c ∈ IntegerRing K)
    (hdiag : c ^ 2 + (a : K) ∈ IntegerRing K)
    (htwo' : (2 : K) * c' ∈ IntegerRing K)
    (hdiag' : c' ^ 2 + (a : K) ∈ IntegerRing K) :
    HasEqualNormGeneratorBasisWitness a c ↔
      HasEqualNormGeneratorBasisWitness a c' := by
  have hcc' : c - c' ∈ IntegerRing K :=
    binaryShear_sub_mem_integerRing a c c' htwo hdiag htwo' hdiag'
  have hc'c : c' - c ∈ IntegerRing K :=
    binaryShear_sub_mem_integerRing a c' c htwo' hdiag' htwo hdiag
  constructor
  · rintro ⟨α, β, hα, hβ, heq⟩
    have hβIntegral : β ∈ IntegerRing K := by
      apply (mem_integerRing_iff K).2
      rw [Dyadic.IsIntegral, hβ]
    refine ⟨α + (c - c') * β, β, ?_, hβ, ?_⟩
    · exact (IntegerRing K).add_mem _ _ hα
        ((IntegerRing K).mul_mem _ _ hcc' hβIntegral)
    · calc
        (α + (c - c') * β) ^ 2 +
              (2 * c') * ((α + (c - c') * β) * β) +
              (c' ^ 2 + (a : K)) * β ^ 2 =
            α ^ 2 + (2 * c) * (α * β) +
              (c ^ 2 + (a : K)) * β ^ 2 := by ring
        _ = 1 := heq
  · rintro ⟨α, β, hα, hβ, heq⟩
    have hβIntegral : β ∈ IntegerRing K := by
      apply (mem_integerRing_iff K).2
      rw [Dyadic.IsIntegral, hβ]
    refine ⟨α + (c' - c) * β, β, ?_, hβ, ?_⟩
    · exact (IntegerRing K).add_mem _ _ hα
        ((IntegerRing K).mul_mem _ _ hc'c hβIntegral)
    · calc
        (α + (c' - c) * β) ^ 2 +
              (2 * c) * ((α + (c' - c) * β) * β) +
              (c ^ 2 + (a : K)) * β ^ 2 =
            α ^ 2 + (2 * c') * (α * β) +
              (c' ^ 2 + (a : K)) * β ^ 2 := by ring
        _ = 1 := heq

/-- Beli (2003), Lemma 3.17, `(1) ↔ (2)` in normalized binary-model
coordinates.  Admissibility supplies a model for the reverse implication. -/
theorem hasSomeEqualNormGeneratorBasis_iff_hasEvery
    (a : Kˣ) (ha : IsBinaryParameterAdmissible a) :
    HasSomeEqualNormGeneratorBasis a ↔
      HasEveryEqualNormGeneratorBasis a := by
  constructor
  · rintro ⟨c, htwo, hdiag, hc⟩ c' htwo' hdiag'
    exact
      (hasEqualNormGeneratorBasisWitness_iff_of_shears
        a c c' htwo hdiag htwo' hdiag').1 hc
  · intro hall
    rcases ha with ⟨c, htwo, hdiag⟩
    exact ⟨c, htwo, hdiag, hall c htwo hdiag⟩

/-- Geometric realization of the existential assertion in Lemma 3.17 for
an arbitrary binary BONG.  The companion has the prescribed head value, and
its projection is a valuation-unit multiple of the recursive tail head.
This is the concrete bridge used when Lemma 6.6 chooses the auxiliary norm
generator `x₀`. -/
theorem exists_equalValueCompanion_of_hasSome
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    (b : BONG V q L 2)
    (hsome : HasSomeEqualNormGeneratorBasis b.binaryParameter) :
    ∃ (x : V) (alpha beta : K),
      alpha ∈ IntegerRing K ∧
        IsValuationUnit K beta ∧
        Lattice.IsNormGenerator q L x ∧
        q.quadratic x = q.quadratic b.head ∧
        x = alpha • b.head + beta • b.binarySecondVector ∧
        q.projectionToOrthogonal b.head b.head_isAnisotropic x =
          beta • b.tail.head := by
  have hall : HasEveryEqualNormGeneratorBasis b.binaryParameter :=
    (hasSomeEqualNormGeneratorBasis_iff_hasEvery b.binaryParameter
      b.binaryParameter_isBinaryParameterAdmissible).1 hsome
  rcases b.binaryModelCoefficient_isAdmissibleWitness with
    ⟨htwo, hdiag⟩
  rcases hall b.binaryModelCoefficient htwo hdiag with
    ⟨alpha, beta, halpha, hbeta, hequation⟩
  let y : Fin 2 → K := binaryModelEqualCompanion alpha beta
  have hbetaIntegral : beta ∈ IntegerRing K := by
    apply (mem_integerRing_iff K).2
    rw [Dyadic.IsIntegral, hbeta]
  have hyMem : y ∈ binaryModelLattice (K := K) :=
    binaryModelEqualCompanion_mem alpha beta halpha hbetaIntegral
  have hyValue :
      (QuadraticSpace.binaryModel b.binaryParameter
          b.binaryModelCoefficient).quadratic y = 1 := by
    dsimp only [y]
    rw [binaryModelEqualCompanion_quadratic]
    exact hequation
  have hfirstGenerator := binaryModelFirst_isNormGenerator
    b.binaryParameter b.binaryModelCoefficient htwo hdiag
  have hyGenerator :
      Lattice.IsNormGenerator
        (QuadraticSpace.binaryModel b.binaryParameter
          b.binaryModelCoefficient)
        (binaryModelLattice (K := K)) y := by
    constructor
    · exact hyMem
    · calc
        Lattice.normIdeal
              (QuadraticSpace.binaryModel b.binaryParameter
                b.binaryModelCoefficient)
              (binaryModelLattice (K := K)) =
            Lattice.principalIdeal (K := K)
              ((QuadraticSpace.binaryModel b.binaryParameter
                b.binaryModelCoefficient).quadratic
                QuadraticSpace.binaryModelFirst) :=
          hfirstGenerator.normIdeal_eq
        _ = Lattice.principalIdeal (K := K)
              ((QuadraticSpace.binaryModel b.binaryParameter
                b.binaryModelCoefficient).quadratic y) := by
          rw [QuadraticSpace.binaryModel_quadratic_first, hyValue]
  have hyScaledGenerator :
      Lattice.IsNormGenerator b.normalizedBinaryModelSpace
        (binaryModelLattice (K := K)) y := by
    exact hyGenerator.rescaleQuadraticUnit (b.valueUnit 0)
  let f := b.normalizedBinaryModelLatticeIsometry
  let x : V := f.toLinearEquiv y
  have hxGenerator : Lattice.IsNormGenerator q L x := by
    exact hyScaledGenerator.mapLatticeIsometry f
  have hxFormula :
      x = alpha • b.head + beta • b.binarySecondVector := by
    dsimp only [x, y, f]
    rw [binaryModelEqualCompanion, map_add, map_smul, map_smul,
      b.normalizedBinaryModelLatticeIsometry_apply_first,
      b.normalizedBinaryModelLatticeIsometry_apply_second]
  have hxValue : q.quadratic x = q.quadratic b.head := by
    calc
      q.quadratic x = b.normalizedBinaryModelSpace.quadratic y :=
        f.map_quadratic y
      _ = b.normalizedBinaryModelSpace.quadratic
          QuadraticSpace.binaryModelFirst := by
        simp only [normalizedBinaryModelSpace,
          QuadraticSpace.rescaleUnit_quadratic, hyValue,
          QuadraticSpace.binaryModel_quadratic_first, mul_one]
      _ = q.quadratic b.head := by
        rw [← b.normalizedBinaryModelLatticeIsometry_apply_first]
        exact (f.map_quadratic QuadraticSpace.binaryModelFirst).symm
  refine ⟨x, alpha, beta, halpha, hbeta, hxGenerator, hxValue,
    hxFormula, ?_⟩
  have hheadProjection :
      q.projectionToOrthogonal b.head b.head_isAnisotropic b.head = 0 := by
    apply Subtype.ext
    exact q.orthogonalProjection_self b.head_isAnisotropic
  rw [hxFormula, map_add, map_smul, map_smul, hheadProjection,
    b.projectionToOrthogonal_binarySecondVector]
  simp

/-- The four parameter alternatives in Lemma 3.17(3) imply the existential
equal-norm-generator basis assertion. -/
theorem hasSomeEqualNormGeneratorBasis_of_parameterCases
    [QuadraticDefectLaws K]
    [UnitQuadraticDefectParityLaws K]
    [PerfectResidueFieldLaws K]
    [PrincipalUnitSquareClassFiltrationLaws K]
    [BinaryNormGeneratorLocalLaws.{u, u} K]
    (R : Int) (ε : Kˣ) (hε : IsValuationUnit K (ε : K))
    (ha : IsBinaryParameterAdmissible
      (uniformizerPowerUnit K R * ε))
    (hcases : BeliLemma317ParameterCases (K := K) R ε) :
    HasSomeEqualNormGeneratorBasis
      (uniformizerPowerUnit K R * ε) := by
  rcases hcases with hi | hii | hiii | hiv
  · apply hasSomeEqualNormGeneratorBasis_of_two_e_lt_order
    rw [ordUnit_uniformizerPower_mul_valuationUnit ε hε R]
    exact hi
  · rcases hii with ⟨hfinite, hR⟩
    exact hasSomeEqualNormGeneratorBasis_of_order_eq_two_e_sub_two_defect
      R ε hε hfinite hR
  · rcases hiii with
      ⟨hboundary, hupper, hEvenR, hEvenHigh, hquarter⟩
    rcases hboundary with htop | ⟨hfinite, hlower⟩
    · exact hasSomeEqualNormGeneratorBasis_of_caseIII_top
        R ε hε ha htop hupper hEvenR hEvenHigh hquarter
    · exact hasSomeEqualNormGeneratorBasis_of_caseIII
        R ε hε hfinite hlower hupper hEvenR hEvenHigh
  · rcases hiv with ⟨hparameter, hres⟩
    rcases hparameter with hR | hquarter
    · subst R
      exact hasSomeEqualNormGeneratorBasis_of_order_eq_two_e ε hε hres
    · exact hasSomeEqualNormGeneratorBasis_of_negativeQuarterClass
        (uniformizerPowerUnit K R * ε) hquarter hres

/-- Lemma 3.17(3) also implies the universal assertion (2), via the already
proved equivalence `(1) ↔ (2)`. -/
theorem hasEveryEqualNormGeneratorBasis_of_parameterCases
    [QuadraticDefectLaws K]
    [UnitQuadraticDefectParityLaws K]
    [PerfectResidueFieldLaws K]
    [PrincipalUnitSquareClassFiltrationLaws K]
    [BinaryNormGeneratorLocalLaws.{u, u} K]
    (R : Int) (ε : Kˣ) (hε : IsValuationUnit K (ε : K))
    (ha : IsBinaryParameterAdmissible
      (uniformizerPowerUnit K R * ε))
    (hcases : BeliLemma317ParameterCases (K := K) R ε) :
    HasEveryEqualNormGeneratorBasis
      (uniformizerPowerUnit K R * ε) := by
  have hsome := hasSomeEqualNormGeneratorBasis_of_parameterCases
    R ε hε ha hcases
  exact
    (hasSomeEqualNormGeneratorBasis_iff_hasEvery
      (uniformizerPowerUnit K R * ε) ha).1 hsome

/-- Obstruction (a) in the proof of Lemma 3.17: an odd parameter order
strictly between `0` and `2e` fails assertion (2) already in the orthogonal
model. -/
theorem not_hasEveryEqualNormGeneratorBasis_of_odd_order
    [DyadicSquareDifferenceLaws K]
    (R : Int) (ε : Kˣ) (hε : IsValuationUnit K (ε : K))
    (hpos : 0 < R)
    (hupper : R < 2 * (ramificationIndex K : Int))
    (hodd : Odd R) :
    ¬HasEveryEqualNormGeneratorBasis
      (uniformizerPowerUnit K R * ε) := by
  let a : Kˣ := uniformizerPowerUnit K R * ε
  have haOrder : ordUnit K a = R :=
    ordUnit_uniformizerPower_mul_valuationUnit ε hε R
  have haIntegral : (a : K) ∈ IntegerRing K := by
    apply (mem_integerRing_iff K).2
    rw [Dyadic.IsIntegral, ← coe_ordUnit, haOrder]
    exact_mod_cast hpos.le
  intro hall
  rcases hall 0 (by simp) (by simpa [a] using haIntegral) with
    ⟨α, β, _hα, hβ, heq⟩
  have heq' : α ^ 2 + (a : K) * β ^ 2 = 1 := by
    simpa [a] using heq
  have honeSub : 1 - α ^ 2 = (a : K) * β ^ 2 := by
    rw [← heq']
    ring
  have honeSubOrder : ord K (1 - α ^ 2) =
      (R : WithTop Int) := by
    rw [honeSub, ord_mul, ← coe_ordUnit, haOrder, ord_pow, hβ]
    simp
  have heven := even_order_one_sub_sq_of_lt_two_mul_e
    (K := K) α R honeSubOrder hpos hupper
  rcases hodd with ⟨m, hm⟩
  rcases heven with ⟨n, hn⟩
  omega

/-- The hyperbolic representative `-1/4` is an admissible binary
parameter, with shear `1/2`. -/
theorem negativeQuarter_isBinaryParameterAdmissible :
    IsBinaryParameterAdmissible (negativeQuarterUnit K) := by
  let c : K := (2 : K)⁻¹
  refine ⟨c, ?_, ?_⟩
  · have heq : (2 : K) * c = 1 := by
      dsimp [c]
      field_simp
    rw [heq]
    exact (IntegerRing K).one_mem
  · have heq : c ^ 2 + (negativeQuarterUnit K : K) = 0 := by
      dsimp [c, negativeQuarterUnit]
      change (2 : K)⁻¹ ^ 2 + -(4 : K)⁻¹ = 0
      norm_num [show (4 : K) = 2 * 2 by norm_num]
    rw [heq]
    exact (IntegerRing K).zero_mem

/-- Obstruction (c), in positive form: assertion (2) for the hyperbolic
class produces a residue-field element different from both `0` and `1`. -/
theorem hasResidueFieldMoreThanTwoElements_of_negativeQuarter_hasEvery
    (hall : HasEveryEqualNormGeneratorBasis (negativeQuarterUnit K)) :
    HasResidueFieldMoreThanTwoElements (K := K) := by
  let c : K := (2 : K)⁻¹
  have htwo : (2 : K) * c ∈ IntegerRing K := by
    have heq : (2 : K) * c = 1 := by
      dsimp [c]
      field_simp
    rw [heq]
    exact (IntegerRing K).one_mem
  have hdiag : c ^ 2 + (negativeQuarterUnit K : K) ∈
      IntegerRing K := by
    have heq : c ^ 2 + (negativeQuarterUnit K : K) = 0 := by
      dsimp [c, negativeQuarterUnit]
      change (2 : K)⁻¹ ^ 2 + -(4 : K)⁻¹ = 0
      norm_num [show (4 : K) = 2 * 2 by norm_num]
    rw [heq]
    exact (IntegerRing K).zero_mem
  rcases hall c htwo hdiag with ⟨α, β, hα, hβ, heq⟩
  have htwoC : (2 : K) * c = 1 := by
    dsimp [c]
    field_simp
  have hdiagZero : c ^ 2 + (negativeQuarterUnit K : K) = 0 := by
    dsimp [c, negativeQuarterUnit]
    change (2 : K)⁻¹ ^ 2 + -(4 : K)⁻¹ = 0
    norm_num [show (4 : K) = 2 * 2 by norm_num]
  have heq' : α ^ 2 + α * β = 1 := by
    rw [htwoC, hdiagZero] at heq
    simpa using heq
  have hβIntegral : β ∈ IntegerRing K := by
    apply (mem_integerRing_iff K).2
    rw [Dyadic.IsIntegral, hβ]
  have hαUnit : IsValuationUnit K α := by
    rw [IsValuationUnit]
    by_contra hne
    have hαNonneg : 0 ≤ ord K α :=
      (mem_integerRing_iff K).1 hα
    have hαMaximal : IsInMaximalIdeal K α :=
      lt_of_le_of_ne hαNonneg (Ne.symm hne)
    have hsqMaximal : IsInMaximalIdeal K (α ^ 2) := by
      rw [pow_two]
      exact isInMaximalIdeal_mul_isIntegral K hαMaximal hαNonneg
    have hprodMaximal : IsInMaximalIdeal K (α * β) :=
      isInMaximalIdeal_mul_isIntegral K hαMaximal
        ((mem_integerRing_iff K).1 hβIntegral)
    have hsumMaximal := isInMaximalIdeal_add K hsqMaximal hprodMaximal
    rw [heq'] at hsumMaximal
    simpa [IsInMaximalIdeal] using hsumMaximal
  have hfactor : α * (α + β) = 1 := by
    rw [← heq']
    ring
  have hsumUnit : IsValuationUnit K (α + β) := by
    rw [IsValuationUnit]
    have horder := congrArg (ord K) hfactor
    rw [ord_mul, ord_one, hαUnit] at horder
    simpa using horder
  have hβne : β ≠ 0 := by
    intro hzero
    rw [hzero, IsValuationUnit, ord_zero] at hβ
    exact WithTop.top_ne_coe hβ
  let ζ : K := -α / β
  have hζUnit : IsValuationUnit K ζ := by
    rw [IsValuationUnit]
    dsimp [ζ]
    rw [div_eq_mul_inv, ord_mul, ord_neg,
      AddValuation.map_inv, hαUnit, hβ]
    simp
  have hζSub : ζ - 1 = -(α + β) / β := by
    dsimp [ζ]
    field_simp [hβne]
    ring
  have hζSubUnit : IsValuationUnit K (ζ - 1) := by
    rw [hζSub, IsValuationUnit, div_eq_mul_inv, ord_mul,
      ord_neg, AddValuation.map_inv, hsumUnit, hβ]
    simp
  refine ⟨ζ, hζUnit, ?_⟩
  change ¬0 < ord K (ζ - 1)
  rw [hζSubUnit]
  exact lt_irrefl 0

/-- Assertion (2) in any representative of the exceptional refined class
forces the residue field to have more than two elements. -/
theorem hasResidueFieldMoreThanTwoElements_of_negativeQuarterClass
    (a : Kˣ) (ha : IsBinaryParameterAdmissible a)
    (hclass : unitSquareClass K a =
      unitSquareClass K (negativeQuarterUnit K))
    (hall : HasEveryEqualNormGeneratorBasis a) :
    HasResidueFieldMoreThanTwoElements (K := K) := by
  have hsomeA : HasSomeEqualNormGeneratorBasis a :=
    (hasSomeEqualNormGeneratorBasis_iff_hasEvery a ha).2 hall
  have hsomeQuarter :
      HasSomeEqualNormGeneratorBasis (negativeQuarterUnit K) :=
    (hasSomeEqualNormGeneratorBasis_iff_of_unitSquareClass_eq
      hclass).1 hsomeA
  have hallQuarter :
      HasEveryEqualNormGeneratorBasis (negativeQuarterUnit K) :=
    (hasSomeEqualNormGeneratorBasis_iff_hasEvery
      (negativeQuarterUnit K)
      (negativeQuarter_isBinaryParameterAdmissible (K := K))).1
        hsomeQuarter
  exact
    hasResidueFieldMoreThanTwoElements_of_negativeQuarter_hasEvery
      hallQuarter

/-- Obstruction (d), in positive form: at order `R=2e`, assertion (2)
forces the residue field to contain more than two elements. -/
theorem hasResidueFieldMoreThanTwoElements_of_order_eq_two_e_hasEvery
    [DyadicSquareDifferenceLaws K]
    (ε : Kˣ) (hε : IsValuationUnit K (ε : K))
    (hall : HasEveryEqualNormGeneratorBasis
      (uniformizerPowerUnit K
        (2 * (ramificationIndex K : Int)) * ε)) :
    HasResidueFieldMoreThanTwoElements (K := K) := by
  let R : Int := 2 * (ramificationIndex K : Int)
  let a : Kˣ := uniformizerPowerUnit K R * ε
  have haOrder : ordUnit K a = R :=
    ordUnit_uniformizerPower_mul_valuationUnit ε hε R
  have haIntegral : (a : K) ∈ IntegerRing K := by
    apply (mem_integerRing_iff K).2
    rw [Dyadic.IsIntegral, ← coe_ordUnit, haOrder]
    dsimp [R]
    exact WithTop.coe_le_coe.mpr (by positivity)
  rcases hall 0 (by simp) (by simpa [a, R] using haIntegral) with
    ⟨α, β, _hα, hβ, heq⟩
  have heq' : α ^ 2 + (a : K) * β ^ 2 = 1 := by
    simpa [a, R] using heq
  have htwoSqNe : (2 : K) ^ 2 ≠ 0 := by norm_num
  have hβne : β ≠ 0 := by
    intro hzero
    rw [hzero, IsValuationUnit, ord_zero] at hβ
    exact WithTop.top_ne_coe hβ
  let βU : Kˣ := Units.mk0 β hβne
  let twoSq : Kˣ := Units.mk0 ((2 : K) ^ 2) htwoSqNe
  let uU : Kˣ := a * βU ^ 2 * twoSq⁻¹
  let u : K := (uU : K)
  have hfourOrder : ord K ((2 : K) ^ 2) =
      ((2 * (ramificationIndex K : Int) : Int) : WithTop Int) := by
    rw [ord_pow, ← ramificationIndex_spec]
    norm_cast
  have hβUOrder : ordUnit K βU = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K βU).1 (by
      simpa [βU] using hβ)
  have htwoSqOrder : ordUnit K twoSq =
      2 * (ramificationIndex K : Int) := by
    apply WithTop.coe_injective
    rw [coe_ordUnit]
    simpa [twoSq] using hfourOrder
  have hu : IsValuationUnit K u := by
    apply (isValuationUnit_iff_ordUnit_eq_zero K uU).2
    dsimp [uU]
    rw [ordUnit_mul, ordUnit_mul, ordUnit_pow, ordUnit_inv,
      haOrder, hβUOrder, htwoSqOrder]
    dsimp [R]
    omega
  have hscaled : (2 : K) ^ 2 * u = (a : K) * β ^ 2 := by
    dsimp [u, uU, twoSq, βU]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val,
      Units.val_mk0, Units.val_inv_eq_inv_val]
    field_simp [htwoSqNe]
  by_contra hnotResidue
  have hresidue : ∀ z : K,
      IsValuationUnit K z → IsInMaximalIdeal K (z - 1) := by
    intro z hz
    by_contra hzNot
    exact hnotResidue ⟨z, hz, hzNot⟩
  have hne := one_sub_four_mul_unit_ne_sq_of_residue_two
    (K := K) u α hu hresidue
  apply hne
  rw [hscaled]
  rw [← heq']
  ring

/-- Common coordinate obstruction behind case (b).  If the mixed correction
and second diagonal correction have distinct positive orders, then their
smaller order is the exact order of `1-α²`; it therefore cannot be odd below
`2e`. -/
theorem not_hasEveryEqualNormGeneratorBasis_of_distinct_correction_orders
    [DyadicSquareDifferenceLaws K]
    (a : Kˣ) (c : K) (m n k : Int)
    (htwo : (2 : K) * c ∈ IntegerRing K)
    (hdiag : c ^ 2 + (a : K) ∈ IntegerRing K)
    (hcrossOrder : ord K ((2 : K) * c) = (m : WithTop Int))
    (hdiagOrder : ord K (c ^ 2 + (a : K)) = (n : WithTop Int))
    (hmPos : 0 < m) (hnPos : 0 < n) (hmn : m ≠ n)
    (hk : min m n = k) (hkPos : 0 < k)
    (hkUpper : k < 2 * (ramificationIndex K : Int))
    (hkOdd : Odd k) :
    ¬HasEveryEqualNormGeneratorBasis a := by
  intro hall
  rcases hall c htwo hdiag with ⟨α, β, hα, hβ, heq⟩
  have hβIntegral : β ∈ IntegerRing K := by
    apply (mem_integerRing_iff K).2
    rw [Dyadic.IsIntegral, hβ]
  have hcrossMaximal : IsInMaximalIdeal K ((2 : K) * c) := by
    rw [IsInMaximalIdeal, hcrossOrder]
    exact_mod_cast hmPos
  have hdiagMaximal : IsInMaximalIdeal K (c ^ 2 + (a : K)) := by
    rw [IsInMaximalIdeal, hdiagOrder]
    exact_mod_cast hnPos
  have hαUnit : IsValuationUnit K α := by
    rw [IsValuationUnit]
    by_contra hne
    have hαNonneg : 0 ≤ ord K α :=
      (mem_integerRing_iff K).1 hα
    have hαMaximal : IsInMaximalIdeal K α :=
      lt_of_le_of_ne hαNonneg (Ne.symm hne)
    have hsqMaximal : IsInMaximalIdeal K (α ^ 2) := by
      rw [pow_two]
      exact isInMaximalIdeal_mul_isIntegral K hαMaximal hαNonneg
    have hcrossTermMaximal :
        IsInMaximalIdeal K ((2 * c) * (α * β)) := by
      exact isInMaximalIdeal_mul_isIntegral K hcrossMaximal
        ((mem_integerRing_iff K).1
          ((IntegerRing K).mul_mem _ _ hα hβIntegral))
    have hdiagTermMaximal :
        IsInMaximalIdeal K ((c ^ 2 + (a : K)) * β ^ 2) := by
      exact isInMaximalIdeal_mul_isIntegral K hdiagMaximal
        ((mem_integerRing_iff K).1
          ((IntegerRing K).pow_mem hβIntegral 2))
    have hsumMaximal := isInMaximalIdeal_add K
      (isInMaximalIdeal_add K hsqMaximal hcrossTermMaximal)
      hdiagTermMaximal
    rw [heq] at hsumMaximal
    simpa [IsInMaximalIdeal] using hsumMaximal
  let X : K := (2 * c) * (α * β)
  let Y : K := (c ^ 2 + (a : K)) * β ^ 2
  have hXOrder : ord K X = (m : WithTop Int) := by
    dsimp [X]
    rw [ord_mul, hcrossOrder, ord_mul, hαUnit, hβ]
    simp
  have hYOrder : ord K Y = (n : WithTop Int) := by
    dsimp [Y]
    rw [ord_mul, hdiagOrder, ord_pow, hβ]
    simp
  have hXYOrder : ord K (X + Y) = (k : WithTop Int) := by
    rcases lt_or_gt_of_ne hmn with hlt | hgt
    · have horder : ord K (X + Y) = ord K X := by
        apply (ord K).map_add_eq_of_lt_left
        rw [hXOrder, hYOrder]
        exact_mod_cast hlt
      calc
        ord K (X + Y) = ord K X := horder
        _ = (m : WithTop Int) := hXOrder
        _ = (k : WithTop Int) := by
          have hmk : m = k := by
            calc
              m = min m n := (min_eq_left hlt.le).symm
              _ = k := hk
          exact_mod_cast hmk
    · have horder : ord K (X + Y) = ord K Y := by
        apply (ord K).map_add_eq_of_lt_right
        rw [hXOrder, hYOrder]
        exact_mod_cast hgt
      calc
        ord K (X + Y) = ord K Y := horder
        _ = (n : WithTop Int) := hYOrder
        _ = (k : WithTop Int) := by
          have hnk : n = k := by
            calc
              n = min m n := (min_eq_right hgt.le).symm
              _ = k := hk
          exact_mod_cast hnk
  have honeSub : 1 - α ^ 2 = X + Y := by
    dsimp [X, Y]
    rw [← heq]
    ring
  have honeSubOrder : ord K (1 - α ^ 2) =
      (k : WithTop Int) := by rw [honeSub, hXYOrder]
  have hkEven := even_order_one_sub_sq_of_lt_two_mul_e
    (K := K) α k honeSubOrder hkPos hkUpper
  rcases hkOdd with ⟨r, hr⟩
  rcases hkEven with ⟨s, hs⟩
  omega

/-- Admissibility of an even presentation gives Beli's integral absolute
defect inequality `R+d(-ε) ≥ 0` in the finite-defect branch. -/
theorem order_add_defect_nonneg_of_admissible_even
    [QuadraticDefectLaws K]
    (R : Int) (ε : Kˣ) (hε : IsValuationUnit K (ε : K))
    (ha : IsBinaryParameterAdmissible
      (uniformizerPowerUnit K R * ε))
    (hfinite : quadraticDefect K (-ε) ≠ ⊤)
    (hEvenR : Even R) :
    0 ≤ R + ((quadraticDefect K (-ε)).toNat : Int) := by
  let a : Kˣ := uniformizerPowerUnit K R * ε
  let d : Nat := (quadraticDefect K (-ε)).toNat
  have haOrder : ordUnit K a = R :=
    ordUnit_uniformizerPower_mul_valuationUnit ε hε R
  have hnegOrder : ordUnit K (-a) = R := by
    apply WithTop.coe_injective
    rw [coe_ordUnit]
    change ord K (-(a : K)) = (R : WithTop Int)
    rw [ord_neg, ← coe_ordUnit, haOrder]
  have hdefectEven : quadraticDefect K (-a) =
      quadraticDefect K (-ε) := by
    change beliParameterDefect K a = quadraticDefect K (-ε)
    exact beliParameterDefect_uniformizerPower_mul_valuationUnit_of_even
      (K := K) R ε hε hEvenR
  have habsolute : HasNonnegativeAbsoluteQuadraticDefect (-a) :=
    ((isBinaryParameterAdmissible_iff_order_add_two_e_and_defect
      a).1 ha).2
  have hthreshold :=
    (hasNonnegativeAbsoluteQuadraticDefect_iff_threshold_le
      (K := K) (-a)).1 habsolute
  rw [hdefectEven, ← ENat.coe_toNat hfinite] at hthreshold
  by_cases hRnonneg : 0 ≤ R
  · have hdNonneg : (0 : Int) ≤ (d : Int) := by positivity
    simpa [d] using add_nonneg hRnonneg hdNonneg
  · have hRneg : R < 0 := lt_of_not_ge hRnonneg
    have hthresholdCast :=
      coe_absoluteDefectThreshold_eq_neg_of_neg
        (K := K) (a := -a) (by simpa [hnegOrder] using hRneg)
    have hthresholdNat : absoluteDefectThreshold (-a) ≤ d := by
      exact_mod_cast hthreshold
    have hthresholdInt :
        (absoluteDefectThreshold (-a) : Int) ≤ (d : Int) := by
      exact_mod_cast hthresholdNat
    rw [hthresholdCast] at hthresholdInt
    simpa [d] using (show 0 ≤ R + (d : Int) by omega)

/-- The defect-adapted model used in obstruction (b), with its two
correction orders exposed to the common coordinate obstruction. -/
theorem not_hasEveryEqualNormGeneratorBasis_of_finite_adapted_orders
    [QuadraticDefectLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicSquareDifferenceLaws K]
    (R : Int) (ε : Kˣ) (hε : IsValuationUnit K (ε : K))
    (hfinite : quadraticDefect K (-ε) ≠ ⊤)
    (hEvenR : Even R)
    (hmPos : 0 < (ramificationIndex K : Int) + R / 2)
    (hnPos : 0 < R + ((quadraticDefect K (-ε)).toNat : Int))
    (hmn : (ramificationIndex K : Int) + R / 2 ≠
      R + ((quadraticDefect K (-ε)).toNat : Int))
    (k : Int)
    (hk : min ((ramificationIndex K : Int) + R / 2)
      (R + ((quadraticDefect K (-ε)).toNat : Int)) = k)
    (hkPos : 0 < k)
    (hkUpper : k < 2 * (ramificationIndex K : Int))
    (hkOdd : Odd k) :
    ¬HasEveryEqualNormGeneratorBasis
      (uniformizerPowerUnit K R * ε) := by
  let q : Kˣ := -ε
  let d : Nat := (quadraticDefect K q).toNat
  have hfiniteQ : quadraticDefect K q ≠ ⊤ := by
    simpa [q] using hfinite
  have hqUnit : IsValuationUnit K (q : K) := by
    change ord K (-((ε : K))) = 0
    change ord K (ε : K) = 0 at hε
    simpa only [ord_neg] using hε
  have hdPos : 0 < d :=
    quadraticDefect_toNat_pos_of_unit_of_ne_top q hqUnit hfiniteQ
  rcases exists_quadraticApproximation_exact_order q hfiniteQ with
    ⟨x, hxError⟩
  let err : K := 1 - x ^ 2 / (q : K)
  have herrOrder : ord K err = ((d : Int) : WithTop Int) := by
    simpa [err, d] using hxError
  have herrPos : 0 < ord K err := by
    rw [herrOrder]
    exact_mod_cast hdPos
  have hquotOrder : ord K (x ^ 2 / (q : K)) = 0 := by
    have hlt : ord K (1 : K) < ord K err := by
      simpa only [ord_one] using herrPos
    have hsub := (ord K).map_sub_eq_of_lt_left hlt
    have heq : 1 - err = x ^ 2 / (q : K) := by
      dsimp [err]
      ring
    rw [heq] at hsub
    simpa using hsub
  have hxNe : x ≠ 0 := by
    intro hzero
    rw [hzero] at hquotOrder
    simp at hquotOrder
  let xu : Kˣ := Units.mk0 x hxNe
  have hqOrder : ordUnit K q = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K q).1 hqUnit
  have hquotUnitOrder : ordUnit K (xu ^ 2 * q⁻¹) = 0 := by
    apply (isValuationUnit_iff_ordUnit_eq_zero K (xu ^ 2 * q⁻¹)).1
    rw [IsValuationUnit]
    have hval : ((xu ^ 2 * q⁻¹ : Kˣ) : K) =
        x ^ 2 / (q : K) := by
      simp [xu, div_eq_mul_inv]
    rw [hval]
    exact hquotOrder
  have hxuOrder : ordUnit K xu = 0 := by
    rw [ordUnit_mul, ordUnit_pow, ordUnit_inv, hqOrder]
      at hquotUnitOrder
    omega
  have hxUnit : IsValuationUnit K x := by
    simpa [xu] using
      (isValuationUnit_iff_ordUnit_eq_zero K xu).2 hxuOrder
  have hbaseEq : x ^ 2 + (ε : K) = (ε : K) * err := by
    dsimp [err, q]
    field_simp [Units.ne_zero ε]
    ring
  have hbaseOrder : ord K (x ^ 2 + (ε : K)) =
      ((d : Int) : WithTop Int) := by
    rw [hbaseEq, ord_mul, hε, herrOrder]
    simp
  have hRDouble : R = 2 * (R / 2) := by
    rcases hEvenR with ⟨r, hr⟩
    omega
  let p : Kˣ := uniformizerPowerUnit K (R / 2)
  have hpSq : p ^ 2 = uniformizerPowerUnit K R := by
    dsimp [p]
    unfold uniformizerPowerUnit
    rw [pow_two, ← zpow_add]
    congr 1
    omega
  let a : Kˣ := uniformizerPowerUnit K R * ε
  let c : K := (p : K) * x
  let D : K := c ^ 2 + (a : K)
  have hDEq : D = (uniformizerPowerUnit K R : K) *
      (x ^ 2 + (ε : K)) := by
    have hpSqVal : (p : K) ^ 2 =
        (uniformizerPowerUnit K R : K) := by
      simpa using congrArg Units.val hpSq
    have haVal : (a : K) =
        (uniformizerPowerUnit K R : K) * (ε : K) := rfl
    dsimp only [D, c]
    rw [mul_pow, hpSqVal, haVal]
    ring
  have hDOrder : ord K D =
      ((R + (d : Int) : Int) : WithTop Int) := by
    rw [hDEq, ord_mul, ← coe_ordUnit,
      ordUnit_uniformizerPowerUnit, hbaseOrder]
    norm_cast
  have hcOrder : ord K c = ((R / 2 : Int) : WithTop Int) := by
    dsimp [c]
    rw [ord_mul, ← coe_ordUnit,
      ordUnit_uniformizerPowerUnit, hxUnit]
    simp
  have htwoCOrder : ord K ((2 : K) * c) =
      (((ramificationIndex K : Int) + R / 2 : Int) : WithTop Int) := by
    rw [ord_mul, ← ramificationIndex_spec, hcOrder]
    norm_cast
  have htwoCIntegral : (2 : K) * c ∈ IntegerRing K := by
    apply (mem_integerRing_iff K).2
    rw [Dyadic.IsIntegral, htwoCOrder]
    exact_mod_cast hmPos.le
  have hDIntegral : D ∈ IntegerRing K := by
    apply (mem_integerRing_iff K).2
    rw [Dyadic.IsIntegral, hDOrder]
    have hnPos' : 0 < R + (d : Int) := by
      simpa [d, q] using hnPos
    exact_mod_cast hnPos'.le
  apply not_hasEveryEqualNormGeneratorBasis_of_distinct_correction_orders
    a c ((ramificationIndex K : Int) + R / 2)
      (R + (d : Int)) k htwoCIntegral
  · simpa [D, a] using hDIntegral
  · exact htwoCOrder
  · simpa [D, a] using hDOrder
  · exact hmPos
  · simpa [d, q] using hnPos
  · simpa [d, q] using hmn
  · simpa [d, q] using hk
  · exact hkPos
  · exact hkUpper
  · exact hkOdd

/-- In the finite-defect branch below Beli's equality boundary, the second
diagonal correction is the smaller one.  Its order is positive and odd, so
the universal equal-norm assertion fails. -/
theorem not_hasEveryEqualNormGeneratorBasis_of_even_order_lt_defect_boundary
    [QuadraticDefectLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicSquareDifferenceLaws K]
    (R : Int) (ε : Kˣ) (hε : IsValuationUnit K (ε : K))
    (ha : IsBinaryParameterAdmissible
      (uniformizerPowerUnit K R * ε))
    (hfinite : quadraticDefect K (-ε) ≠ ⊤)
    (hEvenR : Even R)
    (hbelow : R < 2 * (ramificationIndex K : Int) -
      2 * ((quadraticDefect K (-ε)).toNat : Int)) :
    ¬HasEveryEqualNormGeneratorBasis
      (uniformizerPowerUnit K R * ε) := by
  let q : Kˣ := -ε
  let d : Nat := (quadraticDefect K q).toNat
  have hfiniteQ : quadraticDefect K q ≠ ⊤ := by
    simpa [q] using hfinite
  have hqUnit : IsValuationUnit K (q : K) := by
    change ord K (-((ε : K))) = 0
    change ord K (ε : K) = 0 at hε
    simpa only [ord_neg] using hε
  have hdPos : 0 < d :=
    quadraticDefect_toNat_pos_of_unit_of_ne_top q hqUnit hfiniteQ
  have hnonsquare : ¬IsSquare q := by
    intro hsquare
    exact hfiniteQ
      ((quadraticDefect_eq_top_iff_isSquare (K := K) q).2 hsquare)
  have hdBound := quadraticDefect_le_two_mul_e_of_not_isSquare
    (K := K) hnonsquare
  have hdLe : d ≤ 2 * ramificationIndex K := by
    rw [← ENat.coe_toNat hfiniteQ] at hdBound
    simpa [d] using ENat.coe_le_coe.mp hdBound
  have hnonneg : 0 ≤ R + (d : Int) := by
    simpa [d, q] using
      order_add_defect_nonneg_of_admissible_even R ε hε ha hfinite hEvenR
  have hRDouble : R = 2 * (R / 2) := by
    rcases hEvenR with ⟨r, hr⟩
    omega
  have hbelow' : R < 2 * (ramificationIndex K : Int) -
      2 * (d : Int) := by
    simpa [d, q] using hbelow
  have hdLtInt : (d : Int) <
      2 * (ramificationIndex K : Int) := by
    omega
  have hdLtNat : d < 2 * ramificationIndex K := by
    exact_mod_cast hdLtInt
  have hdLt : quadraticDefect K q <
      ((2 * ramificationIndex K : Nat) : ℕ∞) := by
    rw [← ENat.coe_toNat hfiniteQ]
    exact_mod_cast hdLtNat
  have hdOddNat : Odd d :=
    quadraticDefect_toNat_odd_of_unit_of_lt_two_mul_e
      (K := K) q hqUnit hdLt
  rcases hdOddNat with ⟨s, hs⟩
  have hnPos : 0 < R + (d : Int) := by
    by_contra hnot
    have hzero : R + (d : Int) = 0 := by omega
    rcases hEvenR with ⟨r, hr⟩
    omega
  have hmnLt : R + (d : Int) <
      (ramificationIndex K : Int) + R / 2 := by
    omega
  have hmPos : 0 < (ramificationIndex K : Int) + R / 2 := by
    omega
  have hmUpper : (ramificationIndex K : Int) + R / 2 <
      2 * (ramificationIndex K : Int) := by
    have hePos : (0 : Int) < ramificationIndex K := by
      exact_mod_cast ramificationIndex_pos K
    omega
  have hnUpper : R + (d : Int) <
      2 * (ramificationIndex K : Int) := lt_trans hmnLt hmUpper
  have hnOdd : Odd (R + (d : Int)) := by
    rcases hEvenR with ⟨r, hr⟩
    have hsInt : (d : Int) = 2 * (s : Int) + 1 := by
      exact_mod_cast hs
    refine ⟨r + (s : Int), ?_⟩
    omega
  apply not_hasEveryEqualNormGeneratorBasis_of_finite_adapted_orders
    R ε hε hfinite hEvenR hmPos hnPos
      (ne_of_gt hmnLt) (R + (d : Int))
  · rw [min_eq_right hmnLt.le]
  · simpa [d, q] using hnPos
  · simpa [d, q] using hnUpper
  · simpa [d, q] using hnOdd

/-- In the finite high-defect branch, odd `R/2+e` makes the mixed
correction the smaller positive order below `2e`; this is obstruction (b)
in the other direction from the equality boundary. -/
theorem not_hasEveryEqualNormGeneratorBasis_of_even_high_odd
    [QuadraticDefectLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicSquareDifferenceLaws K]
    (R : Int) (ε : Kˣ) (hε : IsValuationUnit K (ε : K))
    (hfinite : quadraticDefect K (-ε) ≠ ⊤)
    (hlower : 2 * (ramificationIndex K : Int) -
      2 * ((quadraticDefect K (-ε)).toNat : Int) < R)
    (hupper : R < 2 * (ramificationIndex K : Int))
    (hEvenR : Even R)
    (hOddHigh : Odd (R / 2 + (ramificationIndex K : Int))) :
    ¬HasEveryEqualNormGeneratorBasis
      (uniformizerPowerUnit K R * ε) := by
  let q : Kˣ := -ε
  let d : Nat := (quadraticDefect K q).toNat
  have hfiniteQ : quadraticDefect K q ≠ ⊤ := by
    simpa [q] using hfinite
  have hnonsquare : ¬IsSquare q := by
    intro hsquare
    exact hfiniteQ
      ((quadraticDefect_eq_top_iff_isSquare (K := K) q).2 hsquare)
  have hdBound := quadraticDefect_le_two_mul_e_of_not_isSquare
    (K := K) hnonsquare
  have hdLe : d ≤ 2 * ramificationIndex K := by
    rw [← ENat.coe_toNat hfiniteQ] at hdBound
    simpa [d] using ENat.coe_le_coe.mp hdBound
  have hdLeInt : (d : Int) ≤
      2 * (ramificationIndex K : Int) := by
    exact_mod_cast hdLe
  have hRDouble : R = 2 * (R / 2) := by
    rcases hEvenR with ⟨r, hr⟩
    omega
  have hlower' : 2 * (ramificationIndex K : Int) -
      2 * (d : Int) < R := by
    simpa [d, q] using hlower
  have hmPos : 0 < (ramificationIndex K : Int) + R / 2 := by
    omega
  have hmnLt : (ramificationIndex K : Int) + R / 2 <
      R + (d : Int) := by
    omega
  have hnPos : 0 < R + (d : Int) := lt_trans hmPos hmnLt
  have hmUpper : (ramificationIndex K : Int) + R / 2 <
      2 * (ramificationIndex K : Int) := by
    omega
  apply not_hasEveryEqualNormGeneratorBasis_of_finite_adapted_orders
    R ε hε hfinite hEvenR hmPos
      (by simpa [d, q] using hnPos) (ne_of_lt hmnLt)
      ((ramificationIndex K : Int) + R / 2)
  · rw [min_eq_left hmnLt.le]
  · exact hmPos
  · exact hmUpper
  · simpa [add_comm] using hOddHigh

/-- Zero second diagonal is the limiting form of the coordinate obstruction:
the mixed correction itself is `1-α²`, whose positive order below `2e`
cannot be odd. -/
theorem not_hasEveryEqualNormGeneratorBasis_of_zero_diagonal_odd_order
    [DyadicSquareDifferenceLaws K]
    (a : Kˣ) (c : K) (m : Int)
    (htwo : (2 : K) * c ∈ IntegerRing K)
    (hdiagZero : c ^ 2 + (a : K) = 0)
    (hcrossOrder : ord K ((2 : K) * c) = (m : WithTop Int))
    (hmPos : 0 < m)
    (hmUpper : m < 2 * (ramificationIndex K : Int))
    (hmOdd : Odd m) :
    ¬HasEveryEqualNormGeneratorBasis a := by
  intro hall
  have hdiag : c ^ 2 + (a : K) ∈ IntegerRing K := by
    rw [hdiagZero]
    exact (IntegerRing K).zero_mem
  rcases hall c htwo hdiag with ⟨α, β, hα, hβ, heq⟩
  have hβIntegral : β ∈ IntegerRing K := by
    apply (mem_integerRing_iff K).2
    rw [Dyadic.IsIntegral, hβ]
  have hcrossMaximal : IsInMaximalIdeal K ((2 : K) * c) := by
    rw [IsInMaximalIdeal, hcrossOrder]
    exact_mod_cast hmPos
  have hαUnit : IsValuationUnit K α := by
    rw [IsValuationUnit]
    by_contra hne
    have hαNonneg : 0 ≤ ord K α :=
      (mem_integerRing_iff K).1 hα
    have hαMaximal : IsInMaximalIdeal K α :=
      lt_of_le_of_ne hαNonneg (Ne.symm hne)
    have hsqMaximal : IsInMaximalIdeal K (α ^ 2) := by
      rw [pow_two]
      exact isInMaximalIdeal_mul_isIntegral K hαMaximal hαNonneg
    have hcrossTermMaximal :
        IsInMaximalIdeal K ((2 * c) * (α * β)) := by
      exact isInMaximalIdeal_mul_isIntegral K hcrossMaximal
        ((mem_integerRing_iff K).1
          ((IntegerRing K).mul_mem _ _ hα hβIntegral))
    have hsumMaximal :=
      isInMaximalIdeal_add K hsqMaximal hcrossTermMaximal
    rw [hdiagZero, zero_mul, add_zero] at heq
    rw [heq] at hsumMaximal
    simpa [IsInMaximalIdeal] using hsumMaximal
  let X : K := (2 * c) * (α * β)
  have hXOrder : ord K X = (m : WithTop Int) := by
    dsimp [X]
    rw [ord_mul, hcrossOrder, ord_mul, hαUnit, hβ]
    simp
  have honeSub : 1 - α ^ 2 = X := by
    dsimp [X]
    rw [hdiagZero, zero_mul, add_zero] at heq
    rw [← heq]
    ring
  have honeSubOrder : ord K (1 - α ^ 2) =
      (m : WithTop Int) := by rw [honeSub, hXOrder]
  have hmEven := even_order_one_sub_sq_of_lt_two_mul_e
    (K := K) α m honeSubOrder hmPos hmUpper
  rcases hmOdd with ⟨r, hr⟩
  rcases hmEven with ⟨s, hs⟩
  omega

/-- In the infinite-defect branch, odd `R/2+e` is excluded by the
zero-diagonal coordinate obstruction.  Admissibility and exclusion of the
exceptional `-1/4` class provide the strict lower endpoint. -/
theorem not_hasEveryEqualNormGeneratorBasis_of_caseIII_top_odd
    [QuadraticDefectLaws K]
    [DyadicSquareDifferenceLaws K]
    (R : Int) (ε : Kˣ) (hε : IsValuationUnit K (ε : K))
    (ha : IsBinaryParameterAdmissible
      (uniformizerPowerUnit K R * ε))
    (hdefect : quadraticDefect K (-ε) = ⊤)
    (hupper : R < 2 * (ramificationIndex K : Int))
    (hEvenR : Even R)
    (hOddHigh : Odd (R / 2 + (ramificationIndex K : Int)))
    (hquarter : unitSquareClass K (uniformizerPowerUnit K R * ε) ≠
      unitSquareClass K (negativeQuarterUnit K)) :
    ¬HasEveryEqualNormGeneratorBasis
      (uniformizerPowerUnit K R * ε) := by
  have hsquare : IsSquare (-ε) :=
    (quadraticDefect_eq_top_iff_isSquare (K := K) (-ε)).1 hdefect
  have haOrder : ordUnit K (uniformizerPowerUnit K R * ε) = R :=
    ordUnit_uniformizerPower_mul_valuationUnit ε hε R
  have hRge : -(2 * (ramificationIndex K : Int)) ≤ R := by
    rw [← haOrder]
    exact ha.ordUnit_ge_neg_two_mul_e
  have hRne : R ≠ -(2 * (ramificationIndex K : Int)) := by
    intro hR
    exact hquarter
      (unitSquareClass_uniformizerPower_mul_eq_negativeQuarter
        R ε hε hR hsquare)
  have hRlower : -(2 * (ramificationIndex K : Int)) < R := by
    omega
  rcases hsquare with ⟨s, hs⟩
  have hnegUnit : IsValuationUnit K ((-ε : Kˣ) : K) := by
    change ord K (-((ε : K))) = 0
    change ord K (ε : K) = 0 at hε
    simpa only [ord_neg] using hε
  have hsOrder : ordUnit K s = 0 := by
    have hnegOrder : ordUnit K (-ε) = 0 :=
      (isValuationUnit_iff_ordUnit_eq_zero K (-ε)).1 hnegUnit
    rw [hs, ordUnit_mul] at hnegOrder
    omega
  have hsUnit : IsValuationUnit K (s : K) :=
    (isValuationUnit_iff_ordUnit_eq_zero K s).2 hsOrder
  have hRDouble : R = 2 * (R / 2) := by
    rcases hEvenR with ⟨r, hr⟩
    omega
  let p : Kˣ := uniformizerPowerUnit K (R / 2)
  have hpSq : p ^ 2 = uniformizerPowerUnit K R := by
    dsimp [p]
    unfold uniformizerPowerUnit
    rw [pow_two, ← zpow_add]
    congr 1
    omega
  let a : Kˣ := uniformizerPowerUnit K R * ε
  let c : K := (p : K) * (s : K)
  have hdiagZero : c ^ 2 + (a : K) = 0 := by
    have hpSqVal : (p : K) ^ 2 =
        (uniformizerPowerUnit K R : K) := by
      simpa using congrArg Units.val hpSq
    have hsVal : -(ε : K) = (s : K) ^ 2 := by
      simpa [pow_two] using congrArg Units.val hs
    dsimp [c, a]
    rw [mul_pow, hpSqVal]
    change (uniformizerPowerUnit K R : K) * (s : K) ^ 2 +
      (uniformizerPowerUnit K R : K) * (ε : K) = 0
    rw [← hsVal]
    ring
  have hcOrder : ord K c = ((R / 2 : Int) : WithTop Int) := by
    dsimp [c]
    rw [ord_mul, ← coe_ordUnit,
      ordUnit_uniformizerPowerUnit, hsUnit]
    simp
  have hcrossOrder : ord K ((2 : K) * c) =
      (((ramificationIndex K : Int) + R / 2 : Int) : WithTop Int) := by
    rw [ord_mul, ← ramificationIndex_spec, hcOrder]
    norm_cast
  have hmPos : 0 < (ramificationIndex K : Int) + R / 2 := by
    omega
  have hmUpper : (ramificationIndex K : Int) + R / 2 <
      2 * (ramificationIndex K : Int) := by
    omega
  have htwo : (2 : K) * c ∈ IntegerRing K := by
    apply (mem_integerRing_iff K).2
    rw [Dyadic.IsIntegral, hcrossOrder]
    exact_mod_cast hmPos.le
  apply not_hasEveryEqualNormGeneratorBasis_of_zero_diagonal_odd_order
    a c ((ramificationIndex K : Int) + R / 2) htwo hdiagZero
      hcrossOrder hmPos hmUpper
  simpa [add_comm] using hOddHigh

/-- An admissible binary parameter of odd order cannot have negative order:
if the order were negative, integrality of `c²+a` would force equality of
the two negative summand orders, making the parameter order even. -/
theorem order_nonneg_of_admissible_of_odd
    (a : Kˣ) (R : Int)
    (horder : ordUnit K a = R)
    (ha : IsBinaryParameterAdmissible a)
    (hodd : Odd R) :
    0 ≤ R := by
  by_contra hnot
  have hRneg : R < 0 := lt_of_not_ge hnot
  rcases ha with ⟨c, _htwo, hdiag⟩
  have hcNe : c ≠ 0 := by
    intro hc
    subst c
    have haMem : (a : K) ∈ IntegerRing K := by
      simpa using hdiag
    have haNonneg := Lattice.ordUnit_nonneg_of_mem_integerRing a haMem
    rw [horder] at haNonneg
    omega
  let cu : Kˣ := Units.mk0 c hcNe
  have hcOrder : ord K c =
      ((ordUnit K cu : Int) : WithTop Int) := by
    exact (coe_ordUnit K cu).symm
  have haOrderNeg : ord K (a : K) < 0 := by
    rw [← coe_ordUnit, horder]
    exact_mod_cast hRneg
  have hdiagOrder : 0 ≤ ord K (c ^ 2 + (a : K)) :=
    (mem_integerRing_iff K).1 hdiag
  have heqOrder : ord K (c ^ 2) = ord K (a : K) := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hsum := (ord K).map_add_eq_of_lt_left hlt
      rw [hsum] at hdiagOrder
      exact (not_lt_of_ge hdiagOrder) (hlt.trans haOrderNeg)
    · have hsum := (ord K).map_add_eq_of_lt_right hgt
      rw [hsum] at hdiagOrder
      exact (not_lt_of_ge hdiagOrder) haOrderNeg
  have hREven : R = 2 * ordUnit K cu := by
    rw [← horder]
    apply WithTop.coe_injective
    rw [coe_ordUnit, ← heqOrder, ord_pow, hcOrder]
    norm_cast
  rcases hodd with ⟨r, hr⟩
  omega

/-- Necessity in Beli (2003), Lemma 3.17: assertion (2), together with the
global admissibility hypothesis `a ∈ A`, forces one of the four parameter
alternatives in assertion (3). -/
theorem beliLemma317ParameterCases_of_hasEvery
    [QuadraticDefectLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicSquareDifferenceLaws K]
    (R : Int) (ε : Kˣ) (hε : IsValuationUnit K (ε : K))
    (ha : IsBinaryParameterAdmissible
      (uniformizerPowerUnit K R * ε))
    (hall : HasEveryEqualNormGeneratorBasis
      (uniformizerPowerUnit K R * ε)) :
    BeliLemma317ParameterCases (K := K) R ε := by
  simp only [BeliLemma317ParameterCases]
  by_cases hcaseI :
      2 * (ramificationIndex K : Int) < R
  · exact Or.inl hcaseI
  · apply Or.inr
    have hRle : R ≤ 2 * (ramificationIndex K : Int) :=
      le_of_not_gt hcaseI
    by_cases hEvenR : Even R
    · have hRDouble : R = 2 * (R / 2) := by
        rcases hEvenR with ⟨r, hr⟩
        omega
      by_cases hREnd : R = 2 * (ramificationIndex K : Int)
      · apply Or.inr
        apply Or.inr
        refine ⟨Or.inl hREnd, ?_⟩
        apply hasResidueFieldMoreThanTwoElements_of_order_eq_two_e_hasEvery
          ε hε
        simpa [hREnd] using hall
      · have hRlt : R < 2 * (ramificationIndex K : Int) := by
          omega
        by_cases hquarterEq :
            unitSquareClass K (uniformizerPowerUnit K R * ε) =
              unitSquareClass K (negativeQuarterUnit K)
        · apply Or.inr
          apply Or.inr
          refine ⟨Or.inr hquarterEq, ?_⟩
          exact
            hasResidueFieldMoreThanTwoElements_of_negativeQuarterClass
              (uniformizerPowerUnit K R * ε) ha hquarterEq hall
        · by_cases htop : quadraticDefect K (-ε) = ⊤
          · rcases Int.even_or_odd
                (R / 2 + (ramificationIndex K : Int)) with
              hEvenHigh | hOddHigh
            · apply Or.inr
              apply Or.inl
              exact ⟨Or.inl htop, hRlt, hEvenR,
                hEvenHigh, hquarterEq⟩
            · exfalso
              exact
                (not_hasEveryEqualNormGeneratorBasis_of_caseIII_top_odd
                  R ε hε ha htop hRlt hEvenR hOddHigh hquarterEq) hall
          · let d : Nat := (quadraticDefect K (-ε)).toNat
            by_cases hboundary : R =
                2 * (ramificationIndex K : Int) - 2 * (d : Int)
            · apply Or.inl
              exact ⟨htop, by simpa [d] using hboundary⟩
            · by_cases hbelow : R <
                  2 * (ramificationIndex K : Int) - 2 * (d : Int)
              · exfalso
                apply
                  (not_hasEveryEqualNormGeneratorBasis_of_even_order_lt_defect_boundary
                    R ε hε ha htop hEvenR)
                · simpa [d] using hbelow
                · exact hall
              · have habove :
                    2 * (ramificationIndex K : Int) - 2 * (d : Int) < R := by
                  omega
                rcases Int.even_or_odd
                    (R / 2 + (ramificationIndex K : Int)) with
                  hEvenHigh | hOddHigh
                · apply Or.inr
                  apply Or.inl
                  refine ⟨Or.inr ⟨htop, ?_⟩, hRlt, hEvenR,
                    hEvenHigh, hquarterEq⟩
                  simpa [d] using habove
                · exfalso
                  exact
                    (not_hasEveryEqualNormGeneratorBasis_of_even_high_odd
                      R ε hε htop (by simpa [d] using habove)
                        hRlt hEvenR hOddHigh) hall
    · have hOddR : Odd R :=
        (Int.even_or_odd R).resolve_left hEvenR
      have haOrder :
          ordUnit K (uniformizerPowerUnit K R * ε) = R :=
        ordUnit_uniformizerPower_mul_valuationUnit ε hε R
      have hRnonneg : 0 ≤ R :=
        order_nonneg_of_admissible_of_odd
          (uniformizerPowerUnit K R * ε) R haOrder ha hOddR
      have hRpos : 0 < R := by
        rcases hOddR with ⟨r, hr⟩
        omega
      have hRlt : R < 2 * (ramificationIndex K : Int) := by
        rcases hOddR with ⟨r, hr⟩
        omega
      exfalso
      exact
        (not_hasEveryEqualNormGeneratorBasis_of_odd_order
          R ε hε hRpos hRlt hOddR) hall

/-- Assertions (2) and (3) of Beli (2003), Lemma 3.17, are equivalent. -/
theorem hasEveryEqualNormGeneratorBasis_iff_parameterCases
    [QuadraticDefectLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicSquareDifferenceLaws K]
    [PerfectResidueFieldLaws K]
    [PrincipalUnitSquareClassFiltrationLaws K]
    [BinaryNormGeneratorLocalLaws.{u, u} K]
    (R : Int) (ε : Kˣ) (hε : IsValuationUnit K (ε : K))
    (ha : IsBinaryParameterAdmissible
      (uniformizerPowerUnit K R * ε)) :
    HasEveryEqualNormGeneratorBasis
        (uniformizerPowerUnit K R * ε) ↔
      BeliLemma317ParameterCases (K := K) R ε := by
  constructor
  · exact beliLemma317ParameterCases_of_hasEvery R ε hε ha
  · exact hasEveryEqualNormGeneratorBasis_of_parameterCases R ε hε ha

/-- Assertions (1) and (3) of Beli (2003), Lemma 3.17, are equivalent. -/
theorem hasSomeEqualNormGeneratorBasis_iff_parameterCases
    [QuadraticDefectLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicSquareDifferenceLaws K]
    [PerfectResidueFieldLaws K]
    [PrincipalUnitSquareClassFiltrationLaws K]
    [BinaryNormGeneratorLocalLaws.{u, u} K]
    (R : Int) (ε : Kˣ) (hε : IsValuationUnit K (ε : K))
    (ha : IsBinaryParameterAdmissible
      (uniformizerPowerUnit K R * ε)) :
    HasSomeEqualNormGeneratorBasis
        (uniformizerPowerUnit K R * ε) ↔
      BeliLemma317ParameterCases (K := K) R ε := by
  rw [hasSomeEqualNormGeneratorBasis_iff_hasEvery
    (uniformizerPowerUnit K R * ε) ha]
  exact hasEveryEqualNormGeneratorBasis_iff_parameterCases R ε hε ha

/-- Beli (2003), Lemma 3.17 in full: assertions (1), (2), and (3) are
pairwise equivalent for every admissible presentation `a=πʳε`. -/
theorem beliLemma317
    [QuadraticDefectLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicSquareDifferenceLaws K]
    [PerfectResidueFieldLaws K]
    [PrincipalUnitSquareClassFiltrationLaws K]
    [BinaryNormGeneratorLocalLaws.{u, u} K]
    (R : Int) (ε : Kˣ) (hε : IsValuationUnit K (ε : K))
    (ha : IsBinaryParameterAdmissible
      (uniformizerPowerUnit K R * ε)) :
    (HasSomeEqualNormGeneratorBasis
        (uniformizerPowerUnit K R * ε) ↔
      HasEveryEqualNormGeneratorBasis
        (uniformizerPowerUnit K R * ε)) ∧
    (HasEveryEqualNormGeneratorBasis
        (uniformizerPowerUnit K R * ε) ↔
      BeliLemma317ParameterCases (K := K) R ε) := by
  exact ⟨hasSomeEqualNormGeneratorBasis_iff_hasEvery
      (uniformizerPowerUnit K R * ε) ha,
    hasEveryEqualNormGeneratorBasis_iff_parameterCases R ε hε ha⟩

end BONG

end Bong
