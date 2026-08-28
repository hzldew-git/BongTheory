/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinaryValueSet
import Bong.Bong.BinaryInvariant
import Bong.Dyadic.BeliGroups

/-!
# Binary norm-generator value-ratio classes

This file states Beli (2003), Lemma 3.11 in the exact quotient group used by
the paper.  The elementary conversion from norm generators to valuation-unit
ratios is proved.  The reverse value-set calculation, whose last branch uses a
Hensel/Newton-polygon argument, is isolated in `BinaryNormGeneratorLocalLaws`.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

namespace BONG

/-- Every norm generator of a binary lattice is anisotropic. -/
theorem isAnisotropic_of_isNormGenerator_binary
    (b : BONG V q L (n + 1)) {y : V}
    (hy : Lattice.IsNormGenerator q L y) :
    q.IsAnisotropic y := by
  letI := b.basis.finiteDimensional_of_finite
  apply hy.isAnisotropic_of_finrank_pos
  rw [← b.length_eq_finrank]
  omega

/-- The nonzero value ratio `Q(y) / Q(x₁)` for a norm generator `y`. -/
noncomputable def normGeneratorValueRatioUnit
    (b : BONG V q L (n + 1)) (y : V)
    (hy : Lattice.IsNormGenerator q L y) : Kˣ :=
  Units.mk0 (q.quadratic y)
      (b.isAnisotropic_of_isNormGenerator_binary hy) /
    b.valueUnit 0

/-- A norm-generator value ratio is a valuation unit. -/
theorem normGeneratorValueRatioUnit_isValuationUnit
    (b : BONG V q L (n + 1)) (y : V)
    (hy : Lattice.IsNormGenerator q L y) :
    IsValuationUnit K (b.normGeneratorValueRatioUnit y hy : K) := by
  apply (Lattice.principalIdeal_eq_iff_isValuationUnit_div
    (Units.mk0 (q.quadratic y)
      (b.isAnisotropic_of_isNormGenerator_binary hy))
    (b.valueUnit 0)).1
  change Lattice.principalIdeal (K := K) (q.quadratic y) =
    Lattice.principalIdeal (K := K) (b.value 0)
  calc
    _ = Lattice.normIdeal q L := hy.normIdeal_eq.symm
    _ = Lattice.principalIdeal (K := K) (q.quadratic b.head) :=
      b.head_isNormGenerator.normIdeal_eq
    _ = Lattice.principalIdeal (K := K) (b.value 0) := by
      rw [b.value_zero_eq_quadratic_head]

/-- The value ratio, bundled as an element of the valuation-unit subgroup. -/
noncomputable def normGeneratorValueRatioValuationUnit
    (b : BONG V q L (n + 1)) (y : V)
    (hy : Lattice.IsNormGenerator q L y) :
    valuationUnitSubgroup K :=
  ⟨b.normGeneratorValueRatioUnit y hy,
    b.normGeneratorValueRatioUnit_isValuationUnit y hy⟩

/-- The class of a norm-generator value ratio in `𝓞ˣ / 𝓞ˣ²`. -/
noncomputable def normGeneratorValueRatioClass
    (b : BONG V q L (n + 1)) (y : V)
    (hy : Lattice.IsNormGenerator q L y) :
    ValuationUnitClass K :=
  valuationUnitClassHom K
    (b.normGeneratorValueRatioValuationUnit y hy)

/-- The set of all norm-generator value-ratio classes based at the BONG head. -/
noncomputable def normGeneratorValueRatioClassSet
    (b : BONG V q L (n + 1)) : Set (ValuationUnitClass K) :=
  {c | ∃ (y : V) (hy : Lattice.IsNormGenerator q L y),
    b.normGeneratorValueRatioClass y hy = c}

@[simp]
theorem mem_normGeneratorValueRatioClassSet_iff
    (b : BONG V q L (n + 1)) (c : ValuationUnitClass K) :
    c ∈ b.normGeneratorValueRatioClassSet ↔
      ∃ (y : V) (hy : Lattice.IsNormGenerator q L y),
        b.normGeneratorValueRatioClass y hy = c :=
  Iff.rfl

end BONG

/-- The local binary value theorem used in Beli (2003), Lemma 3.11.  Its
high-defect reverse inclusion is the Hensel/Newton-polygon step in the paper. -/
class BinaryNormGeneratorLocalLaws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  valueRatioClassSet_eq
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    (b : BONG V q L 2) :
    b.normGeneratorValueRatioClassSet =
      (beliNormGeneratorGroup K b.binaryParameter :
        Set (ValuationUnitClass K))

variable [BinaryNormGeneratorLocalLaws.{u, v} K]

namespace BONG

/-- Beli (2003), Lemma 3.11. -/
theorem normGeneratorValueRatioClassSet_eq_beliNormGeneratorGroup
    (b : BONG V q L 2) :
    b.normGeneratorValueRatioClassSet =
      (beliNormGeneratorGroup K b.binaryParameter :
        Set (ValuationUnitClass K)) :=
  BinaryNormGeneratorLocalLaws.valueRatioClassSet_eq b

/-- Quotient-class form of Beli 2003, paragraph 3.12. -/
theorem exists_normGenerator_of_mem_beliNormGeneratorGroup
    (b : BONG V q L 2) {c : ValuationUnitClass K}
    (hc : c ∈ beliNormGeneratorGroup K b.binaryParameter) :
    ∃ (y : V) (hy : Lattice.IsNormGenerator q L y),
      b.normGeneratorValueRatioClass y hy = c := by
  have hcSet : c ∈
      (beliNormGeneratorGroup K b.binaryParameter :
        Set (ValuationUnitClass K)) := hc
  rw [← b.normGeneratorValueRatioClassSet_eq_beliNormGeneratorGroup]
    at hcSet
  exact hcSet

omit [BinaryNormGeneratorLocalLaws K] in
/-- Scaling a norm generator by a valuation unit squares its value ratio. -/
theorem normGeneratorValueRatioUnit_smul
    (b : BONG V q L 2) (y : V)
    (hy : Lattice.IsNormGenerator q L y)
    (u : Kˣ) (hu : IsValuationUnit K (u : K)) :
    b.normGeneratorValueRatioUnit ((u : K) • y)
        (hy.smul_valuationUnit u hu) =
      u ^ 2 * b.normGeneratorValueRatioUnit y hy := by
  apply Units.ext
  simp only [normGeneratorValueRatioUnit, Units.val_div_eq_div_val,
    Units.val_mk0, Units.val_mul, Units.val_pow_eq_pow_val,
    coe_valueUnit]
  rw [q.quadratic_smul]
  field_simp [b.value_ne_zero 0]

/-- Exact representative form of paragraph 3.12: every unit class in `g(a)`
is realized by a norm generator after absorbing the quotient ambiguity into a
valuation-unit square. -/
theorem exists_normGeneratorValueRatioUnit_eq_of_mem_beliNormGeneratorGroup
    (b : BONG V q L 2) (u : valuationUnitSubgroup K)
    (hu : valuationUnitClassHom K u ∈
      beliNormGeneratorGroup K b.binaryParameter) :
    ∃ (y : V) (hy : Lattice.IsNormGenerator q L y),
      b.normGeneratorValueRatioUnit y hy = (u : Kˣ) := by
  rcases b.exists_normGenerator_of_mem_beliNormGeneratorGroup hu with
    ⟨y, hy, hclass⟩
  change
    QuotientGroup.mk' (Subgroup.square (valuationUnitSubgroup K))
        (b.normGeneratorValueRatioValuationUnit y hy) =
      QuotientGroup.mk' (Subgroup.square (valuationUnitSubgroup K)) u
    at hclass
  rw [QuotientGroup.mk'_eq_mk'] at hclass
  rcases hclass with ⟨z, hz, hratio⟩
  change IsSquare z at hz
  rcases hz with ⟨v, hv⟩
  have hvUnit : IsValuationUnit K ((v : valuationUnitSubgroup K) : Kˣ) :=
    v.property
  let vK : Kˣ := (v : valuationUnitSubgroup K)
  let y' : V := (vK : K) • y
  have hy' : Lattice.IsNormGenerator q L y' :=
    hy.smul_valuationUnit vK hvUnit
  refine ⟨y', hy', ?_⟩
  have hscale := b.normGeneratorValueRatioUnit_smul y hy vK hvUnit
  have hratioK := congrArg
    (fun w : valuationUnitSubgroup K => (w : Kˣ)) hratio
  have hvK : (v : valuationUnitSubgroup K) ^ 2 = z := by
    simpa [pow_two] using hv.symm
  rw [← hvK] at hratioK
  change b.normGeneratorValueRatioUnit y' hy' = (u : Kˣ)
  rw [hscale]
  simpa [vK, normGeneratorValueRatioValuationUnit, mul_comm] using hratioK

end BONG

end Bong
