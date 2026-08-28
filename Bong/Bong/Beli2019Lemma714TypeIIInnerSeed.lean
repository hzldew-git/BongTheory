/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma714TypeIIReverseDual
import Bong.Bong.Beli2019Lemma710DualProduct
import Bong.Bong.ValueIsometry

/-!
# Beli (2019), Lemma 7.14(ii): the inner reverse-dual construction

At the Type-II stopping point, the reverse dual of the exceptional ternary
block is adjoined to all but the last vector of the reverse dual of the right
suffix.  The last right-suffix vector supplies the unary factor of the block,
while the reverse dual of the rescaled binary lattice supplies its other two
coordinates.

This file first packages that construction independently of Lemma 7.14.  It
then specializes the package to the four concrete reverse-dual BONGs fixed in
`Beli2019Lemma714TypeIIReverseDual`.
-/

namespace Bong

open Dyadic

namespace BONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- A BONG which literally realizes normalized reverse-dual vectors has the
corresponding reciprocal value sequence. -/
private theorem value_eq_inv_reverse_of_ambientVector_eq
    {X : Type v} [AddCommGroup X] [Module K X]
    {form : QuadraticSpace K X} {lattice dualLattice : Lattice K X}
    {length : Nat}
    (source : BONG X form lattice length)
    (dual : BONG X form dualLattice length)
    (vectors : ∀ i, dual.ambientVector i = source.reverseDualVector i)
    (i : Fin length) :
    dual.value i = ((source.valueUnit (Fin.rev i))⁻¹ : K) := by
  rw [← dual.quadratic_ambientVector i, vectors i,
    source.quadratic_reverseDualVector]

/-- A BONG which literally realizes the normalized reverse dual returns the
original ambient BONG vectors after the same operation is applied again. -/
theorem reverseDualVector_eq_ambientVector_of_ambientVector_eq
    {X : Type v} [AddCommGroup X] [Module K X]
    {form : QuadraticSpace K X} {lattice dualLattice : Lattice K X}
    {length : Nat}
    (source : BONG X form lattice length)
    (dual : BONG X form dualLattice length)
    (vectors : ∀ i, dual.ambientVector i = source.reverseDualVector i)
    (i : Fin length) :
    dual.reverseDualVector i = source.ambientVector i := by
  change
    (dual.value (Fin.rev i))⁻¹ • dual.ambientVector (Fin.rev i) =
      source.ambientVector i
  rw [← dual.quadratic_ambientVector, vectors]
  exact source.normalize_reverseDualVector_rev i

private structure ReverseDualProductPrefixSeedData
    {X A B : Type v}
    [AddCommGroup X] [Module K X]
    [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B]
    {sourceForm : QuadraticSpace K X}
    {lineForm : QuadraticSpace K A}
    {binaryForm : QuadraticSpace K B}
    {sourceLattice : Lattice K X}
    {lineLattice : Lattice K A}
    {binaryLattice : Lattice K B}
    {steps : Nat}
    (source : BONG X sourceForm sourceLattice (steps + 1))
    (lineDual : BONG A lineForm
      (Lattice.dualLattice lineForm lineLattice) 1)
    (blockDual : BONG (B × A) (binaryForm.orthogonalSum lineForm)
      (Lattice.dualLattice (binaryForm.orthogonalSum lineForm)
        (Lattice.product binaryLattice lineLattice)) 3) where
  seed : OrthogonalPrefixSeed binaryForm
    (Lattice.dualLattice binaryForm binaryLattice) 3
    (steps := steps) source
  terminal : A →ₗ[K] X
  terminal_ambientVector : terminal (lineDual.ambientVector 0) =
    source.ambientVector ⟨steps, by omega⟩
  baseValue_eq : ∀ j, seed.baseValue j = blockDual.value j
  baseAmbientVector_eq : ∀ j,
    seed.baseAmbientVector j =
      (terminal (blockDual.ambientVector j).2,
        (blockDual.ambientVector j).1)

private noncomputable def reverseDualProductPrefixSeedData
    {X A B : Type v}
    [AddCommGroup X] [Module K X]
    [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B]
    {sourceForm : QuadraticSpace K X}
    {lineForm : QuadraticSpace K A}
    {binaryForm : QuadraticSpace K B}
    {sourceLattice : Lattice K X}
    {lineLattice : Lattice K A}
    {binaryLattice : Lattice K B}
    {steps : Nat}
    (source : BONG X sourceForm sourceLattice (steps + 1))
    (lineDual : BONG A lineForm
      (Lattice.dualLattice lineForm lineLattice) 1)
    (_binaryDual : BONG B binaryForm
      (Lattice.dualLattice binaryForm binaryLattice) 2)
    (blockDual : BONG (B × A) (binaryForm.orthogonalSum lineForm)
      (Lattice.dualLattice (binaryForm.orthogonalSum lineForm)
        (Lattice.product binaryLattice lineLattice)) 3)
    (hlast : source.value ⟨steps, by omega⟩ = lineDual.value 0) :
    ReverseDualProductPrefixSeedData source lineDual blockDual := by
  induction steps generalizing X with
  | zero =>
      have hlineValues : ∀ i, lineDual.value i = source.value i := by
        intro i
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        exact hlast.symm
      let lineToSource :=
        lineDual.latticeIsometryOfValueEq source hlineValues
      let splitBlock := Lattice.dualOrthogonalProductIsometry
        (q := binaryForm) (r := lineForm)
        (L := binaryLattice) (M := lineLattice)
      let swap := Lattice.orthogonalProductSwap
        (q := binaryForm) (r := lineForm)
        (L := Lattice.dualLattice binaryForm binaryLattice)
        (M := Lattice.dualLattice lineForm lineLattice)
      let identifyLine := lineToSource.orthogonalProductBasic
        (Lattice.Isometry.refl binaryForm
          (Lattice.dualLattice binaryForm binaryLattice))
      let seed := OrthogonalPrefixSeed.stopOfLatticeIsometry source blockDual
        ((splitBlock.trans swap).trans identifyLine)
      refine
        { seed := seed
          terminal := lineToSource.toLinearEquiv.toLinearMap
          terminal_ambientVector := by
            change lineToSource.toLinearEquiv (lineDual.ambientVector 0) =
              source.ambientVector (0 : Fin 1)
            exact lineDual.latticeIsometryOfValueEq_apply_ambientVector
              source hlineValues 0
          baseValue_eq := by
            intro j
            simp only [seed, OrthogonalPrefixSeed.stopOfLatticeIsometry,
              OrthogonalPrefixSeed.baseValue, value_mapLatticeIsometry]
          baseAmbientVector_eq := by
            intro j
            simp [seed, OrthogonalPrefixSeed.stopOfLatticeIsometry,
              OrthogonalPrefixSeed.baseAmbientVector,
              BONG.ambientVector_mapLatticeIsometry,
              Lattice.Isometry.trans, LinearEquiv.trans_apply,
              Lattice.dualOrthogonalProductIsometry,
              Lattice.Isometry.refl, LinearEquiv.refl_apply,
              splitBlock, swap, identifyLine] }
  | succ steps ih =>
      cases source with
      | cons x generator anisotropic tail =>
          have hindex :
              (⟨steps + 1, by omega⟩ : Fin ((steps + 1) + 1)) =
                (⟨steps, by omega⟩ : Fin (steps + 1)).succ := by
            apply Fin.ext
            rfl
          rw [hindex, value_cons_succ] at hlast
          let tailData := ih tail hlast
          let seed := OrthogonalPrefixSeed.cons generator anisotropic tail
            tailData.seed
          let terminal : A →ₗ[K] X :=
            (sourceForm.vectorOrthogonal x).subtype.comp tailData.terminal
          refine
            { seed := seed
              terminal := terminal
              terminal_ambientVector := by
                change ((tailData.terminal (lineDual.ambientVector 0) :
                    sourceForm.vectorOrthogonal x) : X) = _
                rw [tailData.terminal_ambientVector]
                have hlastIndex :
                    (⟨steps, by omega⟩ : Fin (steps + 1)).succ =
                      (⟨steps + 1, by omega⟩ : Fin ((steps + 1) + 1)) := by
                  apply Fin.ext
                  rfl
                rw [← hlastIndex, BONG.ambientVector_cons_succ]
              baseValue_eq := by
                intro j
                simpa only [seed, OrthogonalPrefixSeed.baseValue] using
                  tailData.baseValue_eq j
              baseAmbientVector_eq := by
                intro j
                change
                  (((Lattice.projectedOrthogonalProductIsometry
                      (q := sourceForm) (r := binaryForm)
                      (L := sourceLattice)
                      (M := Lattice.dualLattice binaryForm binaryLattice)
                      anisotropic).symm.toLinearEquiv
                        (tailData.seed.baseAmbientVector j) :
                    (sourceForm.orthogonalSum binaryForm).vectorOrthogonal
                      (x, 0)) : X × B) = _
                rw [tailData.baseAmbientVector_eq j]
                rfl }

/-- Adjoin an external binary factor after all but the final vector of a
nonempty source BONG.  At the stopping point the supplied ternary BONG is
identified with the product of that final unary source lattice and the binary
factor by reverse duality, factor exchange, and equality of the unary values.
-/
noncomputable def reverseDualProductPrefixSeed
    {X A B : Type v}
    [AddCommGroup X] [Module K X]
    [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B]
    {sourceForm : QuadraticSpace K X}
    {lineForm : QuadraticSpace K A}
    {binaryForm : QuadraticSpace K B}
    {sourceLattice : Lattice K X}
    {lineLattice : Lattice K A}
    {binaryLattice : Lattice K B}
    {steps : Nat}
    (source : BONG X sourceForm sourceLattice (steps + 1))
    (lineDual : BONG A lineForm
      (Lattice.dualLattice lineForm lineLattice) 1)
    (binaryDual : BONG B binaryForm
      (Lattice.dualLattice binaryForm binaryLattice) 2)
    (blockDual : BONG (B × A) (binaryForm.orthogonalSum lineForm)
      (Lattice.dualLattice (binaryForm.orthogonalSum lineForm)
        (Lattice.product binaryLattice lineLattice)) 3)
    (hlast : source.value ⟨steps, by omega⟩ = lineDual.value 0) :
    OrthogonalPrefixSeed binaryForm
      (Lattice.dualLattice binaryForm binaryLattice) 3
      (steps := steps) source :=
  (reverseDualProductPrefixSeedData source lineDual binaryDual blockDual hlast).seed

/-- The recursive prefix construction never changes the three scalar values
of the stopping reverse-dual block. -/
@[simp]
theorem reverseDualProductPrefixSeed_baseValue
    {X A B : Type v}
    [AddCommGroup X] [Module K X]
    [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B]
    {sourceForm : QuadraticSpace K X}
    {lineForm : QuadraticSpace K A}
    {binaryForm : QuadraticSpace K B}
    {sourceLattice : Lattice K X}
    {lineLattice : Lattice K A}
    {binaryLattice : Lattice K B}
    {steps : Nat}
    (source : BONG X sourceForm sourceLattice (steps + 1))
    (lineDual : BONG A lineForm
      (Lattice.dualLattice lineForm lineLattice) 1)
    (binaryDual : BONG B binaryForm
      (Lattice.dualLattice binaryForm binaryLattice) 2)
    (blockDual : BONG (B × A) (binaryForm.orthogonalSum lineForm)
      (Lattice.dualLattice (binaryForm.orthogonalSum lineForm)
        (Lattice.product binaryLattice lineLattice)) 3)
    (hlast : source.value ⟨steps, by omega⟩ = lineDual.value 0)
    (j : Fin 3) :
    (reverseDualProductPrefixSeed source lineDual binaryDual blockDual hlast).baseValue j =
      blockDual.value j :=
  (reverseDualProductPrefixSeedData source lineDual binaryDual blockDual hlast).baseValue_eq j

/-- The terminal unary factor is embedded into the last source coordinate.
This linear map is the coordinate bridge used when the complete construction
is reversed a second time. -/
noncomputable def reverseDualProductTerminalEmbedding
    {X A B : Type v}
    [AddCommGroup X] [Module K X]
    [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B]
    {sourceForm : QuadraticSpace K X}
    {lineForm : QuadraticSpace K A}
    {binaryForm : QuadraticSpace K B}
    {sourceLattice : Lattice K X}
    {lineLattice : Lattice K A}
    {binaryLattice : Lattice K B}
    {steps : Nat}
    (source : BONG X sourceForm sourceLattice (steps + 1))
    (lineDual : BONG A lineForm
      (Lattice.dualLattice lineForm lineLattice) 1)
    (binaryDual : BONG B binaryForm
      (Lattice.dualLattice binaryForm binaryLattice) 2)
    (blockDual : BONG (B × A) (binaryForm.orthogonalSum lineForm)
      (Lattice.dualLattice (binaryForm.orthogonalSum lineForm)
        (Lattice.product binaryLattice lineLattice)) 3)
    (hlast : source.value ⟨steps, by omega⟩ = lineDual.value 0) :
    A →ₗ[K] X :=
  (reverseDualProductPrefixSeedData source lineDual binaryDual blockDual
    hlast).terminal

/-- The terminal embedding carries the unary reverse-dual BONG vector to
the last vector of the source BONG. -/
@[simp]
theorem reverseDualProductTerminalEmbedding_ambientVector
    {X A B : Type v}
    [AddCommGroup X] [Module K X]
    [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B]
    {sourceForm : QuadraticSpace K X}
    {lineForm : QuadraticSpace K A}
    {binaryForm : QuadraticSpace K B}
    {sourceLattice : Lattice K X}
    {lineLattice : Lattice K A}
    {binaryLattice : Lattice K B}
    {steps : Nat}
    (source : BONG X sourceForm sourceLattice (steps + 1))
    (lineDual : BONG A lineForm
      (Lattice.dualLattice lineForm lineLattice) 1)
    (binaryDual : BONG B binaryForm
      (Lattice.dualLattice binaryForm binaryLattice) 2)
    (blockDual : BONG (B × A) (binaryForm.orthogonalSum lineForm)
      (Lattice.dualLattice (binaryForm.orthogonalSum lineForm)
        (Lattice.product binaryLattice lineLattice)) 3)
    (hlast : source.value ⟨steps, by omega⟩ = lineDual.value 0) :
    reverseDualProductTerminalEmbedding source lineDual binaryDual blockDual
        hlast (lineDual.ambientVector 0) =
      source.ambientVector ⟨steps, by omega⟩ :=
  (reverseDualProductPrefixSeedData source lineDual binaryDual blockDual
    hlast).terminal_ambientVector

/-- The same terminal map also identifies the double-reversed unary vector
with the head of the double-reversed source. -/
theorem reverseDualProductTerminalEmbedding_reverseDualVector
    {X A B : Type v}
    [AddCommGroup X] [Module K X]
    [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B]
    {sourceForm : QuadraticSpace K X}
    {lineForm : QuadraticSpace K A}
    {binaryForm : QuadraticSpace K B}
    {sourceLattice : Lattice K X}
    {lineLattice : Lattice K A}
    {binaryLattice : Lattice K B}
    {steps : Nat}
    (source : BONG X sourceForm sourceLattice (steps + 1))
    (lineDual : BONG A lineForm
      (Lattice.dualLattice lineForm lineLattice) 1)
    (binaryDual : BONG B binaryForm
      (Lattice.dualLattice binaryForm binaryLattice) 2)
    (blockDual : BONG (B × A) (binaryForm.orthogonalSum lineForm)
      (Lattice.dualLattice (binaryForm.orthogonalSum lineForm)
        (Lattice.product binaryLattice lineLattice)) 3)
    (hlast : source.value ⟨steps, by omega⟩ = lineDual.value 0) :
    reverseDualProductTerminalEmbedding source lineDual binaryDual blockDual
        hlast (lineDual.reverseDualVector 0) =
      source.reverseDualVector 0 := by
  let last : Fin (steps + 1) := ⟨steps, by omega⟩
  have hrevLine : Fin.rev (0 : Fin 1) = 0 := Subsingleton.elim _ _
  have hrevSource : Fin.rev (0 : Fin (steps + 1)) = last := by
    apply Fin.ext
    simp [last, Fin.rev]
  have hunit : source.valueUnit last = lineDual.valueUnit 0 := by
    apply Units.ext
    simpa only [BONG.coe_valueUnit] using hlast
  simp only [BONG.reverseDualVector, BONG.dualVector, hrevLine, hrevSource,
    LinearMap.map_smul]
  rw [reverseDualProductTerminalEmbedding_ambientVector, ← hunit]

/-- The transported stopping vectors are the exceptional-block vectors with
their unary coordinate placed in the terminal source line and their binary
coordinate unchanged. -/
@[simp]
theorem reverseDualProductPrefixSeed_baseAmbientVector
    {X A B : Type v}
    [AddCommGroup X] [Module K X]
    [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B]
    {sourceForm : QuadraticSpace K X}
    {lineForm : QuadraticSpace K A}
    {binaryForm : QuadraticSpace K B}
    {sourceLattice : Lattice K X}
    {lineLattice : Lattice K A}
    {binaryLattice : Lattice K B}
    {steps : Nat}
    (source : BONG X sourceForm sourceLattice (steps + 1))
    (lineDual : BONG A lineForm
      (Lattice.dualLattice lineForm lineLattice) 1)
    (binaryDual : BONG B binaryForm
      (Lattice.dualLattice binaryForm binaryLattice) 2)
    (blockDual : BONG (B × A) (binaryForm.orthogonalSum lineForm)
      (Lattice.dualLattice (binaryForm.orthogonalSum lineForm)
        (Lattice.product binaryLattice lineLattice)) 3)
    (hlast : source.value ⟨steps, by omega⟩ = lineDual.value 0)
    (j : Fin 3) :
    (reverseDualProductPrefixSeed source lineDual binaryDual blockDual hlast).baseAmbientVector j =
      (reverseDualProductTerminalEmbedding source lineDual binaryDual blockDual
          hlast (blockDual.ambientVector j).2,
        (blockDual.ambientVector j).1) :=
  (reverseDualProductPrefixSeedData source lineDual binaryDual blockDual
    hlast).baseAmbientVector_eq j

namespace OrthogonalPrefixSeed

universe w

variable {X : Type v} [AddCommGroup X] [Module K X]
variable {W : Type w} [AddCommGroup W] [Module K W]
variable {sourceForm : QuadraticSpace K X} {rightForm : QuadraticSpace K W}
variable {sourceLattice : Lattice K X} {rightLattice : Lattice K W}
variable {sourceLength steps baseLength : Nat}
variable {source : BONG X sourceForm sourceLattice sourceLength}

/-- The right block of a seed result has the intrinsic stopping values. -/
@[simp]
theorem value_result_right
    {rightLength : Nat}
    (seed : OrthogonalPrefixSeed rightForm rightLattice baseLength
      (steps := steps) source)
    (right : BONG W rightForm rightLattice (rightLength + 1))
    (horder : ∀ i : Fin steps,
      source.order (seed.sourceIndex i) ≤ right.order 0)
    (j : Fin baseLength) :
    (seed.result right horder).value
        (orthogonalProductRightIndex steps j) = seed.baseValue j := by
  change (seed.toData right horder).result.value
      (orthogonalProductRightIndex steps j) = _
  rw [OrthogonalPrefixData.value_result_right,
    seed.baseValue_toData right horder]

/-- The normalized reverse of the intrinsic stopping block.  This is the
coordinate-free form of the vectors which occur first after reverse
duality of a prefix result. -/
noncomputable def baseReverseDualVector
    (seed : OrthogonalPrefixSeed rightForm rightLattice baseLength
      (steps := steps) source)
    (i : Fin baseLength) : X × W :=
  ((seed.baseValue (Fin.rev i))⁻¹ : K) •
    seed.baseAmbientVector (Fin.rev i)

/-- After reversing a prefix result, its first block is exactly the
normalized reverse of the intrinsic stopping block. -/
theorem reverseDualVector_result_block
    {rightLength : Nat}
    (seed : OrthogonalPrefixSeed rightForm rightLattice baseLength
      (steps := steps) source)
    (right : BONG W rightForm rightLattice (rightLength + 1))
    (horder : ∀ i : Fin steps,
      source.order (seed.sourceIndex i) ≤ right.order 0)
    (i : Fin baseLength) :
    (seed.result right horder).reverseDualVector
        ⟨i.val, by omega⟩ =
      seed.baseReverseDualVector i := by
  let resultIndex : Fin (baseLength + steps) := ⟨i.val, by omega⟩
  let baseIndex : Fin baseLength := Fin.rev i
  have hrev : Fin.rev resultIndex =
      orthogonalProductRightIndex steps baseIndex := by
    apply Fin.ext
    simp only [resultIndex, baseIndex, Fin.rev,
      orthogonalProductRightIndex]
    omega
  change
    (((seed.result right horder).valueUnit (Fin.rev resultIndex))⁻¹ : K) •
        (seed.result right horder).ambientVector (Fin.rev resultIndex) = _
  rw [hrev, seed.ambientVector_result_right]
  change
    (((seed.result right horder).valueUnit
      (orthogonalProductRightIndex steps baseIndex))⁻¹ : K) •
        seed.baseAmbientVector baseIndex = _
  congr 1
  change
    (((seed.result right horder).valueUnit
      (orthogonalProductRightIndex steps baseIndex))⁻¹ : K) =
        (seed.baseValue baseIndex)⁻¹
  congr 1
  change
    ((seed.result right horder).valueUnit
      (orthogonalProductRightIndex steps baseIndex) : K) =
        seed.baseValue baseIndex
  exact seed.value_result_right right horder baseIndex

/-- When the source has one vector beyond the retained prefix, the remaining
reverse-dual vectors are exactly the non-head reverse-dual source vectors,
embedded in the left factor. -/
theorem reverseDualVector_result_suffix
    {rightLength : Nat} {source : BONG X sourceForm sourceLattice (steps + 1)}
    (seed : OrthogonalPrefixSeed rightForm rightLattice baseLength
      (steps := steps) source)
    (right : BONG W rightForm rightLattice (rightLength + 1))
    (horder : ∀ i : Fin steps,
      source.order (seed.sourceIndex i) ≤ right.order 0)
    (j : Fin steps) :
    (seed.result right horder).reverseDualVector
        ⟨baseLength + j.val, by omega⟩ =
      (source.reverseDualVector ⟨j.val + 1, by omega⟩, 0) := by
  let resultIndex : Fin (baseLength + steps) :=
    ⟨baseLength + j.val, by omega⟩
  let sourceIndex : Fin (steps + 1) := ⟨j.val + 1, by omega⟩
  let prefixIndex : Fin steps := Fin.rev j
  have hrevResult : Fin.rev resultIndex =
      orthogonalProductLeftIndex baseLength prefixIndex := by
    apply Fin.ext
    simp only [resultIndex, prefixIndex, Fin.rev,
      orthogonalProductLeftIndex]
    omega
  have hrevSource : Fin.rev sourceIndex = seed.sourceIndex prefixIndex := by
    apply Fin.ext
    simp only [sourceIndex, prefixIndex, Fin.rev,
      OrthogonalPrefixSeed.sourceIndex_val]
    omega
  change (seed.result right horder).reverseDualVector resultIndex =
    (source.reverseDualVector sourceIndex, 0)
  simp only [BONG.reverseDualVector, BONG.dualVector]
  rw [hrevResult, seed.ambientVector_result_left, ← hrevSource]
  have hvalue :
      (seed.result right horder).value
          (orthogonalProductLeftIndex baseLength prefixIndex) =
        source.value (Fin.rev sourceIndex) := by
    rw [OrthogonalPrefixSeed.value_result_left, hrevSource]
  have hunit :
      (seed.result right horder).valueUnit
          (orthogonalProductLeftIndex baseLength prefixIndex) =
        source.valueUnit (Fin.rev sourceIndex) := by
    apply Units.ext
    simpa only [BONG.coe_valueUnit] using hvalue
  rw [hunit]
  simp

end OrthogonalPrefixSeed

/-- Reversing the transported stopping block commutes with the terminal
embedding and leaves the binary coordinate unchanged. -/
theorem reverseDualProductPrefixSeed_baseReverseDualVector
    {X A B : Type v}
    [AddCommGroup X] [Module K X]
    [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B]
    {sourceForm : QuadraticSpace K X}
    {lineForm : QuadraticSpace K A}
    {binaryForm : QuadraticSpace K B}
    {sourceLattice : Lattice K X}
    {lineLattice : Lattice K A}
    {binaryLattice : Lattice K B}
    {steps : Nat}
    (source : BONG X sourceForm sourceLattice (steps + 1))
    (lineDual : BONG A lineForm
      (Lattice.dualLattice lineForm lineLattice) 1)
    (binaryDual : BONG B binaryForm
      (Lattice.dualLattice binaryForm binaryLattice) 2)
    (blockDual : BONG (B × A) (binaryForm.orthogonalSum lineForm)
      (Lattice.dualLattice (binaryForm.orthogonalSum lineForm)
        (Lattice.product binaryLattice lineLattice)) 3)
    (hlast : source.value ⟨steps, by omega⟩ = lineDual.value 0)
    (i : Fin 3) :
    (reverseDualProductPrefixSeed source lineDual binaryDual blockDual hlast).baseReverseDualVector i =
      (reverseDualProductTerminalEmbedding source lineDual binaryDual blockDual
          hlast (blockDual.reverseDualVector i).2,
        (blockDual.reverseDualVector i).1) := by
  unfold OrthogonalPrefixSeed.baseReverseDualVector
  rw [reverseDualProductPrefixSeed_baseValue,
    reverseDualProductPrefixSeed_baseAmbientVector]
  simp only [BONG.reverseDualVector, BONG.dualVector, Prod.smul_mk]
  change
    (((blockDual.valueUnit (Fin.rev i))⁻¹ : K) •
        reverseDualProductTerminalEmbedding source lineDual binaryDual
          blockDual hlast (blockDual.ambientVector (Fin.rev i)).2,
      ((blockDual.valueUnit (Fin.rev i))⁻¹ : K) •
        (blockDual.ambientVector (Fin.rev i)).1) = _
  apply Prod.ext
  · change
      ((blockDual.valueUnit (Fin.rev i))⁻¹ : K) •
          reverseDualProductTerminalEmbedding source lineDual binaryDual
            blockDual hlast (blockDual.ambientVector (Fin.rev i)).2 =
        reverseDualProductTerminalEmbedding source lineDual binaryDual
          blockDual hlast
          (((blockDual.valueUnit (Fin.rev i))⁻¹ : K) •
            (blockDual.ambientVector (Fin.rev i)).2)
    exact (reverseDualProductTerminalEmbedding source lineDual binaryDual
      blockDual hlast).map_smul _ _ |>.symm
  · rfl

namespace GoodBONG

variable {V : Type v} [AddCommGroup V] [Module K V]
variable {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

private theorem lemma714TypeIIInnerSeed_two_le_rank (n : Nat) :
    2 ≤ n + 3 := by
  omega

/-- Transporting only the length index of a good BONG does not change its
scalar values. -/
@[simp]
theorem value_castLength
    {m length : Nat} {form : QuadraticSpace K V} {M : Lattice K V}
    (a : GoodBONG form M m) (h : m = length) (i : Fin length) :
    (a.castLength h).value i = a.value ⟨i.val, by omega⟩ := by
  subst length
  rfl

/-- Transporting only the length index of a good BONG does not change its
ambient vectors. -/
@[simp]
theorem ambientVector_castLength
    {m length : Nat} {form : QuadraticSpace K V} {M : Lattice K V}
    (a : GoodBONG form M m) (h : m = length) (i : Fin length) :
    (a.castLength h).toBONG.ambientVector i =
      a.toBONG.ambientVector ⟨i.val, by omega⟩ := by
  subst length
  rfl

/-- Transporting only the length index of a good BONG commutes with its
normalized reverse-dual vectors. -/
@[simp]
theorem reverseDualVector_castLength
    {m length : Nat} {form : QuadraticSpace K V} {M : Lattice K V}
    (a : GoodBONG form M m) (h : m = length) (i : Fin length) :
    (a.castLength h).toBONG.reverseDualVector i =
      a.toBONG.reverseDualVector ⟨i.val, by omega⟩ := by
  subst length
  rfl

/-- The right suffix retains the value units of the original BONG, beginning
at the stopping index `s`. -/
@[simp]
theorem lemma714TypeIIRightSuffix_valueUnit
    (b : GoodBONG q L (n + 3))
    (S : BONG.TwoBlockSplitWitness b.toBONG 2
      (lemma714TypeIIInnerSeed_two_le_rank n))
    (s : Nat) (hsTwo : 2 ≤ s) (hs : s < n + 3)
    (U : (b.lemma714Tail S).toBONG.TwoBlockSplitWitness
      (s - 2) (by omega)) (i : Fin (n + 3 - s)) :
    (b.lemma714TypeIIRightSuffix S s hsTwo hs U).valueUnit i =
      b.valueUnit ⟨s + i.val, by omega⟩ := by
  rw [lemma714TypeIIRightSuffix, valueUnit_castLength]
  change U.right.bong.valueUnit ⟨i.val, by omega⟩ = _
  rw [U.right.valueUnit_eq]
  change (b.lemma714Tail S).valueUnit
      (U.right.sourceIndex ⟨i.val, by omega⟩) = _
  rw [b.lemma714Tail_valueUnit S]
  congr 1
  apply Fin.ext
  simp [BONG.SegmentWitness.sourceIndex]
  omega

/-- The head of the right suffix is literally the unary stopping-line
vector, regarded in the larger right carrier. -/
@[simp]
theorem lemma714TypeIIRightSuffix_ambientVector_zero
    (b : GoodBONG q L (n + 3))
    (S : BONG.TwoBlockSplitWitness b.toBONG 2
      (lemma714TypeIIInnerSeed_two_le_rank n))
    (s : Nat) (hsTwo : 2 ≤ s) (hs : s < n + 3)
    (U : (b.lemma714Tail S).toBONG.TwoBlockSplitWitness
      (s - 2) (by omega)) :
    (b.lemma714TypeIIRightSuffix S s hsTwo hs U).toBONG.ambientVector
        ⟨0, by omega⟩ =
      b.lemma714TypeIILineToRight S s hsTwo hs U
        ((b.lemma714TypeIILine S s hsTwo hs).toBONG.ambientVector 0) := by
  rw [lemma714TypeIIRightSuffix, GoodBONG.ambientVector_castLength]
  change U.right.bong.ambientVector ⟨0, by omega⟩ = _
  apply Subtype.ext
  rw [b.lemma714TypeIILineToRight_coe S s hsTwo hs U]
  change
    ((U.right.bong.ambientVector ⟨0, by omega⟩ : U.right.carrier) :
        S.right.carrier) =
      (((b.lemma714TypeIILineSegment S s hsTwo hs).bong.ambientVector 0 :
        (b.lemma714TypeIILineSegment S s hsTwo hs).carrier) :
        S.right.carrier)
  rw [U.right.ambientVector_eq,
    (b.lemma714TypeIILineSegment S s hsTwo hs).ambientVector_eq]
  apply congrArg (b.lemma714Tail S).toBONG.ambientVector
  apply Fin.ext
  simp only [BONG.SegmentWitness.sourceIndex_val]
  omega

section TypeIIInnerSeed

variable [DyadicDiscriminantClassLaws K]
variable [BONGReverseDualLaws.{u, v} K]
variable [BeliLemma43ConstructionLaws.{u, v} K]
variable (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
variable (D : Lemma714StoppingData b R s)
variable (hsCurrent : s < n + 3)
variable (S : BONG.TwoBlockSplitWitness b.toBONG 2
  (lemma714TypeIIInnerSeed_two_le_rank n))
variable (hsFour : s = 2 ∨ 4 ≤ s)
variable (U : (b.lemma714Tail S).toBONG.TwoBlockSplitWitness
  (s - 2) (by have := D.le_rank; omega))
variable (block : GoodBONG
  ((q.restrict S.left.carrier S.left.nondegenerate).orthogonalSum
    ((q.restrict S.right.carrier S.right.nondegenerate).restrict
      (b.lemma714TypeIILineSegment S s D.two_le hsCurrent).carrier
      (b.lemma714TypeIILineSegment S s D.two_le hsCurrent).nondegenerate))
  (Lattice.product
    (Lattice.rescale (uniformizerUnit K) S.left.lattice)
    (b.lemma714TypeIILineSegment S s D.two_le hsCurrent).lattice) 3)

/-- The right reverse dual reindexed as a nonempty BONG with exactly
`n + 2 - s` prefix steps and one terminal unary entry. -/
noncomputable def lemma714TypeIIRightReverseDualForStop :=
  (b.lemma714TypeIIRightReverseDual R s D hsCurrent S U).castLength
    (by omega : n + 3 - s = (n + 2 - s) + 1)

/-- Length normalization does not change the right-reverse-dual values. -/
@[simp]
theorem lemma714TypeIIRightReverseDualForStop_value
    (i : Fin ((n + 2 - s) + 1)) :
    (b.lemma714TypeIIRightReverseDualForStop R s D hsCurrent S U).value i =
      (b.lemma714TypeIIRightReverseDual R s D hsCurrent S U).value
        ⟨i.val, by omega⟩ := by
  rw [lemma714TypeIIRightReverseDualForStop, GoodBONG.value_castLength]

/-- The terminal value of the reindexed right reverse dual agrees with the
value of the unary reverse dual. -/
theorem lemma714TypeIIRightReverseDualForStop_lastValue :
    (b.lemma714TypeIIRightReverseDualForStop R s D hsCurrent S U).value
        ⟨n + 2 - s, by omega⟩ =
      (b.lemma714TypeIILineReverseDual R s D hsCurrent S).value 0 := by
  rw [lemma714TypeIIRightReverseDualForStop, GoodBONG.value_castLength]
  let iRight : Fin (n + 3 - s) := ⟨n + 2 - s, by omega⟩
  change
    (b.lemma714TypeIIRightReverseDual R s D hsCurrent S U).toBONG.value
        iRight =
      (b.lemma714TypeIILineReverseDual R s D hsCurrent S).toBONG.value 0
  let zeroRight : Fin (n + 3 - s) := ⟨0, by omega⟩
  have hrightRev : Fin.rev iRight = zeroRight := by
    apply Fin.ext
    simp only [iRight, zeroRight, Fin.rev]
    omega
  have hlineRev : Fin.rev (0 : Fin 1) = 0 := Subsingleton.elim _ _
  rw [value_eq_inv_reverse_of_ambientVector_eq
      (b.lemma714TypeIIRightSuffix S s D.two_le hsCurrent U).toBONG
      (b.lemma714TypeIIRightReverseDual R s D hsCurrent S U).toBONG
      (b.lemma714TypeIIRightReverseDual_ambientVector R s D hsCurrent
        S U) iRight,
    value_eq_inv_reverse_of_ambientVector_eq
      (b.lemma714TypeIILine S s D.two_le hsCurrent).toBONG
      (b.lemma714TypeIILineReverseDual R s D hsCurrent S).toBONG
      (b.lemma714TypeIILineReverseDual_ambientVector R s D hsCurrent S) 0,
    hrightRev, hlineRev]
  change
    ((b.lemma714TypeIIRightSuffix S s D.two_le hsCurrent U).valueUnit
      zeroRight : K)⁻¹ =
    ((b.lemma714TypeIILine S s D.two_le hsCurrent).valueUnit 0 : K)⁻¹
  rw [b.lemma714TypeIIRightSuffix_valueUnit S s D.two_le hsCurrent U,
    b.lemma714TypeIILine_valueUnit_zero S s D.two_le hsCurrent]
  have hindex :
      (⟨s + zeroRight.val, by omega⟩ : Fin (n + 3)) =
        ⟨s, hsCurrent⟩ := by
    apply Fin.ext
    simp [zeroRight]
  rw [hindex]

/-- The inner Lemma-7.10 seed: retain the initial `n + 2 - s` vectors of the
right reverse dual and replace its last unary lattice by the complete
exceptional-block reverse dual. -/
noncomputable def lemma714TypeIIInnerSeed :
    OrthogonalPrefixSeed
      (q.restrict S.left.carrier S.left.nondegenerate)
      (Lattice.dualLattice
        (q.restrict S.left.carrier S.left.nondegenerate)
        (Lattice.rescale (uniformizerUnit K) S.left.lattice)) 3
      (steps := n + 2 - s)
      (b.lemma714TypeIIRightReverseDualForStop R s D hsCurrent S U).toBONG :=
  BONG.reverseDualProductPrefixSeed
    (b.lemma714TypeIIRightReverseDualForStop R s D hsCurrent S U).toBONG
    (b.lemma714TypeIILineReverseDual R s D hsCurrent S).toBONG
    (b.lemma714TypeIIRescaledBinaryReverseDual S).toBONG
    (lemma714TypeIIBlockReverseDual (b := b) (R := R) (s := s)
      (D := D) (hsCurrent := hsCurrent) (S := S) (block := block)).toBONG
    (b.lemma714TypeIIRightReverseDualForStop_lastValue R s D hsCurrent
      S U)

/-- The stopping values stored by the specialized inner seed are exactly the
three values of the exceptional-block reverse dual. -/
@[simp]
theorem lemma714TypeIIInnerSeed_baseValue (j : Fin 3) :
    (b.lemma714TypeIIInnerSeed R s D hsCurrent S U block).baseValue j =
      (lemma714TypeIIBlockReverseDual (b := b) (R := R) (s := s)
        (D := D) (hsCurrent := hsCurrent) (S := S) (block := block)).value j :=
  BONG.reverseDualProductPrefixSeed_baseValue
    (b.lemma714TypeIIRightReverseDualForStop R s D hsCurrent S U).toBONG
    (b.lemma714TypeIILineReverseDual R s D hsCurrent S).toBONG
    (b.lemma714TypeIIRescaledBinaryReverseDual S).toBONG
    (lemma714TypeIIBlockReverseDual (b := b) (R := R) (s := s)
      (D := D) (hsCurrent := hsCurrent) (S := S) (block := block)).toBONG
    (b.lemma714TypeIIRightReverseDualForStop_lastValue R s D hsCurrent
      S U) j

/-- The terminal unary coordinate map retained by the inner seed. -/
noncomputable def lemma714TypeIIInnerTerminalEmbedding :
    (b.lemma714TypeIILineSegment S s D.two_le hsCurrent).carrier →ₗ[K]
      U.right.carrier :=
  BONG.reverseDualProductTerminalEmbedding
    (b.lemma714TypeIIRightReverseDualForStop R s D hsCurrent S U).toBONG
    (b.lemma714TypeIILineReverseDual R s D hsCurrent S).toBONG
    (b.lemma714TypeIIRescaledBinaryReverseDual S).toBONG
    (lemma714TypeIIBlockReverseDual (b := b) (R := R) (s := s)
      (D := D) (hsCurrent := hsCurrent) (S := S) (block := block)).toBONG
    (b.lemma714TypeIIRightReverseDualForStop_lastValue R s D hsCurrent
      S U)

/-- The terminal map constructed recursively from values is not an arbitrary
one-dimensional isometry: it is exactly the natural inclusion of the line
generated by `x_s` into the right suffix. -/
@[simp]
theorem lemma714TypeIIInnerTerminalEmbedding_apply
    (z : (b.lemma714TypeIILineSegment S s D.two_le hsCurrent).carrier) :
    b.lemma714TypeIIInnerTerminalEmbedding R s D hsCurrent S U block z =
      b.lemma714TypeIILineToRight S s D.two_le hsCurrent U z := by
  let lineDual :=
    (b.lemma714TypeIILineReverseDual R s D hsCurrent S).toBONG
  let rightDual :=
    (b.lemma714TypeIIRightReverseDual R s D hsCurrent S U).toBONG
  let rightDualForStop :=
    (b.lemma714TypeIIRightReverseDualForStop R s D hsCurrent S U).toBONG
  let binaryDual :=
    (b.lemma714TypeIIRescaledBinaryReverseDual S).toBONG
  let blockDual :=
    (lemma714TypeIIBlockReverseDual (b := b) (R := R) (s := s)
      (D := D) (hsCurrent := hsCurrent) (S := S) (block := block)).toBONG
  let hlast := b.lemma714TypeIIRightReverseDualForStop_lastValue R s D
    hsCurrent S U
  let inclusion :
      (b.lemma714TypeIILineSegment S s D.two_le hsCurrent).carrier →ₗ[K]
        U.right.carrier :=
    { toFun := fun x =>
        b.lemma714TypeIILineToRight S s D.two_le hsCurrent U x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hrightDouble : rightDualForStop.reverseDualVector 0 =
      (b.lemma714TypeIIRightSuffix S s D.two_le hsCurrent U).toBONG.ambientVector
        ⟨0, by omega⟩ := by
    dsimp only [rightDualForStop]
    rw [lemma714TypeIIRightReverseDualForStop,
      GoodBONG.reverseDualVector_castLength]
    exact BONG.reverseDualVector_eq_ambientVector_of_ambientVector_eq
      (b.lemma714TypeIIRightSuffix S s D.two_le hsCurrent U).toBONG
      rightDual
      (b.lemma714TypeIIRightReverseDual_ambientVector R s D hsCurrent
        S U) ⟨0, by omega⟩
  have hlineDouble : lineDual.reverseDualVector 0 =
      (b.lemma714TypeIILine S s D.two_le hsCurrent).toBONG.ambientVector 0 :=
    BONG.reverseDualVector_eq_ambientVector_of_ambientVector_eq
      (b.lemma714TypeIILine S s D.two_le hsCurrent).toBONG
      lineDual
      (b.lemma714TypeIILineReverseDual_ambientVector R s D hsCurrent S) 0
  have hmaps :
      BONG.reverseDualProductTerminalEmbedding rightDualForStop lineDual
          binaryDual blockDual hlast = inclusion := by
    apply lineDual.reverseDualBasis.ext
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rw [BONG.reverseDualBasis_apply,
      BONG.reverseDualProductTerminalEmbedding_reverseDualVector,
      hrightDouble, hlineDouble]
    exact b.lemma714TypeIIRightSuffix_ambientVector_zero S s D.two_le
      hsCurrent U
  change
    BONG.reverseDualProductTerminalEmbedding rightDualForStop lineDual
        binaryDual blockDual hlast z = inclusion z
  rw [hmaps]

/-- Every right-suffix order which survives into the inner prefix is at
least the second order of the rescaled binary block.  This is the two-parity
monotonicity argument immediately preceding the second use of Lemma 7.10 in
the paper. -/
theorem lemma714TypeIIRescaledBinary_second_le_rightSuffix
    (hsecond : b.order ⟨1, by omega⟩ =
      R - 2 * (ramificationIndex K : Int))
    (hcurrent : b.order ⟨s, hsCurrent⟩ = R + 1)
    (i : Fin (n + 2 - s)) :
    ((b.lemma714InitialBinary S).lemma714RescaledBinary).order 1 ≤
      (b.lemma714TypeIIRightSuffix S s D.two_le hsCurrent U).order
        (Fin.rev ⟨i.val, by omega⟩) := by
  let j : Fin (n + 3 - s) := Fin.rev ⟨i.val, by omega⟩
  have hjPos : 0 < j.val := by
    simp only [j, Fin.rev]
    omega
  have hjBound : s + j.val < n + 3 := by
    have := j.isLt
    omega
  have hbinary :
      ((b.lemma714InitialBinary S).lemma714RescaledBinary).order 1 =
        R - 2 * (ramificationIndex K : Int) + 2 := by
    rw [lemma714RescaledBinary_order]
    have hinitial : (b.lemma714InitialBinary S).order 1 =
        b.order ⟨1, by omega⟩ := by
      calc
        (b.lemma714InitialBinary S).order 1 =
            b.order (S.left.sourceIndex 1) := S.left.order_eq 1
        _ = b.order ⟨1, by omega⟩ := by
          congr 1
    rw [hinitial, hsecond]
  rw [hbinary, b.lemma714TypeIIRightSuffix_order S s D.two_le hsCurrent U]
  change R - 2 * (ramificationIndex K : Int) + 2 ≤
    b.order ⟨s + j.val, hjBound⟩
  rcases Nat.even_or_odd j.val with hjEven | hjOdd
  · have hmono := b.orderSequence.entryOrZero_le_of_evenGap
      s (s + j.val) (by omega) hjBound (by
        simpa only [Nat.add_sub_cancel_left] using hjEven)
    rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence hsCurrent,
      BeliOrderSequence.entryOrZero_of_lt b.orderSequence hjBound] at hmono
    change b.order ⟨s, hsCurrent⟩ ≤
      b.order ⟨s + j.val, hjBound⟩ at hmono
    rw [hcurrent] at hmono
    have hePos := ramificationIndex_pos (K := K)
    omega
  · rcases hjOdd with ⟨k, hk⟩
    have hstop : R - 2 * (ramificationIndex K : Int) + 2 ≤
        b.order ⟨s + 1, by omega⟩ :=
      b.lemma714_stopOrder_ge R s D (by omega)
    have hgapEven : Even ((s + j.val) - (s + 1)) := by
      refine ⟨k, ?_⟩
      omega
    have hmono := b.orderSequence.entryOrZero_le_of_evenGap
      (s + 1) (s + j.val) (by omega) hjBound hgapEven
    rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence (by omega),
      BeliOrderSequence.entryOrZero_of_lt b.orderSequence hjBound] at hmono
    change b.order ⟨s + 1, by omega⟩ ≤
      b.order ⟨s + j.val, hjBound⟩ at hmono
    exact hstop.trans hmono

/-- The order comparison required to run the inner right-end construction
against the binary reverse dual. -/
theorem lemma714TypeIIInnerSeed_orderBound
    (hsecond : b.order ⟨1, by omega⟩ =
      R - 2 * (ramificationIndex K : Int))
    (hcurrent : b.order ⟨s, hsCurrent⟩ = R + 1) :
    ∀ i : Fin (n + 2 - s),
      (b.lemma714TypeIIRightReverseDualForStop R s D hsCurrent S U).order
          ((b.lemma714TypeIIInnerSeed R s D hsCurrent S U block).sourceIndex i) ≤
        (b.lemma714TypeIIRescaledBinaryReverseDual S).order 0 := by
  intro i
  let iRight : Fin (n + 3 - s) := ⟨i.val, by omega⟩
  have hsource :
      (b.lemma714TypeIIRightReverseDualForStop R s D hsCurrent S U).order
          ((b.lemma714TypeIIInnerSeed R s D hsCurrent S U block).sourceIndex i) =
        (b.lemma714TypeIIRightReverseDual R s D hsCurrent S U).order
          iRight := by
    simp only [lemma714TypeIIRightReverseDualForStop,
      GoodBONG.order_castLength]
    congr 1
  calc
    _ = -(b.lemma714TypeIIRightSuffix S s D.two_le hsCurrent U).order
          (Fin.rev iRight) := by
      rw [hsource,
        b.lemma714TypeIIRightReverseDual_order R s D hsCurrent S U]
    _ ≤ -((b.lemma714InitialBinary S).lemma714RescaledBinary).order 1 := by
      exact neg_le_neg
        (b.lemma714TypeIIRescaledBinary_second_le_rightSuffix R s D
          hsCurrent S U hsecond hcurrent i)
    _ = (b.lemma714TypeIIRescaledBinaryReverseDual S).order 0 := by
      rw [b.lemma714TypeIIRescaledBinaryReverseDual_order S]
      congr 2

/-- The uncast BONG produced by the inner right-end construction. -/
noncomputable def lemma714TypeIIInnerProductRaw
    (hsecond : b.order ⟨1, by omega⟩ =
      R - 2 * (ramificationIndex K : Int))
    (hcurrent : b.order ⟨s, hsCurrent⟩ = R + 1) :=
  (b.lemma714TypeIIInnerSeed R s D hsCurrent S U block).result
    (b.lemma714TypeIIRescaledBinaryReverseDual S).toBONG
    (b.lemma714TypeIIInnerSeed_orderBound R s D hsCurrent S U
      block hsecond hcurrent)

/-- The inner product BONG with its length normalized to the stopping-segment
length. -/
noncomputable def lemma714TypeIIInnerProductBONG
    (hsecond : b.order ⟨1, by omega⟩ =
      R - 2 * (ramificationIndex K : Int))
    (hcurrent : b.order ⟨s, hsCurrent⟩ = R + 1) :
    BONG (U.right.carrier × S.left.carrier)
      (((q.restrict S.right.carrier S.right.nondegenerate).restrict
          U.right.carrier U.right.nondegenerate).orthogonalSum
        (q.restrict S.left.carrier S.left.nondegenerate))
      (Lattice.product
        (Lattice.dualLattice
          ((q.restrict S.right.carrier S.right.nondegenerate).restrict
            U.right.carrier U.right.nondegenerate) U.right.lattice)
        (Lattice.dualLattice
          (q.restrict S.left.carrier S.left.nondegenerate)
          (Lattice.rescale (uniformizerUnit K) S.left.lattice)))
      (lemma714TypeIIBaseLength n s) :=
  (b.lemma714TypeIIInnerProductRaw R s D hsCurrent S U block
    hsecond hcurrent).castLength (by
      unfold lemma714TypeIIBaseLength lemma714TypeIIBaseTail
      omega)

/-- After the inner construction is reversed, its initial three vectors are
the original exceptional block, with the unary coordinate first and the
binary coordinate second. -/
theorem lemma714TypeIIInnerProductRaw_reverseDualVector_block
    (hsecond : b.order ⟨1, by omega⟩ =
      R - 2 * (ramificationIndex K : Int))
    (hcurrent : b.order ⟨s, hsCurrent⟩ = R + 1)
    (i : Fin 3) :
    (b.lemma714TypeIIInnerProductRaw R s D hsCurrent S U block
      hsecond hcurrent).reverseDualVector ⟨i.val, by omega⟩ =
      (b.lemma714TypeIILineToRight S s D.two_le hsCurrent U
          (block.toBONG.ambientVector i).2,
        (block.toBONG.ambientVector i).1) := by
  let seed := b.lemma714TypeIIInnerSeed R s D hsCurrent S U block
  let right := (b.lemma714TypeIIRescaledBinaryReverseDual S).toBONG
  let horder := b.lemma714TypeIIInnerSeed_orderBound R s D hsCurrent S
    U block hsecond hcurrent
  let source :=
    (b.lemma714TypeIIRightReverseDualForStop R s D hsCurrent S U).toBONG
  let lineDual :=
    (b.lemma714TypeIILineReverseDual R s D hsCurrent S).toBONG
  let blockDual :=
    (lemma714TypeIIBlockReverseDual (b := b) (R := R) (s := s)
      (D := D) (hsCurrent := hsCurrent) (S := S) (block := block)).toBONG
  let hlast := b.lemma714TypeIIRightReverseDualForStop_lastValue R s D
    hsCurrent S U
  calc
    _ = seed.baseReverseDualVector i :=
      seed.reverseDualVector_result_block right horder i
    _ =
        (BONG.reverseDualProductTerminalEmbedding source lineDual right
            blockDual hlast (blockDual.reverseDualVector i).2,
          (blockDual.reverseDualVector i).1) := by
      exact BONG.reverseDualProductPrefixSeed_baseReverseDualVector
        source lineDual right blockDual hlast i
    _ = _ := by
      have hblockDouble : blockDual.reverseDualVector i =
          block.toBONG.ambientVector i :=
        BONG.reverseDualVector_eq_ambientVector_of_ambientVector_eq
          block.toBONG blockDual
          (b.lemma714TypeIIBlockReverseDual_ambientVector R s D hsCurrent
            S block) i
      rw [hblockDouble]
      exact Prod.ext
        (b.lemma714TypeIIInnerTerminalEmbedding_apply R s D hsCurrent S
          U block (block.toBONG.ambientVector i).2)
        rfl

/-- The remaining reversed vectors are the non-head original right-suffix
vectors, with zero binary coordinate. -/
theorem lemma714TypeIIInnerProductRaw_reverseDualVector_suffix
    (hsecond : b.order ⟨1, by omega⟩ =
      R - 2 * (ramificationIndex K : Int))
    (hcurrent : b.order ⟨s, hsCurrent⟩ = R + 1)
    (j : Fin (n + 2 - s)) :
    (b.lemma714TypeIIInnerProductRaw R s D hsCurrent S U block
      hsecond hcurrent).reverseDualVector ⟨3 + j.val, by omega⟩ =
      ((b.lemma714TypeIIRightSuffix S s D.two_le hsCurrent U).toBONG.ambientVector
          ⟨j.val + 1, by omega⟩,
        0) := by
  let seed := b.lemma714TypeIIInnerSeed R s D hsCurrent S U block
  let right := (b.lemma714TypeIIRescaledBinaryReverseDual S).toBONG
  let horder := b.lemma714TypeIIInnerSeed_orderBound R s D hsCurrent S
    U block hsecond hcurrent
  let sourceDual :=
    (b.lemma714TypeIIRightReverseDual R s D hsCurrent S U).toBONG
  calc
    _ =
        ((b.lemma714TypeIIRightReverseDualForStop R s D hsCurrent S U).toBONG.reverseDualVector
            ⟨j.val + 1, by omega⟩,
          0) :=
      seed.reverseDualVector_result_suffix right horder j
    _ = (sourceDual.reverseDualVector ⟨j.val + 1, by omega⟩, 0) := by
      rw [lemma714TypeIIRightReverseDualForStop,
        GoodBONG.reverseDualVector_castLength]
    _ = _ := by
      rw [BONG.reverseDualVector_eq_ambientVector_of_ambientVector_eq
        (b.lemma714TypeIIRightSuffix S s D.two_le hsCurrent U).toBONG
        sourceDual
        (b.lemma714TypeIIRightReverseDual_ambientVector R s D hsCurrent
          S U)]

/-- Length normalization preserves the initial double-reversed exceptional
block formula. -/
theorem lemma714TypeIIInnerProductBONG_reverseDualVector_block
    (hsecond : b.order ⟨1, by omega⟩ =
      R - 2 * (ramificationIndex K : Int))
    (hcurrent : b.order ⟨s, hsCurrent⟩ = R + 1)
    (i : Fin 3) :
    (b.lemma714TypeIIInnerProductBONG R s D hsCurrent S U block
      hsecond hcurrent).reverseDualVector
        ⟨i.val, by
          unfold lemma714TypeIIBaseLength lemma714TypeIIBaseTail
          omega⟩ =
      (b.lemma714TypeIILineToRight S s D.two_le hsCurrent U
          (block.toBONG.ambientVector i).2,
        (block.toBONG.ambientVector i).1) := by
  rw [lemma714TypeIIInnerProductBONG, BONG.reverseDualVector_castLength]
  exact b.lemma714TypeIIInnerProductRaw_reverseDualVector_block R s D
    hsCurrent S U block hsecond hcurrent i

/-- Length normalization preserves the non-head right-suffix formula. -/
theorem lemma714TypeIIInnerProductBONG_reverseDualVector_suffix
    (hsecond : b.order ⟨1, by omega⟩ =
      R - 2 * (ramificationIndex K : Int))
    (hcurrent : b.order ⟨s, hsCurrent⟩ = R + 1)
    (j : Fin (n + 2 - s)) :
    (b.lemma714TypeIIInnerProductBONG R s D hsCurrent S U block
      hsecond hcurrent).reverseDualVector
        ⟨3 + j.val, by
          unfold lemma714TypeIIBaseLength lemma714TypeIIBaseTail
          omega⟩ =
      ((b.lemma714TypeIIRightSuffix S s D.two_le hsCurrent U).toBONG.ambientVector
          ⟨j.val + 1, by omega⟩,
        0) := by
  rw [lemma714TypeIIInnerProductBONG, BONG.reverseDualVector_castLength]
  exact b.lemma714TypeIIInnerProductRaw_reverseDualVector_suffix R s D
    hsCurrent S U block hsecond hcurrent j

/-- The uncast inner product retains the full chosen right-reverse-dual
prefix. -/
@[simp]
theorem lemma714TypeIIInnerProductRaw_value_prefix
    (hsecond : b.order ⟨1, by omega⟩ =
      R - 2 * (ramificationIndex K : Int))
    (hcurrent : b.order ⟨s, hsCurrent⟩ = R + 1)
    (i : Fin (n + 2 - s)) :
    (b.lemma714TypeIIInnerProductRaw R s D hsCurrent S U block
      hsecond hcurrent).value (orthogonalProductLeftIndex 3 i) =
      (b.lemma714TypeIIRightReverseDual R s D hsCurrent S U).value
        ⟨i.val, by omega⟩ := by
  rw [lemma714TypeIIInnerProductRaw,
    OrthogonalPrefixSeed.value_result_left]
  change
    (b.lemma714TypeIIRightReverseDualForStop R s D hsCurrent S U).value
        ((b.lemma714TypeIIInnerSeed R s D hsCurrent S U block).sourceIndex i) =
      (b.lemma714TypeIIRightReverseDual R s D hsCurrent S U).value
        ⟨i.val, by omega⟩
  rw [b.lemma714TypeIIRightReverseDualForStop_value R s D hsCurrent
    S U]
  congr 1

/-- The uncast inner product ends with the three chosen exceptional-block
reverse-dual values. -/
@[simp]
theorem lemma714TypeIIInnerProductRaw_value_block
    (hsecond : b.order ⟨1, by omega⟩ =
      R - 2 * (ramificationIndex K : Int))
    (hcurrent : b.order ⟨s, hsCurrent⟩ = R + 1)
    (j : Fin 3) :
    (b.lemma714TypeIIInnerProductRaw R s D hsCurrent S U block
      hsecond hcurrent).value
        (orthogonalProductRightIndex (n + 2 - s) j) =
      (lemma714TypeIIBlockReverseDual (b := b) (R := R) (s := s)
        (D := D) (hsCurrent := hsCurrent) (S := S) (block := block)).value j := by
  rw [lemma714TypeIIInnerProductRaw,
    OrthogonalPrefixSeed.value_result_right,
    b.lemma714TypeIIInnerSeed_baseValue R s D hsCurrent S U block]

/-- The normalized inner product has the right-reverse-dual values on its
initial block. -/
@[simp]
theorem lemma714TypeIIInnerProductBONG_value_prefix
    (hsecond : b.order ⟨1, by omega⟩ =
      R - 2 * (ramificationIndex K : Int))
    (hcurrent : b.order ⟨s, hsCurrent⟩ = R + 1)
    (i : Fin (n + 2 - s)) :
    (b.lemma714TypeIIInnerProductBONG R s D hsCurrent S U block
      hsecond hcurrent).value
        ⟨i.val, by
          unfold lemma714TypeIIBaseLength lemma714TypeIIBaseTail
          omega⟩ =
      (b.lemma714TypeIIRightReverseDual R s D hsCurrent S U).value
        ⟨i.val, by omega⟩ := by
  rw [lemma714TypeIIInnerProductBONG, BONG.value_castLength]
  have hindex :
      (⟨i.val, by omega⟩ : Fin (3 + (n + 2 - s))) =
        orthogonalProductLeftIndex 3 i := by
    apply Fin.ext
    rfl
  rw [hindex,
    b.lemma714TypeIIInnerProductRaw_value_prefix R s D hsCurrent S U
      block hsecond hcurrent i]

/-- The normalized inner product has the exceptional-block reverse-dual
values on its final three entries. -/
@[simp]
theorem lemma714TypeIIInnerProductBONG_value_block
    (hsecond : b.order ⟨1, by omega⟩ =
      R - 2 * (ramificationIndex K : Int))
    (hcurrent : b.order ⟨s, hsCurrent⟩ = R + 1)
    (j : Fin 3) :
    (b.lemma714TypeIIInnerProductBONG R s D hsCurrent S U block
      hsecond hcurrent).value
        ⟨n + 2 - s + j.val, by
          unfold lemma714TypeIIBaseLength lemma714TypeIIBaseTail
          omega⟩ =
      (lemma714TypeIIBlockReverseDual (b := b) (R := R) (s := s)
        (D := D) (hsCurrent := hsCurrent) (S := S) (block := block)).value j := by
  rw [lemma714TypeIIInnerProductBONG, BONG.value_castLength]
  have hindex :
      (⟨n + 2 - s + j.val, by omega⟩ : Fin (3 + (n + 2 - s))) =
        orthogonalProductRightIndex (n + 2 - s) j := by
    apply Fin.ext
    rfl
  rw [hindex,
    b.lemma714TypeIIInnerProductRaw_value_block R s D hsCurrent S U
      block hsecond hcurrent j]

/-- The complete stopping reverse dual and the inner product BONG have the
same scalar value sequence. -/
theorem lemma714TypeIIStopReverseDual_value_eq_innerProduct
    {N : Lattice K (S.right.carrier × S.left.carrier)}
    (target : GoodBONG
      ((q.restrict S.right.carrier S.right.nondegenerate).orthogonalSum
        (q.restrict S.left.carrier S.left.nondegenerate)) N (n + 3))
    (htargetVectors : ∀ i, target.toBONG.ambientVector i =
      lemma714TypeIITargetVector b S s D.two_le hsCurrent block i)
    (hsecond : b.order ⟨1, by omega⟩ =
      R - 2 * (ramificationIndex K : Int))
    (hcurrent : b.order ⟨s, hsCurrent⟩ = R + 1)
    (i : Fin (lemma714TypeIIBaseLength n s)) :
    (b.lemma714TypeIIStopReverseDual R s D hsCurrent S hsFour U target).value i =
      (b.lemma714TypeIIInnerProductBONG R s D hsCurrent S U block
        hsecond hcurrent).value i := by
  have hlength : lemma714TypeIIBaseLength n s = (n + 2 - s) + 3 := by
    unfold lemma714TypeIIBaseLength lemma714TypeIIBaseTail
    omega
  have hiBound : i.val < (n + 2 - s) + 3 := by
    rw [← hlength]
    exact i.isLt
  by_cases hi : i.val < n + 2 - s
  · let j : Fin (n + 2 - s) := ⟨i.val, hi⟩
    have hindex : i =
        ⟨j.val, by
          unfold lemma714TypeIIBaseLength lemma714TypeIIBaseTail
          omega⟩ := by
      apply Fin.ext
      rfl
    rw [hindex,
      b.lemma714TypeIIStopReverseDual_value_prefix R s D hsCurrent S hsFour U
        block target htargetVectors j,
      b.lemma714TypeIIInnerProductBONG_value_prefix R s D hsCurrent S U
        block hsecond hcurrent j]
  · let j : Fin 3 := ⟨i.val - (n + 2 - s), by
      omega⟩
    have hindex : i =
        ⟨n + 2 - s + j.val, by
          rw [hlength]
          omega⟩ := by
      apply Fin.ext
      simp only [j]
      omega
    rw [hindex,
      b.lemma714TypeIIStopReverseDual_value_block R s D hsCurrent S hsFour U
        block target htargetVectors j,
      b.lemma714TypeIIInnerProductBONG_value_block R s D hsCurrent S U
        block hsecond hcurrent j]

/-- The non-circular inner conclusion of the Type-II reverse-dual argument:
the dual of the complete stopping segment is isometric to the product of the
right-suffix dual and the rescaled-binary dual. -/
noncomputable def lemma714TypeIIStopDualProductIsometry
    {N : Lattice K (S.right.carrier × S.left.carrier)}
    (target : GoodBONG
      ((q.restrict S.right.carrier S.right.nondegenerate).orthogonalSum
        (q.restrict S.left.carrier S.left.nondegenerate)) N (n + 3))
    (htargetVectors : ∀ i, target.toBONG.ambientVector i =
      lemma714TypeIITargetVector b S s D.two_le hsCurrent block i)
    (hsecond : b.order ⟨1, by omega⟩ =
      R - 2 * (ramificationIndex K : Int))
    (hcurrent : b.order ⟨s, hsCurrent⟩ = R + 1) :=
  (b.lemma714TypeIIStopReverseDual R s D hsCurrent S hsFour U target).toBONG
    |>.latticeIsometryOfValueEq
      (b.lemma714TypeIIInnerProductBONG R s D hsCurrent S U block
        hsecond hcurrent)
      (b.lemma714TypeIIStopReverseDual_value_eq_innerProduct R s D hsCurrent
        S hsFour U block target htargetVectors hsecond hcurrent)

/-- Dualize the inner isometry, exchange its two factors, and use integral
double-duality.  The result is the concrete paper replacement from the
stopping segment to `πJ ⊥ rightSuffix`. -/
noncomputable def lemma714TypeIIStopProductIsometry
    {N : Lattice K (S.right.carrier × S.left.carrier)}
    (target : GoodBONG
      ((q.restrict S.right.carrier S.right.nondegenerate).orthogonalSum
        (q.restrict S.left.carrier S.left.nondegenerate)) N (n + 3))
    (htargetVectors : ∀ i, target.toBONG.ambientVector i =
      lemma714TypeIITargetVector b S s D.two_le hsCurrent block i)
    (hsecond : b.order ⟨1, by omega⟩ =
      R - 2 * (ramificationIndex K : Int))
    (hcurrent : b.order ⟨s, hsCurrent⟩ = R + 1) := by
  let segment := b.lemma714TypeIIStopSegment R s D hsCurrent S hsFour U
    target
  let stopForm :=
    (((((q.restrict S.right.carrier S.right.nondegenerate).restrict
            U.left.carrier U.left.nondegenerate).orthogonalSum
          (q.restrict S.left.carrier S.left.nondegenerate)).orthogonalSum
        ((q.restrict S.right.carrier S.right.nondegenerate).restrict
          U.right.carrier U.right.nondegenerate))).restrict
      segment.carrier segment.nondegenerate
  let binaryForm := q.restrict S.left.carrier S.left.nondegenerate
  let rightForm :=
    (q.restrict S.right.carrier S.right.nondegenerate).restrict
      U.right.carrier U.right.nondegenerate
  let f := b.lemma714TypeIIStopDualProductIsometry R s D hsCurrent S hsFour
    U block target htargetVectors hsecond hcurrent
  let reflectStop :=
    Lattice.Isometry.ofLatticeEq stopForm
      (Lattice.dualLattice_dualLattice stopForm segment.lattice).symm
  have hfactor :
      Lattice.product
          (Lattice.dualLattice binaryForm
            (Lattice.dualLattice binaryForm
              (Lattice.rescale (uniformizerUnit K) S.left.lattice)))
          (Lattice.dualLattice rightForm
            (Lattice.dualLattice rightForm U.right.lattice)) =
        Lattice.product
          (Lattice.rescale (uniformizerUnit K) S.left.lattice)
          U.right.lattice := by
    rw [Lattice.dualLattice_dualLattice,
      Lattice.dualLattice_dualLattice]
  let reflectFactors := Lattice.Isometry.ofLatticeEq
    (binaryForm.orthogonalSum rightForm) hfactor
  exact (reflectStop.trans f.swappedDualOrthogonalProduct).trans
    reflectFactors

/-- The concrete replacement has the expected underlying coordinate map:
apply the inner dual isometry and exchange its two factors. -/
@[simp]
theorem lemma714TypeIIStopProductIsometry_apply
    {N : Lattice K (S.right.carrier × S.left.carrier)}
    (target : GoodBONG
      ((q.restrict S.right.carrier S.right.nondegenerate).orthogonalSum
        (q.restrict S.left.carrier S.left.nondegenerate)) N (n + 3))
    (htargetVectors : ∀ i, target.toBONG.ambientVector i =
      lemma714TypeIITargetVector b S s D.two_le hsCurrent block i)
    (hsecond : b.order ⟨1, by omega⟩ =
      R - 2 * (ramificationIndex K : Int))
    (hcurrent : b.order ⟨s, hsCurrent⟩ = R + 1)
    (x : (b.lemma714TypeIIStopSegment R s D hsCurrent S hsFour U
      target).carrier) :
    (b.lemma714TypeIIStopProductIsometry R s D hsCurrent S hsFour U block
      target htargetVectors hsecond hcurrent).toLinearEquiv x =
      (((b.lemma714TypeIIStopDualProductIsometry R s D hsCurrent S hsFour U
          block target htargetVectors hsecond hcurrent).toLinearEquiv x).2,
        ((b.lemma714TypeIIStopDualProductIsometry R s D hsCurrent S hsFour U
          block target htargetVectors hsecond hcurrent).toLinearEquiv x).1) := by
  simp [lemma714TypeIIStopProductIsometry, Lattice.Isometry.trans,
    LinearEquiv.trans_apply]

/-- The dual value-isometry carries the reverse-dual vectors of the complete
stopping dual to those of the inner product. -/
theorem lemma714TypeIIStopDualProductIsometry_reverseDualVector
    {N : Lattice K (S.right.carrier × S.left.carrier)}
    (target : GoodBONG
      ((q.restrict S.right.carrier S.right.nondegenerate).orthogonalSum
        (q.restrict S.left.carrier S.left.nondegenerate)) N (n + 3))
    (htargetVectors : ∀ i, target.toBONG.ambientVector i =
      lemma714TypeIITargetVector b S s D.two_le hsCurrent block i)
    (hsecond : b.order ⟨1, by omega⟩ =
      R - 2 * (ramificationIndex K : Int))
    (hcurrent : b.order ⟨s, hsCurrent⟩ = R + 1)
    (i : Fin (lemma714TypeIIBaseLength n s)) :
    (b.lemma714TypeIIStopDualProductIsometry R s D hsCurrent S hsFour U
      block target htargetVectors hsecond hcurrent).toLinearEquiv
        ((b.lemma714TypeIIStopReverseDual R s D hsCurrent S hsFour U
          target).toBONG.reverseDualVector i) =
      (b.lemma714TypeIIInnerProductBONG R s D hsCurrent S U block
        hsecond hcurrent).reverseDualVector i := by
  apply Lattice.Isometry.map_reverseDualVector_of_ambientVector_eq
    (b.lemma714TypeIIStopDualProductIsometry R s D hsCurrent S hsFour U
      block target htargetVectors hsecond hcurrent)
    (b.lemma714TypeIIStopReverseDual R s D hsCurrent S hsFour U target).toBONG
    (b.lemma714TypeIIInnerProductBONG R s D hsCurrent S U block
      hsecond hcurrent)
  intro j
  exact BONG.latticeIsometryOfValueEq_apply_ambientVector _ _ _ j

set_option maxHeartbeats 1000000 in
/-- On the exceptional ternary block, the concrete replacement is exactly
the block vector written in the factor order `πJ ⊥ rightSuffix`. -/
theorem lemma714TypeIIStopProductIsometry_apply_block
    {N : Lattice K (S.right.carrier × S.left.carrier)}
    (target : GoodBONG
      ((q.restrict S.right.carrier S.right.nondegenerate).orthogonalSum
        (q.restrict S.left.carrier S.left.nondegenerate)) N (n + 3))
    (htargetVectors : ∀ i, target.toBONG.ambientVector i =
      lemma714TypeIITargetVector b S s D.two_le hsCurrent block i)
    (hsecond : b.order ⟨1, by omega⟩ =
      R - 2 * (ramificationIndex K : Int))
    (hcurrent : b.order ⟨s, hsCurrent⟩ = R + 1)
    (i : Fin 3) :
    (b.lemma714TypeIIStopProductIsometry R s D hsCurrent S hsFour U block
      target htargetVectors hsecond hcurrent).toLinearEquiv
        ((b.lemma714TypeIIStopSegment R s D hsCurrent S hsFour U
          target).bong.ambientVector
            ⟨i.val, by
              unfold lemma714TypeIIBaseLength lemma714TypeIIBaseTail
              omega⟩) =
      ((block.toBONG.ambientVector i).1,
        b.lemma714TypeIILineToRight S s D.two_le hsCurrent U
          (block.toBONG.ambientVector i).2) := by
  let stopIndex : Fin (lemma714TypeIIBaseLength n s) :=
    ⟨i.val, by
      unfold lemma714TypeIIBaseLength lemma714TypeIIBaseTail
      omega⟩
  have hstopDouble :
      (b.lemma714TypeIIStopReverseDual R s D hsCurrent S hsFour U
        target).toBONG.reverseDualVector stopIndex =
      (b.lemma714TypeIIStopSegment R s D hsCurrent S hsFour U
        target).bong.ambientVector stopIndex :=
    BONG.reverseDualVector_eq_ambientVector_of_ambientVector_eq
      (b.lemma714TypeIIStopGoodBONG R s D hsCurrent S hsFour U target).toBONG
      (b.lemma714TypeIIStopReverseDual R s D hsCurrent S hsFour U target).toBONG
      (b.lemma714TypeIIStopReverseDual_ambientVector R s D hsCurrent S
        hsFour U target) stopIndex
  change
    (b.lemma714TypeIIStopProductIsometry R s D hsCurrent S hsFour U block
      target htargetVectors hsecond hcurrent).toLinearEquiv
        ((b.lemma714TypeIIStopSegment R s D hsCurrent S hsFour U
          target).bong.ambientVector stopIndex) = _
  calc
    _ = (b.lemma714TypeIIStopProductIsometry R s D hsCurrent S hsFour U
          block target htargetVectors hsecond hcurrent).toLinearEquiv
        ((b.lemma714TypeIIStopReverseDual R s D hsCurrent S hsFour U
          target).toBONG.reverseDualVector stopIndex) :=
      congrArg _ hstopDouble.symm
    _ = _ := by
      rw [b.lemma714TypeIIStopProductIsometry_apply R s D hsCurrent S
        hsFour U block target htargetVectors hsecond hcurrent,
        b.lemma714TypeIIStopDualProductIsometry_reverseDualVector R s D
          hsCurrent S hsFour U block target htargetVectors hsecond hcurrent
          stopIndex,
        b.lemma714TypeIIInnerProductBONG_reverseDualVector_block R s D
          hsCurrent S U block hsecond hcurrent i]

set_option maxHeartbeats 1000000 in
/-- On the unchanged suffix, the concrete replacement has zero binary
coordinate and the original non-head right-suffix vector. -/
theorem lemma714TypeIIStopProductIsometry_apply_suffix
    {N : Lattice K (S.right.carrier × S.left.carrier)}
    (target : GoodBONG
      ((q.restrict S.right.carrier S.right.nondegenerate).orthogonalSum
        (q.restrict S.left.carrier S.left.nondegenerate)) N (n + 3))
    (htargetVectors : ∀ i, target.toBONG.ambientVector i =
      lemma714TypeIITargetVector b S s D.two_le hsCurrent block i)
    (hsecond : b.order ⟨1, by omega⟩ =
      R - 2 * (ramificationIndex K : Int))
    (hcurrent : b.order ⟨s, hsCurrent⟩ = R + 1)
    (j : Fin (n + 2 - s)) :
    (b.lemma714TypeIIStopProductIsometry R s D hsCurrent S hsFour U block
      target htargetVectors hsecond hcurrent).toLinearEquiv
        ((b.lemma714TypeIIStopSegment R s D hsCurrent S hsFour U
          target).bong.ambientVector
            ⟨3 + j.val, by
              unfold lemma714TypeIIBaseLength lemma714TypeIIBaseTail
              omega⟩) =
      (0,
        (b.lemma714TypeIIRightSuffix S s D.two_le hsCurrent U).toBONG.ambientVector
          ⟨j.val + 1, by omega⟩) := by
  let stopIndex : Fin (lemma714TypeIIBaseLength n s) :=
    ⟨3 + j.val, by
      unfold lemma714TypeIIBaseLength lemma714TypeIIBaseTail
      omega⟩
  have hstopDouble :
      (b.lemma714TypeIIStopReverseDual R s D hsCurrent S hsFour U
        target).toBONG.reverseDualVector stopIndex =
      (b.lemma714TypeIIStopSegment R s D hsCurrent S hsFour U
        target).bong.ambientVector stopIndex :=
    BONG.reverseDualVector_eq_ambientVector_of_ambientVector_eq
      (b.lemma714TypeIIStopGoodBONG R s D hsCurrent S hsFour U target).toBONG
      (b.lemma714TypeIIStopReverseDual R s D hsCurrent S hsFour U target).toBONG
      (b.lemma714TypeIIStopReverseDual_ambientVector R s D hsCurrent S
        hsFour U target) stopIndex
  change
    (b.lemma714TypeIIStopProductIsometry R s D hsCurrent S hsFour U block
      target htargetVectors hsecond hcurrent).toLinearEquiv
        ((b.lemma714TypeIIStopSegment R s D hsCurrent S hsFour U
          target).bong.ambientVector stopIndex) = _
  calc
    _ = (b.lemma714TypeIIStopProductIsometry R s D hsCurrent S hsFour U
          block target htargetVectors hsecond hcurrent).toLinearEquiv
        ((b.lemma714TypeIIStopReverseDual R s D hsCurrent S hsFour U
          target).toBONG.reverseDualVector stopIndex) :=
      congrArg _ hstopDouble.symm
    _ = _ := by
      rw [b.lemma714TypeIIStopProductIsometry_apply R s D hsCurrent S
        hsFour U block target htargetVectors hsecond hcurrent,
        b.lemma714TypeIIStopDualProductIsometry_reverseDualVector R s D
          hsCurrent S hsFour U block target htargetVectors hsecond hcurrent
          stopIndex,
        b.lemma714TypeIIInnerProductBONG_reverseDualVector_suffix R s D
          hsCurrent S U block hsecond hcurrent j]

end TypeIIInnerSeed

end GoodBONG

end BONG

end Bong
