/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma710DualProduct
import Bong.Bong.ValueIsometry
import Bong.Lattice.OrthogonalProductIsometry

/-!
# Beli (2019), Lemma 7.10: arbitrary reverse-dual stopping blocks

This module generalizes the reverse-dual prefix seed from a binary external
factor to an external factor of arbitrary BONG length. It is the geometric
interface required by Corollary 7.13.
-/

namespace Bong

open Dyadic

namespace BONG

universe u x a b

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

private structure ArbitraryReverseDualProductPrefixSeedData
    {X : Type x} {A : Type a} {B : Type b}
    [AddCommGroup X] [Module K X]
    [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B]
    {sourceForm : QuadraticSpace K X}
    {lineForm : QuadraticSpace K A}
    {externalForm : QuadraticSpace K B}
    {sourceLattice : Lattice K X}
    {lineLattice : Lattice K A}
    {externalLattice : Lattice K B}
    {steps externalLength : Nat}
    (source : BONG X sourceForm sourceLattice (steps + 1))
    (lineDual : BONG A lineForm
      (Lattice.dualLattice lineForm lineLattice) 1)
    (blockDual : BONG (B × A) (externalForm.orthogonalSum lineForm)
      (Lattice.dualLattice (externalForm.orthogonalSum lineForm)
        (Lattice.product externalLattice lineLattice)) (externalLength + 1)) where
  seed : OrthogonalPrefixSeed externalForm
    (Lattice.dualLattice externalForm externalLattice) (externalLength + 1)
    (steps := steps) source
  terminal : A →ₗ[K] X
  terminal_ambientVector : terminal (lineDual.ambientVector 0) =
    source.ambientVector ⟨steps, by omega⟩
  baseValue_eq : ∀ j, seed.baseValue j = blockDual.value j
  baseAmbientVector_eq : ∀ j,
    seed.baseAmbientVector j =
      (terminal (blockDual.ambientVector j).2,
        (blockDual.ambientVector j).1)

private noncomputable def arbitraryReverseDualProductPrefixSeedData
    {X : Type x} {A : Type a} {B : Type b}
    [AddCommGroup X] [Module K X]
    [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B]
    {sourceForm : QuadraticSpace K X}
    {lineForm : QuadraticSpace K A}
    {externalForm : QuadraticSpace K B}
    {sourceLattice : Lattice K X}
    {lineLattice : Lattice K A}
    {externalLattice : Lattice K B}
    {steps externalLength : Nat}
    (source : BONG X sourceForm sourceLattice (steps + 1))
    (lineDual : BONG A lineForm
      (Lattice.dualLattice lineForm lineLattice) 1)
    (_externalDual : BONG B externalForm
      (Lattice.dualLattice externalForm externalLattice) externalLength)
    (blockDual : BONG (B × A) (externalForm.orthogonalSum lineForm)
      (Lattice.dualLattice (externalForm.orthogonalSum lineForm)
        (Lattice.product externalLattice lineLattice)) (externalLength + 1))
    (hlast : source.value ⟨steps, by omega⟩ = lineDual.value 0) :
    ArbitraryReverseDualProductPrefixSeedData source lineDual blockDual := by
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
        (q := externalForm) (r := lineForm)
        (L := externalLattice) (M := lineLattice)
      let swap := Lattice.orthogonalProductSwap
        (q := externalForm) (r := lineForm)
        (L := Lattice.dualLattice externalForm externalLattice)
        (M := Lattice.dualLattice lineForm lineLattice)
      let identifyLine := lineToSource.orthogonalProductBasic
        (Lattice.Isometry.refl externalForm
          (Lattice.dualLattice externalForm externalLattice))
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
                      (q := sourceForm) (r := externalForm)
                      (L := sourceLattice)
                      (M := Lattice.dualLattice externalForm externalLattice)
                      anisotropic).symm.toLinearEquiv
                        (tailData.seed.baseAmbientVector j) :
                    (sourceForm.orthogonalSum externalForm).vectorOrthogonal
                      (x, 0)) : X × B) = _
                rw [tailData.baseAmbientVector_eq j]
                rfl }

/-- Adjoin an external factor after all but the final vector of a
nonempty source BONG.  At the stopping point the supplied stopping BONG is
identified with the product of that final unary source lattice and the external
factor by reverse duality, factor exchange, and equality of the unary values.
-/
noncomputable def arbitraryReverseDualProductPrefixSeed
    {X : Type x} {A : Type a} {B : Type b}
    [AddCommGroup X] [Module K X]
    [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B]
    {sourceForm : QuadraticSpace K X}
    {lineForm : QuadraticSpace K A}
    {externalForm : QuadraticSpace K B}
    {sourceLattice : Lattice K X}
    {lineLattice : Lattice K A}
    {externalLattice : Lattice K B}
    {steps externalLength : Nat}
    (source : BONG X sourceForm sourceLattice (steps + 1))
    (lineDual : BONG A lineForm
      (Lattice.dualLattice lineForm lineLattice) 1)
    (externalDual : BONG B externalForm
      (Lattice.dualLattice externalForm externalLattice) externalLength)
    (blockDual : BONG (B × A) (externalForm.orthogonalSum lineForm)
      (Lattice.dualLattice (externalForm.orthogonalSum lineForm)
        (Lattice.product externalLattice lineLattice)) (externalLength + 1))
    (hlast : source.value ⟨steps, by omega⟩ = lineDual.value 0) :
    OrthogonalPrefixSeed externalForm
      (Lattice.dualLattice externalForm externalLattice) (externalLength + 1)
      (steps := steps) source :=
  (arbitraryReverseDualProductPrefixSeedData source lineDual externalDual blockDual hlast).seed

/-- The recursive prefix construction never changes the stopping-block scalar values
of the stopping reverse-dual block. -/
@[simp]
theorem arbitraryReverseDualProductPrefixSeed_baseValue
    {X : Type x} {A : Type a} {B : Type b}
    [AddCommGroup X] [Module K X]
    [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B]
    {sourceForm : QuadraticSpace K X}
    {lineForm : QuadraticSpace K A}
    {externalForm : QuadraticSpace K B}
    {sourceLattice : Lattice K X}
    {lineLattice : Lattice K A}
    {externalLattice : Lattice K B}
    {steps externalLength : Nat}
    (source : BONG X sourceForm sourceLattice (steps + 1))
    (lineDual : BONG A lineForm
      (Lattice.dualLattice lineForm lineLattice) 1)
    (externalDual : BONG B externalForm
      (Lattice.dualLattice externalForm externalLattice) externalLength)
    (blockDual : BONG (B × A) (externalForm.orthogonalSum lineForm)
      (Lattice.dualLattice (externalForm.orthogonalSum lineForm)
        (Lattice.product externalLattice lineLattice)) (externalLength + 1))
    (hlast : source.value ⟨steps, by omega⟩ = lineDual.value 0)
    (j : Fin (externalLength + 1)) :
    (arbitraryReverseDualProductPrefixSeed source lineDual externalDual blockDual hlast).baseValue j =
      blockDual.value j :=
  (arbitraryReverseDualProductPrefixSeedData source lineDual externalDual blockDual hlast).baseValue_eq j

/-- The terminal unary factor is embedded into the last source coordinate.
This linear map is the coordinate bridge used when the complete construction
is reversed a second time. -/
noncomputable def arbitraryReverseDualProductTerminalEmbedding
    {X : Type x} {A : Type a} {B : Type b}
    [AddCommGroup X] [Module K X]
    [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B]
    {sourceForm : QuadraticSpace K X}
    {lineForm : QuadraticSpace K A}
    {externalForm : QuadraticSpace K B}
    {sourceLattice : Lattice K X}
    {lineLattice : Lattice K A}
    {externalLattice : Lattice K B}
    {steps externalLength : Nat}
    (source : BONG X sourceForm sourceLattice (steps + 1))
    (lineDual : BONG A lineForm
      (Lattice.dualLattice lineForm lineLattice) 1)
    (externalDual : BONG B externalForm
      (Lattice.dualLattice externalForm externalLattice) externalLength)
    (blockDual : BONG (B × A) (externalForm.orthogonalSum lineForm)
      (Lattice.dualLattice (externalForm.orthogonalSum lineForm)
        (Lattice.product externalLattice lineLattice)) (externalLength + 1))
    (hlast : source.value ⟨steps, by omega⟩ = lineDual.value 0) :
    A →ₗ[K] X :=
  (arbitraryReverseDualProductPrefixSeedData source lineDual externalDual blockDual
    hlast).terminal

/-- The terminal embedding carries the unary reverse-dual BONG vector to
the last vector of the source BONG. -/
@[simp]
theorem arbitraryReverseDualProductTerminalEmbedding_ambientVector
    {X : Type x} {A : Type a} {B : Type b}
    [AddCommGroup X] [Module K X]
    [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B]
    {sourceForm : QuadraticSpace K X}
    {lineForm : QuadraticSpace K A}
    {externalForm : QuadraticSpace K B}
    {sourceLattice : Lattice K X}
    {lineLattice : Lattice K A}
    {externalLattice : Lattice K B}
    {steps externalLength : Nat}
    (source : BONG X sourceForm sourceLattice (steps + 1))
    (lineDual : BONG A lineForm
      (Lattice.dualLattice lineForm lineLattice) 1)
    (externalDual : BONG B externalForm
      (Lattice.dualLattice externalForm externalLattice) externalLength)
    (blockDual : BONG (B × A) (externalForm.orthogonalSum lineForm)
      (Lattice.dualLattice (externalForm.orthogonalSum lineForm)
        (Lattice.product externalLattice lineLattice)) (externalLength + 1))
    (hlast : source.value ⟨steps, by omega⟩ = lineDual.value 0) :
    arbitraryReverseDualProductTerminalEmbedding source lineDual externalDual blockDual
        hlast (lineDual.ambientVector 0) =
      source.ambientVector ⟨steps, by omega⟩ :=
  (arbitraryReverseDualProductPrefixSeedData source lineDual externalDual blockDual
    hlast).terminal_ambientVector

/-- The same terminal map also identifies the double-reversed unary vector
with the head of the double-reversed source. -/
theorem arbitraryReverseDualProductTerminalEmbedding_reverseDualVector
    {X : Type x} {A : Type a} {B : Type b}
    [AddCommGroup X] [Module K X]
    [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B]
    {sourceForm : QuadraticSpace K X}
    {lineForm : QuadraticSpace K A}
    {externalForm : QuadraticSpace K B}
    {sourceLattice : Lattice K X}
    {lineLattice : Lattice K A}
    {externalLattice : Lattice K B}
    {steps externalLength : Nat}
    (source : BONG X sourceForm sourceLattice (steps + 1))
    (lineDual : BONG A lineForm
      (Lattice.dualLattice lineForm lineLattice) 1)
    (externalDual : BONG B externalForm
      (Lattice.dualLattice externalForm externalLattice) externalLength)
    (blockDual : BONG (B × A) (externalForm.orthogonalSum lineForm)
      (Lattice.dualLattice (externalForm.orthogonalSum lineForm)
        (Lattice.product externalLattice lineLattice)) (externalLength + 1))
    (hlast : source.value ⟨steps, by omega⟩ = lineDual.value 0) :
    arbitraryReverseDualProductTerminalEmbedding source lineDual externalDual blockDual
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
  rw [arbitraryReverseDualProductTerminalEmbedding_ambientVector, ← hunit]

/-- The transported stopping vectors are the stopping-block vectors with
their unary coordinate placed in the terminal source line and their binary
coordinate unchanged. -/
@[simp]
theorem arbitraryReverseDualProductPrefixSeed_baseAmbientVector
    {X : Type x} {A : Type a} {B : Type b}
    [AddCommGroup X] [Module K X]
    [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B]
    {sourceForm : QuadraticSpace K X}
    {lineForm : QuadraticSpace K A}
    {externalForm : QuadraticSpace K B}
    {sourceLattice : Lattice K X}
    {lineLattice : Lattice K A}
    {externalLattice : Lattice K B}
    {steps externalLength : Nat}
    (source : BONG X sourceForm sourceLattice (steps + 1))
    (lineDual : BONG A lineForm
      (Lattice.dualLattice lineForm lineLattice) 1)
    (externalDual : BONG B externalForm
      (Lattice.dualLattice externalForm externalLattice) externalLength)
    (blockDual : BONG (B × A) (externalForm.orthogonalSum lineForm)
      (Lattice.dualLattice (externalForm.orthogonalSum lineForm)
        (Lattice.product externalLattice lineLattice)) (externalLength + 1))
    (hlast : source.value ⟨steps, by omega⟩ = lineDual.value 0)
    (j : Fin (externalLength + 1)) :
    (arbitraryReverseDualProductPrefixSeed source lineDual externalDual blockDual hlast).baseAmbientVector j =
      (arbitraryReverseDualProductTerminalEmbedding source lineDual externalDual blockDual
          hlast (blockDual.ambientVector j).2,
        (blockDual.ambientVector j).1) :=
  (arbitraryReverseDualProductPrefixSeedData source lineDual externalDual
    blockDual hlast).baseAmbientVector_eq j


end BONG

end Bong
