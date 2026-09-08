/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.QuadraticSpace.He2025SubspaceDescent
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# The topological base case in He (2025), Lemma 2.2

This file derives the one-dimensional descent premise from the two inputs
used in the publisher proof: density of the smaller field and openness of
the nonzero square classes.  For a number-field finite completion, mathlib
supplies the density input directly.  The remaining concrete obligation is
the openness of square classes in that completion.
-/

namespace Bong

namespace QuadraticSpace

open scoped NumberField Valued
open scoped Topology

universe u v w

variable {F : Type u} {E : Type v}
  [Field F] [Field E] [CharZero F] [CharZero E] [Algebra F E]

/-- Every nonzero square class is open in the field topology. -/
def HasOpenNonzeroSquareClasses [TopologicalSpace E] : Prop :=
  ∀ A : Eˣ,
    IsOpen {z : E | ∃ c : Eˣ, z = (A : E) * (c : E) ^ 2}

/-- Nonzero square classes are open in every complete nontrivially normed
field of characteristic zero. -/
theorem hasOpenNonzeroSquareClasses_of_complete
    {K : Type u} [NontriviallyNormedField K] [CompleteSpace K]
    [CharZero K] :
    HasOpenNonzeroSquareClasses (E := K) := by
  intro A
  let squareTranslate : K → K := fun x ↦ (A : K) * x ^ 2
  let nonzero : Set K := {0}ᶜ
  have hnonzeroOpen : IsOpen nonzero := isOpen_compl_singleton
  have himageOpen : IsOpen (squareTranslate '' nonzero) := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hxnhds : nonzero ∈ 𝓝 x := hnonzeroOpen.mem_nhds hx
    have hxNe : x ≠ 0 := by
      simpa only [nonzero, Set.mem_compl_iff, Set.mem_singleton_iff]
        using hx
    have hderivNe : (A : K) * ((2 : K) * x ^ (2 - 1)) ≠ 0 :=
      mul_ne_zero (Units.ne_zero A)
        (mul_ne_zero (OfNat.ofNat_ne_zero 2)
          (pow_ne_zero (2 - 1) hxNe))
    have hmap :
        Filter.map squareTranslate (𝓝 x) =
          𝓝 (squareTranslate x) := by
      simpa only [squareTranslate] using
        ((hasStrictDerivAt_pow 2 x).const_mul (A : K)).map_nhds_eq
          hderivNe
    rw [← hmap]
    change squareTranslate ⁻¹' (squareTranslate '' nonzero) ∈ 𝓝 x
    exact Filter.mem_of_superset hxnhds
      (Set.subset_preimage_image squareTranslate nonzero)
  have hsetEq :
      {z : K | ∃ c : Kˣ, z = (A : K) * (c : K) ^ 2} =
        squareTranslate '' nonzero := by
    ext z
    constructor
    · rintro ⟨c, rfl⟩
      refine ⟨(c : K), ?_, rfl⟩
      simpa only [nonzero, Set.mem_compl_iff, Set.mem_singleton_iff]
        using Units.ne_zero c
    · rintro ⟨x, hx, rfl⟩
      have hxNe : x ≠ 0 := by
        simpa only [nonzero, Set.mem_compl_iff, Set.mem_singleton_iff]
          using hx
      exact ⟨Units.mk0 x hxNe, rfl⟩
  rw [hsetEq]
  exact himageOpen

omit [CharZero F] [CharZero E] in
private theorem continuous_diagonalQuadratic
    [TopologicalSpace E] [IsTopologicalRing E]
    {n : Nat} (a : Fin n → E) :
    Continuous (diagonalQuadratic a) := by
  unfold diagonalQuadratic
  fun_prop

omit [CharZero F] [CharZero E] in
private theorem map_diagonalQuadratic
    {n : Nat} (a x : Fin n → F) :
    algebraMap F E (diagonalQuadratic a x) =
      diagonalQuadratic (fun i ↦ algebraMap F E (a i))
        (fun i ↦ algebraMap F E (x i)) := by
  simp [diagonalQuadratic, map_sum, map_mul, map_pow]

/- Density and openness of nonzero square classes imply the exact
one-dimensional descent premise used in He (2025), Lemma 2.2. -/
omit [CharZero E] in
theorem hasOneDimensionalSubspaceDescent_of_denseRange_of_openSquareClasses
    [TopologicalSpace E] [IsTopologicalRing E]
    (hdense : DenseRange (algebraMap F E))
    (hsquare : HasOpenNonzeroSquareClasses (E := E)) :
    HasOneDimensionalSubspaceDescent.{u, v, w} (F := F) (E := E) := by
  intro T _ _ _ q A hrep
  let coefficientsF := q.fieldDiagonalCoefficients
  let coefficientsE : Fin (Module.finrank F T) → E :=
    fun i ↦ algebraMap F E (coefficientsF i)
  have hcoefficientsF : ∀ i, coefficientsF i ≠ 0 :=
    q.fieldDiagonalCoefficients_ne_zero
  have hcoefficientsE : ∀ i, coefficientsE i ≠ 0 := by
    intro i
    exact (map_ne_zero (algebraMap F E)).mpr (hcoefficientsF i)
  let extensionToDiagonal :=
    q.fieldDiagonalizationIsometry.scalarExtension (E := E) |>.trans
      (scalarExtensionFiniteDiagonalIsometry
        (E := E) coefficientsF hcoefficientsF)
  rcases hrep with ⟨lineInExtension⟩
  let lineInDiagonal :=
    extensionToDiagonal.toRepresentation.trans lineInExtension
  let localVector : Fin (Module.finrank F T) → E :=
    lineInDiagonal.toLinearMap 1
  have hlocalValue :
      diagonalQuadratic coefficientsE localVector = (A : E) := by
    simpa only [coefficientsE, localVector,
      finiteDiagonal_quadratic_apply, scaledLine_quadratic_apply,
      one_pow, mul_one] using lineInDiagonal.map_quadratic 1
  let squareClass :=
    {z : E | ∃ c : Eˣ, z = (A : E) * (c : E) ^ 2}
  have hopen : IsOpen
      (diagonalQuadratic coefficientsE ⁻¹' squareClass) :=
    (hsquare A).preimage (continuous_diagonalQuadratic coefficientsE)
  have hnonempty :
      (diagonalQuadratic coefficientsE ⁻¹' squareClass).Nonempty := by
    refine ⟨localVector, ?_⟩
    change ∃ c : Eˣ,
      diagonalQuadratic coefficientsE localVector =
        (A : E) * (c : E) ^ 2
    exact ⟨1, by simpa using hlocalValue⟩
  let coordinateMap :
      (Fin (Module.finrank F T) → F) →
        (Fin (Module.finrank F T) → E) :=
    Pi.map (fun _ ↦ algebraMap F E)
  have hcoordinateDense : DenseRange coordinateMap := by
    exact DenseRange.piMap (fun _ ↦ hdense)
  obtain ⟨globalVector, hglobalVector⟩ :=
    hcoordinateDense.exists_mem_open hopen hnonempty
  change ∃ c : Eˣ,
    diagonalQuadratic coefficientsE (coordinateMap globalVector) =
      (A : E) * (c : E) ^ 2 at hglobalVector
  obtain ⟨c, hc⟩ := hglobalVector
  have hmapValue :
      algebraMap F E (diagonalQuadratic coefficientsF globalVector) =
        diagonalQuadratic coefficientsE (coordinateMap globalVector) := by
    rw [map_diagonalQuadratic]
    apply congrArg (diagonalQuadratic coefficientsE)
    funext i
    exact (Pi.map_apply (fun _ ↦ algebraMap F E) globalVector i).symm
  have hglobalValue : diagonalQuadratic coefficientsF globalVector ≠ 0 := by
    apply (map_ne_zero (algebraMap F E)).mp
    rw [hmapValue, hc]
    exact mul_ne_zero (Units.ne_zero A)
      (pow_ne_zero 2 (Units.ne_zero c))
  let a : Fˣ := Units.mk0
    (diagonalQuadratic coefficientsF globalVector) hglobalValue
  have hdiagonalRepresents :
      (finiteDiagonal coefficientsF hcoefficientsF).Represents
        (scaledLine a) :=
    fieldFiniteDiagonalRepresentsScaledLineOfValue
      coefficientsF hcoefficientsF a globalVector rfl
  have hqDiagonal :
      q.Represents (finiteDiagonal coefficientsF hcoefficientsF) :=
    ⟨q.fieldDiagonalizationIsometry.symm.toRepresentation⟩
  have hqRepresents : q.Represents (scaledLine a) :=
    hqDiagonal.trans hdiagonalRepresents
  let aE : Eˣ := Units.map (algebraMap F E).toMonoidHom a
  have haE : (aE : E) = (A : E) * (c : E) ^ 2 := by
    change algebraMap F E
      (diagonalQuadratic coefficientsF globalVector) =
        (A : E) * (c : E) ^ 2
    rw [hmapValue]
    exact hc
  exact ⟨a, hqRepresents,
    ⟨(scalarExtensionScaledLineIsometry (E := E) a).trans
      (fieldScaledLineIsometryOfEqMulSquare aE A c haE)⟩⟩

/-- Density for a number-field finite completion reduces the one-dimensional
descent premise to square-class openness. -/
theorem numberFieldFiniteCompletionHasOneDimensionalSubspaceDescent_of_openSquareClasses
    {K : Type u} [Field K] [NumberField K]
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hsquare : HasOpenNonzeroSquareClasses
      (E := p.adicCompletion K)) :
    HasOneDimensionalSubspaceDescent.{u, u, w}
      (F := K) (E := p.adicCompletion K) := by
  exact hasOneDimensionalSubspaceDescent_of_denseRange_of_openSquareClasses
    (F := K) (E := p.adicCompletion K)
    (p.denseRange_algebraMap K) hsquare

/-- The exact one-dimensional descent premise used in He (2025), Lemma 2.2,
for every number-field finite completion. -/
theorem numberFieldFiniteCompletionHasOneDimensionalSubspaceDescent
    {K : Type u} [Field K] [NumberField K]
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    HasOneDimensionalSubspaceDescent.{u, u, w}
      (F := K) (E := p.adicCompletion K) := by
  letI : CharZero (p.adicCompletion K) :=
    Algebra.charZero_of_charZero K (p.adicCompletion K)
  intro T _ _ _ q A hrep
  exact
    (numberFieldFiniteCompletionHasOneDimensionalSubspaceDescent_of_openSquareClasses
      p (hasOpenNonzeroSquareClasses_of_complete
        (K := p.adicCompletion K))) q A hrep

/-- He (2025), Lemma 2.2 for a number field and one of its finite-place
completions, in the publisher's literal subspace form. -/
theorem heADC2025Lemma22_numberFieldFiniteCompletion
    {K : Type u} [Field K] [NumberField K]
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    {V : Type v} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    {W : Type w} [AddCommGroup W]
    [Module (p.adicCompletion K) W]
    [FiniteDimensional (p.adicCompletion K) W]
    (q : QuadraticSpace K V)
    (r : QuadraticSpace (p.adicCompletion K) W)
    (hrep : (q.scalarExtension (E := p.adicCompletion K)).Represents r) :
    ∃ (U : Submodule K V)
      (hU : (q.bilin.restrict U).Nondegenerate),
      ((q.restrict U hU).scalarExtension
        (E := p.adicCompletion K)).IsIsometric r := by
  letI : CharZero (p.adicCompletion K) :=
    Algebra.charZero_of_charZero K (p.adicCompletion K)
  exact heADC2025Lemma22_of_oneDimensionalDescent
    (numberFieldFiniteCompletionHasOneDimensionalSubspaceDescent p)
    q r hrep

end QuadraticSpace

end Bong
