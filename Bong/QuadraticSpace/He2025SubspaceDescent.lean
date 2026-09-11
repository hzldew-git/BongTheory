/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.QuadraticSpace.LineOrthogonalSplit
import Bong.QuadraticSpace.RepresentationRange
import Bong.QuadraticSpace.ScalarExtension

/-!
# Subspace descent in He (2025), Lemma 2.2

This file proves the algebraic induction in the publisher's proof of Lemma
2.2.  The only arithmetic input left explicit is its one-dimensional case:
density of the number field in one finite completion together with openness
of the local square classes.  All higher-dimensional descent, orthogonal
splitting, scalar extension, and Witt cancellation are proved here.
-/

namespace Bong

namespace QuadraticSpace

universe u v w x

variable {F : Type u} {E : Type v}
  [Field F] [Field E] [CharZero F] [CharZero E] [Algebra F E]
  {V : Type w} [AddCommGroup V] [Module F V]
  {W : Type x} [AddCommGroup W] [Module E W]

/-- The one-dimensional arithmetic input in He (2025), Lemma 2.2.

For every finite-dimensional quadratic space over the smaller field, each
represented line after scalar extension is isometric to the scalar extension
of a line already represented over the smaller field. -/
def HasOneDimensionalSubspaceDescent : Prop :=
  ∀ {T : Type w} [AddCommGroup T] [Module F T]
    [FiniteDimensional F T] (q : QuadraticSpace F T) (A : Eˣ),
    (q.scalarExtension (E := E)).Represents (scaledLine A) →
      ∃ a : Fˣ, q.Represents (scaledLine a) ∧
        ((scaledLine a).scalarExtension (E := E)).IsIsometric
          (scaledLine A)

private def Representation.orthogonalSumForSubspaceDescent
    {S₁ T₁ S₂ T₂ : Type*}
    [AddCommGroup S₁] [Module F S₁]
    [AddCommGroup T₁] [Module F T₁]
    [AddCommGroup S₂] [Module F S₂]
    [AddCommGroup T₂] [Module F T₂]
    {q₁ : QuadraticSpace F S₁} {r₁ : QuadraticSpace F T₁}
    {q₂ : QuadraticSpace F S₂} {r₂ : QuadraticSpace F T₂}
    (f : Representation q₁ r₁) (g : Representation q₂ r₂) :
    Representation (q₁.orthogonalSum q₂) (r₁.orthogonalSum r₂) where
  toLinearMap :=
    { toFun := fun z ↦ (f.toLinearMap z.1, g.toLinearMap z.2)
      map_add' := by intro z z'; ext <;> simp
      map_smul' := by intro c z; ext <;> simp }
  injective := by
    intro z z' h
    apply Prod.ext
    · exact f.injective (congrArg Prod.fst h)
    · exact g.injective (congrArg Prod.snd h)
  map_bilin := by
    intro z z'
    change r₁.bilin (f.toLinearMap z.1) (f.toLinearMap z'.1) +
        r₂.bilin (g.toLinearMap z.2) (g.toLinearMap z'.2) =
      q₁.bilin z.1 z'.1 + q₂.bilin z.2 z'.2
    rw [f.map_bilin, g.map_bilin]

private def orthogonalSumInrRepresentation
    {T₁ T₂ : Type*} [AddCommGroup T₁] [Module F T₁]
    [AddCommGroup T₂] [Module F T₂]
    (q₁ : QuadraticSpace F T₁) (q₂ : QuadraticSpace F T₂) :
    Representation q₂ (q₁.orthogonalSum q₂) where
  toLinearMap :=
    { toFun := fun z ↦ (0, z)
      map_add' := by intro z z'; simp
      map_smul' := by intro c z; simp }
  injective := by
    intro z z' h
    exact congrArg Prod.snd h
  map_bilin := by
    intro z z'
    simp

private def emptyDiagonalRepresentation
    [FiniteDimensional F V] (q : QuadraticSpace F V) :
    Representation
      (finiteDiagonal (fun i : Fin 0 ↦ Fin.elim0 i)
        (fun i ↦ Fin.elim0 i)) q where
  toLinearMap := 0
  injective := by
    intro z z' _
    exact Subsingleton.elim z z'
  map_bilin := by
    intro z z'
    simp [finiteDiagonal_bilin_apply]

/- The inductive core of He (2025), Lemma 2.2 for a diagonal local
subspace.  The descended coefficient list has exactly the same length. -/
omit [CharZero F] in
theorem finiteDiagonalSubspaceDescent
    (hline : HasOneDimensionalSubspaceDescent.{u, v, w}
      (F := F) (E := E))
    [FiniteDimensional F V] {n : Nat}
    (q : QuadraticSpace F V) (A : Fin n → E)
    (hA : ∀ i, A i ≠ 0)
    (hrep : (q.scalarExtension (E := E)).Represents
      (finiteDiagonal A hA)) :
    ∃ (a : Fin n → F) (ha : ∀ i, a i ≠ 0),
      q.Represents (finiteDiagonal a ha) ∧
        ((finiteDiagonal a ha).scalarExtension (E := E)).IsIsometric
          (finiteDiagonal A hA) := by
  induction n generalizing V with
  | zero =>
      let a : Fin 0 → F := fun i ↦ Fin.elim0 i
      have ha : ∀ i, a i ≠ 0 := fun i ↦ Fin.elim0 i
      refine ⟨a, ha, ⟨emptyDiagonalRepresentation q⟩, ?_⟩
      let f := scalarExtensionFiniteDiagonalIsometry
        (E := E) a ha
      have hcoeff : (fun i ↦ algebraMap F E (a i)) = A :=
        Subsingleton.elim _ _
      subst A
      exact ⟨f⟩
  | succ n ih =>
      let tail : Fin n → E := Fin.init A
      have htail : ∀ i, tail i ≠ 0 := fun i ↦ hA i.castSucc
      let last : Eˣ := Units.mk0 (A (Fin.last n)) (hA (Fin.last n))
      let tailSpace := finiteDiagonal tail htail
      let lineSpace := scaledLine last
      have hcoeff : Fin.snoc tail (last : E) = A := by
        change Fin.snoc (Fin.init A) (A (Fin.last n)) = A
        exact Fin.snoc_init_self A
      have sourceSplit :
          Isometry (tailSpace.orthogonalSum lineSpace)
            (finiteDiagonal A hA) := by
        let raw :=
          fieldFiniteDiagonalScaledLineSnocIsometry tail htail last
        simpa only [tailSpace, lineSpace, hcoeff] using raw
      rcases hrep with ⟨totalRepresentation⟩
      have lineRep :
          (q.scalarExtension (E := E)).Represents lineSpace := by
        exact ⟨totalRepresentation.trans <|
          sourceSplit.toRepresentation.trans <|
            orthogonalSumInrRepresentation tailSpace lineSpace⟩
      obtain ⟨a, hlineRep, ⟨lineIso⟩⟩ :=
        hline (T := V) q last lineRep
      rcases hlineRep with ⟨lineRepresentation⟩
      let z : V := lineRepresentation.toLinearMap 1
      have hzValue : q.quadratic z = (a : F) := by
        change q.quadratic (lineRepresentation.toLinearMap 1) = (a : F)
        rw [lineRepresentation.map_quadratic,
          scaledLine_quadratic_apply]
        simp
      have hz : q.IsAnisotropic z := by
        rw [IsAnisotropic, hzValue]
        exact Units.ne_zero a
      let complement := q.orthogonalSpace z hz
      let split := scaledLineOrthogonalIsometry q z a hz hzValue
      let complementE := complement.scalarExtension (E := E)
      have targetSplit :
          Isometry (lineSpace.orthogonalSum complementE)
            (q.scalarExtension (E := E)) :=
        (lineIso.symm.fieldOrthogonalSum (Isometry.refl complementE)).trans <|
          (scalarExtensionOrthogonalSumIsometry
            (E := E) (scaledLine a) complement).symm.trans
              split.scalarExtension
      have sourceSplitSwapped :
          Isometry (lineSpace.orthogonalSum tailSpace)
            (finiteDiagonal A hA) :=
        (fieldOrthogonalSumSwap lineSpace tailSpace).trans sourceSplit
      have tailRep : complementE.Represents tailSpace := by
        apply fieldOrthogonalSumLeftCancelRepresents
          lineSpace tailSpace complementE
        exact ⟨targetSplit.symm.toRepresentation.trans <|
          totalRepresentation.trans sourceSplitSwapped.toRepresentation⟩
      obtain ⟨b, hb, hbRep, ⟨tailIso⟩⟩ :=
        ih complement tail htail tailRep
      let c : Fin (n + 1) → F := Fin.snoc b (a : F)
      have hc : ∀ i, c i ≠ 0 := by
        intro i
        refine Fin.lastCases ?_ (fun j ↦ ?_) i
        · dsimp only [c]
          rw [Fin.snoc_last]
          exact Units.ne_zero a
        · dsimp only [c]
          rw [Fin.snoc_castSucc]
          exact hb j
      let sourceF := finiteDiagonal b hb
      have sourceFSplit :
          Isometry (sourceF.orthogonalSum (scaledLine a))
            (finiteDiagonal c hc) := by
        exact fieldFiniteDiagonalScaledLineSnocIsometry b hb a
      rcases hbRep with ⟨tailRepresentation⟩
      have descendedRep : q.Represents (finiteDiagonal c hc) := by
        exact ⟨split.toRepresentation.trans <|
          (Representation.refl (scaledLine a)).orthogonalSumForSubspaceDescent
              tailRepresentation |>.trans <|
            (fieldOrthogonalSumSwap sourceF (scaledLine a)).toRepresentation.trans
              sourceFSplit.symm.toRepresentation⟩
      refine ⟨c, hc, descendedRep, ?_⟩
      exact ⟨sourceFSplit.symm.scalarExtension.trans <|
        (scalarExtensionOrthogonalSumIsometry
          (E := E) sourceF (scaledLine a)).trans <|
          (tailIso.fieldOrthogonalSum lineIso).trans sourceSplit⟩

/- He (2025), Lemma 2.2 in representation form: every nondegenerate local
subspace descends once the publisher's one-dimensional density argument is
available. -/
omit [CharZero F] in
theorem heADC2025Lemma22_representation
    (hline : HasOneDimensionalSubspaceDescent.{u, v, w}
      (F := F) (E := E))
    [FiniteDimensional F V] [FiniteDimensional E W]
    (q : QuadraticSpace F V) (r : QuadraticSpace E W)
    (hrep : (q.scalarExtension (E := E)).Represents r) :
    ∃ (a : Fin (Module.finrank E W) → F)
      (ha : ∀ i, a i ≠ 0),
      q.Represents (finiteDiagonal a ha) ∧
        ((finiteDiagonal a ha).scalarExtension (E := E)).IsIsometric r := by
  have diagonalRep :
      (q.scalarExtension (E := E)).Represents r.fieldDiagonalModel := by
    rcases hrep with ⟨f⟩
    exact ⟨f.trans r.fieldDiagonalizationIsometry.symm.toRepresentation⟩
  obtain ⟨a, ha, haRep, ⟨haIso⟩⟩ := finiteDiagonalSubspaceDescent
    hline q r.fieldDiagonalCoefficients
      r.fieldDiagonalCoefficients_ne_zero diagonalRep
  exact ⟨a, ha, haRep,
    ⟨haIso.trans r.fieldDiagonalizationIsometry.symm⟩⟩

/- Literal subspace form of He (2025), Lemma 2.2.  The returned submodule
is the actual range of the descended representation inside the original
global quadratic space. -/
omit [CharZero F] in
theorem heADC2025Lemma22_of_oneDimensionalDescent
    (hline : HasOneDimensionalSubspaceDescent.{u, v, w}
      (F := F) (E := E))
    [FiniteDimensional F V] [FiniteDimensional E W]
    (q : QuadraticSpace F V) (r : QuadraticSpace E W)
    (hrep : (q.scalarExtension (E := E)).Represents r) :
    ∃ (U : Submodule F V)
      (hU : (q.bilin.restrict U).Nondegenerate),
      ((q.restrict U hU).scalarExtension (E := E)).IsIsometric r := by
  obtain ⟨a, ha, haRep, ⟨haIso⟩⟩ :=
    heADC2025Lemma22_representation hline q r hrep
  rcases haRep with ⟨f⟩
  let U := LinearMap.range f.toLinearMap
  let hU := f.range_nondegenerate
  refine ⟨U, hU, ?_⟩
  exact ⟨f.rangeIsometry.scalarExtension.symm.trans haIso⟩

end QuadraticSpace

end Bong
