/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.HeHu2022Proposition37
import Bong.Bong.HeHu2022Proposition35iii
import Bong.Bong.HeHu2022Definition36
import Bong.Bong.BeliUniversalCorollary45
import Bong.Lattice.BinaryDeterminantHyperbolic
import Bong.Lattice.OMaximalRepresentation

/-!
# He--Hu (2024), Theorem 1.2

This file formalizes the explicit minimal testing family for local
`n`-universality.  The family is indexed by the two columns `N₁ⁿ(c)` and
`N₂ⁿ(c)` of Tables 1--2, with the unique undefined binary square-class
entry removed.  As in the paper, minimality is a statement about isometry
classes of lattices, not about duplicate presentations of the same class.

The proof combines Proposition 3.5(ii)--(iii), Proposition 3.7, O'Meara
82:18, and uniqueness of maximal lattices on a fixed local quadratic space.
The latter two inputs are exposed through
`Lattice.IsOMaximal.represents_iff_ambient`.
-/

namespace Bong

open Dyadic Module BONG.GoodBONG

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

namespace Lattice.QuadraticLatticeModel

/-- Ambient isometry of bundled quadratic lattices. -/
def IsAmbientlyIsometric
    (X Y : QuadraticLatticeModel (K := K)) : Prop := by
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  letI : AddCommGroup Y.Carrier := Y.addCommGroup
  letI : Module K Y.Carrier := Y.module
  exact X.form.IsIsometric Y.form

namespace IsAmbientlyIsometric

theorem refl (X : QuadraticLatticeModel (K := K)) :
    X.IsAmbientlyIsometric X := by
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  exact ⟨QuadraticSpace.Isometry.refl X.form⟩

theorem symm {X Y : QuadraticLatticeModel (K := K)}
    (h : X.IsAmbientlyIsometric Y) : Y.IsAmbientlyIsometric X := by
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  letI : AddCommGroup Y.Carrier := Y.addCommGroup
  letI : Module K Y.Carrier := Y.module
  rcases h with ⟨f⟩
  exact ⟨f.symm⟩

theorem trans {X Y Z : QuadraticLatticeModel (K := K)}
    (hXY : X.IsAmbientlyIsometric Y)
    (hYZ : Y.IsAmbientlyIsometric Z) : X.IsAmbientlyIsometric Z := by
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  letI : AddCommGroup Y.Carrier := Y.addCommGroup
  letI : Module K Y.Carrier := Y.module
  letI : AddCommGroup Z.Carrier := Z.addCommGroup
  letI : Module K Z.Carrier := Z.module
  rcases hXY with ⟨f⟩
  rcases hYZ with ⟨g⟩
  exact ⟨f.trans g⟩

end IsAmbientlyIsometric

/-- A family tests rank-`n` universality if an integral lattice representing
every member is `n`-universal. -/
def IsUniversalityTestingFamily {I : Type u}
    (family : I → QuadraticLatticeModel (K := K)) (n : Nat) : Prop :=
  ∀ M : QuadraticLatticeModel (K := K),
    M.IsIntegral → (∀ i, M.Represents (family i)) → M.IsNUniversal n

/-- Minimality of a testing family, with repeated presentations identified
by ambient isometry.  For every member there is an integral witness which
misses its isometry class and represents every other class in the family. -/
def IsMinimalUniversalityTestingFamily {I : Type u}
    (family : I → QuadraticLatticeModel (K := K)) (n : Nat) : Prop :=
  IsUniversalityTestingFamily family n ∧
    ∀ i, ∃ M : QuadraticLatticeModel (K := K),
      M.IsIntegral ∧ ¬ M.Represents (family i) ∧
        ∀ j, ¬ (family j).IsAmbientlyIsometric (family i) →
          M.Represents (family j)

end Lattice.QuadraticLatticeModel

/-- Indices of the even-rank Table 1 family. -/
inductive HeHuEvenTestingIndex (pairs : Nat) : Type u
  | first (c : Kˣ)
  | second (c : Kˣ) (defined : HeHuEvenSecondDefined pairs c)

/-- Indices of the odd-rank Table 1 family. -/
inductive HeHuOddTestingIndex (pairs : Nat) : Type u
  | first (c : Kˣ)
  | second (c : Kˣ)

namespace HeHuEvenTestingIndex

/-- The diagonal coefficient family attached to an even-rank table index. -/
noncomputable def coefficients {pairs : Nat} :
    HeHuEvenTestingIndex (K := K) pairs → Fin (2 * pairs + 2) → Kˣ
  | .first c => heHuEvenFirst pairs c
  | .second c hdefined => heHuEvenSecond pairs c hdefined

/-- The canonical maximal lattice attached to an even-rank table index. -/
noncomputable def model {pairs : Nat}
    (i : HeHuEvenTestingIndex (K := K) pairs) :
    Lattice.QuadraticLatticeModel (K := K) :=
  heHuOMaximalModel i.coefficients

/-- The `(n+2)`-dimensional exceptional target from Proposition 3.5(iii). -/
noncomputable def excludingTarget {pairs : Nat} :
    HeHuEvenTestingIndex (K := K) pairs → Fin ((2 * pairs + 2) + 2) → Kˣ
  | .first c =>
      heHuFinFamilyCast (by omega :
          2 * (pairs + 1) + 2 = (2 * pairs + 2) + 2)
        (heHuEvenSecondNext pairs c)
  | .second c _ =>
      heHuFinFamilyCast (by omega :
          2 * (pairs + 1) + 2 = (2 * pairs + 2) + 2)
        (heHuEvenFirst (pairs + 1) c)

@[simp] theorem model_rank {pairs : Nat}
    (i : HeHuEvenTestingIndex (K := K) pairs) :
    i.model.rank = 2 * pairs + 2 :=
  heHuOMaximalModel_rank _

theorem model_isOMaximal {pairs : Nat}
    (i : HeHuEvenTestingIndex (K := K) pairs) : i.model.IsOMaximal :=
  heHuOMaximalModel_isOMaximal _

/-- Proposition 3.5(iii) for either column of the even table. -/
theorem excludingTarget_exact {pairs : Nat}
    (i : HeHuEvenTestingIndex (K := K) pairs) :
    HeHuMissesExactly i.coefficients i.excludingTarget := by
  cases i with
  | first c =>
      simpa [coefficients, excludingTarget] using
        (heHu2022Proposition35iiiEvenFirst (K := K) pairs c).exactness
  | second c hdefined =>
      simpa [coefficients, excludingTarget] using
        (heHu2022Proposition35iiiEvenSecond
          (K := K) pairs c hdefined).exactness

end HeHuEvenTestingIndex

namespace HeHuOddTestingIndex

/-- The diagonal coefficient family attached to an odd-rank table index. -/
noncomputable def coefficients {pairs : Nat} :
    HeHuOddTestingIndex (K := K) pairs → Fin (2 * pairs + 3) → Kˣ
  | .first c => heHuOddFirst pairs c
  | .second c => heHuOddSecond pairs c

/-- The canonical maximal lattice attached to an odd-rank table index. -/
noncomputable def model {pairs : Nat}
    (i : HeHuOddTestingIndex (K := K) pairs) :
    Lattice.QuadraticLatticeModel (K := K) :=
  heHuOMaximalModel i.coefficients

/-- The `(n+2)`-dimensional exceptional target from Proposition 3.5(iii). -/
noncomputable def excludingTarget {pairs : Nat} :
    HeHuOddTestingIndex (K := K) pairs → Fin ((2 * pairs + 3) + 2) → Kˣ
  | .first c =>
      heHuFinFamilyCast (by omega :
          2 * (pairs + 1) + 3 = (2 * pairs + 3) + 2)
        (heHuOddSecond (pairs + 1) c)
  | .second c =>
      heHuFinFamilyCast (by omega :
          2 * (pairs + 1) + 3 = (2 * pairs + 3) + 2)
        (heHuOddFirst (pairs + 1) c)

@[simp] theorem model_rank {pairs : Nat}
    (i : HeHuOddTestingIndex (K := K) pairs) :
    i.model.rank = 2 * pairs + 3 :=
  heHuOMaximalModel_rank _

theorem model_isOMaximal {pairs : Nat}
    (i : HeHuOddTestingIndex (K := K) pairs) : i.model.IsOMaximal :=
  heHuOMaximalModel_isOMaximal _

/-- Proposition 3.5(iii) for either column of the odd table. -/
theorem excludingTarget_exact {pairs : Nat}
    (i : HeHuOddTestingIndex (K := K) pairs) :
    HeHuMissesExactly i.coefficients i.excludingTarget := by
  cases i with
  | first c =>
      simpa [coefficients, excludingTarget] using
        (heHu2022Proposition35iiiOddFirst (K := K) pairs c).exactness
  | second c =>
      simpa [coefficients, excludingTarget] using
        (heHu2022Proposition35iiiOddSecond (K := K) pairs c).exactness

end HeHuOddTestingIndex

namespace Lattice.QuadraticLatticeModel

/-- Canonical diagonal maximal models represent one another exactly when
their coefficient spaces are in the corresponding diagonal representation
relation. -/
theorem heHuOMaximalModel_represents_iff {m n : Nat}
    (target : Fin m → Kˣ) (source : Fin n → Kˣ) :
    (heHuOMaximalModel target).Represents (heHuOMaximalModel source) ↔
      DiagonalRepresents (diagonalUnitCoefficients source)
        (diagonalUnitCoefficients target) := by
  let T := heHuOMaximalModel target
  let S := heHuOMaximalModel source
  letI : AddCommGroup T.Carrier := T.addCommGroup
  letI : Module K T.Carrier := T.module
  letI : AddCommGroup S.Carrier := S.addCommGroup
  letI : Module K S.Carrier := S.module
  change Lattice.Represents T.form S.form T.lattice S.lattice ↔ _
  rw [(heHuOMaximalModel_isOMaximal target).represents_iff_ambient
    (heHuOMaximalModel_isOMaximal source)]
  exact QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
    source target

/-- Equal-rank canonical diagonal models are ambiently isometric whenever
the first coefficient family is diagonally represented by the second. -/
theorem heHuOMaximalModel_form_isIsometric_of_diagonalRepresents {n : Nat}
    (source target : Fin n → Kˣ)
    (hrep : DiagonalRepresents (diagonalUnitCoefficients source)
      (diagonalUnitCoefficients target)) :
    (heHuOMaximalModel source).IsAmbientlyIsometric
      (heHuOMaximalModel target) := by
  let S := heHuOMaximalModel source
  let T := heHuOMaximalModel target
  letI : AddCommGroup S.Carrier := S.addCommGroup
  letI : Module K S.Carrier := S.module
  letI : AddCommGroup T.Carrier := T.addCommGroup
  letI : Module K T.Carrier := T.module
  change S.form.IsIsometric T.form
  have hspace :=
    (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
      source target).2 hrep
  rcases hspace with ⟨f⟩
  exact ⟨f.toIsometryOfFinrankEq (by simp)⟩

/-- The diagonal coefficient family of a bundled lattice, transported to a
specified equal cardinality.  The wrapper keeps the bundled carrier's type
class fields internal. -/
noncomputable def diagonalUnitsCast
    (X : QuadraticLatticeModel (K := K)) (n : Nat)
    (hRank : X.rank = n) : Fin n → Kˣ := by
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  letI : Module.Finite K X.Carrier := X.lattice.moduleFinite
  exact heHuFinFamilyCast (by
    change finrank K X.Carrier = n at hRank
    exact hRank) X.form.diagonalUnits

/-- Diagonalizing a bundled lattice and transporting its coordinate type
identifies its ambient form with the canonical diagonal maximal model. -/
theorem ambientlyIsometric_heHuOMaximalModel_diagonalUnitsCast
    (X : QuadraticLatticeModel (K := K)) (n : Nat)
    (hRank : X.rank = n) :
    X.IsAmbientlyIsometric
      (heHuOMaximalModel (X.diagonalUnitsCast n hRank)) := by
  classical
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  letI : Module.Finite K X.Carrier := X.lattice.moduleFinite
  have hdim : finrank K X.Carrier = n := by
    change finrank K X.Carrier = n at hRank
    exact hRank
  let e : Fin n ≃ Fin (finrank K X.Carrier) := finCongr hdim.symm
  let reindex := QuadraticSpace.finiteDiagonalReindexIsometry
    (fun i ↦ (X.form.diagonalUnits i : K))
    (fun i ↦ Units.ne_zero (X.form.diagonalUnits i)) e
  let f := X.form.diagonalizationIsometry.trans reindex
  let T := heHuOMaximalModel (X.diagonalUnitsCast n hRank)
  letI : AddCommGroup T.Carrier := T.addCommGroup
  letI : Module K T.Carrier := T.module
  change X.form.IsIsometric T.form
  refine ⟨?_⟩
  change QuadraticSpace.Isometry X.form
    (BONG.coefficientDiagonalSpace
      (X.diagonalUnitsCast n hRank))
  simpa [f, reindex, T, BONG.coefficientDiagonalSpace,
    QuadraticSpace.diagonalModel, diagonalUnitCoefficients,
    diagonalUnitsCast, heHuFinFamilyCast, e] using f

/-- Proposition 3.5(ii): every even-rank ambient quadratic space occurs in
one of the two displayed table columns. -/
theorem exists_evenTestingIndex_ambientlyIsometric
    (pairs : Nat) (X : QuadraticLatticeModel (K := K))
    (hRank : X.rank = 2 * pairs + 2) :
    ∃ i : HeHuEvenTestingIndex (K := K) pairs,
      X.IsAmbientlyIsometric i.model := by
  let w := X.diagonalUnitsCast (2 * pairs + 2) hRank
  have hXw :=
    ambientlyIsometric_heHuOMaximalModel_diagonalUnitsCast
      X (2 * pairs + 2) hRank
  obtain ⟨c, hfirst | hsecond⟩ :=
    heHu2022Proposition35iiEven (K := K) pairs w
  · let i : HeHuEvenTestingIndex (K := K) pairs := .first c
    refine ⟨i, hXw.trans ?_⟩
    simpa only [i, HeHuEvenTestingIndex.model,
      HeHuEvenTestingIndex.coefficients, w] using
      heHuOMaximalModel_form_isIsometric_of_diagonalRepresents
        w (heHuEvenFirst pairs c) hfirst
  · obtain ⟨hdefined, hrep⟩ := hsecond
    let i : HeHuEvenTestingIndex (K := K) pairs := .second c hdefined
    refine ⟨i, hXw.trans ?_⟩
    simpa only [i, HeHuEvenTestingIndex.model,
      HeHuEvenTestingIndex.coefficients, w] using
      heHuOMaximalModel_form_isIsometric_of_diagonalRepresents
        w (heHuEvenSecond pairs c hdefined) hrep

/-- Proposition 3.5(ii): every odd-rank ambient quadratic space occurs in
one of the two displayed table columns. -/
theorem exists_oddTestingIndex_ambientlyIsometric
    (pairs : Nat) (X : QuadraticLatticeModel (K := K))
    (hRank : X.rank = 2 * pairs + 3) :
    ∃ i : HeHuOddTestingIndex (K := K) pairs,
      X.IsAmbientlyIsometric i.model := by
  let w := X.diagonalUnitsCast (2 * pairs + 3) hRank
  have hXw :=
    ambientlyIsometric_heHuOMaximalModel_diagonalUnitsCast
      X (2 * pairs + 3) hRank
  obtain ⟨c, hfirst | hsecond⟩ :=
    heHu2022Proposition35iiOdd (K := K) pairs w
  · let i : HeHuOddTestingIndex (K := K) pairs := .first c
    refine ⟨i, hXw.trans ?_⟩
    simpa only [i, HeHuOddTestingIndex.model,
      HeHuOddTestingIndex.coefficients, w] using
      heHuOMaximalModel_form_isIsometric_of_diagonalRepresents
        w (heHuOddFirst pairs c) hfirst
  · let i : HeHuOddTestingIndex (K := K) pairs := .second c
    refine ⟨i, hXw.trans ?_⟩
    simpa only [i, HeHuOddTestingIndex.model,
      HeHuOddTestingIndex.coefficients, w] using
      heHuOMaximalModel_form_isIsometric_of_diagonalRepresents
        w (heHuOddSecond pairs c) hsecond

/-- Any complete family of maximal representatives tests universality.  The
proof enlarges an arbitrary integral test lattice to an `O`-maximal one and
then uses uniqueness on its classified ambient space. -/
theorem completeMaximalFamily_isUniversalityTestingFamily
    {I : Type u} (family : I → QuadraticLatticeModel (K := K)) (n : Nat)
    (hmaximal : ∀ i, (family i).IsOMaximal)
    (hcomplete : ∀ X : QuadraticLatticeModel (K := K),
      X.rank = n → ∃ i, X.IsAmbientlyIsometric (family i)) :
    IsUniversalityTestingFamily family n := by
  intro M hMIntegral htests
  letI : AddCommGroup M.Carrier := M.addCommGroup
  letI : Module K M.Carrier := M.module
  rw [isNUniversal_iff_models]
  refine ⟨hMIntegral, ?_⟩
  intro X hXrank hXIntegral
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  obtain ⟨P, hXP, hPmaximal⟩ :=
    Lattice.exists_oMaximal_superlattice
      (q := X.form) (L := X.lattice) hXIntegral
  let Pmodel : QuadraticLatticeModel (K := K) :=
    { Carrier := X.Carrier
      form := X.form
      lattice := P }
  have hPmodelRank : Pmodel.rank = n := by
    change finrank K X.Carrier = n
    change finrank K X.Carrier = n at hXrank
    exact hXrank
  obtain ⟨i, hi⟩ := hcomplete Pmodel hPmodelRank
  let F := family i
  letI : AddCommGroup F.Carrier := F.addCommGroup
  letI : Module K F.Carrier := F.module
  have hi' : Pmodel.form.IsIsometric F.form := hi
  have hPF : Lattice.IsIsometric Pmodel.form F.form Pmodel.lattice F.lattice :=
    Lattice.oMaximal_isIsometric_of_isometric hPmaximal
      (hmaximal i) hi'
  have hFRepP : F.Represents Pmodel := by
    rcases hPF with ⟨f⟩
    exact ⟨f.toRepresentation⟩
  have hMRepP : M.Represents Pmodel := (htests i).trans hFRepP
  change Lattice.Represents M.form X.form M.lattice X.lattice
  exact hMRepP.trans (Lattice.represents_of_le X.form hXP)

/-- The two even-dimensional table columns form a universality testing
family. -/
theorem heHuEvenTestingFamily_testsUniversality (pairs : Nat) :
    IsUniversalityTestingFamily
      (HeHuEvenTestingIndex.model (K := K) (pairs := pairs))
      (2 * pairs + 2) := by
  apply completeMaximalFamily_isUniversalityTestingFamily
  · exact HeHuEvenTestingIndex.model_isOMaximal
  · exact exists_evenTestingIndex_ambientlyIsometric pairs

/-- The two odd-dimensional table columns form a universality testing
family. -/
theorem heHuOddTestingFamily_testsUniversality (pairs : Nat) :
    IsUniversalityTestingFamily
      (HeHuOddTestingIndex.model (K := K) (pairs := pairs))
      (2 * pairs + 3) := by
  apply completeMaximalFamily_isUniversalityTestingFamily
  · exact HeHuOddTestingIndex.model_isOMaximal
  · exact exists_oddTestingIndex_ambientlyIsometric pairs

/-- He--Hu, Theorem 1.2(i): the even-rank table is a minimal testing family,
with presentations identified up to ambient isometry. -/
theorem heHu2022Theorem12Even (pairs : Nat) :
    IsMinimalUniversalityTestingFamily
      (HeHuEvenTestingIndex.model (K := K) (pairs := pairs))
      (2 * pairs + 2) := by
  refine ⟨heHuEvenTestingFamily_testsUniversality pairs, ?_⟩
  intro i
  let W := heHuOMaximalModel i.excludingTarget
  letI : AddCommGroup W.Carrier := W.addCommGroup
  letI : Module K W.Carrier := W.module
  have hWmaximal : W.IsOMaximal :=
    heHuOMaximalModel_isOMaximal i.excludingTarget
  refine ⟨W, hWmaximal.isIntegral, ?_, ?_⟩
  · intro hrep
    apply i.excludingTarget_exact.misses
    apply (heHuOMaximalModel_represents_iff
      i.excludingTarget i.coefficients).mp
    simpa only [W, HeHuEvenTestingIndex.model] using hrep
  · intro j hnotIso
    have hdiag : DiagonalRepresents
        (diagonalUnitCoefficients j.coefficients)
        (diagonalUnitCoefficients i.excludingTarget) := by
      apply i.excludingTarget_exact.represents_other
      intro hji
      apply hnotIso
      simpa only [HeHuEvenTestingIndex.model] using
        heHuOMaximalModel_form_isIsometric_of_diagonalRepresents
          j.coefficients i.coefficients hji
    have hrep := (heHuOMaximalModel_represents_iff
      i.excludingTarget j.coefficients).mpr hdiag
    simpa only [W, HeHuEvenTestingIndex.model] using hrep

/-- He--Hu, Theorem 1.2(ii): the odd-rank table is a minimal testing family,
with presentations identified up to ambient isometry. -/
theorem heHu2022Theorem12Odd (pairs : Nat) :
    IsMinimalUniversalityTestingFamily
      (HeHuOddTestingIndex.model (K := K) (pairs := pairs))
      (2 * pairs + 3) := by
  refine ⟨heHuOddTestingFamily_testsUniversality pairs, ?_⟩
  intro i
  let W := heHuOMaximalModel i.excludingTarget
  letI : AddCommGroup W.Carrier := W.addCommGroup
  letI : Module K W.Carrier := W.module
  have hWmaximal : W.IsOMaximal :=
    heHuOMaximalModel_isOMaximal i.excludingTarget
  refine ⟨W, hWmaximal.isIntegral, ?_, ?_⟩
  · intro hrep
    apply i.excludingTarget_exact.misses
    apply (heHuOMaximalModel_represents_iff
      i.excludingTarget i.coefficients).mp
    simpa only [W, HeHuOddTestingIndex.model] using hrep
  · intro j hnotIso
    have hdiag : DiagonalRepresents
        (diagonalUnitCoefficients j.coefficients)
        (diagonalUnitCoefficients i.excludingTarget) := by
      apply i.excludingTarget_exact.represents_other
      intro hji
      apply hnotIso
      simpa only [HeHuOddTestingIndex.model] using
        heHuOMaximalModel_form_isIsometric_of_diagonalRepresents
          j.coefficients i.coefficients hji
    have hrep := (heHuOMaximalModel_represents_iff
      i.excludingTarget j.coefficients).mpr hdiag
    simpa only [W, HeHuOddTestingIndex.model] using hrep

end Lattice.QuadraticLatticeModel

end Bong
