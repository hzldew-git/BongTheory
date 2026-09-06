/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCLemma720Ambient
import Bong.Bong.He2023ADCLemma718

/-!
# He (2025), Lemma 7.20

This file completes the construction in part (iii).  For a unit `omega`
of defect `2 * r + 1`, the two named products from Lemma 7.19 realize the
class selected by the paper's Hilbert-symbol equation.  Parts (i) and (ii)
are imported from `He2023ADCLemma720Maximal`.
-/

namespace Bong

open Dyadic Module

universe u

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The paper's range `r <= e - 1` puts the prescribed odd defect strictly
below `2e`, as required by Lemma 7.19. -/
theorem heADC2025Lemma720_defectLt (rIndex : Nat) (omega : Kˣ)
    (hr : rIndex ≤ ramificationIndex K - 1)
    (hdefect : quadraticDefect K omega =
      ((2 * rIndex + 1 : Nat) : ℕ∞)) :
    quadraticDefect K omega <
      ((2 * ramificationIndex K : Nat) : ℕ∞) := by
  rw [hdefect]
  exact_mod_cast (show 2 * rIndex + 1 < 2 * ramificationIndex K by
    have he := ramificationIndex_pos (K := K)
    omega)

/-- The integer defect extracted by Lemma 7.19 is literally `2r+1`. -/
theorem heADC2025Lemma720_defectDataValue (rIndex : Nat) (omega : Kˣ)
    (homega : IsValuationUnit K (omega : K))
    (hr : rIndex ≤ ramificationIndex K - 1)
    (hdefect : quadraticDefect K omega =
      ((2 * rIndex + 1 : Nat) : ℕ∞)) :
    let hlt := heADC2025Lemma720_defectLt rIndex omega hr hdefect
    (heADC2025Lemma719_unitDefectData omega homega hlt).d =
      (2 * rIndex + 1 : Nat) := by
  dsimp only
  unfold heADC2025Lemma719_unitDefectData
  dsimp only
  generalize heq :
    heADCUnitSharpDefectData omega homega
      (heADC2025Lemma719_sharpDomain_of_defect_lt omega homega
        (heADC2025Lemma720_defectLt rIndex omega hr hdefect)) = data
  rcases data with ⟨hodd, hnonnegative, hlt, hdata⟩
  rw [hdefect]
  simp only [ENat.toNat_coe]

/-- Multiplication by the unit `omega` preserves the allowed order of the
line parameter. -/
theorem heADC2025Lemma720_lineOrder (omega c : Kˣ)
    (homega : IsValuationUnit K (omega : K))
    (hcOrder : ordUnit K c = 0 ∨ ordUnit K c = 1) :
    ordUnit K (omega * c) = 0 ∨ ordUnit K (omega * c) = 1 := by
  have homegaOrder : ordUnit K omega = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K omega).1 homega
  rcases hcOrder with hc | hc
  · left
    rw [ordUnit_mul, homegaOrder, hc]
    norm_num
  · right
    rw [ordUnit_mul, homegaOrder, hc]
    norm_num

/-- Lemma 7.20(iii), first selected column: the named product realizes
`M_{nu,r}^{n+2}(c)` whenever the paper's sign equation selects column one. -/
theorem heADC2025Lemma720iiiFirst (k rIndex : Nat) (omega c : Kˣ)
    (nu : HeADC716Column)
    (homega : IsValuationUnit K (omega : K))
    (hr : rIndex ≤ ramificationIndex K - 1)
    (hdefect : quadraticDefect K omega =
      ((2 * rIndex + 1 : Nat) : ℕ∞))
    (hcOrder : ordUnit K c = 0 ∨ ordUnit K c = 1)
    (hselect : HeADC716Column.one.paperSign =
      nu.paperSign * hilbertSymbol K omega c) :
    ∃ full : GoodBONG
        ((BONG.coefficientDiagonalSpace
          (heADCW1Even (k + 1) omega)).orthogonalSum
          ((QuadraticSpace.line K).rescaleUnit (omega * c)))
        (Lattice.product (heADCN1Even (k + 1) omega).lattice
          (BONG.unaryModelLattice (K := K))) (2 * k + 5),
      HeADC2025Definition716 k rIndex nu c full := by
  have hlt := heADC2025Lemma720_defectLt rIndex omega hr hdefect
  have H := heADC2025Lemma719FirstNamedPublished k omega (omega * c)
    homega hlt (heADC2025Lemma720_lineOrder omega c homega hcOrder)
  obtain ⟨full, hADC, horder⟩ := H
  refine ⟨full, ?_⟩
  refine
    { indexBound := hr.trans (Nat.sub_le _ _)
      parameterOrder := hcOrder
      nADC := hADC
      ambient := heADC2025Lemma720_productSpaceIsometric
        k omega c HeADC716Column.one nu hselect
      penultimate := ?_ }
  rw [horder,
    heADC2025Lemma720_defectDataValue rIndex omega homega hr hdefect]
  omega

/-- Lemma 7.20(iii), second selected column: the named product realizes
`M_{nu,r}^{n+2}(c)` whenever the paper's sign equation selects column two. -/
theorem heADC2025Lemma720iiiSecond (k rIndex : Nat) (omega c : Kˣ)
    (nu : HeADC716Column)
    (homega : IsValuationUnit K (omega : K))
    (hr : rIndex ≤ ramificationIndex K - 1)
    (hdefect : quadraticDefect K omega =
      ((2 * rIndex + 1 : Nat) : ℕ∞))
    (hcOrder : ordUnit K c = 0 ∨ ordUnit K c = 1)
    (hselect : HeADC716Column.two.paperSign =
      nu.paperSign * hilbertSymbol K omega c) :
    let hlt := heADC2025Lemma720_defectLt rIndex omega hr hdefect
    let D := heADC2025Lemma719_unitDefectData omega homega hlt
    ∃ full : GoodBONG
        ((BONG.coefficientDiagonalSpace
          (heADCW2Even (k + 1) omega
            (Or.inr D.sharp.notSquare))).orthogonalSum
          ((QuadraticSpace.line K).rescaleUnit (omega * c)))
        (Lattice.product
          (heADCN2Even (k + 1) omega
            (Or.inr D.sharp.notSquare)).lattice
          (BONG.unaryModelLattice (K := K))) (2 * k + 5),
      HeADC2025Definition716 k rIndex nu c full := by
  dsimp only
  let hlt := heADC2025Lemma720_defectLt rIndex omega hr hdefect
  let D := heADC2025Lemma719_unitDefectData omega homega hlt
  have H := heADC2025Lemma719SecondNamedPublished k omega (omega * c)
    homega hlt (heADC2025Lemma720_lineOrder omega c homega hcOrder)
  obtain ⟨full, hADC, horder⟩ := H
  refine ⟨full, ?_⟩
  refine
    { indexBound := hr.trans (Nat.sub_le _ _)
      parameterOrder := hcOrder
      nADC := hADC
      ambient := ?_
      penultimate := ?_ }
  · exact heADC2025Lemma720_productSpaceIsometric
      k omega c HeADC716Column.two nu hselect
  · rw [horder,
      heADC2025Lemma720_defectDataValue rIndex omega homega hr hdefect]
    omega

/-- Branch-independent packaging of the named product in Lemma 7.20(iii).
The match is only over the paper's two possible values of `nuPrime`. -/
noncomputable def HeADC2025Lemma720iiiNamedConclusion
    (k rIndex : Nat) (omega c : Kˣ)
    (nuPrime nu : HeADC716Column)
    (homega : IsValuationUnit K (omega : K))
    (hr : rIndex ≤ ramificationIndex K - 1)
    (hdefect : quadraticDefect K omega =
      ((2 * rIndex + 1 : Nat) : ℕ∞)) : Prop :=
  match nuPrime with
  | .one =>
      ∃ full : GoodBONG
          ((BONG.coefficientDiagonalSpace
            (heADCW1Even (k + 1) omega)).orthogonalSum
            ((QuadraticSpace.line K).rescaleUnit (omega * c)))
          (Lattice.product (heADCN1Even (k + 1) omega).lattice
            (BONG.unaryModelLattice (K := K))) (2 * k + 5),
        HeADC2025Definition716 k rIndex nu c full
  | .two =>
      let hlt := heADC2025Lemma720_defectLt rIndex omega hr hdefect
      let D := heADC2025Lemma719_unitDefectData omega homega hlt
      ∃ full : GoodBONG
          ((BONG.coefficientDiagonalSpace
            (heADCW2Even (k + 1) omega
              (Or.inr D.sharp.notSquare))).orthogonalSum
            ((QuadraticSpace.line K).rescaleUnit (omega * c)))
          (Lattice.product
            (heADCN2Even (k + 1) omega
              (Or.inr D.sharp.notSquare)).lattice
            (BONG.unaryModelLattice (K := K))) (2 * k + 5),
        HeADC2025Definition716 k rIndex nu c full

/-- The two branch theorems combine to the literal arbitrary-`nuPrime`
form of Lemma 7.20(iii). -/
theorem heADC2025Lemma720iii (k rIndex : Nat) (omega c : Kˣ)
    (nuPrime nu : HeADC716Column)
    (homega : IsValuationUnit K (omega : K))
    (hr : rIndex ≤ ramificationIndex K - 1)
    (hdefect : quadraticDefect K omega =
      ((2 * rIndex + 1 : Nat) : ℕ∞))
    (hcOrder : ordUnit K c = 0 ∨ ordUnit K c = 1)
    (hselect : nuPrime.paperSign =
      nu.paperSign * hilbertSymbol K omega c) :
    HeADC2025Lemma720iiiNamedConclusion k rIndex omega c
      nuPrime nu homega hr hdefect := by
  cases nuPrime
  · exact heADC2025Lemma720iiiFirst k rIndex omega c nu homega hr
      hdefect hcOrder hselect
  · exact heADC2025Lemma720iiiSecond k rIndex omega c nu homega hr
      hdefect hcOrder hselect

/-- In every nonmaximal row `0 <= r <= e-1`, a permitted odd-defect unit
and the Hilbert-selected named product exist.  This discharges the
"is defined" clause of Lemma 7.20 for part (iii). -/
theorem heADC2025Lemma720iii_defined (k rIndex : Nat) (c : Kˣ)
    (nu : HeADC716Column)
    (hr : rIndex ≤ ramificationIndex K - 1)
    (hcOrder : ordUnit K c = 0 ∨ ordUnit K c = 1) :
    ∃ (omega : Kˣ) (nuPrime : HeADC716Column),
      ∃ homega : IsValuationUnit K (omega : K),
      ∃ hdefect : quadraticDefect K omega =
          ((2 * rIndex + 1 : Nat) : ℕ∞),
        nuPrime.paperSign =
          nu.paperSign * hilbertSymbol K omega c ∧
        HeADC2025Lemma720iiiNamedConclusion k rIndex omega c
          nuPrime nu homega hr hdefect := by
  have he : 0 < ramificationIndex K := ramificationIndex_pos (K := K)
  have hdPositive : 0 < 2 * rIndex + 1 := by omega
  have hdOdd : Odd (2 * rIndex + 1) := ⟨rIndex, by omega⟩
  have hdLt : 2 * rIndex + 1 < 2 * ramificationIndex K := by omega
  obtain ⟨omega, homega, hdefect⟩ :=
    exists_unit_quadraticDefect_eq_odd (K := K)
      (2 * rIndex + 1) hdPositive hdOdd hdLt
  rcases Int.units_eq_one_or
      (nu.paperSign * hilbertSymbol K omega c) with hsign | hsign
  · refine ⟨omega, HeADC716Column.two, homega, hdefect, ?_, ?_⟩
    · simpa only [HeADC716Column.paperSign] using hsign.symm
    · apply heADC2025Lemma720iii k rIndex omega c
        HeADC716Column.two nu homega hr hdefect hcOrder
      simpa only [HeADC716Column.paperSign] using hsign.symm
  · refine ⟨omega, HeADC716Column.one, homega, hdefect, ?_, ?_⟩
    · simpa only [HeADC716Column.paperSign] using hsign.symm
    · apply heADC2025Lemma720iii k rIndex omega c
        HeADC716Column.one nu homega hr hdefect hcOrder
      simpa only [HeADC716Column.paperSign] using hsign.symm

/-- A universe-safe meaning of the paper's phrase "the class is defined":
some quadratic lattice and some good BONG satisfy Definition 7.16. -/
def HeADC2025Definition716IsDefined (k rIndex : Nat)
    (nu : HeADC716Column) (c : Kˣ) : Prop :=
  ∃ X : Lattice.QuadraticLatticeModel (K := K),
    letI : AddCommGroup X.Carrier := X.addCommGroup
    letI : Module K X.Carrier := X.module
    ∃ a : GoodBONG X.form X.lattice (2 * k + 5),
      HeADC2025Definition716 k rIndex nu c a

/-- Any concrete realization of Definition 7.16 certifies that its class
is defined in the bundled sense. -/
theorem HeADC2025Definition716.isDefined
    {V : Type u} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    {k rIndex : Nat} {nu : HeADC716Column} {c : Kˣ}
    {a : GoodBONG q L (2 * k + 5)}
    (A : HeADC2025Definition716 k rIndex nu c a) :
    HeADC2025Definition716IsDefined k rIndex nu c := by
  refine ⟨Lattice.quadraticLatticeModel q L, ?_⟩
  exact ⟨a, A⟩

/-- The exceptional triple `(2,e,U)` is genuinely undefined, not merely
absent from the displayed list of models. -/
theorem heADC2025Lemma720_exceptional_undefined
    (k : Nat) (epsilon : Kˣ)
    (hepsilon : IsValuationUnit K (epsilon : K)) :
    ¬ HeADC2025Definition716IsDefined k (ramificationIndex K)
      HeADC716Column.two epsilon := by
  intro hdefined
  rcases hdefined with ⟨X, hrealization⟩
  letI : AddCommGroup X.Carrier := X.addCommGroup
  letI : Module K X.Carrier := X.module
  rcases hrealization with ⟨a, A⟩
  exact (heADC2025Lemma718_not_definition716 k epsilon hepsilon a) A

/-- Every triple allowed by Lemma 7.20 has a concrete realization.  The
maximal endpoint uses parts (i)--(ii); every lower row uses part (iii). -/
theorem heADC2025Lemma720_defined_of_not_exception
    (k rIndex : Nat) (nu : HeADC716Column) (c : Kˣ)
    (hr : rIndex ≤ ramificationIndex K)
    (hcOrder : ordUnit K c = 0 ∨ ordUnit K c = 1)
    (hnot : ¬ (nu = HeADC716Column.two ∧
      rIndex = ramificationIndex K ∧ ordUnit K c = 0)) :
    HeADC2025Definition716IsDefined k rIndex nu c := by
  rcases lt_or_eq_of_le hr with hrlt | hre
  · have hrLower : rIndex ≤ ramificationIndex K - 1 := by omega
    obtain ⟨omega, nuPrime, homega, hdefect, hselect, H⟩ :=
      heADC2025Lemma720iii_defined k rIndex c nu hrLower hcOrder
    cases nuPrime <;> obtain ⟨full, A⟩ := H
    · exact A.isDefined
    · exact A.isDefined
  · subst rIndex
    cases nu with
    | one =>
        exact (heADC2025Lemma720iFirst k c hcOrder).isDefined
    | two =>
        rcases hcOrder with hc | hc
        · exact (hnot ⟨rfl, rfl, hc⟩).elim
        · exact (heADC2025Lemma720iSecond k c hc).isDefined

/-- Complete formal statement of the first sentence of Lemma 7.20:
within the stated index and parameter domains, Definition 7.16 is inhabited
exactly away from `(nu,r,c)=(2,e,U)`. -/
theorem heADC2025Lemma720_defined_iff
    (k rIndex : Nat) (nu : HeADC716Column) (c : Kˣ)
    (hr : rIndex ≤ ramificationIndex K)
    (hcOrder : ordUnit K c = 0 ∨ ordUnit K c = 1) :
    HeADC2025Definition716IsDefined k rIndex nu c ↔
      ¬ (nu = HeADC716Column.two ∧
        rIndex = ramificationIndex K ∧ ordUnit K c = 0) := by
  constructor
  · intro hdefined hexception
    rcases hexception with ⟨rfl, rfl, hc⟩
    apply heADC2025Lemma720_exceptional_undefined k c
      ((isValuationUnit_iff_ordUnit_eq_zero K c).2 hc)
    exact hdefined
  · exact heADC2025Lemma720_defined_of_not_exception
      k rIndex nu c hr hcOrder

/-- Any realization of the class selected by the first even column is
integrally isometric to the first named product in Lemma 7.20(iii). -/
theorem heADC2025Lemma720iiiFirst_isometricNamed
    {V : Type u} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    (k rIndex : Nat) (omega c : Kˣ) (nu : HeADC716Column)
    (a : GoodBONG q L (2 * k + 5))
    (A : HeADC2025Definition716 k rIndex nu c a)
    (homega : IsValuationUnit K (omega : K))
    (hr : rIndex ≤ ramificationIndex K - 1)
    (hdefect : quadraticDefect K omega =
      ((2 * rIndex + 1 : Nat) : ℕ∞))
    (hselect : HeADC716Column.one.paperSign =
      nu.paperSign * hilbertSymbol K omega c) :
    Lattice.IsIsometric q
      ((BONG.coefficientDiagonalSpace
        (heADCW1Even (k + 1) omega)).orthogonalSum
        ((QuadraticSpace.line K).rescaleUnit (omega * c))) L
      (Lattice.product (heADCN1Even (k + 1) omega).lattice
        (BONG.unaryModelLattice (K := K))) := by
  obtain ⟨full, B⟩ := heADC2025Lemma720iiiFirst k rIndex omega c nu
    homega hr hdefect A.parameterOrder hselect
  exact heADC2025Remark717_unique k rIndex nu c a full A B

/-- Any realization of the class selected by the second even column is
integrally isometric to the second named product in Lemma 7.20(iii). -/
theorem heADC2025Lemma720iiiSecond_isometricNamed
    {V : Type u} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    (k rIndex : Nat) (omega c : Kˣ) (nu : HeADC716Column)
    (a : GoodBONG q L (2 * k + 5))
    (A : HeADC2025Definition716 k rIndex nu c a)
    (homega : IsValuationUnit K (omega : K))
    (hr : rIndex ≤ ramificationIndex K - 1)
    (hdefect : quadraticDefect K omega =
      ((2 * rIndex + 1 : Nat) : ℕ∞))
    (hselect : HeADC716Column.two.paperSign =
      nu.paperSign * hilbertSymbol K omega c) :
    let hlt := heADC2025Lemma720_defectLt rIndex omega hr hdefect
    let D := heADC2025Lemma719_unitDefectData omega homega hlt
    Lattice.IsIsometric q
      ((BONG.coefficientDiagonalSpace
        (heADCW2Even (k + 1) omega
          (Or.inr D.sharp.notSquare))).orthogonalSum
        ((QuadraticSpace.line K).rescaleUnit (omega * c))) L
      (Lattice.product
        (heADCN2Even (k + 1) omega
          (Or.inr D.sharp.notSquare)).lattice
        (BONG.unaryModelLattice (K := K))) := by
  dsimp only
  obtain ⟨full, B⟩ := heADC2025Lemma720iiiSecond k rIndex omega c nu
    homega hr hdefect A.parameterOrder hselect
  exact heADC2025Remark717_unique k rIndex nu c a full A B

end BONG.GoodBONG

end Bong
