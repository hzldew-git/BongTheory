/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCLemma720

/-!
# He (2025), Theorem 7.2

The theorem is first stated without choosing a finite system of unit square
class representatives.  A nonmaximal model therefore carries an arbitrary
valuation unit of defect below `2e`; this is the representative-independent
form of the source condition `delta in U \ {1, Delta}`.
-/

namespace Bong

open Dyadic Module

universe u

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type u} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

/-- The representative-independent product family in Theorem 7.2.  The
line parameter has order zero or one, equivalently it is `epsilon*pi^k`
with `epsilon` a unit and `k` in `{0,1}`. -/
def HeADC2025Theorem72Product (q : QuadraticSpace K V)
    (L : Lattice K V) (k : Nat) : Prop :=
  (∃ (delta line : Kˣ)
      (_hdelta : IsValuationUnit K (delta : K))
      (_hlt : quadraticDefect K delta <
        ((2 * ramificationIndex K : Nat) : ℕ∞)),
    (ordUnit K line = 0 ∨ ordUnit K line = 1) ∧
      Lattice.IsIsometric q
        ((BONG.coefficientDiagonalSpace
          (heADCW1Even (k + 1) delta)).orthogonalSum
          ((QuadraticSpace.line K).rescaleUnit line)) L
        (Lattice.product (heADCN1Even (k + 1) delta).lattice
          (BONG.unaryModelLattice (K := K)))) ∨
  (∃ (delta line : Kˣ)
      (_hdelta : IsValuationUnit K (delta : K))
      (_hlt : quadraticDefect K delta <
        ((2 * ramificationIndex K : Nat) : ℕ∞)),
    let D := heADC2025Lemma719_unitDefectData delta _hdelta _hlt
    (ordUnit K line = 0 ∨ ordUnit K line = 1) ∧
      Lattice.IsIsometric q
        ((BONG.coefficientDiagonalSpace
          (heADCW2Even (k + 1) delta
            (Or.inr D.sharp.notSquare))).orthogonalSum
          ((QuadraticSpace.line K).rescaleUnit line)) L
        (Lattice.product
          (heADCN2Even (k + 1) delta
            (Or.inr D.sharp.notSquare)).lattice
          (BONG.unaryModelLattice (K := K))))

/-- A lattice in either displayed product family is `n`-ADC. -/
theorem HeADC2025Theorem72Product.isNADC (k : Nat)
    (H : HeADC2025Theorem72Product q L k) :
    Lattice.IsNADC.{u, u, u} q L (2 * k + 3) := by
  rcases H with H | H
  · obtain ⟨delta, line, hdelta, hlt, hline, hisometric⟩ := H
    have Hmodel := heADC2025Lemma719FirstNamedPublished k delta line
      hdelta hlt hline
    obtain ⟨full, hADC, horder⟩ := Hmodel
    obtain ⟨f⟩ := hisometric
    exact hADC.of_latticeIsometry f.symm
  · obtain ⟨delta, line, hdelta, hlt, hline, hisometric⟩ := H
    have Hmodel := heADC2025Lemma719SecondNamedPublished k delta line
      hdelta hlt hline
    obtain ⟨full, hADC, horder⟩ := Hmodel
    obtain ⟨f⟩ := hisometric
    exact hADC.of_latticeIsometry f.symm

/-- Necessity in Theorem 7.2.  Remark 7.17 supplies a Definition 7.16
class; Lemma 7.20 turns its top row into a maximal lattice and every lower
row into one of the two displayed products. -/
theorem heADC2025Theorem72Necessity (k : Nat)
    (a : GoodBONG q L (2 * k + 5))
    (hADC : Lattice.IsNADC.{u, u, u} q L (2 * k + 3)) :
    Lattice.IsOMaximal q L ∨ HeADC2025Theorem72Product q L k := by
  obtain ⟨nu, rIndex, c, A⟩ := a.heADC2025Remark717_exhaustion k hADC
  rcases lt_or_eq_of_le A.indexBound with hrlt | hre
  · right
    have hr : rIndex ≤ ramificationIndex K - 1 := by omega
    obtain ⟨omega, nuPrime, homega, hdefect, hselect, H⟩ :=
      heADC2025Lemma720iii_defined k rIndex c nu hr A.parameterOrder
    have hlt := heADC2025Lemma720_defectLt rIndex omega hr hdefect
    have hline := heADC2025Lemma720_lineOrder omega c
      homega A.parameterOrder
    cases nuPrime <;> obtain ⟨full, B⟩ := H
    · left
      refine ⟨omega, omega * c, homega, hlt, hline, ?_⟩
      exact heADC2025Remark717_unique k rIndex nu c a full A B
    · right
      refine ⟨omega, omega * c, homega, hlt, hline, ?_⟩
      exact heADC2025Remark717_unique k rIndex nu c a full A B
  · subst rIndex
    left
    cases nu with
    | one =>
        let b := heADCMaximalGoodBONG
          (heADCW1Odd (K := K) (k + 1) c)
        have B := heADC2025Lemma720iFirst k c A.parameterOrder
        have hisometric := heADC2025Remark717_unique k
          (ramificationIndex K) HeADC716Column.one c a b A B
        exact (heHuOMaximalLattice_isOMaximal
          (heADCW1Odd (K := K) (k + 1) c)).of_latticeIsometry
            (Classical.choice hisometric).symm
    | two =>
        rcases A.parameterOrder with hc | hc
        · exact (heADC2025Lemma718_not_definition716 k c
            ((isValuationUnit_iff_ordUnit_eq_zero K c).2 hc) a A).elim
        · let b := heADCMaximalGoodBONG
            (heADCW2Odd (K := K) (k + 1) c)
          have B := heADC2025Lemma720iSecond k c hc
          have hisometric := heADC2025Remark717_unique k
            (ramificationIndex K) HeADC716Column.two c a b A B
          exact (heHuOMaximalLattice_isOMaximal
            (heADCW2Odd (K := K) (k + 1) c)).of_latticeIsometry
              (Classical.choice hisometric).symm

/-- He (2025), Theorem 7.2, representative-independent local form. -/
theorem heADC2025Theorem72 (k : Nat)
    (a : GoodBONG q L (2 * k + 5)) :
    Lattice.IsNADC.{u, u, u} q L (2 * k + 3) ↔
      Lattice.IsOMaximal q L ∨ HeADC2025Theorem72Product q L k := by
  constructor
  · exact heADC2025Theorem72Necessity k a
  · rintro (hmaximal | hproduct)
    · exact hmaximal.isNADC (2 * k + 3)
    · exact hproduct.isNADC k

end BONG.GoodBONG

end Bong
