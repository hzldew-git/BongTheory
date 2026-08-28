/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.BinaryModularShiftSpinor
import Bong.Bong.BinaryModularSpinorUpper

/-!
# Reverse containment in the even non-low modular branch

Lemma 3.13(ii) identifies Beli's spinor group with the norm-generator group
of an even shifted parameter.  The modular shifted-model construction then
realizes that entire group by proper integral rotations of any admissible
binary model of the original parameter.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- Reverse containment for an arbitrary admissible model of an even
parameter in the non-low branch.  No sign assumption on the parameter order
is needed. -/
theorem beliSpinorGroupRepresentative_le_spinorNormImage_binaryModel_of_even_nonlow
    (a : Kˣ) (c : K)
    (ha : IsBinaryParameterAdmissible a)
    (hRupper : ordUnit K a ≤ 2 * (ramificationIndex K : Int))
    (hEven : Even (ordUnit K a))
    (hdLower : ¬2 * beliParameterDefect K a ≤
      (beliSpinorCaseIIILowerCutoff K a : ℕ∞))
    (htwo : (2 : K) * c ∈ IntegerRing K)
    (hdiag : c ^ 2 + (a : K) ∈ IntegerRing K) :
    beliSpinorGroupRepresentative K a ≤
      Lattice.spinorNormImageSubgroup
        (q := QuadraticSpace.binaryModel a c)
        (L := binaryModelLattice (K := K)) := by
  let R : Int := ordUnit K a
  let ε : Kˣ := normalizedUnitPart K a
  have hε : IsValuationUnit K (ε : K) := by
    simpa only [ε] using normalizedUnitPart_isValuationUnit K a
  have hfactor : uniformizerPowerUnit K R * ε = a := by
    simpa only [R, ε] using uniformizerPower_mul_normalizedUnitPart K a
  have hdefect : quadraticDefect K (-ε) =
      beliParameterDefect K a := by
    have h :=
      beliParameterDefect_uniformizerPower_mul_valuationUnit_of_even
        (K := K) R ε hε (by simpa only [R] using hEven)
    rw [hfactor] at h
    exact h.symm
  have hdLower' : ¬2 * quadraticDefect K (-ε) ≤
      (Int.toNat (2 * (ramificationIndex K : Int) - R) : ℕ∞) := by
    unfold beliSpinorCaseIIILowerCutoff at hdLower
    rw [hdefect]
    simpa only [R] using hdLower
  have hshiftFormula :=
    beliSpinorGroupRepresentative_eq_evenShift_normGenerator
      (K := K) R ε hε (by simpa only [hfactor] using ha)
        (by simpa only [R] using hRupper)
          (by simpa only [R] using hEven) hdLower'
  have hreverse :=
    evenShiftedNormGeneratorGroup_le_spinorNormImage_binaryModel
      (K := K) R ε hε (by simpa only [hfactor] using ha)
        (by simpa only [R] using hRupper)
          (by simpa only [R] using hEven) hdLower' c
            (by simpa only [hfactor] using htwo)
              (by simpa only [hfactor] using hdiag)
  intro A hA
  have hshiftMem : A ∈ beliNormGeneratorSquareClassGroup K
      (uniformizerPowerUnit K
        (beliLemma313EvenShift (K := K) R) * ε) := by
    rw [← hshiftFormula]
    simpa only [hfactor] using hA
  have hmem := hreverse hshiftMem
  simpa only [hfactor] using hmem

/-- Intrinsic reverse containment for an arbitrary binary BONG. -/
theorem beliSpinorGroupRepresentative_le_spinorNormImage_of_even_nonlow
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    (b : BONG V q L 2)
    (hRupper : b.binaryOrderGap ≤
      2 * (ramificationIndex K : Int))
    (hEven : Even b.binaryOrderGap)
    (hdLower : ¬2 * beliParameterDefect K b.binaryParameter ≤
      (beliSpinorCaseIIILowerCutoff K b.binaryParameter : ℕ∞)) :
    beliSpinorGroupRepresentative K b.binaryParameter ≤
      Lattice.spinorNormImageSubgroup (q := q) (L := L) := by
  have hmodel :=
    beliSpinorGroupRepresentative_le_spinorNormImage_binaryModel_of_even_nonlow
      (K := K) b.binaryParameter b.binaryModelCoefficient
        b.binaryParameter_isBinaryParameterAdmissible
        (by
          change b.binaryParameterOrder ≤
            2 * (ramificationIndex K : Int)
          rwa [b.binaryParameterOrder_eq_orderGap])
        (by
          change Even b.binaryParameterOrder
          rwa [b.binaryParameterOrder_eq_orderGap])
        hdLower b.binaryModelCoefficient_isAdmissibleWitness.1
          b.binaryModelCoefficient_isAdmissibleWitness.2
  intro A hA
  have hmem := hmodel hA
  change A ∈ Lattice.spinorNormImage
    (q := QuadraticSpace.binaryModel b.binaryParameter
      b.binaryModelCoefficient)
    (L := binaryModelLattice (K := K)) at hmem
  change A ∈ Lattice.spinorNormImage (q := q) (L := L)
  rw [b.spinorNormImage_eq_binaryModel]
  exact hmem

end BONG

end Bong
