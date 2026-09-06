/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCLemma719
import Bong.Lattice.NADCMonotonicity
import Bong.Lattice.OrthogonalProductIsometry

/-!
# He (2025), Lemma 7.19: identification with the published models

The explicit good-BONG construction from `He2023ADCLemma719` is identified
with the named maximal lattices `N₁` and `N₂` from Definition 4.1.  Appending
the unary line then gives the literal orthogonal products printed in Lemma
7.19, rather than merely a lattice with the same order profile.
-/

namespace Bong

open Dyadic Module

universe u

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The complete Lemma 7.19 conclusion is invariant under an integral
lattice isometry; in particular, the transported good BONG retains its
penultimate order. -/
theorem HeADC719Conclusion.of_latticeIsometry
    {V W : Type u} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W} {k : Nat} {d : Int}
    (H : HeADC719Conclusion q L k d)
    (f : Lattice.Isometry q r L M) : HeADC719Conclusion r M k d := by
  obtain ⟨b, hADC, horder⟩ := H
  let c := b.mapLatticeIsometry f
  refine ⟨c, hADC.of_latticeIsometry f, ?_⟩
  simpa only [c, order_mapLatticeIsometry] using horder

/-- The explicit first-column even base is the chosen published maximal
lattice `N₁`. -/
theorem heADC2025Lemma719FirstBasePublishedData (k : Nat) (delta : Kˣ)
    (d : Int) (hdelta : IsValuationUnit K (delta : K))
    (hdOdd : Odd d) (hdNonnegative : 0 ≤ d)
    (hdLt : d < 2 * (ramificationIndex K : Int))
    (hdefect : defectOrder (K := K) delta =
      (((d : Int) : ℚ) : WithTop ℚ)) :
    Lattice.IsIsometric
      (heADC719BaseSpace k 1 delta d (by simp [IsValuationUnit])
        hdelta hdOdd hdNonnegative hdLt hdefect)
      (BONG.coefficientDiagonalSpace (heADCW1Even (k + 1) delta))
      (heADC719BaseLattice (K := K) k)
      (heADCN1Even (k + 1) delta).lattice := by
  have hone : IsValuationUnit K ((1 : Kˣ) : K) := by
    simp [IsValuationUnit]
  let b := heHuUnitDefectTailGoodBONG 1 delta d hone hdelta
    hdOdd hdNonnegative hdLt hdefect
  have hBinary : Lattice.IsIntegral
      (heADC719BinarySpace 1 delta d hone hdelta hdOdd
        hdNonnegative hdLt hdefect)
      (BONG.binaryDiagonalModelLattice (K := K)) := by
    apply heHuIntegral_of_firstOrder_nonneg b
    rw [heHuUnitDefectTailGoodBONG_order]
    norm_num
  have hmax := heHu2022Proposition37EvenGeneric 1 delta d hone
    hdelta hdOdd hdNonnegative hdLt hdefect (k + 1)
  have htail := heADCUnitDefectTail_represents_twist 1 delta d hone
    hdelta hdOdd hdNonnegative hdLt hdefect
  have hfirst : heHuBinaryTwist delta 1 = heHuBinaryFirst delta := by
    simp [heHuBinaryTwist, heHuBinaryFirst]
  rw [hfirst] at htail
  let base := heHu2022Lemma310BONG b hBinary (k + 1)
  have hrep := heADCBinaryTower_represents_evenFirst b hBinary
    (k + 1) delta htail
  have hambient := base.ambientIsometric_of_diagonalRepresents
    (heADCW1Even (k + 1) delta) (by omega) hrep
  exact Lattice.oMaximal_isIsometric_of_isometric hmax
    (heHuOMaximalLattice_isOMaximal _) hambient

/-- The explicit second-column even base is the chosen published maximal
lattice `N₂`. -/
theorem heADC2025Lemma719SecondBasePublishedData (k : Nat) (delta : Kˣ)
    (hs : HeHuSharpDomain delta) (d : Int)
    (hdelta : IsValuationUnit K (delta : K))
    (hdOdd : Odd d) (hdNonnegative : 0 ≤ d)
    (hdLt : d < 2 * (ramificationIndex K : Int))
    (hdefect : defectOrder (K := K) delta =
      (((d : Int) : ℚ) : WithTop ℚ)) :
    Lattice.IsIsometric
      (heADC719BaseSpace k (heHuSharp delta hs) delta d
        (heHu2022Proposition32 delta hs).1 hdelta hdOdd
        hdNonnegative hdLt hdefect)
      (BONG.coefficientDiagonalSpace
        (heADCW2Even (k + 1) delta (Or.inr hs.notSquare)))
      (heADC719BaseLattice (K := K) k)
      (heADCN2Even (k + 1) delta (Or.inr hs.notSquare)).lattice := by
  let eta := heHuSharp delta hs
  have heta : IsValuationUnit K (eta : K) :=
    (heHu2022Proposition32 delta hs).1
  let b := heHuUnitDefectTailGoodBONG eta delta d heta hdelta
    hdOdd hdNonnegative hdLt hdefect
  have hBinary : Lattice.IsIntegral
      (heADC719BinarySpace eta delta d heta hdelta hdOdd
        hdNonnegative hdLt hdefect)
      (BONG.binaryDiagonalModelLattice (K := K)) := by
    apply heHuIntegral_of_firstOrder_nonneg b
    rw [heHuUnitDefectTailGoodBONG_order]
    norm_num
  have hmax := heHu2022Proposition37EvenGeneric eta delta d heta
    hdelta hdOdd hdNonnegative hdLt hdefect (k + 1)
  have htail := heADCUnitDefectTail_represents_twist eta delta d heta
    hdelta hdOdd hdNonnegative hdLt hdefect
  have hsecond : heHuBinaryTwist delta eta = heHuBinarySecond delta hs := by
    rfl
  rw [hsecond] at htail
  let base := heHu2022Lemma310BONG b hBinary (k + 1)
  have hrep := heADCBinaryTower_represents_evenSecond b hBinary
    (k + 1) delta hs htail
  have hambient := base.ambientIsometric_of_diagonalRepresents
    (heADCW2Even (k + 1) delta (Or.inr hs.notSquare)) (by omega) hrep
  exact Lattice.oMaximal_isIsometric_of_isometric hmax
    (heHuOMaximalLattice_isOMaximal _) hambient

/-- Literal first-column conclusion of Lemma 7.19 on the named product
`N₁^(n+1)(delta) ⊥ <c>`. -/
theorem heADC2025Lemma719FirstNamedPublished (k : Nat) (delta c : Kˣ)
    (hdelta : IsValuationUnit K (delta : K))
    (hlt : quadraticDefect K delta <
      ((2 * ramificationIndex K : Nat) : ℕ∞))
    (hcOrder : ordUnit K c = 0 ∨ ordUnit K c = 1) :
    let D := heADC2025Lemma719_unitDefectData delta hdelta hlt
    HeADC719Conclusion
      ((BONG.coefficientDiagonalSpace
        (heADCW1Even (k + 1) delta)).orthogonalSum
        ((QuadraticSpace.line K).rescaleUnit c))
      (Lattice.product (heADCN1Even (k + 1) delta).lattice
        (BONG.unaryModelLattice (K := K))) k D.d := by
  dsimp only
  let D := heADC2025Lemma719_unitDefectData delta hdelta hlt
  have H := heADC2025Lemma719First k delta c D.d hdelta D.odd
    D.nonnegative D.ltTwoE D.defect hcOrder
  have hbase := heADC2025Lemma719FirstBasePublishedData k delta D.d
    hdelta D.odd D.nonnegative D.ltTwoE D.defect
  obtain ⟨f⟩ := hbase
  let lineIdentity := Lattice.Isometry.refl
    ((QuadraticSpace.line K).rescaleUnit c)
    (BONG.unaryModelLattice (K := K))
  exact H.of_latticeIsometry (f.orthogonalProductBasic lineIdentity)

/-- Literal second-column conclusion of Lemma 7.19 on the named product
`N₂^(n+1)(delta) ⊥ <c>`. -/
theorem heADC2025Lemma719SecondNamedPublished (k : Nat) (delta c : Kˣ)
    (hdelta : IsValuationUnit K (delta : K))
    (hlt : quadraticDefect K delta <
      ((2 * ramificationIndex K : Nat) : ℕ∞))
    (hcOrder : ordUnit K c = 0 ∨ ordUnit K c = 1) :
    let D := heADC2025Lemma719_unitDefectData delta hdelta hlt
    HeADC719Conclusion
      ((BONG.coefficientDiagonalSpace
        (heADCW2Even (k + 1) delta
          (Or.inr D.sharp.notSquare))).orthogonalSum
        ((QuadraticSpace.line K).rescaleUnit c))
      (Lattice.product
        (heADCN2Even (k + 1) delta
          (Or.inr D.sharp.notSquare)).lattice
        (BONG.unaryModelLattice (K := K))) k D.d := by
  dsimp only
  let D := heADC2025Lemma719_unitDefectData delta hdelta hlt
  have H := heADC2025Lemma719Second k delta c D.sharp D.d
    hdelta D.odd D.nonnegative D.ltTwoE D.defect hcOrder
  have hbase := heADC2025Lemma719SecondBasePublishedData k delta
    D.sharp D.d hdelta D.odd D.nonnegative D.ltTwoE D.defect
  obtain ⟨f⟩ := hbase
  let lineIdentity := Lattice.Isometry.refl
    ((QuadraticSpace.line K).rescaleUnit c)
    (BONG.unaryModelLattice (K := K))
  exact H.of_latticeIsometry (f.orthogonalProductBasic lineIdentity)

end BONG.GoodBONG

end Bong
