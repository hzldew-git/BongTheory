/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Bong.He2023ADCLemma719Tower
import Bong.Bong.He2023ADCGenericProfiles
import Bong.Bong.He2023ADCEvenFirstDefects

/-!
# He (2025), Lemma 7.19

For a unit square class of defect `d < 2e`, both explicit maximal rows
`N_1` and `N_2` may be extended by a unary coefficient of order zero or
one.  The resulting lattice is `n`-ADC, and its penultimate BONG order is
the printed value `1-d`.
-/

namespace Bong

open Dyadic Module

universe u

/-- The explicit binary quadratic space used for the two generic rows in
Table 2. -/
noncomputable abbrev heADC719BinarySpace
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    (a delta : Kˣ) (d : Int)
    (ha : IsValuationUnit K (a : K))
    (hdelta : IsValuationUnit K (delta : K))
    (hdOdd : Odd d) (hdNonnegative : 0 ≤ d)
    (hdLt : d < 2 * (ramificationIndex K : Int))
    (hdefect : BONG.GoodBONG.defectOrder (K := K) delta =
      (((d : Int) : ℚ) : WithTop ℚ)) :
    QuadraticSpace K (Fin 2 → K) :=
  BONG.binaryDiagonalModelSpace
    (BONG.GoodBONG.heHuUnitDefectTailValues (K := K) a delta d 0)
    (BONG.GoodBONG.heHuUnitDefectTailValues (K := K) a delta d 1)
    (BONG.GoodBONG.heHuUnitDefectTail_admissible a delta d ha hdelta hdOdd
      hdNonnegative hdLt hdefect)

/-- The explicit even-rank base space below the unary row in Lemma 7.19. -/
noncomputable abbrev heADC719BaseSpace
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    (k : Nat) (a delta : Kˣ) (d : Int)
    (ha : IsValuationUnit K (a : K))
    (hdelta : IsValuationUnit K (delta : K))
    (hdOdd : Odd d) (hdNonnegative : 0 ≤ d)
    (hdLt : d < 2 * (ramificationIndex K : Int))
    (hdefect : BONG.GoodBONG.defectOrder (K := K) delta =
      (((d : Int) : ℚ) : WithTop ℚ)) :=
  Lattice.halfHyperbolicExtensionForm
    (heADC719BinarySpace a delta d ha hdelta hdOdd
      hdNonnegative hdLt hdefect) (k + 1)

/-- The explicit even-rank base lattice below the unary row in Lemma 7.19. -/
noncomputable abbrev heADC719BaseLattice
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] (k : Nat) :=
  Lattice.halfHyperbolicExtensionLattice
    (BONG.binaryDiagonalModelLattice (K := K)) (k + 1)

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The finite defect package extracted from the literal hypotheses of
Lemma 7.19. -/
structure HeADC719UnitDefectData (delta : Kˣ) where
  d : Int
  sharp : HeHuSharpDomain delta
  odd : Odd d
  nonnegative : 0 ≤ d
  ltTwoE : d < 2 * (ramificationIndex K : Int)
  defect : defectOrder (K := K) delta = ((d : ℚ) : WithTop ℚ)

/-- A unit whose quadratic defect is strictly below `2e` lies in the sharp
domain used to define the second column. -/
theorem heADC2025Lemma719_sharpDomain_of_defect_lt (delta : Kˣ)
    (_hdelta : IsValuationUnit K (delta : K))
    (hlt : quadraticDefect K delta <
      ((2 * ramificationIndex K : Nat) : ℕ∞)) :
    HeHuSharpDomain delta := by
  let laws := Dyadic.dyadicDiscriminantClassLawsProved (K := K)
  constructor
  · intro hsquare
    have htop := quadraticDefect_eq_top_of_isSquare (K := K) hsquare
    rw [htop] at hlt
    exact (not_lt_of_ge le_top) hlt
  · intro hdiscriminant
    have htwisted :=
      isSquare_mul_discriminant_of_div_discriminant_square delta hdiscriminant
    have heq := heADCQuadraticDefect_eq_of_squareProduct
      delta laws.discriminantUnit htwisted
    rw [laws.discriminant_defect] at heq
    rw [heq] at hlt
    exact (lt_irrefl _ hlt)

/-- Convert the source's `d(delta) < 2e` hypothesis into the exact integer
data used by the explicit BONG construction. -/
noncomputable def heADC2025Lemma719_unitDefectData (delta : Kˣ)
    (hdelta : IsValuationUnit K (delta : K))
    (hlt : quadraticDefect K delta <
      ((2 * ramificationIndex K : Nat) : ℕ∞)) :
    HeADC719UnitDefectData delta := by
  let hs := heADC2025Lemma719_sharpDomain_of_defect_lt delta hdelta hlt
  let d : Int := (quadraticDefect K delta).toNat
  obtain ⟨hdOdd, hdNonnegative, hdLt, hdefect⟩ :=
    heADCUnitSharpDefectData delta hdelta hs
  exact
    { d := d
      sharp := hs
      odd := hdOdd
      nonnegative := hdNonnegative
      ltTwoE := hdLt
      defect := hdefect }

/-- The complete conclusion of Lemma 7.19 for a fixed displayed model. -/
def HeADC719Conclusion {V : Type u} [AddCommGroup V] [Module K V]
    (q : QuadraticSpace K V) (L : Lattice K V) (k : Nat) (d : Int) : Prop :=
  ∃ full : GoodBONG q L (2 * k + 5),
    Lattice.IsNADC.{u, u, u} q L (2 * k + 3) ∧
      full.order ⟨2 * k + 3, by omega⟩ = 1 - d

/-- Lemma 7.19 with the finite defect data exposed.  The witness is the
actual good BONG constructed from the displayed binary row and unary line. -/
theorem heADC2025Lemma719ExplicitData (k : Nat) (a delta c : Kˣ)
    (d : Int) (ha : IsValuationUnit K (a : K))
    (hdelta : IsValuationUnit K (delta : K))
    (hdOdd : Odd d) (hdNonnegative : 0 ≤ d)
    (hdLt : d < 2 * (ramificationIndex K : Int))
    (hdefect : defectOrder (K := K) delta =
      (((d : Int) : ℚ) : WithTop ℚ))
    (hcOrder : ordUnit K c = 0 ∨ ordUnit K c = 1) :
    HeADC719Conclusion
      ((Lattice.halfHyperbolicExtensionForm
        (heADC719BinarySpace a delta d ha hdelta hdOdd
          hdNonnegative hdLt hdefect) (k + 1)).orthogonalSum
        ((QuadraticSpace.line K).rescaleUnit c))
      (Lattice.product
        (Lattice.halfHyperbolicExtensionLattice
          (BONG.binaryDiagonalModelLattice (K := K)) (k + 1))
        (BONG.unaryModelLattice (K := K))) k d := by
  let tail := heHuUnitDefectTailGoodBONG a delta d ha hdelta
    hdOdd hdNonnegative hdLt hdefect
  have hIntegral : Lattice.IsIntegral
      (heADC719BinarySpace a delta d ha hdelta hdOdd
        hdNonnegative hdLt hdefect)
      (BONG.binaryDiagonalModelLattice (K := K)) := by
    apply heHuIntegral_of_firstOrder_nonneg tail
    rw [heHuUnitDefectTailGoodBONG_order]
    norm_num
  let raw := heHu2022Lemma310BONG tail hIntegral (k + 1)
  let base := raw.castLength (by omega : 2 + 2 * (k + 1) = 2 * k + 4)
  have hzero : tail.order 0 = 0 := by
    dsimp only [tail]
    rw [heHuUnitDefectTailGoodBONG_order]
    rfl
  have hlast : tail.order 1 = 1 - d := by
    dsimp only [tail]
    rw [heHuUnitDefectTailGoodBONG_order]
    rfl
  have hadjacent : tail.adjacentDefect 0 =
      (((d : Int) : ℚ) : WithTop ℚ) := by
    exact heHuUnitDefectTailGoodBONG_adjacentDefect a delta d ha hdelta
      hdOdd hdNonnegative hdLt hdefect
  have B : HeADC719BaseConditions k d base :=
    heADC2025Lemma719_towerBaseConditions k d tail hIntegral
      hzero hlast hadjacent
  let full := heADC2025Lemma719Append k d c base B hdOdd
    hdNonnegative hcOrder
  refine ⟨full, ?_, ?_⟩
  · exact base.heADC2025Lemma719Core k d c B hdOdd hdNonnegative
      hdLt hcOrder
  · have hleft := heADC2025Lemma719Append_order_left k d c base B
      hdOdd hdNonnegative hcOrder ⟨2 * k + 3, by omega⟩
    exact hleft.trans B.last

/-- The first ambient column in Lemma 7.19, obtained by taking the unit
multiplier of the binary row to be one. -/
theorem heADC2025Lemma719First (k : Nat) (delta c : Kˣ)
    (d : Int) (hdelta : IsValuationUnit K (delta : K))
    (hdOdd : Odd d) (hdNonnegative : 0 ≤ d)
    (hdLt : d < 2 * (ramificationIndex K : Int))
    (hdefect : defectOrder (K := K) delta =
      (((d : Int) : ℚ) : WithTop ℚ))
    (hcOrder : ordUnit K c = 0 ∨ ordUnit K c = 1) :
    HeADC719Conclusion
      ((Lattice.halfHyperbolicExtensionForm
        (heADC719BinarySpace 1 delta d (by simp [IsValuationUnit])
          hdelta hdOdd hdNonnegative hdLt hdefect) (k + 1)).orthogonalSum
        ((QuadraticSpace.line K).rescaleUnit c))
      (Lattice.product
        (Lattice.halfHyperbolicExtensionLattice
          (BONG.binaryDiagonalModelLattice (K := K)) (k + 1))
        (BONG.unaryModelLattice (K := K))) k d := by
  exact heADC2025Lemma719ExplicitData k 1 delta c d
    (by simp [IsValuationUnit]) hdelta hdOdd hdNonnegative hdLt
      hdefect hcOrder

/-- The second ambient column in Lemma 7.19, obtained from the proved sharp
unit associated with `delta`. -/
theorem heADC2025Lemma719Second (k : Nat) (delta c : Kˣ)
    (hs : HeHuSharpDomain delta)
    (d : Int) (hdelta : IsValuationUnit K (delta : K))
    (hdOdd : Odd d) (hdNonnegative : 0 ≤ d)
    (hdLt : d < 2 * (ramificationIndex K : Int))
    (hdefect : defectOrder (K := K) delta =
      (((d : Int) : ℚ) : WithTop ℚ))
    (hcOrder : ordUnit K c = 0 ∨ ordUnit K c = 1) :
    HeADC719Conclusion
      ((Lattice.halfHyperbolicExtensionForm
        (heADC719BinarySpace (heHuSharp delta hs) delta d
          (heHu2022Proposition32 delta hs).1 hdelta hdOdd
          hdNonnegative hdLt hdefect) (k + 1)).orthogonalSum
        ((QuadraticSpace.line K).rescaleUnit c))
      (Lattice.product
        (Lattice.halfHyperbolicExtensionLattice
          (BONG.binaryDiagonalModelLattice (K := K)) (k + 1))
        (BONG.unaryModelLattice (K := K))) k d := by
  exact heADC2025Lemma719ExplicitData k (heHuSharp delta hs)
    delta c d (heHu2022Proposition32 delta hs).1 hdelta hdOdd
      hdNonnegative hdLt hdefect hcOrder

/-- The hypotheses `delta in U` and `d(delta) < 2e` supply all finite
defect data used in the two preceding constructions. -/
theorem heADC2025Lemma719DefectData (delta : Kˣ)
    (hdelta : IsValuationUnit K (delta : K))
    (hs : HeHuSharpDomain delta) :
    let d : Int := (quadraticDefect K delta).toNat
    Odd d ∧ 0 ≤ d ∧ d < 2 * (ramificationIndex K : Int) ∧
      defectOrder (K := K) delta = ((d : ℚ) : WithTop ℚ) :=
  heADCUnitSharpDefectData delta hdelta hs

/-- Published first-column form of Lemma 7.19, with only the paper's unit,
defect, and unary-parameter hypotheses. -/
theorem heADC2025Lemma719FirstPublished (k : Nat) (delta c : Kˣ)
    (hdelta : IsValuationUnit K (delta : K))
    (hlt : quadraticDefect K delta <
      ((2 * ramificationIndex K : Nat) : ℕ∞))
    (hcOrder : ordUnit K c = 0 ∨ ordUnit K c = 1) :
    let D := heADC2025Lemma719_unitDefectData delta hdelta hlt
    HeADC719Conclusion
      ((Lattice.halfHyperbolicExtensionForm
        (heADC719BinarySpace 1 delta D.d (by simp [IsValuationUnit])
          hdelta D.odd D.nonnegative D.ltTwoE D.defect)
        (k + 1)).orthogonalSum ((QuadraticSpace.line K).rescaleUnit c))
      (Lattice.product
        (Lattice.halfHyperbolicExtensionLattice
          (BONG.binaryDiagonalModelLattice (K := K)) (k + 1))
        (BONG.unaryModelLattice (K := K))) k D.d := by
  dsimp only
  let D := heADC2025Lemma719_unitDefectData delta hdelta hlt
  exact heADC2025Lemma719First k delta c D.d hdelta D.odd
    D.nonnegative D.ltTwoE D.defect hcOrder

/-- Published second-column form of Lemma 7.19.  Its sharp parameter is
derived from `d(delta) < 2e`, not supplied by the caller. -/
theorem heADC2025Lemma719SecondPublished (k : Nat) (delta c : Kˣ)
    (hdelta : IsValuationUnit K (delta : K))
    (hlt : quadraticDefect K delta <
      ((2 * ramificationIndex K : Nat) : ℕ∞))
    (hcOrder : ordUnit K c = 0 ∨ ordUnit K c = 1) :
    let D := heADC2025Lemma719_unitDefectData delta hdelta hlt
    HeADC719Conclusion
      ((Lattice.halfHyperbolicExtensionForm
        (heADC719BinarySpace (heHuSharp delta D.sharp) delta D.d
          (heHu2022Proposition32 delta D.sharp).1 hdelta D.odd
          D.nonnegative D.ltTwoE D.defect) (k + 1)).orthogonalSum
        ((QuadraticSpace.line K).rescaleUnit c))
      (Lattice.product
        (Lattice.halfHyperbolicExtensionLattice
          (BONG.binaryDiagonalModelLattice (K := K)) (k + 1))
        (BONG.unaryModelLattice (K := K))) k D.d := by
  dsimp only
  let D := heADC2025Lemma719_unitDefectData delta hdelta hlt
  exact heADC2025Lemma719Second k delta c D.sharp D.d hdelta
    D.odd D.nonnegative D.ltTwoE D.defect hcOrder

end BONG.GoodBONG

end Bong
