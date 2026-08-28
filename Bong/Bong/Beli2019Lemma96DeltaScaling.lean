/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma96SquareBranch
import Bong.Bong.Beli2019Lemma96NormalForm
import Bong.Bong.Beli2019Lemma88Binary
import Bong.Bong.Beli2019Lemma73

/-!
# Beli (2019), Lemma 9.6: the critical Delta scaling

In the remaining ordinary-square branch, the preceding reduction gives
`R_4 - R_3 = 2e`.  Hence `alpha_3 = 2e`, and the distinguished
discriminant unit `Delta` lies in the norm group of the final binary pair.
The binary scaling theorem followed by Beli's segment replacement lemma
therefore changes the third BONG value by exactly `Delta`, inside the same
lattice and while fixing the first two values.
-/

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {N : Nat}

/-- The last binary pair `[a_3,a_4]` as an alpha-localization segment. -/
def lemma96LastPairLocalization : AlphaLocalizationIndex (N + 3) where
  start := 2
  pivot := 2
  stop := 3
  start_le_pivot := by omega
  pivot_lt_stop := by omega
  stop_lt := by omega

/-- The distinguished discriminant unit has rational defect order `2e`. -/
theorem defectOrder_discriminantUnit
    [laws : DyadicDiscriminantClassLaws K] :
    defectOrder (K := K) laws.discriminantUnit =
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) := by
  unfold defectOrder
  rw [laws.discriminant_defect]
  rfl

/-- At the equality boundary `R_4 = R_1 + 2e`, the third alpha occurring
in Lemma 9.6 is exactly `2e`. -/
theorem lemma96_thirdAlpha_eq_twoE
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M (N + 4))
    (houter : a.order (0 : Fin (N + 4)) = a.order (2 : Fin (N + 4)))
    (hfourth : a.order (3 : Fin (N + 4)) =
      a.order (0 : Fin (N + 4)) +
        2 * (ramificationIndex K : Int))
    (hdefect : a.Beli2019Lemma96DefectBound b) :
    a.alphaValue (2 : Fin (N + 3)) =
      2 * (ramificationIndex K : ℚ) := by
  have hlower := a.lemma96_targetThirdAlpha_ge_twoE b (by omega) hdefect
  have hgap : a.orderGap (2 : Fin (N + 3)) =
      2 * (ramificationIndex K : Int) := by
    change a.order (3 : Fin (N + 4)) - a.order (2 : Fin (N + 4)) = _
    rw [hfourth, ← houter]
    omega
  have hupper : a.alphaValue (2 : Fin (N + 3)) <=
      2 * (ramificationIndex K : ℚ) :=
    (a.alphaValue_le_twoE_iff_orderGap_le_twoE
      (2 : Fin (N + 3))).mpr hgap.le
  exact le_antisymm hupper hlower

/-- The equality-boundary third alpha attains its half-gap candidate, so it
localizes to the final binary pair. -/
theorem lemma96_thirdAttainsHalfGap
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M (N + 4))
    (houter : a.order (0 : Fin (N + 4)) = a.order (2 : Fin (N + 4)))
    (hfourth : a.order (3 : Fin (N + 4)) =
      a.order (0 : Fin (N + 4)) +
        2 * (ramificationIndex K : Int))
    (hdefect : a.Beli2019Lemma96DefectBound b) :
    a.AttainsHalfGap (2 : Fin (N + 3)) := by
  have halpha := a.lemma96_thirdAlpha_eq_twoE b houter hfourth hdefect
  have hgap : a.orderGap (2 : Fin (N + 3)) =
      2 * (ramificationIndex K : Int) := by
    change a.order (3 : Fin (N + 4)) - a.order (2 : Fin (N + 4)) = _
    rw [hfourth, ← houter]
    omega
  unfold AttainsHalfGap halfGapValue
  rw [halpha, hgap]
  push_cast
  ring

/-- The concrete full-rank coordinate change used in Lemma 9.6.  It is a
new good BONG of the original target lattice; the first two values are fixed
and the third is multiplied by the distinguished `Delta`. -/
structure Beli2019Lemma96DeltaScalingData
    [laws : DyadicDiscriminantClassLaws K]
    (a : GoodBONG q L (N + 4)) where
  transformed : GoodBONG q L (N + 4)
  firstValue_eq : transformed.valueUnit (0 : Fin (N + 4)) =
    a.valueUnit (0 : Fin (N + 4))
  secondValue_eq : transformed.valueUnit (1 : Fin (N + 4)) =
    a.valueUnit (1 : Fin (N + 4))
  thirdValue_eq : transformed.valueUnit (2 : Fin (N + 4)) =
    laws.discriminantUnit * a.valueUnit (2 : Fin (N + 4))

/-- Prescribed binary scaling by `Delta`, inserted into positions three and
four of the full BONG. -/
theorem exists_lemma96DeltaScaling
    [QuadraticDefectLaws K]
    [laws : DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [targetLaws : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M (N + 4))
    (houter : a.order (0 : Fin (N + 4)) = a.order (2 : Fin (N + 4)))
    (hfourth : a.order (3 : Fin (N + 4)) =
      a.order (0 : Fin (N + 4)) +
        2 * (ramificationIndex K : Int))
    (hdefect : a.Beli2019Lemma96DefectBound b) :
    Nonempty (Beli2019Lemma96DeltaScalingData a) := by
  let p := lemma96LastPairLocalization (N := N)
  let segment := a.toBONG.segmentWitness 2 2 (by omega)
  let s := segment.toGoodBONG a.good
  have hhalf := a.lemma96_thirdAttainsHalfGap b houter hfourth hdefect
  have hlocalAlpha : s.alphaValue (0 : Fin 1) =
      a.alphaValue (2 : Fin (N + 3)) := by
    have h := a.segmentAlpha_eq_global_of_attainsHalfGap p segment hhalf
    convert h using 1 <;> congr 1
  have hglobalAlpha := a.lemma96_thirdAlpha_eq_twoE
    b houter hfourth hdefect
  have hdeltaDefect : defectOrder (K := K) laws.discriminantUnit =
      (s.alphaValue (0 : Fin 1) : WithTop ℚ) := by
    rw [hlocalAlpha, hglobalAlpha, defectOrder_discriminantUnit]
    norm_num
  have hadjacent : s.adjacentProduct (0 : Fin 1) =
      -(a.valueUnit (2 : Fin (N + 4)) *
        a.valueUnit (3 : Fin (N + 4))) := by
    unfold adjacentProduct
    change -(segment.bong.valueUnit 0 * segment.bong.valueUnit 1) = _
    rw [segment.valueUnit_eq, segment.valueUnit_eq]
    congr 2
  have hadjacentOrder : Even
      (ordUnit K (s.adjacentProduct (0 : Fin 1))) := by
    have horderTwo : ordUnit K (a.valueUnit (2 : Fin (N + 4))) =
        a.order (2 : Fin (N + 4)) :=
      (a.toBONG.order_eq_ordUnit (2 : Fin (N + 4))).symm
    have horderThree : ordUnit K (a.valueUnit (3 : Fin (N + 4))) =
        a.order (3 : Fin (N + 4)) :=
      (a.toBONG.order_eq_ordUnit (3 : Fin (N + 4))).symm
    rw [hadjacent, ordUnit_neg, ordUnit_mul,
      horderTwo, horderThree, hfourth, ← houter]
    refine ⟨a.order (0 : Fin (N + 4)) +
      (ramificationIndex K : Int), ?_⟩
    omega
  have hhilbert : hilbertSymbol K laws.discriminantUnit
      (s.adjacentProduct (0 : Fin 1)) = 1 :=
    (hilbertSymbol_discriminant_eq_one_iff_even_order
      (s.adjacentProduct (0 : Fin 1))).mpr hadjacentOrder
  rcases s.beli2019Lemma88_binary_scaling_of_hilbert
      laws.discriminantUnit laws.discriminant_isValuationUnit
      hdeltaDefect hhilbert with ⟨c, hc⟩
  rcases a.toBONG.beliLemma49_ii a.good segment
      c.toBONG c.good with ⟨replacement⟩
  let transformed : GoodBONG q L (N + 4) :=
    ⟨replacement.bong, replacement.good⟩
  have beforeValue_eq (i : Fin (N + 4)) (hi : i.1 < 2) :
      transformed.valueUnit i = a.valueUnit i := by
    apply Units.ext
    change replacement.bong.value i = a.toBONG.value i
    rw [← replacement.bong.quadratic_ambientVector,
      ← a.toBONG.quadratic_ambientVector]
    exact congrArg q.quadratic (replacement.before_eq i hi)
  have hthirdLocal : transformed.valueUnit (2 : Fin (N + 4)) =
      c.valueUnit (0 : Fin 2) := by
    apply Units.ext
    change replacement.bong.value 2 = c.toBONG.value 0
    rw [← replacement.bong.quadratic_ambientVector,
      ← c.toBONG.quadratic_ambientVector]
    change q.quadratic (replacement.bong.ambientVector 2) =
      q.quadratic (c.toBONG.ambientVector 0 : V)
    have hinside := replacement.inside_eq (0 : Fin 2)
    convert congrArg q.quadratic hinside using 1 <;> congr 1
  have hsegmentFirst : s.valueUnit (0 : Fin 2) =
      a.valueUnit (2 : Fin (N + 4)) := by
    change segment.bong.valueUnit 0 = a.toBONG.valueUnit 2
    rw [segment.valueUnit_eq]
    congr 1
  exact ⟨{
    transformed := transformed
    firstValue_eq := beforeValue_eq (0 : Fin (N + 4)) (by norm_num)
    secondValue_eq := beforeValue_eq (1 : Fin (N + 4)) (by norm_num)
    thirdValue_eq := hthirdLocal.trans <| hc.trans <|
      congrArg (laws.discriminantUnit * ·) hsegmentFirst
  }⟩

namespace Beli2019Lemma96DeltaScalingData

variable [laws : DyadicDiscriminantClassLaws K]
  {a : GoodBONG q L (N + 4)}

/-- The first-three determinant acquires exactly one discriminant factor. -/
theorem prefixProduct_three_eq
    (D : Beli2019Lemma96DeltaScalingData a) :
    D.transformed.prefixProduct 3 =
      laws.discriminantUnit * a.prefixProduct 3 := by
  unfold GoodBONG.prefixProduct
  rw [D.transformed.toBONG.prefixProduct_succ 2 (by omega),
    D.transformed.toBONG.prefixProduct_succ 1 (by omega),
    D.transformed.toBONG.prefixProduct_succ 0 (by omega),
    a.toBONG.prefixProduct_succ 2 (by omega),
    a.toBONG.prefixProduct_succ 1 (by omega),
    a.toBONG.prefixProduct_succ 0 (by omega)]
  simp only [BONG.prefixProduct_zero, one_mul]
  have hfirst : D.transformed.toBONG.valueUnit ⟨0, by omega⟩ =
      a.toBONG.valueUnit ⟨0, by omega⟩ := by
    convert D.firstValue_eq using 1 <;> congr 1
  have hsecond : D.transformed.toBONG.valueUnit ⟨1, by omega⟩ =
      a.toBONG.valueUnit ⟨1, by omega⟩ := by
    convert D.secondValue_eq using 1 <;> congr 1
  have hthird : D.transformed.toBONG.valueUnit ⟨2, by omega⟩ =
      laws.discriminantUnit * a.toBONG.valueUnit ⟨2, by omega⟩ := by
    convert D.thirdValue_eq using 1 <;> congr 1
  rw [hfirst, hsecond, hthird]
  ac_rfl

/-- Dividing the new raw first-third product by `Delta` recovers the old
raw product, so the ordinary square branch becomes the discriminant branch. -/
theorem twistedRawSquare
    (D : Beli2019Lemma96DeltaScalingData a)
    (b : GoodBONG r M (N + 4))
    (hrawSquare : IsSquare
      ((-1) * a.prefixProduct 3 * b.prefixProduct 1)) :
    IsSquare
      (((-1) * D.transformed.prefixProduct 3 * b.prefixProduct 1) /
        laws.discriminantUnit) := by
  rw [D.prefixProduct_three_eq]
  have heq :
      (((-1 : Kˣ) * (laws.discriminantUnit * a.prefixProduct 3) *
          b.prefixProduct 1) / laws.discriminantUnit) =
        (-1) * a.prefixProduct 3 * b.prefixProduct 1 := by
    simp only [div_eq_mul_inv]
    calc
      (-1 : Kˣ) * (laws.discriminantUnit * a.prefixProduct 3) *
            b.prefixProduct 1 * laws.discriminantUnit⁻¹ =
          (laws.discriminantUnit * laws.discriminantUnit⁻¹) *
            ((-1) * a.prefixProduct 3 * b.prefixProduct 1) := by
        ac_rfl
      _ = (-1) * a.prefixProduct 3 * b.prefixProduct 1 := by simp
  rw [heq]
  exact hrawSquare

/-- Scaling the third coefficient by `Delta` preserves ternary isotropy in
the Lemma 9.6 order pattern.  The extra Hilbert factor is trivial because
the first adjacent product has even valuation. -/
theorem firstThreeIsotropic_iff
    [DyadicUnramifiedNormLaws K]
    [HilbertSymbolLaws K]
    (D : Beli2019Lemma96DeltaScalingData a)
    (hfirstGap :
      a.order (1 : Fin (N + 4)) - a.order (0 : Fin (N + 4)) =
        2 * (ramificationIndex K : Int) - 2) :
    D.transformed.Lemma814FirstThreeIsotropic ↔
      a.Lemma814FirstThreeIsotropic := by
  let oldHead : Fin 3 → Kˣ := a.prefixValueUnits 3 (by omega)
  let newHead : Fin 3 → Kˣ :=
    D.transformed.prefixValueUnits 3 (by omega)
  have holdValues : a.prefixValues 3 (by omega) =
      diagonalUnitCoefficients oldHead := by
    exact (a.diagonalUnitCoefficients_prefixValueUnits 3 (by omega)).symm
  have hnewValues : D.transformed.prefixValues 3 (by omega) =
      diagonalUnitCoefficients newHead := by
    exact (D.transformed.diagonalUnitCoefficients_prefixValueUnits
      3 (by omega)).symm
  have hfirstAdjacent :
      -(newHead 0 * newHead 1) = -(oldHead 0 * oldHead 1) := by
    dsimp only [newHead, oldHead, prefixValueUnits]
    have hzero :
        D.transformed.valueUnit ⟨(0 : Fin 3).val, by omega⟩ =
          a.valueUnit ⟨(0 : Fin 3).val, by omega⟩ := by
      convert D.firstValue_eq using 1 <;> congr 1
    have hone :
        D.transformed.valueUnit ⟨(1 : Fin 3).val, by omega⟩ =
          a.valueUnit ⟨(1 : Fin 3).val, by omega⟩ := by
      convert D.secondValue_eq using 1 <;> congr 1
    rw [hzero, hone]
  have hsecondAdjacent :
      -(newHead 1 * newHead 2) =
        laws.discriminantUnit * (-(oldHead 1 * oldHead 2)) := by
    dsimp only [newHead, oldHead, prefixValueUnits]
    have hone :
        D.transformed.valueUnit ⟨(1 : Fin 3).val, by omega⟩ =
          a.valueUnit ⟨(1 : Fin 3).val, by omega⟩ := by
      convert D.secondValue_eq using 1 <;> congr 1
    have htwo :
        D.transformed.valueUnit ⟨(2 : Fin 3).val, by omega⟩ =
          laws.discriminantUnit *
            a.valueUnit ⟨(2 : Fin 3).val, by omega⟩ := by
      convert D.thirdValue_eq using 1 <;> congr 1
    rw [hone, htwo]
    apply Units.ext
    simp only [Units.val_neg, Units.val_mul]
    ring
  let firstAdjacent : Kˣ := -(oldHead 0 * oldHead 1)
  have hfirstOrder : ordUnit K firstAdjacent =
      a.order (0 : Fin (N + 4)) + a.order (1 : Fin (N + 4)) := by
    dsimp only [firstAdjacent, oldHead, prefixValueUnits]
    rw [ordUnit_neg, ordUnit_mul]
    have hzero : ordUnit K
        (a.valueUnit ⟨(0 : Fin 3).val, by omega⟩) =
          a.order (0 : Fin (N + 4)) := by
      convert (a.toBONG.order_eq_ordUnit
        (0 : Fin (N + 4))).symm using 1 <;> congr 1
    have hone : ordUnit K
        (a.valueUnit ⟨(1 : Fin 3).val, by omega⟩) =
          a.order (1 : Fin (N + 4)) := by
      convert (a.toBONG.order_eq_ordUnit
        (1 : Fin (N + 4))).symm using 1 <;> congr 1
    rw [hzero, hone]
  have hfirstEven : Even (ordUnit K firstAdjacent) := by
    rw [hfirstOrder]
    refine ⟨a.order (0 : Fin (N + 4)) +
      (ramificationIndex K : Int) - 1, ?_⟩
    omega
  have hdeltaFirst :
      hilbertSymbol K firstAdjacent laws.discriminantUnit = 1 := by
    rw [hilbertSymbol_comm]
    exact (hilbertSymbol_discriminant_eq_one_iff_even_order
      firstAdjacent).mpr hfirstEven
  have hhilbert :
      hilbertSymbol K (-(newHead 0 * newHead 1))
          (-(newHead 1 * newHead 2)) =
        hilbertSymbol K (-(oldHead 0 * oldHead 1))
          (-(oldHead 1 * oldHead 2)) := by
    rw [hfirstAdjacent, hsecondAdjacent]
    change hilbertSymbol K firstAdjacent
        (laws.discriminantUnit * (-(oldHead 1 * oldHead 2))) = _
    rw [hilbertSymbol_mul_right, hdeltaFirst, one_mul]
  change DiagonalIsotropic (D.transformed.prefixValues 3 (by omega)) ↔
    DiagonalIsotropic (a.prefixValues 3 (by omega))
  rw [holdValues, hnewValues,
    diagonalUnitTernary_isotropic_iff_adjacentHilbertOne,
    diagonalUnitTernary_isotropic_iff_adjacentHilbertOne,
    hhilbert]

/-- In particular, the first ternary prefix remains anisotropic after the
critical `Delta` scaling, as asserted in the paper. -/
theorem firstThreeAnisotropic
    [DyadicUnramifiedNormLaws K]
    [HilbertSymbolLaws K]
    (D : Beli2019Lemma96DeltaScalingData a)
    (hfirstGap :
      a.order (1 : Fin (N + 4)) - a.order (0 : Fin (N + 4)) =
        2 * (ramificationIndex K : Int) - 2)
    (hanisotropic : a.Lemma814FirstThreeAnisotropic) :
    D.transformed.Lemma814FirstThreeAnisotropic := by
  change DiagonalAnisotropic (D.transformed.prefixValues 3 (by omega))
  apply (not_diagonalIsotropic_iff_diagonalAnisotropic _).mp
  intro hnew
  have hold : a.Lemma814FirstThreeIsotropic :=
    (D.firstThreeIsotropic_iff hfirstGap).mp hnew
  change DiagonalAnisotropic (a.prefixValues 3 (by omega)) at hanisotropic
  exact ((not_diagonalIsotropic_iff_diagonalAnisotropic _).mpr
    hanisotropic) hold

end Beli2019Lemma96DeltaScalingData

/-- The output of the complete head reduction in Lemma 9.6.  The target
good BONG may be the original one or its critical `Delta`-scaled replacement,
but it belongs to the same lattice, has the same order sequence, and carries
the exact matched unary--binary normal form. -/
structure Beli2019Lemma96HeadReductionData
    [DyadicDiscriminantClassLaws K]
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M (N + 4)) where
  targetBONG : GoodBONG q L (N + 4)
  sameOrders : a.SameOrders targetBONG
  matchedNormalForm :
    Beli2019Lemma96MatchedNormalFormData targetBONG b

/-- The ordinary square branch is converted by the critical `Delta`
scaling, while the discriminant branch goes directly to the normal form.
Thus both branches of the maximal-defect dichotomy now produce the exact
matched head required by the projected-tail argument of Lemma 9.6. -/
theorem beli2019Lemma96_headReduction
    [QuadraticDefectLaws K]
    [laws : DyadicDiscriminantClassLaws K]
    [DyadicMaximalDefectClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [BONGStructuralLaws.{u, u} K]
    [Beli2009WeightIdealData.{u, u} K]
    [Beli2019UnaryBinaryJordanLaws.{u} K]
    [Beli2009JordanWeightOrderLaws.{u, u} K]
    [targetAlpha : Beli2006AlphaLaws.{u, v} K]
    [sourceAlpha : Beli2006AlphaLaws.{u, w} K]
    [modelAlpha : Beli2006AlphaLaws.{u, u} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [HilbertSymbolLaws K]
    [DyadicDiagonalClassificationLaws K]
    [modelClassification : GoodBONGClassificationLaws.{u, v, u} K]
    [targetClassification : GoodBONGClassificationLaws.{u, v, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [DyadicTernaryRepresentationObstructionLaws K]
    (a : GoodBONG q L (N + 4)) (b : GoodBONG r M (N + 4))
    (hconditions : RepresentationConditions a b (Nat.le_refl (N + 3)))
    (houter : a.order (0 : Fin (N + 4)) =
      a.order (2 : Fin (N + 4)))
    (hfirstGap :
      a.order (1 : Fin (N + 4)) - a.order (0 : Fin (N + 4)) =
        2 * (ramificationIndex K : Int) - 2)
    (hsourceOrder : b.order (0 : Fin (N + 4)) =
      a.order (0 : Fin (N + 4)))
    (hdefect : a.Beli2019Lemma96DefectBound b)
    (hanisotropic : a.Lemma814FirstThreeAnisotropic) :
    Nonempty (Beli2019Lemma96HeadReductionData a b) := by
  rcases a.lemma96_rawSquareClassCases b hdefect with
    hrawSquare | htwisted
  · have hfourth := a.beli2019Lemma96_fourthOrder_eq_of_rawSquare
      (targetLaws := targetAlpha) (sourceLaws := sourceAlpha)
      b hconditions ⟨houter, hsourceOrder.symm⟩ hdefect
      hanisotropic hrawSquare
    rcases a.exists_lemma96DeltaScaling
        (targetLaws := targetAlpha) b houter hfourth hdefect with ⟨D⟩
    have horders : a.SameOrders D.transformed := by
      letI : GoodBONGClassificationLaws.{u, v, v} K :=
        targetClassification
      exact a.order_invariant D.transformed
    have houter' : D.transformed.order (0 : Fin (N + 4)) =
        D.transformed.order (2 : Fin (N + 4)) := by
      rw [← horders (0 : Fin (N + 4)),
        ← horders (2 : Fin (N + 4))]
      exact houter
    have hfirstGap' :
        D.transformed.order (1 : Fin (N + 4)) -
            D.transformed.order (0 : Fin (N + 4)) =
          2 * (ramificationIndex K : Int) - 2 := by
      rw [← horders (1 : Fin (N + 4)),
        ← horders (0 : Fin (N + 4))]
      exact hfirstGap
    have hsourceOrder' : b.order (0 : Fin (N + 4)) =
        D.transformed.order (0 : Fin (N + 4)) :=
      hsourceOrder.trans (horders (0 : Fin (N + 4)))
    have hanisotropic' :
        D.transformed.Lemma814FirstThreeAnisotropic :=
      D.firstThreeAnisotropic hfirstGap hanisotropic
    have htwisted' := D.twistedRawSquare b hrawSquare
    letI : GoodBONGClassificationLaws.{u, v, u} K :=
      modelClassification
    rcases D.transformed.beli2019Lemma96_matchedNormalForm_of_twistedRawSquare
        (targetAlpha := targetAlpha) (modelAlpha := modelAlpha)
        b houter' hfirstGap' hanisotropic' hsourceOrder' htwisted' with
      ⟨E⟩
    exact ⟨{
      targetBONG := D.transformed
      sameOrders := horders
      matchedNormalForm := E
    }⟩
  · letI : GoodBONGClassificationLaws.{u, v, u} K :=
      modelClassification
    rcases a.beli2019Lemma96_matchedNormalForm_of_twistedRawSquare
        (targetAlpha := targetAlpha) (modelAlpha := modelAlpha)
        b houter hfirstGap hanisotropic hsourceOrder htwisted with ⟨E⟩
    exact ⟨{
      targetBONG := a
      sameOrders := fun _ ↦ rfl
      matchedNormalForm := E
    }⟩

end BONG.GoodBONG

end Bong
