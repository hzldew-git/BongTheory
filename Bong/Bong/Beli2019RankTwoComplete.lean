/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019RankTwo
import Bong.Bong.Beli2019Lemma714RescaledBinary
import Bong.Bong.Beli2019Lemma716DefectEasy
import Bong.Bong.Beli2019SectionSevenStrictCommonSpace
import Bong.Bong.BinaryHyperbolicEndpoint
import Bong.Bong.BinaryEndpointProduct
import Bong.Dyadic.UnramifiedNorm

/-!
# Beli (2019): the complete rank-two boundary

At the minimal binary gap `-2e`, the endpoint square class is either
hyperbolic or discriminant.  The hyperbolic branch is norm-maximal.  In the
discriminant branch the unramified norm-group parity excludes a first-order
jump of one, after which the literal sublattice `pi L` satisfies all four
representation conditions and gives a strict rank-volume descent.

Together with the ordinary Section 7 construction away from the endpoint
and the equal-norm calculation, this closes every rank-two counterexample.
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
  {L : Lattice K V} {M : Lattice K W} {N : Lattice K V}

/-- A discriminant binary endpoint cannot represent a unary coefficient
whose order is exactly one above its first order. -/
theorem discriminantEndpoint_not_firstOrder_add_one
    [laws : DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [HilbertSymbolLaws K]
    (a : GoodBONG q L 2) (c : GoodBONG q N 2)
    (hclass : a.toBONG.binaryUnitSquareClass = unitSquareClass K
      (negativeQuarterUnit K * laws.discriminantUnit))
    (hfirst : c.order (0 : Fin 2) = a.order (0 : Fin 2) + 1) :
    False := by
  let a₀ : Kˣ := a.valueUnit (0 : Fin 2)
  let a₁ : Kˣ := a.valueUnit (1 : Fin 2)
  let c₀ : Kˣ := c.valueUnit (0 : Fin 2)
  have hsigned : IsSquare (-(a₀ * a₁) * laws.discriminantUnit) := by
    have hparameter :=
      isSquare_neg_mul_discriminant_of_endpointClass hclass
    have hproduct : -(a₀ * a₁) =
        (-(a.toBONG.binaryParameter)) * a₀ ^ 2 := by
      unfold BONG.binaryParameter
      apply Units.ext
      simp only [a₀, a₁, GoodBONG.valueUnit, Units.val_neg,
        Units.val_mul, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val]
      field_simp [Units.ne_zero (a.toBONG.valueUnit 0)]
    rw [hproduct]
    have hreorder :
        ((-(a.toBONG.binaryParameter)) * a₀ ^ 2) *
            laws.discriminantUnit =
          (-(a.toBONG.binaryParameter) * laws.discriminantUnit) *
            a₀ ^ 2 := by
      apply Units.ext
      simp only [Units.val_neg, Units.val_mul, Units.val_pow_eq_pow_val]
      ring
    rw [hreorder]
    exact hparameter.mul ⟨a₀, by simp [pow_two]⟩
  have hfull : DiagonalRepresents c.toBONG.value a.toBONG.value :=
    a.toBONG.diagonalRepresents_of_ambient c.toBONG
      (QuadraticSpace.represents_refl q)
  have hunaryPrefix :
      DiagonalRepresents
        (fun i : Fin 1 => c.toBONG.value ⟨i.val, i.isLt.trans_le (by omega)⟩)
        c.toBONG.value :=
    DiagonalRepresents.prefixOfLE c.toBONG.value (by omega)
  have hunary : DiagonalRepresents
      (fun i : Fin 1 => c.toBONG.value ⟨i.val, i.isLt.trans_le (by omega)⟩)
      a.toBONG.value := hunaryPrefix.trans hfull
  have hrepUnits : DiagonalRepresents
      (fun _ : Fin 1 => (c₀ : K))
      (Fin.cons (a₀ : K) (fun _ : Fin 1 => (a₁ : K))) := by
    convert hunary using 1
    · funext i
      fin_cases i
      rfl
    · funext i
      fin_cases i <;> rfl
  have hhilbert :
      hilbertSymbol K (c₀ * a₀⁻¹) (-(a₀ * a₁)) = 1 :=
    (DiagonalRepresents.unary_binary_iff_hilbertSymbol_one a₀ a₁ c₀).mp
      hrepUnits
  have hhilbert' :
      hilbertSymbol K laws.discriminantUnit (c₀ * a₀⁻¹) = 1 := by
    have hsame := hilbertSymbol_eq_discriminant_of_isSquare_mul_discriminant
      (K := K) (b := c₀ * a₀⁻¹) hsigned
    rw [hilbertSymbol_comm K (c₀ * a₀⁻¹) (-(a₀ * a₁))] at hhilbert
    rw [hsame] at hhilbert
    exact hhilbert
  have heven : Even (ordUnit K (c₀ * a₀⁻¹)) :=
    (hilbertSymbol_discriminant_eq_one_iff_even_order
      (c₀ * a₀⁻¹)).mp hhilbert'
  have hratioOrder : ordUnit K (c₀ * a₀⁻¹) = 1 := by
    rw [ordUnit_mul, ordUnit_inv]
    change c.order 0 - a.order 0 = 1
    omega
  rw [hratioOrder] at heven
  rcases heven with ⟨k, hk⟩
  omega

/-- If the source first order is at least two above a discriminant endpoint,
then uniformly rescaling the target binary lattice by the uniformizer
preserves all four representation conditions. -/
theorem rescaledBinary_representationConditions
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L 2) (c : GoodBONG q N 2)
    (hgap : a.order (1 : Fin 2) - a.order (0 : Fin 2) =
      -(2 * (ramificationIndex K : Int)))
    (hfirst : a.order (0 : Fin 2) + 2 ≤ c.order (0 : Fin 2)) :
    RepresentationConditions a.lemma714RescaledBinary c le_rfl := by
  have hsourceGap := c.orderGap_ge_neg_two_mul_e (0 : Fin 1)
  unfold orderGap at hsourceGap
  change -(2 * (ramificationIndex K : Int)) ≤
    c.order (1 : Fin 2) - c.order (0 : Fin 2) at hsourceGap
  have hsecond : a.order (1 : Fin 2) + 2 ≤ c.order (1 : Fin 2) := by
    omega
  refine {
    orderCondition := ?_
    defectCondition := ?_
    centralRepresentations := ?_
    longRepresentations := ?_ }
  · intro i
    left
    fin_cases i
    · simpa using hfirst
    · simpa using hsecond
  · apply (a.lemma714RescaledBinary.representationDefectCondition_iff_forall_at c).2
    intro i
    apply a.lemma714RescaledBinary.representationDefectAt_of_add_twoE_le c i
    have hipos := i.pos
    have hilt := i.lt_large
    have hi : i.val = 1 := by omega
    simp [hi]
    omega
  · intro i
    have := i.one_lt
    have := i.lt_large
    omega
  · intro i
    have := i.one_lt
    have := i.succ_lt_large
    omega

/-- The discriminant endpoint produces the literal strict sublattice
reduction `pi L`. -/
theorem exists_discriminantEndpoint_sublatticeReduction
    [laws : DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [HilbertSymbolLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L 2) (b : GoodBONG r M 2)
    (ambient : q.Represents r)
    (conditions : RepresentationConditions a b le_rfl)
    (hgap : a.order (1 : Fin 2) - a.order (0 : Fin 2) =
      -(2 * (ramificationIndex K : Int)))
    (hclass : a.toBONG.binaryUnitSquareClass = unitSquareClass K
      (negativeQuarterUnit K * laws.discriminantUnit))
    (hfirstLt : a.order (0 : Fin 2) < b.order (0 : Fin 2)) :
    Nonempty (Beli2019RepresentationProblem.SublatticeReduction
      (Beli2019RepresentationProblem.ofData
        a b le_rfl ambient conditions)) := by
  let D : Beli2019SameRankCommonSpace a b :=
    Beli2019SameRankCommonSpace.ofAmbient ambient
  let c : GoodBONG q D.sourceImage 2 := D.sourceImageBONG
  have hfirstImageLt : a.order (0 : Fin 2) < c.order (0 : Fin 2) := by
    calc
      a.order (0 : Fin 2) < b.order (0 : Fin 2) := hfirstLt
      _ = c.order (0 : Fin 2) := D.source_scalarAgreement.order_eq 0
  have hfirstImageNe : c.order (0 : Fin 2) ≠ a.order (0 : Fin 2) + 1 := by
    intro hfirst
    exact discriminantEndpoint_not_firstOrder_add_one a c hclass hfirst
  have hfirstImageTwo :
      a.order (0 : Fin 2) + 2 ≤ c.order (0 : Fin 2) := by
    omega
  have conditionsImage :
      RepresentationConditions a.lemma714RescaledBinary c le_rfl :=
    rescaledBinary_representationConditions a c hgap hfirstImageTwo
  have conditionsOriginal :
      RepresentationConditions a.lemma714RescaledBinary b le_rfl :=
    (ScalarAgreement.refl a.lemma714RescaledBinary)
      |>.representationConditions_transport
        D.source_scalarAgreement.symm conditionsImage
  let P := Beli2019RepresentationProblem.ofData
    a b le_rfl ambient conditions
  letI : AddCommGroup P.Target := P.targetAddCommGroup
  letI : Module K P.Target := P.targetModule
  letI : AddCommGroup P.Source := P.sourceAddCommGroup
  letI : Module K P.Source := P.sourceModule
  change Nonempty (Beli2019RepresentationProblem.SublatticeReduction P)
  exact ⟨{
    index_eq := rfl
    lattice := Lattice.rescale (uniformizerUnit K) L
    lattice_le := a.lemma714RescaledBinary_lattice_le
    volumeOrder_lt := a.lemma714RescaledBinary_volumeOrder_lt
    targetBONG := a.lemma714RescaledBinary
    conditions := conditionsOriginal }⟩

/-- The hyperbolic endpoint is represented directly by norm maximality. -/
theorem hyperbolicEndpoint_sufficiency
    [structural : BONGStructuralLaws.{u, v} K]
    [maximal : ScaledHyperbolicMaximalLaws.{u, v, v} K]
    (a : GoodBONG q L 2) (b : GoodBONG r M 2)
    (ambient : q.Represents r)
    (conditions : RepresentationConditions a b le_rfl)
    (hclass : a.toBONG.binaryUnitSquareClass =
      unitSquareClass K (negativeQuarterUnit K)) :
    Lattice.Represents q r L M := by
  let D : Beli2019SameRankCommonSpace a b :=
    Beli2019SameRankCommonSpace.ofAmbient ambient
  let c : GoodBONG q D.sourceImage 2 := D.sourceImageBONG
  have conditionsImage : RepresentationConditions a c le_rfl :=
    D.conditions conditions
  have horders : ∀ i, a.order i ≤ c.order i := by
    intro i
    rcases conditionsImage.orderCondition i with h | h
    · exact h
    · rcases h with ⟨hi0, hiLarge, _⟩
      omega
  have hhyperbolic : Lattice.IsScaledHyperbolicLattice q L :=
    a.toBONG.isScaledHyperbolicLattice_of_binaryUnitSquareClass_eq_negativeQuarter
      hclass
  have himage : Lattice.Represents q q L D.sourceImage :=
    beli2019Lemma97_ii
      (structuralV := structural) (structuralW := structural)
      (maximalVW := maximal) (maximalWV := maximal)
      a c horders (QuadraticSpace.isIsometric_refl q) (Or.inl hhyperbolic)
  exact D.represents_image_iff.mp himage

/-- Every unequal-norm rank-two counterexample either descends through the
ordinary Section 7 construction or through the discriminant sublattice.
The hyperbolic endpoint cannot be a counterexample. -/
theorem rankTwo_equalNorm_or_counterexampleDescent
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [structuralV : BONGStructuralLaws.{u, v} K]
    [QuadraticDefectLaws K]
    [PerfectResidueFieldLaws K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [laws : DyadicDiscriminantClassLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    [DyadicUnramifiedNormLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DyadicDiagonalCodimensionTwoLaws K]
    [Beli2019SectionFiveLaws.{u, v} K]
    [Beli2019SectionFourLaws.{u, v} K]
    [BeliCorollary44Laws.{u, v} K]
    [ScaledHyperbolicMaximalLaws.{u, v, v} K]
    (a : GoodBONG q L 2) (b : GoodBONG r M 2)
    (ambient : q.Represents r)
    (conditions : RepresentationConditions a b le_rfl)
    (hp : (Beli2019RepresentationProblem.ofData
      a b le_rfl ambient conditions).Counterexample) :
    (Beli2019RepresentationProblem.ofData
      a b le_rfl ambient conditions).EqualNorm ∨
      ∃ next, next.Counterexample ∧
        next.sourceIndex = next.targetIndex ∧
        next.sourceIndex = 1 ∧
        Beli2019ProblemSmaller Beli2019RepresentationProblem.measure next
          (Beli2019RepresentationProblem.ofData
            a b le_rfl ambient conditions) := by
  let p := Beli2019RepresentationProblem.ofData
    a b le_rfl ambient conditions
  letI : AddCommGroup p.Target := p.targetAddCommGroup
  letI : Module K p.Target := p.targetModule
  letI : AddCommGroup p.Source := p.sourceAddCommGroup
  letI : Module K p.Source := p.sourceModule
  by_cases hequal : p.EqualNorm
  · exact Or.inl hequal
  · right
    have hfirstLe : a.order (0 : Fin 2) ≤ b.order (0 : Fin 2) := by
      rcases conditions.orderCondition (0 : Fin 2) with h | h
      · exact h
      · rcases h with ⟨hi0, _⟩
        simp at hi0
    have hfirstNe : a.order (0 : Fin 2) ≠ b.order (0 : Fin 2) := by
      intro h
      apply hequal
      exact (Beli2019RepresentationProblem.equalNorm_iff_firstOrder_eq p).2 h
    have hfirstLt : a.order (0 : Fin 2) < b.order (0 : Fin 2) :=
      lt_of_le_of_ne hfirstLe hfirstNe
    have hnorm : Lattice.normIdeal r M < Lattice.normIdeal q L := by
      rw [a.toBONG.normIdeal_eq_powerIdeal_order_zero,
        b.toBONG.normIdeal_eq_powerIdeal_order_zero,
        Lattice.powerIdeal_lt_iff]
      exact hfirstLt
    by_cases hgap : a.order (1 : Fin 2) - a.order (0 : Fin 2) =
        -(2 * (ramificationIndex K : Int))
    · have hclasses := a.toBONG.adjacentUnitSquareClass_endpoint_cases
          (0 : Fin 2) (by omega) hgap
      change a.toBONG.binaryUnitSquareClass =
          unitSquareClass K (negativeQuarterUnit K) ∨
        a.toBONG.binaryUnitSquareClass = unitSquareClass K
          (negativeQuarterUnit K * laws.discriminantUnit) at hclasses
      rcases hclasses with hquarter | hdiscriminant
      · exact (hp (hyperbolicEndpoint_sufficiency
          (structural := structuralV) a b ambient conditions hquarter)).elim
      · rcases exists_discriminantEndpoint_sublatticeReduction
            a b ambient conditions hgap hdiscriminant hfirstLt with ⟨R⟩
        exact ⟨R.next, R.nextCounterexample p hp, rfl, rfl, R.smaller⟩
    · let R := sectionSevenStrictIndexPReduction_of_ambient
          (n := 0) a b ambient conditions hgap hnorm
      exact ⟨R.next, R.nextCounterexample p hp, rfl, rfl, R.smaller⟩

end BONG.GoodBONG

namespace Beli2019RepresentationProblem

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- Complete rank-two boundary theorem for the final rank-volume induction. -/
theorem not_counterexample_of_sourceIndex_eq_one
    [alphaV : Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [structuralV : BONGStructuralLaws.{u, v} K]
    [QuadraticDefectLaws K]
    [PerfectResidueFieldLaws K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicDiscriminantClassLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    [DyadicUnramifiedNormLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    [DiagonalCodimensionOneCancellationLaws K]
    [DyadicDiagonalCodimensionTwoLaws K]
    [Beli2019SectionFiveLaws.{u, v} K]
    [Beli2019SectionFourLaws.{u, v} K]
    [BeliCorollary44Laws.{u, v} K]
    [ScaledHyperbolicMaximalLaws.{u, v, v} K]
    [Beli2009BinaryNormContainmentLaws (K := K)]
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    (p : Beli2019RepresentationProblem.{u, v, w} K)
    (hindex : p.sourceIndex = p.targetIndex)
    (hone : p.sourceIndex = 1) : ¬p.Counterexample := by
  revert hindex hone
  apply (beli2019ProblemSmaller_wellFounded measure).induction p
  intro current ih hindexCurrent honeCurrent hp
  letI : AddCommGroup current.Target := current.targetAddCommGroup
  letI : Module K current.Target := current.targetModule
  letI : AddCommGroup current.Source := current.sourceAddCommGroup
  letI : Module K current.Source := current.sourceModule
  let a := current.targetBONG.castLength
    (show current.targetIndex + 1 = 2 by omega)
  let b := current.sourceBONG.castLength
    (show current.sourceIndex + 1 = 2 by omega)
  let conditions' := representationConditions_castIndices
    current.targetBONG current.sourceBONG current.rankBound current.conditions
      (show current.targetIndex = 1 by omega) honeCurrent
  let p' := Beli2019RepresentationProblem.ofData a b
    (Nat.le_refl 1) current.ambient conditions'
  have hproblem : p' = current := by
    dsimp only [p', a, b, conditions']
    exact (ofData_castIndices_eq
      current.targetBONG current.sourceBONG current.rankBound current.ambient
        current.conditions (show current.targetIndex = 1 by omega) honeCurrent).trans
      (ofData_self current)
  have hp' : p'.Counterexample := by
    rwa [hproblem]
  have hparent : Beli2019RepresentationProblem.ofData a b
      (Nat.le_refl 1) current.ambient conditions' = current := by
    simpa only [p'] using hproblem
  have H := BONG.GoodBONG.rankTwo_equalNorm_or_counterexampleDescent
    (K := K) (V := current.Target) (W := current.Source)
    a b current.ambient conditions' hp'
  rcases H with hequal | ⟨next, hnext, hnextIndex, hnextRank, hsmaller⟩
  · have hequalCurrent : current.EqualNorm := by
      rwa [hparent] at hequal
    exact (not_counterexample_of_sourceIndex_eq_one_of_equalNorm
      (alphaLaws := alphaV) (structural := structuralV)
      current hindexCurrent honeCurrent hequalCurrent) hp
  · rw [hparent] at hsmaller
    exact ih next hsmaller hnextIndex hnextRank hnext

end Beli2019RepresentationProblem

end Bong
