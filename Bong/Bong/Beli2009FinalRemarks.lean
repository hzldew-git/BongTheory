/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009BinaryRemarks
import Bong.Bong.BeliLemma317
import Bong.Bong.Beli2009ClassificationProof
import Bong.Bong.Rescale
import Bong.Dyadic.UnitDefectClassification
import Bong.Lattice.ModularParameter
import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Beli (2009/2010), final remarks

This file records the exact recursive alpha formula behind the heuristic in
Section 5, defines the paper's binary transformations and their finite chains,
and gives precise interfaces for the residue-field dichotomy and the explicit
rank-four `ℚ₂` counterexample.  The two field-specific existence assertions
have no default instances because the paper only sketches them.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

namespace BONG.GoodBONG

/-- The heuristic recursion in Section 5 is the exact formula already proved
as Corollary 2.5(ii). -/
theorem beli2009Section5_recursiveAlphaFormula
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    (b : GoodBONG q L (n + 2)) (i : Fin (n + 1)) :
    b.alpha i =
      (b.segmentRecursiveAlphaCandidates i).min'
        (b.segmentRecursiveAlphaCandidates_nonempty i) :=
  b.beli2009Corollary25_ii i

end BONG.GoodBONG

/-- Apply a binary transformation at two neighboring positions. -/
def beli2009BinaryTransformAt
    (a : Fin (n + 1) → Kˣ) (i : Fin n) (η : Kˣ) :
    Fin (n + 1) → Kˣ :=
  Function.update
    (Function.update a i.castSucc (η * a i.castSucc))
    i.succ (η * a i.succ)

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K]
  [DyadicContext K] in
@[simp]
theorem beli2009BinaryTransformAt_castSucc
    (a : Fin (n + 1) → Kˣ) (i : Fin n) (η : Kˣ) :
    beli2009BinaryTransformAt a i η i.castSucc =
      η * a i.castSucc := by
  simp [beli2009BinaryTransformAt, ne_of_lt i.castSucc_lt_succ]

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K]
  [DyadicContext K] in
@[simp]
theorem beli2009BinaryTransformAt_succ
    (a : Fin (n + 1) → Kˣ) (i : Fin n) (η : Kˣ) :
    beli2009BinaryTransformAt a i η i.succ = η * a i.succ := by
  simp [beli2009BinaryTransformAt]

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K]
  [DyadicContext K] in
theorem beli2009BinaryTransformAt_of_ne
    (a : Fin (n + 1) → Kˣ) (i : Fin n) (η : Kˣ)
    (j : Fin (n + 1)) (hjleft : j ≠ i.castSucc)
    (hjright : j ≠ i.succ) :
    beli2009BinaryTransformAt a i η j = a j := by
  simp [beli2009BinaryTransformAt, hjleft, hjright]

/-- One of the binary transformations described at the end of Section 5. -/
def IsBeli2009BinaryTransformation
    (a b : Fin (n + 1) → Kˣ) : Prop :=
  ∃ (i : Fin n) (η : valuationUnitSubgroup K),
    valuationUnitClassHom K η ∈
        beliNormGeneratorGroup K (a i.succ / a i.castSucc) ∧
      b = beli2009BinaryTransformAt a i (η : Kˣ)

/-- Pointwise equality of BONG coefficients modulo squares of valuation
units.  This quotient is implicit in the paper's final discussion: its
explicit `ℚ₂` obstruction records whether each coefficient belongs to
`𝒪ˣ²`, `5𝒪ˣ²`, `7𝒪ˣ²`, or `3𝒪ˣ²`, rather than fixing representatives. -/
def Beli2009ValueSequenceEquivalent
    (a b : Fin (n + 1) → Kˣ) : Prop :=
  ∀ i, unitSquareClass K (a i) = unitSquareClass K (b i)

theorem beli2009ValueSequenceEquivalent_refl
    (a : Fin (n + 1) → Kˣ) :
    Beli2009ValueSequenceEquivalent (K := K) a a :=
  fun _ ↦ rfl

theorem Beli2009ValueSequenceEquivalent.symm
    {a b : Fin (n + 1) → Kˣ}
    (h : Beli2009ValueSequenceEquivalent (K := K) a b) :
    Beli2009ValueSequenceEquivalent (K := K) b a :=
  fun i ↦ (h i).symm

theorem Beli2009ValueSequenceEquivalent.trans
    {a b c : Fin (n + 1) → Kˣ}
    (hab : Beli2009ValueSequenceEquivalent (K := K) a b)
    (hbc : Beli2009ValueSequenceEquivalent (K := K) b c) :
    Beli2009ValueSequenceEquivalent (K := K) a c :=
  fun i ↦ (hab i).trans (hbc i)

/-- One admissible step in the paper's convention: either change only the
chosen representatives modulo valuation-unit squares, or perform one genuine
adjacent binary transformation. -/
def IsBeli2009BinaryStep
    (a b : Fin (n + 1) → Kˣ) : Prop :=
  Beli2009ValueSequenceEquivalent (K := K) a b ∨
    IsBeli2009BinaryTransformation (K := K) a b

/-- Reachability by a finite succession of binary transformations, with the
coefficient representatives understood modulo valuation-unit squares as in
the source. -/
def Beli2009BinaryReachable
    (a b : Fin (n + 1) → Kˣ) : Prop :=
  Relation.ReflTransGen (IsBeli2009BinaryStep (K := K)) a b

theorem beli2009BinaryReachable_refl (a : Fin (n + 1) → Kˣ) :
    Beli2009BinaryReachable (K := K) a a :=
  Relation.ReflTransGen.refl

theorem IsBeli2009BinaryTransformation.reachable
    {a b : Fin (n + 1) → Kˣ}
    (h : IsBeli2009BinaryTransformation (K := K) a b) :
    Beli2009BinaryReachable (K := K) a b :=
  Relation.ReflTransGen.single (Or.inr h)

theorem Beli2009ValueSequenceEquivalent.reachable
    {a b : Fin (n + 1) → Kˣ}
    (h : Beli2009ValueSequenceEquivalent (K := K) a b) :
    Beli2009BinaryReachable (K := K) a b :=
  Relation.ReflTransGen.single (Or.inl h)

theorem Beli2009BinaryReachable.trans
    {a b c : Fin (n + 1) → Kˣ}
    (hab : Beli2009BinaryReachable (K := K) a b)
    (hbc : Beli2009BinaryReachable (K := K) b c) :
    Beli2009BinaryReachable (K := K) a c :=
  Relation.ReflTransGen.trans hab hbc

/-- A counterexample consists of two good BONGs of the same rank-four
lattice which cannot be joined by binary transformations. -/
structure Beli2009BinaryTransformationCounterexample where
  carrier : ModuleCat.{v} K
  q : QuadraticSpace K carrier
  L : Lattice K carrier
  first : BONG.GoodBONG q L 4
  second : BONG.GoodBONG q L 4
  not_reachable : ¬Beli2009BinaryReachable (K := K)
    (fun i => first.valueUnit i) (fun i => second.valueUnit i)

/-- The unit `7` used in the explicit `ℚ₂` example at the end of the paper. -/
noncomputable def beli2009SevenUnit : Kˣ :=
  Units.mk0 (7 : K) (by norm_num)

/-- The order `R = 2e - 2d` in the residue-two counterexample. -/
noncomputable def beli2009ResidueTwoOrder (d : Nat) : Int :=
  2 * (ramificationIndex K : Int) - 2 * (d : Int)

/-- The first value sequence in the parameterized residue-two
counterexample. -/
noncomputable def beli2009ResidueTwoFirstValues
    (d : Nat) (epsilon eta : valuationUnitSubgroup K) : Fin 4 → Kˣ :=
  let piR := uniformizerPowerUnit K (beli2009ResidueTwoOrder (K := K) d)
  ![1, -(piR * (epsilon : Kˣ)),
    (epsilon : Kˣ) * (eta : Kˣ), -(piR * (eta : Kˣ))]

/-- The second value sequence in the parameterized residue-two
counterexample. -/
noncomputable def beli2009ResidueTwoSecondValues
    (d : Nat) (epsilon eta : valuationUnitSubgroup K) : Fin 4 → Kˣ :=
  let piR := uniformizerPowerUnit K (beli2009ResidueTwoOrder (K := K) d)
  ![(eta : Kˣ), -(piR * (epsilon : Kˣ) * (eta : Kˣ)),
    (epsilon : Kˣ), -piR]

private theorem one_le_order_of_mem_maximalIdeal
    {x : K} (hx : IsInMaximalIdeal K x) :
    (1 : WithTop Int) ≤ ord K x := by
  by_cases htop : ord K x = ⊤
  · rw [htop]
    exact le_top
  · obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp htop
    rw [← hd]
    change 0 < ord K x at hx
    rw [← hd] at hx
    exact_mod_cast (show (1 : Int) ≤ d by
      have : (0 : Int) < d := by exact_mod_cast hx
      omega)

/-- In the absolutely unramified residue-two case, the class `-1` has
relative quadratic defect exactly one.  This is the valuation calculation
behind the final `ℚ₂` example. -/
theorem beli2009_quadraticDefect_negOne_eq_one
    (htwoAdic : ramificationIndex K = 1)
    (hres : ¬BONG.HasResidueFieldMoreThanTwoElements (K := K)) :
    quadraticDefect K (-1 : Kˣ) = (1 : ℕ∞) := by
  have hresidue : ∀ z : K,
      IsValuationUnit K z → IsInMaximalIdeal K (z - 1) := by
    intro z hz
    by_contra hnot
    exact hres ⟨z, hz, hnot⟩
  have hminusOneUnit : IsValuationUnit K (((-1 : Kˣ) : K)) := by
    simp [IsValuationUnit]
  have hlower : (1 : ℕ∞) ≤ quadraticDefect K (-1 : Kˣ) :=
    one_le_quadraticDefect_of_unit (-1 : Kˣ) hminusOneUnit
  have hnoDepthTwo : ¬IsQuadraticApproximation K (-1 : Kˣ) 2 := by
    rintro ⟨x, hx⟩
    have hnormalized :
        1 - x ^ 2 / (((-1 : Kˣ) : K)) = 1 + x ^ 2 := by
      simp [div_eq_mul_inv]
    rw [hnormalized] at hx
    have herrorPos : (0 : WithTop Int) < ord K (1 + x ^ 2) := by
      exact (show (0 : WithTop Int) < 2 by norm_num).trans_le hx
    have hxSqOrder : ord K (x ^ 2) = 0 := by
      have hstrict : ord K (1 : K) < ord K (1 + x ^ 2) := by
        simpa only [ord_one] using herrorPos
      have hsub := (ord K).map_sub_eq_of_lt_left hstrict
      have heq : (1 : K) - (1 + x ^ 2) = -(x ^ 2) := by ring
      simpa only [heq, ord_neg, ord_one] using hsub
    have hxNe : x ≠ 0 := by
      intro hzero
      subst x
      simp at hxSqOrder
    let xu : Kˣ := Units.mk0 x hxNe
    have hxuPowOrder : ordUnit K (xu ^ 2) = 0 := by
      apply WithTop.coe_injective
      rw [coe_ordUnit]
      change ord K (x ^ 2) = 0
      exact hxSqOrder
    have hxuOrder : ordUnit K xu = 0 := by
      rw [ordUnit_pow] at hxuPowOrder
      omega
    have hxUnit : IsValuationUnit K x := by
      change ord K (xu : K) = 0
      rw [← coe_ordUnit, hxuOrder]
      norm_num
    have hxMinus : IsInMaximalIdeal K (x - 1) := hresidue x hxUnit
    have hxPlus : IsInMaximalIdeal K (x + 1) := by
      have htwoMax : IsInMaximalIdeal K (2 : K) := two_isInMaximalIdeal K
      have hadd := isInMaximalIdeal_add K hxMinus htwoMax
      simpa only [show x - 1 + 2 = x + 1 by ring] using hadd
    have hxMinusOne : (1 : WithTop Int) ≤ ord K (x - 1) :=
      one_le_order_of_mem_maximalIdeal hxMinus
    have hxPlusOne : (1 : WithTop Int) ≤ ord K (x + 1) :=
      one_le_order_of_mem_maximalIdeal hxPlus
    have hproduct : (2 : WithTop Int) ≤
        ord K ((x - 1) * (x + 1)) := by
      rw [ord_mul]
      have hadd := add_le_add hxMinusOne hxPlusOne
      norm_num at hadd ⊢
      exact hadd
    have htwoOrder : ord K (2 : K) = (1 : WithTop Int) := by
      rw [← ramificationIndex_spec, htwoAdic]
      norm_num
    have hstrict : ord K (2 : K) < ord K ((x - 1) * (x + 1)) := by
      rw [htwoOrder]
      exact (show (1 : WithTop Int) < 2 by norm_num).trans_le hproduct
    have hsum := (ord K).map_add_eq_of_lt_left hstrict
    have hfield : (2 : K) + (x - 1) * (x + 1) = 1 + x ^ 2 := by ring
    rw [hfield, htwoOrder] at hsum
    rw [hsum] at hx
    norm_num at hx
  have hupper : quadraticDefect K (-1 : Kˣ) ≤ (1 : ℕ∞) := by
    by_contra hnot
    have honeLt : (1 : ℕ∞) < quadraticDefect K (-1 : Kˣ) :=
      lt_of_not_ge hnot
    have htwoLe : (2 : ℕ∞) ≤ quadraticDefect K (-1 : Kˣ) := by
      have hadd := (ENat.add_one_le_iff (ENat.coe_ne_top 1)).2 honeLt
      norm_num at hadd ⊢
      exact hadd
    exact hnoDepthTwo ((isQuadraticApproximation_iff_le_defect K).2 htwoLe)
  exact le_antisymm hupper hlower

/-- When `e = 1`, Hensel's square theorem gives a valuation unit whose
square changes `-1` into the paper's representative `7`. -/
theorem beli2009_exists_unit_square_mul_negOne_eq_seven
    (htwoAdic : ramificationIndex K = 1) :
    ∃ s : Kˣ, IsValuationUnit K (s : K) ∧
      s ^ 2 * (-1 : Kˣ) = beli2009SevenUnit (K := K) := by
  letI : QuadraticDefectLaws K := quadraticDefectLawsOfHensel K
  let eight : Kˣ := Units.mk0 (8 : K) (by norm_num)
  have heightOrder : ordUnit K eight = 3 := by
    apply WithTop.coe_injective
    rw [coe_ordUnit]
    change ord K (8 : K) = ((3 : Int) : WithTop Int)
    rw [show (8 : K) = (2 : K) ^ 3 by norm_num, ord_pow,
      ← ramificationIndex_spec, htwoAdic]
    norm_num
  have hdeep : 2 * (ramificationIndex K : Int) < ordUnit K eight := by
    rw [heightOrder, htwoAdic]
    norm_num
  let near : Kˣ := Units.mk0 (1 - (eight : K))
    (BONG.one_sub_ne_zero_of_two_e_lt_order eight hdeep)
  have hnearSquare : IsSquare near := by
    exact BONG.isSquare_one_sub_of_two_e_lt_order eight hdeep
  have hnearUnit : IsValuationUnit K (near : K) := by
    change ord K (1 - (eight : K)) = 0
    exact BONG.ord_one_sub_eq_zero_of_two_e_lt_order eight hdeep
  rcases hnearSquare with ⟨s, hs⟩
  have hsOrder : ordUnit K s = 0 := by
    have hnearOrder : ordUnit K near = 0 :=
      (isValuationUnit_iff_ordUnit_eq_zero K near).1 hnearUnit
    rw [hs, ordUnit_mul] at hnearOrder
    omega
  have hsUnit : IsValuationUnit K (s : K) :=
    (isValuationUnit_iff_ordUnit_eq_zero K s).2 hsOrder
  refine ⟨s, hsUnit, ?_⟩
  have hsPow : s ^ 2 = near := by
    simpa only [pow_two] using hs.symm
  rw [hsPow]
  apply Units.ext
  simp only [near, eight, beli2009SevenUnit]
  norm_num

private noncomputable def castGoodBONGLattice
    {M P : Lattice K V} {m : Nat}
    (b : BONG.GoodBONG q M m) (h : M = P) :
    BONG.GoodBONG q P m :=
  h ▸ b

@[simp]
private theorem valueUnit_castGoodBONGLattice
    {M P : Lattice K V} {m : Nat}
    (b : BONG.GoodBONG q M m) (h : M = P) (i : Fin m) :
    (castGoodBONGLattice b h).valueUnit i = b.valueUnit i := by
  subst P
  rfl

/-- The assertions in the unnumbered final discussion of Section 5.  They
are stated as a non-default interface because the paper only sketches them. -/
class Beli2009BinaryTransformationLaws : Prop where
  reachable_of_large_residue
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (hres : BONG.HasResidueFieldMoreThanTwoElements (K := K))
    (a b : BONG.GoodBONG q L (n + 1)) :
    Beli2009BinaryReachable (K := K)
      (fun i => a.valueUnit i) (fun i => b.valueUnit i)
  parametric_counterexample_of_residue_two
    (hres : ¬BONG.HasResidueFieldMoreThanTwoElements (K := K))
    (d : Nat) (hdpos : 0 < d)
    (hdlt : d < 2 * ramificationIndex K) (hdodd : Odd d)
    (epsilon eta : valuationUnitSubgroup K)
    (hepsilon : quadraticDefect K (epsilon : Kˣ) =
      (d : WithTop Nat))
    (heta : quadraticDefect K (eta : Kˣ) =
      (2 * ramificationIndex K - d : WithTop Nat)) :
    ∃ C : Beli2009BinaryTransformationCounterexample.{u, u} (K := K),
      (∀ i, C.first.valueUnit i =
        beli2009ResidueTwoFirstValues (K := K) d epsilon eta i) ∧
      ∀ i, C.second.valueUnit i =
        beli2009ResidueTwoSecondValues (K := K) d epsilon eta i

/-- Binary reachability implies all four necessary conditions in the main
theorem, as asserted in the second final remark. -/
theorem beli2009Section5_binaryTransformations_necessary
    (a b : BONG.GoodBONG q L (n + 1))
    (_h : Beli2009BinaryReachable (K := K)
      (fun i => a.valueUnit i) (fun i => b.valueUnit i)) :
    ClassificationConditions a b := by
  exact (BONG.GoodBONG.beli2009Theorem31_concrete
    (QuadraticSpace.isIsometric_refl q) a b).mp
      (Lattice.isIsometric_refl q L)

/-- The parameterized rank-four obstruction displayed in the final
paragraph for a residue field with two elements. -/
theorem beli2009Section5_residueTwoParametricCounterexample
    [Beli2009BinaryTransformationLaws.{u, v} (K := K)]
    (hres : ¬BONG.HasResidueFieldMoreThanTwoElements (K := K))
    (d : Nat) (hdpos : 0 < d)
    (hdlt : d < 2 * ramificationIndex K) (hdodd : Odd d)
    (epsilon eta : valuationUnitSubgroup K)
    (hepsilon : quadraticDefect K (epsilon : Kˣ) =
      (d : WithTop Nat))
    (heta : quadraticDefect K (eta : Kˣ) =
      (2 * ramificationIndex K - d : WithTop Nat)) :
    ∃ C : Beli2009BinaryTransformationCounterexample.{u, u} (K := K),
      (∀ i, C.first.valueUnit i =
        beli2009ResidueTwoFirstValues (K := K) d epsilon eta i) ∧
      ∀ i, C.second.valueUnit i =
        beli2009ResidueTwoSecondValues (K := K) d epsilon eta i :=
  Beli2009BinaryTransformationLaws.parametric_counterexample_of_residue_two
    hres d hdpos hdlt hdodd epsilon eta hepsilon heta

/-- The unparameterized residue-two counterexample follows from any proof of
the parameterized family and the realization of every admissible odd unit
defect.  Keeping the family as an explicit argument lets the concrete proof
module use this construction without assuming the unrelated large-residue
connectivity assertion. -/
theorem beli2009Section5_residueTwoCounterexample_of_parametric
    (hparam :
      ∀ (hres : ¬BONG.HasResidueFieldMoreThanTwoElements (K := K))
        (d : Nat) (hdpos : 0 < d)
        (hdlt : d < 2 * ramificationIndex K) (hdodd : Odd d)
        (epsilon eta : valuationUnitSubgroup K),
        quadraticDefect K (epsilon : Kˣ) = (d : WithTop Nat) →
        quadraticDefect K (eta : Kˣ) =
          (2 * ramificationIndex K - d : WithTop Nat) →
        ∃ C : Beli2009BinaryTransformationCounterexample.{u, u} (K := K),
          (∀ i, C.first.valueUnit i =
            beli2009ResidueTwoFirstValues (K := K) d epsilon eta i) ∧
          ∀ i, C.second.valueUnit i =
            beli2009ResidueTwoSecondValues (K := K) d epsilon eta i)
    (hres : ¬BONG.HasResidueFieldMoreThanTwoElements (K := K)) :
    Nonempty
      (Beli2009BinaryTransformationCounterexample.{u, u} (K := K)) := by
  have hepos : 0 < ramificationIndex K := ramificationIndex_pos (K := K)
  have honeLt : 1 < 2 * ramificationIndex K := by omega
  obtain ⟨epsilonRaw, hepsilonUnit, hepsilonDefect⟩ :=
    exists_unit_quadraticDefect_eq_odd (K := K) 1 (by omega) odd_one honeLt
  let epsilon : valuationUnitSubgroup K :=
    ⟨epsilonRaw, hepsilonUnit⟩
  let etaDefect : Nat := 2 * ramificationIndex K - 1
  have hetaDefectPos : 0 < etaDefect := by
    dsimp [etaDefect]
    omega
  have hetaDefectOdd : Odd etaDefect := by
    refine ⟨ramificationIndex K - 1, ?_⟩
    dsimp [etaDefect]
    omega
  have hetaDefectLt : etaDefect < 2 * ramificationIndex K := by
    dsimp [etaDefect]
    omega
  obtain ⟨etaRaw, hetaUnit, hetaDefectEq⟩ :=
    exists_unit_quadraticDefect_eq_odd (K := K) etaDefect
      hetaDefectPos hetaDefectOdd hetaDefectLt
  let eta : valuationUnitSubgroup K := ⟨etaRaw, hetaUnit⟩
  obtain ⟨C, _hfirst, _hsecond⟩ :=
    hparam
      hres 1 (by omega) honeLt odd_one epsilon eta
        (by
          change quadraticDefect K epsilonRaw = (1 : WithTop Nat)
          exact hepsilonDefect)
        (by
          change quadraticDefect K etaRaw =
            (2 * ramificationIndex K - 1 : WithTop Nat)
          calc
            quadraticDefect K etaRaw = (etaDefect : ℕ∞) := hetaDefectEq
            _ = ((2 * ramificationIndex K - 1 : Nat) : ℕ∞) := rfl
            _ = (2 * ramificationIndex K - 1 : WithTop Nat) := by
              rw [ENat.coe_sub]
              norm_cast)
  exact ⟨C⟩

/-- The unparameterized residue-two counterexample obtained from the
historical combined final-remarks interface. -/
theorem beli2009Section5_residueTwoCounterexample
    [Beli2009BinaryTransformationLaws.{u, v} (K := K)]
    (hres : ¬BONG.HasResidueFieldMoreThanTwoElements (K := K)) :
    Nonempty
      (Beli2009BinaryTransformationCounterexample.{u, u} (K := K)) :=
  beli2009Section5_residueTwoCounterexample_of_parametric
    (fun hres d hdpos hdlt hdodd epsilon eta hepsilon heta ↦
      Beli2009BinaryTransformationLaws.parametric_counterexample_of_residue_two
        hres d hdpos hdlt hdodd epsilon eta hepsilon heta)
    hres

/-- Beli (2009/2010), final remark: the binary-transformation question has
a positive answer for larger residue fields and a rank-four counterexample
for the two-element residue field. -/
theorem beli2009Section5_binaryTransformationDichotomy
    [Beli2009BinaryTransformationLaws.{u, v} (K := K)] :
    (BONG.HasResidueFieldMoreThanTwoElements (K := K) →
      ∀ {V : Type v} [AddCommGroup V] [Module K V]
        {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
        (a b : BONG.GoodBONG q L (n + 1)),
        Beli2009BinaryReachable (K := K)
          (fun i => a.valueUnit i) (fun i => b.valueUnit i)) ∧
      (¬BONG.HasResidueFieldMoreThanTwoElements (K := K) →
        Nonempty
          (Beli2009BinaryTransformationCounterexample.{u, u}
            (K := K))) := by
  constructor
  · intro hres V _ _ q L n a b
    exact Beli2009BinaryTransformationLaws.reachable_of_large_residue
      hres a b
  · exact beli2009Section5_residueTwoCounterexample

/-- The explicit final example `⟨1,1,1,1⟩ ≅ ⟨7,7,7,7⟩` over `ℚ₂`,
derived from any proof of the parameterized residue-two family. -/
theorem beli2009Section5_q2Counterexample_of_parametric
    (hparam :
      ∀ (hres : ¬BONG.HasResidueFieldMoreThanTwoElements (K := K))
        (d : Nat) (hdpos : 0 < d)
        (hdlt : d < 2 * ramificationIndex K) (hdodd : Odd d)
        (epsilon eta : valuationUnitSubgroup K),
        quadraticDefect K (epsilon : Kˣ) = (d : WithTop Nat) →
        quadraticDefect K (eta : Kˣ) =
          (2 * ramificationIndex K - d : WithTop Nat) →
        ∃ C : Beli2009BinaryTransformationCounterexample.{u, u} (K := K),
          (∀ i, C.first.valueUnit i =
            beli2009ResidueTwoFirstValues (K := K) d epsilon eta i) ∧
          ∀ i, C.second.valueUnit i =
            beli2009ResidueTwoSecondValues (K := K) d epsilon eta i)
    (htwoAdic : ramificationIndex K = 1)
    (hres : ¬BONG.HasResidueFieldMoreThanTwoElements (K := K)) :
    ∃ C : Beli2009BinaryTransformationCounterexample.{u, u} (K := K),
      (∀ i, C.first.valueUnit i = 1) ∧
        ∀ i, C.second.valueUnit i = beli2009SevenUnit (K := K) :=
by
  have hdefect : quadraticDefect K (-1 : Kˣ) = (1 : ℕ∞) :=
    beli2009_quadraticDefect_negOne_eq_one htwoAdic hres
  have hgap : 1 < 2 * ramificationIndex K := by
    rw [htwoAdic]
    norm_num
  let minusOne : valuationUnitSubgroup K :=
    ⟨(-1 : Kˣ), by simp [IsValuationUnit]⟩
  obtain ⟨C, hfirstRaw, hsecondRaw⟩ :=
    hparam
      hres 1 (by omega) hgap odd_one minusOne minusOne
        (by
          change quadraticDefect K (-1 : Kˣ) = (1 : WithTop Nat)
          exact hdefect)
        (by
          change quadraticDefect K (-1 : Kˣ) =
            (2 * ramificationIndex K - 1 : WithTop Nat)
          calc
            quadraticDefect K (-1 : Kˣ) = (1 : ℕ∞) := hdefect
            _ = ((2 * ramificationIndex K - 1 : Nat) : ℕ∞) := by
              rw [htwoAdic]
              norm_num
            _ = (2 * ramificationIndex K - 1 : WithTop Nat) := by
              rw [ENat.coe_sub]
              norm_cast)
  have hfirst : ∀ i, C.first.valueUnit i = 1 := by
    intro i
    rw [hfirstRaw i]
    fin_cases i <;>
      simp [beli2009ResidueTwoFirstValues, beli2009ResidueTwoOrder,
        htwoAdic, minusOne, uniformizerPowerUnit]
  have hsecond : ∀ i, C.second.valueUnit i = (-1 : Kˣ) := by
    intro i
    rw [hsecondRaw i]
    fin_cases i <;>
      simp [beli2009ResidueTwoSecondValues, beli2009ResidueTwoOrder,
        htwoAdic, minusOne, uniformizerPowerUnit]
  obtain ⟨s, hsUnit, hsSeven⟩ :=
    beli2009_exists_unit_square_mul_negOne_eq_seven (K := K) htwoAdic
  have hscaledLattice : Lattice.rescale s C.L = C.L :=
    Lattice.rescale_eq_self_of_isValuationUnit C.L s hsUnit
  let scaledSecond : BONG.GoodBONG C.q C.L 4 :=
    castGoodBONGLattice (C.second.rescale s) hscaledLattice
  have hscaledValue : ∀ i, scaledSecond.valueUnit i =
      s ^ 2 * C.second.valueUnit i := by
    intro i
    simp only [scaledSecond, valueUnit_castGoodBONGLattice,
      BONG.GoodBONG.valueUnit_rescale]
  have hequivalent : Beli2009ValueSequenceEquivalent (K := K)
      (fun i => scaledSecond.valueUnit i)
      (fun i => C.second.valueUnit i) := by
    intro i
    change unitSquareClass K (scaledSecond.valueUnit i) =
      unitSquareClass K (C.second.valueUnit i)
    rw [hscaledValue i]
    simpa only [mul_comm] using
      unitSquareClass_mul_unit_square K (C.second.valueUnit i) s hsUnit
  have hnotReachable : ¬Beli2009BinaryReachable (K := K)
      (fun i => C.first.valueUnit i)
      (fun i => scaledSecond.valueUnit i) := by
    intro hreach
    exact C.not_reachable
      (hreach.trans hequivalent.reachable)
  let D : Beli2009BinaryTransformationCounterexample.{u, u} (K := K) := {
    carrier := C.carrier
    q := C.q
    L := C.L
    first := C.first
    second := scaledSecond
    not_reachable := hnotReachable
  }
  refine ⟨D, ?_, ?_⟩
  · intro i
    exact hfirst i
  · intro i
    change scaledSecond.valueUnit i = beli2009SevenUnit (K := K)
    rw [hscaledValue i, hsecond i]
    exact hsSeven

/-- The explicit final `ℚ₂` example obtained from the historical combined
final-remarks interface. -/
theorem beli2009Section5_q2Counterexample
    [Beli2009BinaryTransformationLaws.{u, v} (K := K)]
    (htwoAdic : ramificationIndex K = 1)
    (hres : ¬BONG.HasResidueFieldMoreThanTwoElements (K := K)) :
    ∃ C : Beli2009BinaryTransformationCounterexample.{u, u} (K := K),
      (∀ i, C.first.valueUnit i = 1) ∧
        ∀ i, C.second.valueUnit i = beli2009SevenUnit (K := K) :=
  beli2009Section5_q2Counterexample_of_parametric
    (fun hres d hdpos hdlt hdodd epsilon eta hepsilon heta ↦
      Beli2009BinaryTransformationLaws.parametric_counterexample_of_residue_two
        hres d hdpos hdlt hdodd epsilon eta hepsilon heta)
    htwoAdic hres

end Bong
