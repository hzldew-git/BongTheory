/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009ComponentCongruence
import Bong.Bong.PrefixDeterminant
import Bong.Lattice.Omeara9328Conditions

/-!
# Beli's prefix defects and O'Meara 93:28(i)

This file identifies the determinant unit of every proper Jordan prefix with
the corresponding good-BONG prefix product, modulo valuation-unit squares.
It then translates Beli's condition 3.1(iii) into the determinant congruences
of O'Meara 93:28(i).
-/

namespace Bong

open Dyadic Module

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

namespace Lattice.JordanDecomposition

/-- Reindexing the component count does not change any prefix quadratic
sublattice. -/
@[simp] theorem castComponentCount_prefixQuadraticSublattice
    {c d : Nat} (J : JordanDecomposition q L c) (h : c = d) (k : Nat) :
    (J.castComponentCount h).toOrthogonalDecomposition.prefixQuadraticSublattice k =
      J.toOrthogonalDecomposition.prefixQuadraticSublattice k := by
  subst d
  rfl

end Lattice.JordanDecomposition

namespace BONG.GoodBONG

variable {n : Nat} {a : GoodBONG q L (n + 2)}
  {b : GoodBONG r M (n + 2)}

/-- A defect bound at one good-BONG prefix, expressed at an integral ideal
order, is exactly the corresponding square-class congruence of the two prefix
products. -/
theorem prefixProducts_congruent_of_integral_defectBound
    (horders : a.SameOrders b) (i : Fin (n + 1))
    (d : Int) (hd : 0 ≤ d)
    (hdefect : ((((d : Int) : ℚ) : WithTop ℚ) ≤
      defectOrder (K := K) (a.comparisonPrefixProduct b i))) :
    UnitsCongruentModulo
      (b.prefixProduct (i.val + 1)) (a.prefixProduct (i.val + 1))
      (Lattice.powerIdeal (K := K) d) := by
  apply (unitsCongruentModulo_powerIdeal_iff_intCast_le_defectOrder_mul
    (b.prefixProduct (i.val + 1)) (a.prefixProduct (i.val + 1)) d hd
      ((a.ordUnit_prefixProduct_eq_of_sameOrders b horders
        (i.val + 1) (by omega)).symm)).2
  simpa only [comparisonPrefixProduct, mul_comm] using hdefect

end BONG.GoodBONG

namespace BONG.StrictJordanAdaptedAlignment

variable {n : Nat} {a : GoodBONG q L (n + 2)}
  {b : GoodBONG r M (n + 2)}

/-- The BONG product ending at a source Jordan boundary represents the
refined determinant class of the actual Jordan prefix. -/
theorem unitSquareClass_sourcePrefixProduct_eq_prefixDeterminantUnit
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1) (i : Fin t) :
    unitSquareClass K
        (a.prefixProduct (((S.sourceProfileSucc h).boundaryIndex i).val + 1)) =
      unitSquareClass K ((S.sourceJordanSucc h).prefixDeterminantUnit i) := by
  let k : Fin S.componentCount := Fin.cast h.symm
    (Lattice.JordanDecomposition.boundaryRightIndex i)
  have hk : 0 < k.val := by
    simp [k, Lattice.JordanDecomposition.boundaryRightIndex]
  let hcut : S.componentStart k ≤ n + 2 := by
    exact le_trans (Nat.le_of_lt (S.componentStart_lt_componentStop k))
      (S.componentStop_le k)
  let T : a.toBONG.TwoBlockSplitWitness (S.componentStart k) hcut :=
    Classical.choice (S.source_hasTwoBlockSplit_componentStart k hk)
  let P := T.leftPrefixWitness
  have hprefixClass :
      unitSquareClass K (a.prefixProduct (S.componentStart k)) =
        Lattice.determinantClass
          (q.restrict T.left.carrier T.left.nondegenerate) T.left.lattice := by
    calc
      unitSquareClass K (a.prefixProduct (S.componentStart k)) =
          unitSquareClass K P.bong.valueProduct := by
        exact congrArg (unitSquareClass K)
          P.valueProduct_eq_prefixProduct.symm
      _ = Lattice.determinantClass
          (q.restrict T.left.carrier T.left.nondegenerate) T.left.lattice := by
        exact P.bong.determinantClass_eq_valueProduct.symm
  have hisometry := Lattice.determinantClass_eq_of_isometry
    (S.sourceSplitLeftLatticeIsometry k hk T)
  have hstart := S.sourceBoundaryIndex_succ_val_eq_componentStart h i
  rw [hstart]
  calc
    unitSquareClass K (a.prefixProduct (S.componentStart k)) =
        Lattice.determinantClass
          (q.restrict T.left.carrier T.left.nondegenerate) T.left.lattice :=
      hprefixClass
    _ = Lattice.determinantClass
        ((S.sourceJordan.toOrthogonalDecomposition.prefixQuadraticSublattice
          k.val).space)
        ((S.sourceJordan.toOrthogonalDecomposition.prefixQuadraticSublattice
          k.val).lattice) := hisometry
    _ = unitSquareClass K
        ((S.sourceJordanSucc h).prefixDeterminantUnit i) := by
      have hkval : k.val = i.val + 1 := by
        simp [k, Lattice.JordanDecomposition.boundaryRightIndex]
      unfold Lattice.JordanDecomposition.prefixDeterminantUnit
        Lattice.QuadraticSublattice.refinedDeterminantUnit
        Lattice.determinantClass
      unfold sourceJordanSucc
      rw [Lattice.JordanDecomposition.castComponentCount_prefixQuadraticSublattice]
      rw [hkval]

/-- Target counterpart of the preceding determinant-prefix identification. -/
theorem unitSquareClass_targetPrefixProduct_eq_prefixDeterminantUnit
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1) (i : Fin t) :
    unitSquareClass K
        (b.prefixProduct (((S.targetProfileSucc h).boundaryIndex i).val + 1)) =
      unitSquareClass K ((S.targetJordanSucc h).prefixDeterminantUnit i) := by
  simpa using
    (S.symm.unitSquareClass_sourcePrefixProduct_eq_prefixDeterminantUnit h i)

/-- Beli's prefix-defect condition gives the square-class congruence of the
two prefix products modulo the actual O'Meara fundamental ideal at every
Jordan boundary.  In the exceptional odd branch the defect is deeper than
`2e`, hence the comparison product is a square and the congruence holds at
the larger fundamental-ideal order as well. -/
theorem prefixProducts_congruent_mod_fundamentalIdeal
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1)
    (horders : a.SameOrders b) (hprefix : a.PrefixDefectBounds b)
    (i : Fin t) :
    GoodBONG.UnitsCongruentModulo
      (b.prefixProduct (((S.sourceProfileSucc h).boundaryIndex i).val + 1))
      (a.prefixProduct (((S.sourceProfileSucc h).boundaryIndex i).val + 1))
      ((S.sourceJordanSucc h).fundamentalIdeal i) := by
  let P := S.sourceProfileSucc h
  let J := S.sourceJordanSucc h
  let j : Fin (n + 1) := P.boundaryIndex i
  by_cases heven : Even (J.boundaryNormOrderSum i)
  · let E := J.evenOrderedFundamentalIdeal i
      (P.boundaryLeftValue i) (P.boundaryRightValue i)
      (S.sourceBoundaryLeftValue_isNormGeneratorValue h i)
      (S.sourceBoundaryRightValue_isNormGeneratorValue h i) heven
    have hE : ((E.order : Int) : ℚ) = a.alphaValue j := by
      simpa only [E, J, P, j] using
        S.sourceEvenBoundaryFundamentalOrder_eq_alpha h i heven
    have hEnonnegative : 0 ≤ E.order := by
      have hq : (0 : ℚ) ≤ (E.order : ℚ) := by
        rw [hE]
        exact a.zero_le_alphaValue j
      exact_mod_cast hq
    have hbound : ((((E.order : Int) : ℚ) : WithTop ℚ) ≤
        GoodBONG.defectOrder (K := K) (a.comparisonPrefixProduct b j)) := by
      rw [hE]
      exact hprefix j
    have hraw := a.prefixProducts_congruent_of_integral_defectBound
      horders j E.order hEnonnegative hbound
    have hcarrier : J.fundamentalIdeal i =
        Lattice.powerIdeal (K := K) E.order := by
      have hEcarrier : E.carrier = J.fundamentalIdeal i := rfl
      rw [← hEcarrier]
      exact E.carrier_eq_powerIdeal
    simpa only [P, J, j, hcarrier] using hraw
  · have hodd : Odd (J.boundaryNormOrderSum i) :=
      Int.not_even_iff_odd.mp heven
    let D := S.sourceOddBoundaryAlphaData h i hodd
    have hD := S.sourceOddBoundaryAlphaData_lemma216 h i hodd
    have hindex : D.index = j := rfl
    have hcarrier : J.fundamentalIdeal i =
        Lattice.powerIdeal (K := K) D.fundamental.order := by
      have hDcarrier : D.fundamental.carrier = J.fundamentalIdeal i := rfl
      rw [← hDcarrier]
      exact D.fundamental.carrier_eq_powerIdeal
    have hDnonnegative : 0 ≤ D.fundamental.order := by
      by_cases hordinary : Even (a.orderGap D.index) ∨
          a.orderGap D.index ≤ 2 * (ramificationIndex K : Int)
      · have hq : (0 : ℚ) ≤ (D.fundamental.order : ℚ) := by
          rw [← hD.1 hordinary]
          exact a.zero_le_alphaValue D.index
        exact_mod_cast hq
      · have hlarge := (hD.2 hordinary).2.2.2.2
        have htwoNonnegative : (0 : ℚ) ≤
            2 * (ramificationIndex K : ℚ) := by positivity
        have hpositive : (0 : ℚ) < (D.fundamental.order : ℚ) :=
          lt_of_le_of_lt htwoNonnegative hlarge
        exact_mod_cast hpositive.le
    have hbound : (((((D.fundamental.order : Int) : ℚ) : WithTop ℚ)) ≤
        GoodBONG.defectOrder (K := K) (a.comparisonPrefixProduct b j)) := by
      by_cases hordinary : Even (a.orderGap D.index) ∨
          a.orderGap D.index ≤ 2 * (ramificationIndex K : Int)
      · have hregular := hD.1 hordinary
        have hp := hprefix j
        rw [← hindex] at hp
        rw [hregular] at hp
        exact hp
      · have hlarge := (hD.2 hordinary).2.2.2.1
        have htwoEAlpha :
            ((((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
              (a.alphaValue j : WithTop ℚ)) := by
          rw [← hindex]
          exact_mod_cast hlarge
        have htwoEDefect :
            ((((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
              GoodBONG.defectOrder (K := K)
                (a.comparisonPrefixProduct b j)) :=
          htwoEAlpha.trans_le (hprefix j)
        have hsquare := GoodBONG.isSquare_of_two_mul_e_lt_defectOrder
          (K := K) (a.comparisonPrefixProduct b j) htwoEDefect
        rw [GoodBONG.defectOrder_eq_top_of_isSquare hsquare]
        exact le_top
    have hraw := a.prefixProducts_congruent_of_integral_defectBound
      horders j D.fundamental.order hDnonnegative hbound
    simpa only [P, J, j, hcarrier] using hraw

/-- Concrete forward translation from Beli 3.1(iii) to O'Meara 93:28(i). -/
theorem omeara9328ConditionI_of_prefixDefectBounds
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1)
    (horders : a.SameOrders b) (hprefix : a.PrefixDefectBounds b) :
    (S.sourceJordanSucc h).Omeara9328ConditionI (S.targetJordanSucc h) := by
  intro i
  let P := S.sourceProfileSucc h
  have hraw := S.prefixProducts_congruent_mod_fundamentalIdeal
    h horders hprefix i
  apply GoodBONG.unitsCongruentModulo_of_unitSquareClass_eq
    (b.prefixProduct ((P.boundaryIndex i).val + 1))
    ((S.targetJordanSucc h).prefixDeterminantUnit i)
    (a.prefixProduct ((P.boundaryIndex i).val + 1))
    ((S.sourceJordanSucc h).prefixDeterminantUnit i)
    ((S.sourceJordanSucc h).fundamentalIdeal i)
  · have ht := S.unitSquareClass_targetPrefixProduct_eq_prefixDeterminantUnit h i
    rw [← S.sourceBoundaryIndex_eq_targetBoundaryIndex h i] at ht
    exact ht
  · exact S.unitSquareClass_sourcePrefixProduct_eq_prefixDeterminantUnit h i
  · simpa only [P] using hraw

/-- Concrete reverse translation at the Jordan boundaries: O'Meara 93:28(i)
implies Beli's prefix-defect inequality at every strict Jordan cut. -/
theorem boundaryPrefixDefectBounds_of_omeara9328ConditionI
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1)
    (horders : a.SameOrders b)
    (hcondition : (S.sourceJordanSucc h).Omeara9328ConditionI
      (S.targetJordanSucc h)) :
    ∀ i : Fin t,
      (a.alphaValue ((S.sourceProfileSucc h).boundaryIndex i) : WithTop ℚ) ≤
        GoodBONG.defectOrder (K := K)
          (a.comparisonPrefixProduct b
            ((S.sourceProfileSucc h).boundaryIndex i)) := by
  intro i
  let P := S.sourceProfileSucc h
  let J := S.sourceJordanSucc h
  let j : Fin (n + 1) := P.boundaryIndex i
  have htargetClass :=
    S.unitSquareClass_targetPrefixProduct_eq_prefixDeterminantUnit h i
  rw [← S.sourceBoundaryIndex_eq_targetBoundaryIndex h i] at htargetClass
  have hsourceClass :=
    S.unitSquareClass_sourcePrefixProduct_eq_prefixDeterminantUnit h i
  have hraw : GoodBONG.UnitsCongruentModulo
      (b.prefixProduct (j.val + 1)) (a.prefixProduct (j.val + 1))
      (J.fundamentalIdeal i) := by
    apply GoodBONG.unitsCongruentModulo_of_unitSquareClass_eq
      ((S.targetJordanSucc h).prefixDeterminantUnit i)
      (b.prefixProduct (j.val + 1))
      ((S.sourceJordanSucc h).prefixDeterminantUnit i)
      (a.prefixProduct (j.val + 1)) (J.fundamentalIdeal i)
    · simpa only [P, J, j] using htargetClass.symm
    · simpa only [P, J, j] using hsourceClass.symm
    · exact hcondition i
  have hproductOrder : ordUnit K (b.prefixProduct (j.val + 1)) =
      ordUnit K (a.prefixProduct (j.val + 1)) :=
    (a.ordUnit_prefixProduct_eq_of_sameOrders b horders
      (j.val + 1) (by omega)).symm
  by_cases heven : Even (J.boundaryNormOrderSum i)
  · let E := J.evenOrderedFundamentalIdeal i
      (P.boundaryLeftValue i) (P.boundaryRightValue i)
      (S.sourceBoundaryLeftValue_isNormGeneratorValue h i)
      (S.sourceBoundaryRightValue_isNormGeneratorValue h i) heven
    have hE : ((E.order : Int) : ℚ) = a.alphaValue j := by
      simpa only [E, J, P, j] using
        S.sourceEvenBoundaryFundamentalOrder_eq_alpha h i heven
    have hEnonnegative : 0 ≤ E.order := by
      have hq : (0 : ℚ) ≤ (E.order : ℚ) := by
        rw [hE]
        exact a.zero_le_alphaValue j
      exact_mod_cast hq
    have hEcarrier : E.carrier = J.fundamentalIdeal i := rfl
    have hrawPower : GoodBONG.UnitsCongruentModulo
        (b.prefixProduct (j.val + 1)) (a.prefixProduct (j.val + 1))
        (Lattice.powerIdeal (K := K) E.order) := by
      rw [← E.carrier_eq_powerIdeal, hEcarrier]
      exact hraw
    have hdefect :=
      GoodBONG.intCast_le_defectOrder_mul_of_unitsCongruentModulo_powerIdeal
        (b.prefixProduct (j.val + 1)) (a.prefixProduct (j.val + 1))
        E.order hEnonnegative hproductOrder hrawPower
    rw [← hE]
    simpa only [P, j, GoodBONG.comparisonPrefixProduct, mul_comm] using hdefect
  · have hodd : Odd (J.boundaryNormOrderSum i) :=
      Int.not_even_iff_odd.mp heven
    let D := S.sourceOddBoundaryAlphaData h i hodd
    have hD := S.sourceOddBoundaryAlphaData_lemma216 h i hodd
    have hindex : D.index = j := rfl
    have hDnonnegative : 0 ≤ D.fundamental.order := by
      by_cases hordinary : Even (a.orderGap D.index) ∨
          a.orderGap D.index ≤ 2 * (ramificationIndex K : Int)
      · have hq : (0 : ℚ) ≤ (D.fundamental.order : ℚ) := by
          rw [← hD.1 hordinary]
          exact a.zero_le_alphaValue D.index
        exact_mod_cast hq
      · have hlarge := (hD.2 hordinary).2.2.2.2
        have htwoNonnegative : (0 : ℚ) ≤
            2 * (ramificationIndex K : ℚ) := by positivity
        have hpositive : (0 : ℚ) < (D.fundamental.order : ℚ) :=
          lt_of_le_of_lt htwoNonnegative hlarge
        exact_mod_cast hpositive.le
    have hDcarrier : D.fundamental.carrier = J.fundamentalIdeal i := rfl
    have hrawPower : GoodBONG.UnitsCongruentModulo
        (b.prefixProduct (j.val + 1)) (a.prefixProduct (j.val + 1))
        (Lattice.powerIdeal (K := K) D.fundamental.order) := by
      rw [← D.fundamental.carrier_eq_powerIdeal, hDcarrier]
      exact hraw
    have hdefect :=
      GoodBONG.intCast_le_defectOrder_mul_of_unitsCongruentModulo_powerIdeal
        (b.prefixProduct (j.val + 1)) (a.prefixProduct (j.val + 1))
        D.fundamental.order hDnonnegative hproductOrder hrawPower
    have hdefect' : ((((D.fundamental.order : Int) : ℚ) : WithTop ℚ) ≤
        GoodBONG.defectOrder (K := K) (a.comparisonPrefixProduct b j)) := by
      simpa only [GoodBONG.comparisonPrefixProduct, mul_comm] using hdefect
    change (a.alphaValue j : WithTop ℚ) ≤
      GoodBONG.defectOrder (K := K) (a.comparisonPrefixProduct b j)
    by_cases hordinary : Even (a.orderGap D.index) ∨
        a.orderGap D.index ≤ 2 * (ramificationIndex K : Int)
    · have hregular := hD.1 hordinary
      rw [← hindex]
      rw [hregular]
      exact hdefect'
    · have hexceptional := hD.2 hordinary
      have halphaLeFund : a.alphaValue D.index ≤
          (D.fundamental.order : ℚ) := by
        rw [hexceptional.2.2.1]
        have heNonnegative : (0 : ℚ) ≤
            2 * (ramificationIndex K : ℚ) := by positivity
        linarith [hexceptional.2.2.2.1]
      have halphaLeFundTop : (a.alphaValue D.index : WithTop ℚ) ≤
          ((D.fundamental.order : ℚ) : WithTop ℚ) := by
        exact_mod_cast halphaLeFund
      rw [← hindex]
      exact halphaLeFundTop.trans hdefect'

/-- O'Meara's condition I supplies the prefix-defect seed at the right end
of every nonterminal concrete Jordan component. -/
theorem componentBoundaryPrefixDefectBounds_of_omeara9328ConditionI
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1)
    (horders : a.SameOrders b)
    (hcondition : (S.sourceJordanSucc h).Omeara9328ConditionI
      (S.targetJordanSucc h)) :
    ∀ (k : Fin S.componentCount) (hstop : S.componentStop k < n + 2),
      (a.alphaValue ⟨S.componentStop k - 1, by omega⟩ : WithTop ℚ) ≤
        GoodBONG.comparisonPrefixDefect a b (S.componentStop k) := by
  have hraw := S.boundaryPrefixDefectBounds_of_omeara9328ConditionI
    h horders hcondition
  intro k hstop
  have hsucc : k.val + 1 < S.componentCount :=
    S.source_component_has_successor_of_stop_lt k hstop
  let z : Fin t := ⟨k.val, by omega⟩
  let l : Fin S.componentCount := ⟨k.val + 1, hsucc⟩
  have hright :
      Fin.cast h.symm
          (Lattice.JordanDecomposition.boundaryRightIndex z) = l := by
    apply Fin.ext
    rfl
  have hstopStart : S.componentStop k = S.componentStart l :=
    S.componentStop_eq_componentStart_of_val_succ k l rfl
  have hboundaryStart := S.sourceBoundaryIndex_succ_val_eq_componentStart h z
  rw [hright] at hboundaryStart
  have hboundaryIndex :
      (S.sourceProfileSucc h).boundaryIndex z =
        (⟨S.componentStop k - 1, by omega⟩ : Fin (n + 1)) := by
    apply Fin.ext
    change ((S.sourceProfileSucc h).boundaryIndex z).val =
      S.componentStop k - 1
    omega
  have hz := hraw z
  rw [hboundaryIndex] at hz
  unfold GoodBONG.comparisonPrefixDefect GoodBONG.comparisonPrefixUnit
  simpa only [GoodBONG.comparisonPrefixProduct,
    show S.componentStop k - 1 + 1 = S.componentStop k by
      have hpositive := S.componentStart_lt_componentStop k
      omega] using hz

/-- Boundary seeds are exactly the left-end seeds required to start the
Lemma 3.2 recurrence in every noninitial Jordan component. -/
theorem componentLeftPrefixDefectBounds_of_boundaries
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (hboundary : ∀ (k : Fin S.componentCount)
      (hstop : S.componentStop k < n + 2),
      (a.alphaValue ⟨S.componentStop k - 1, by omega⟩ : WithTop ℚ) ≤
        GoodBONG.comparisonPrefixDefect a b (S.componentStop k)) :
    ∀ k : Fin S.componentCount,
      S.componentStart k = 0 ∨ ∃ hs : 0 < S.componentStart k,
        (a.alphaValue ⟨S.componentStart k - 1, by
          have hstop := S.componentStop_le k
          have hstart := S.componentStart_lt_componentStop k
          omega⟩ : WithTop ℚ) ≤
          GoodBONG.comparisonPrefixDefect a b (S.componentStart k) := by
  intro k
  by_cases hkzero : k.val = 0
  · left
    have hk : k = S.sourceFirstComponent := by
      apply Fin.ext
      exact hkzero
    subst k
    unfold componentStart
    rw [S.Iio_sourceFirstComponent_eq_empty]
    simp
  · have hk : 0 < k.val := Nat.pos_of_ne_zero hkzero
    let p : Fin S.componentCount := ⟨k.val - 1, by omega⟩
    have hpSucc : k.val = p.val + 1 := by
      dsimp only [p]
      omega
    have hstopStart : S.componentStop p = S.componentStart k :=
      S.componentStop_eq_componentStart_of_val_succ p k hpSucc
    have hstartPositive : 0 < S.componentStart k := by
      rw [← hstopStart]
      exact (S.componentStart_lt_componentStop p).trans_le' (Nat.zero_le _)
    right
    refine ⟨hstartPositive, ?_⟩
    have hstop : S.componentStop p < n + 2 := by
      rw [hstopStart]
      exact (S.componentStart_lt_componentStop k).trans_le (S.componentStop_le k)
    have hb := hboundary p hstop
    have hindex : (⟨S.componentStart k - 1, by omega⟩ : Fin (n + 1)) =
        ⟨S.componentStop p - 1, by omega⟩ := by
      apply Fin.ext
      change S.componentStart k - 1 = S.componentStop p - 1
      omega
    rw [hindex, ← hstopStart]
    exact hb

/-- Same fundamental type supplies the non-unary component congruence; after
the preceding boundary is controlled, the local equivalence in Lemma 3.3
turns it into the head prefix-defect seed. -/
theorem componentHeadPrefixDefectBounds_of_sameFundamentalType
    [Beli2006AlphaLaws.{u, v} K]
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (horders : a.SameOrders b)
    (F : Lattice.JordanDecomposition.SameFundamentalType
      S.sourceJordan S.targetJordan)
    (hleft : ∀ k : Fin S.componentCount,
      S.componentStart k = 0 ∨ ∃ hs : 0 < S.componentStart k,
        (a.alphaValue ⟨S.componentStart k - 1, by
          have hstop := S.componentStop_le k
          have hstart := S.componentStart_lt_componentStop k
          omega⟩ : WithTop ℚ) ≤
          GoodBONG.comparisonPrefixDefect a b (S.componentStart k)) :
    ∀ (k : Fin S.componentCount)
      (hrank : 2 ≤ S.sourceJordan.componentRank k),
      (a.alphaValue ⟨S.componentStart k, by
        have hstop := S.componentStop_le k
        unfold componentStop at hstop
        change 2 ≤
          S.sourceJordan.toOrthogonalDecomposition.componentRank k at hrank
        omega⟩ : WithTop ℚ) ≤
        GoodBONG.comparisonPrefixDefect a b (S.componentStart k + 1) := by
  intro k hrank
  have hleftAlpha :
      (a.alphaValue ⟨S.componentStart k, by
        have hstop := S.componentStop_le k
        unfold componentStop at hstop
        change 2 ≤
          S.sourceJordan.toOrthogonalDecomposition.componentRank k at hrank
        omega⟩ : WithTop ℚ) ≤
        GoodBONG.comparisonPrefixDefect a b (S.componentStart k) := by
    rcases hleft k with hzero | ⟨hpositive, hprevious⟩
    · have htop : GoodBONG.comparisonPrefixDefect a b
          (S.componentStart k) = ⊤ := by
        rw [hzero, GoodBONG.comparisonPrefixDefect_zero]
      rw [htop]
      exact le_top
    · have hk : 0 < k.val := by
        by_contra hknot
        have hkzero : k.val = 0 := Nat.eq_zero_of_not_pos hknot
        have hkfirst : k = S.sourceFirstComponent := by
          apply Fin.ext
          exact hkzero
        subst k
        apply (Nat.ne_of_gt hpositive)
        unfold componentStart
        rw [S.Iio_sourceFirstComponent_eq_empty]
        simp
      have hmono :=
        S.source_alpha_componentStart_le_predecessor_of_rank_two k hk hrank
      have hmonoTop :
          (a.alphaValue ⟨S.componentStart k, by
            have hstop := S.componentStop_le k
            unfold componentStop at hstop
            change 2 ≤
              S.sourceJordan.toOrthogonalDecomposition.componentRank k at hrank
            omega⟩ : WithTop ℚ) ≤
            (a.alphaValue ⟨S.componentStart k - 1, by
              have hstop := S.componentStop_le k
              unfold componentStop at hstop
              change 2 ≤
                S.sourceJordan.toOrthogonalDecomposition.componentRank k at hrank
              omega⟩ : WithTop ℚ) := by
        exact_mod_cast hmono
      exact hmonoTop.trans hprevious
  have hcomponent := S.componentGenerator_congruent_of_sameFundamentalType
    horders F k
  apply (S.componentGenerator_congruent_iff_headPrefixDefect_of_rank_two
    horders k hrank hleftAlpha).1
  simpa only [sourceNormalizedFundamentalWeightOrder] using hcomponent

/-- Reverse half of Beli (2009), Lemma 3.3: under equal good-BONG orders,
equality of the complete O'Meara fundamental type together with condition I
implies every one of Beli's prefix-defect inequalities. -/
theorem prefixDefectBounds_of_sameFundamentalType_of_omeara9328ConditionI
    [Beli2006AlphaLaws.{u, v} K]
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1)
    (horders : a.SameOrders b)
    (F : Lattice.JordanDecomposition.SameFundamentalType
      S.sourceJordan S.targetJordan)
    (hcondition : (S.sourceJordanSucc h).Omeara9328ConditionI
      (S.targetJordanSucc h)) :
    a.PrefixDefectBounds b := by
  have halphas := S.sameAlphas_of_sameOrders_of_fundamentalType F horders
  have hboundary :=
    S.componentBoundaryPrefixDefectBounds_of_omeara9328ConditionI
      h horders hcondition
  have hleft := S.componentLeftPrefixDefectBounds_of_boundaries hboundary
  have hhead := S.componentHeadPrefixDefectBounds_of_sameFundamentalType
    horders F hleft
  exact S.prefixDefectBounds_of_componentSeeds horders halphas
    hboundary hleft hhead

/-- Beli (2009), Lemma 3.3 in its complete concrete form.  Assuming the
common ambient quadratic space and equal BONG orders, Beli's alpha and prefix
conditions are equivalent to equality of O'Meara's fundamental type together
with O'Meara 93:28(i). -/
theorem beli2009Lemma33
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AmbientDeterminantLaws.{u, v, w} K]
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1)
    (ambient : q.IsIsometric r) (horders : a.SameOrders b) :
    (Nonempty (Lattice.JordanDecomposition.SameFundamentalType
          S.sourceJordan S.targetJordan) ∧
        (S.sourceJordanSucc h).Omeara9328ConditionI
          (S.targetJordanSucc h)) ↔
      (a.SameAlphas b ∧ a.PrefixDefectBounds b) := by
  constructor
  · rintro ⟨⟨F⟩, hcondition⟩
    exact ⟨S.sameAlphas_of_sameOrders_of_fundamentalType F horders,
      S.prefixDefectBounds_of_sameFundamentalType_of_omeara9328ConditionI
        h horders F hcondition⟩
  · rintro ⟨halphas, hprefix⟩
    exact ⟨⟨S.sameFundamentalType_of_firstThreeConditions
        ambient horders halphas hprefix⟩,
      S.omeara9328ConditionI_of_prefixDefectBounds h horders hprefix⟩

end BONG.StrictJordanAdaptedAlignment

end Bong
