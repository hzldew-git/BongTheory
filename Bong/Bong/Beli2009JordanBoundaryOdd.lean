/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009JordanConcreteCoordinates
import Bong.Bong.Beli2006AlphaP2P3Proof
import Bong.Lattice.OmearaFundamentalIdeals

namespace Bong

open Dyadic Module

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {m t : Nat}

namespace BONG.JordanOrderProfileWitness

variable {a : GoodBONG q L (m + 1)}
  {J : Lattice.JordanDecomposition q L (t + 1)}

/-- The last global BONG coordinate in the component to the left of a
Jordan boundary. -/
noncomputable def boundaryIndex
    (P : JordanOrderProfileWitness a.toBONG J) (i : Fin t) : Fin m := by
  let li : Fin (t + 1) := Lattice.JordanDecomposition.boundaryLeftIndex i
  let ri : Fin (t + 1) := Lattice.JordanDecomposition.boundaryRightIndex i
  let last : Fin (J.toOrthogonalDecomposition.componentRank li) :=
    ⟨J.toOrthogonalDecomposition.componentRank li - 1, by
      exact Nat.sub_lt (J.component_finrank_pos li) Nat.zero_lt_one⟩
  let first : Fin (J.toOrthogonalDecomposition.componentRank ri) :=
    ⟨0, J.component_finrank_pos ri⟩
  let leftGlobal : Fin (m + 1) := P.indexEquiv.symm ⟨li, last⟩
  let rightGlobal : Fin (m + 1) := P.indexEquiv.symm ⟨ri, first⟩
  have hnext : rightGlobal.val = leftGlobal.val + 1 := by
    apply P.inverse_index_val_next_component li ri
    · rfl
    · dsimp only [last]
      exact Nat.sub_add_cancel (J.component_finrank_pos li)
  exact ⟨leftGlobal.val, by omega⟩

/-- The rescaled last value of a profiled Jordan component. -/
noncomputable def terminalValue
    {c : Nat} {H : Lattice.JordanDecomposition q L c}
    (P : JordanOrderProfileWitness a.toBONG H) (k : Fin c) : Kˣ :=
  let last : Fin (H.toOrthogonalDecomposition.componentRank k) :=
    ⟨H.toOrthogonalDecomposition.componentRank k - 1, by
      exact Nat.sub_lt (H.component_finrank_pos k) Nat.zero_lt_one⟩
  uniformizerPowerUnit K
      (2 * ordUnit K (H.normGenerator k) -
        2 * ordUnit K (H.scaleGenerator k)) *
    a.valueUnit (P.indexEquiv.symm ⟨k, last⟩)

theorem order_boundaryIndex
    (P : JordanOrderProfileWitness a.toBONG J) (i : Fin t)
    (hterminal : Lattice.IsNormGeneratorValue q
      (J.fundamentalLattice
        (Lattice.JordanDecomposition.boundaryLeftIndex i))
      (P.terminalValue
        (Lattice.JordanDecomposition.boundaryLeftIndex i)))
    (hnorm : ordUnit K
        (J.normGenerator
          (Lattice.JordanDecomposition.boundaryLeftIndex i)) =
      ordUnit K
        (J.fundamentalNormGenerator
          (Lattice.JordanDecomposition.boundaryLeftIndex i))) :
    a.order (P.boundaryIndex i).castSucc =
      2 * J.fundamentalScaleOrder
          (Lattice.JordanDecomposition.boundaryLeftIndex i) -
        ordUnit K
          (J.fundamentalNormGenerator
            (Lattice.JordanDecomposition.boundaryLeftIndex i)) := by
  let li : Fin (t + 1) := Lattice.JordanDecomposition.boundaryLeftIndex i
  let last : Fin (J.toOrthogonalDecomposition.componentRank li) :=
    ⟨J.toOrthogonalDecomposition.componentRank li - 1, by
      exact Nat.sub_lt (J.component_finrank_pos li) Nat.zero_lt_one⟩
  let global : Fin (m + 1) := P.indexEquiv.symm ⟨li, last⟩
  have hglobal : (P.boundaryIndex i).castSucc = global := by
    apply Fin.ext
    rfl
  rw [hglobal]
  change a.toBONG.order global = _
  rw [P.order_inverse_indexEquiv li last]
  change Lattice.IsNormGeneratorValue q (J.fundamentalLattice li)
      (P.terminalValue li) at hterminal
  have hlastValueOrder :
      ordUnit K (P.terminalValue li) =
        ordUnit K (J.fundamentalNormGenerator li) := by
    exact (Lattice.principalIdeal_eq_iff_ordUnit_eq _ _).mp
      (hterminal.2.symm.trans (J.fundamentalNormGenerator_spec li).2)
  change ordUnit K
      (uniformizerPowerUnit K
          (2 * ordUnit K (J.normGenerator li) -
            2 * ordUnit K (J.scaleGenerator li)) *
        a.toBONG.valueUnit global) =
      ordUnit K (J.fundamentalNormGenerator li) at hlastValueOrder
  rw [ordUnit_mul, ordUnit_uniformizerPowerUnit,
    ← a.toBONG.order_eq_ordUnit] at hlastValueOrder
  rw [P.order_inverse_indexEquiv li last] at hlastValueOrder
  change ordUnit K (J.normGenerator li) =
      ordUnit K (J.fundamentalNormGenerator li) at hnorm
  change _ = 2 * J.fundamentalScaleOrder li -
    ordUnit K (J.fundamentalNormGenerator li)
  unfold Lattice.JordanDecomposition.fundamentalScaleOrder at *
  omega

theorem order_boundaryIndex_succ
    (P : JordanOrderProfileWitness a.toBONG J) (i : Fin t) :
    a.order (P.boundaryIndex i).succ =
      ordUnit K
        (J.fundamentalNormGenerator
          (Lattice.JordanDecomposition.boundaryRightIndex i)) := by
  let li : Fin (t + 1) := Lattice.JordanDecomposition.boundaryLeftIndex i
  let ri : Fin (t + 1) := Lattice.JordanDecomposition.boundaryRightIndex i
  let last : Fin (J.toOrthogonalDecomposition.componentRank li) :=
    ⟨J.toOrthogonalDecomposition.componentRank li - 1, by
      exact Nat.sub_lt (J.component_finrank_pos li) Nat.zero_lt_one⟩
  let first : Fin (J.toOrthogonalDecomposition.componentRank ri) :=
    ⟨0, J.component_finrank_pos ri⟩
  let leftGlobal : Fin (m + 1) := P.indexEquiv.symm ⟨li, last⟩
  let rightGlobal : Fin (m + 1) := P.indexEquiv.symm ⟨ri, first⟩
  have hnext : rightGlobal.val = leftGlobal.val + 1 := by
    apply P.inverse_index_val_next_component li ri
    · rfl
    · dsimp only [last]
      exact Nat.sub_add_cancel (J.component_finrank_pos li)
  have hleft : (P.boundaryIndex i).val = leftGlobal.val := rfl
  have hglobal : (P.boundaryIndex i).succ = rightGlobal := by
    apply Fin.ext
    simp only [Fin.val_succ]
    omega
  rw [hglobal]
  change a.toBONG.order rightGlobal = _
  rw [P.order_inverse_indexEquiv ri first]
  have hfirst : BONG.jordanExpectedOrder J ri first =
      BONG.jordanEffectiveNormOrder J ri := by
    unfold BONG.jordanExpectedOrder
    by_cases hproper : ordUnit K (J.scaleGenerator ri) =
        BONG.jordanEffectiveNormOrder J ri
    · rw [if_pos hproper, hproper]
    · rw [if_neg hproper]
      simp only [first, even_iff_two_dvd, dvd_zero, if_true]
  rw [hfirst]
  change BONG.jordanEffectiveNormOrder J ri =
    ordUnit K (J.fundamentalNormGenerator ri)
  exact (J.fundamentalNormGenerator_order_eq_effective ri).symm

theorem orderGap_boundaryIndex
    (P : JordanOrderProfileWitness a.toBONG J) (i : Fin t)
    (hterminal : Lattice.IsNormGeneratorValue q
      (J.fundamentalLattice
        (Lattice.JordanDecomposition.boundaryLeftIndex i))
      (P.terminalValue
        (Lattice.JordanDecomposition.boundaryLeftIndex i)))
    (hnorm : ordUnit K
        (J.normGenerator
          (Lattice.JordanDecomposition.boundaryLeftIndex i)) =
      ordUnit K
        (J.fundamentalNormGenerator
          (Lattice.JordanDecomposition.boundaryLeftIndex i))) :
    a.orderGap (P.boundaryIndex i) =
      J.boundaryNormOrderSum i -
        2 * J.fundamentalScaleOrder
          (Lattice.JordanDecomposition.boundaryLeftIndex i) := by
  unfold GoodBONG.orderGap
  rw [P.order_boundaryIndex_succ i,
    P.order_boundaryIndex i hterminal hnorm]
  unfold Lattice.JordanDecomposition.boundaryNormOrderSum
  ring

end BONG.JordanOrderProfileWitness

namespace Lattice.JordanDecomposition

noncomputable def castComponentCount
    {c d : Nat} (J : JordanDecomposition q L c) (h : c = d) :
    JordanDecomposition q L d := by
  subst d
  exact J

end Lattice.JordanDecomposition

namespace BONG.JordanOrderProfileWitness

noncomputable def castComponentCount
    {c d : Nat} {J : Lattice.JordanDecomposition q L c}
    {a : GoodBONG q L (m + 1)}
    (P : JordanOrderProfileWitness a.toBONG J) (h : c = d) :
    JordanOrderProfileWitness a.toBONG (J.castComponentCount h) := by
  subst d
  exact P

theorem castComponentCount_terminalGenerator
    {c d : Nat} {J : Lattice.JordanDecomposition q L c}
    {a : GoodBONG q L (m + 1)}
    (P : JordanOrderProfileWitness a.toBONG J) (h : c = d)
    (hterminal : ∀ i : Fin c, Lattice.IsNormGeneratorValue q
      (J.fundamentalLattice i) (P.terminalValue i))
    (i : Fin d) :
    Lattice.IsNormGeneratorValue q
      ((J.castComponentCount h).fundamentalLattice i)
      ((P.castComponentCount h).terminalValue i) := by
  subst d
  exact hterminal i

theorem castComponentCount_normOrder
    {c d : Nat} {J : Lattice.JordanDecomposition q L c}
    {a : GoodBONG q L (m + 1)}
    (_P : JordanOrderProfileWitness a.toBONG J) (h : c = d)
    (hnorm : ∀ i : Fin c,
      ordUnit K (J.normGenerator i) =
        ordUnit K (J.fundamentalNormGenerator i))
    (i : Fin d) :
    ordUnit K ((J.castComponentCount h).normGenerator i) =
      ordUnit K ((J.castComponentCount h).fundamentalNormGenerator i) := by
  subst d
  exact hnorm i

end BONG.JordanOrderProfileWitness

namespace BONG.StrictJordanAdaptedAlignment

variable {W : Type w} [AddCommGroup W] [Module K W]
  {r : QuadraticSpace K W} {M : Lattice K W}
  {a : GoodBONG q L (m + 1)} {b : GoodBONG r M (m + 1)}

noncomputable def sourceJordanSucc
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1) :
    Lattice.JordanDecomposition q L (t + 1) :=
  S.sourceJordan.castComponentCount h

noncomputable def sourceProfileSucc
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1) :
    JordanOrderProfileWitness a.toBONG (S.sourceJordanSucc h) :=
  S.sourceProfile.castComponentCount h

theorem sourceTerminalValue_isNormGeneratorValue
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1) (i : Fin (t + 1)) :
    Lattice.IsNormGeneratorValue q
      ((S.sourceJordanSucc h).fundamentalLattice i)
      ((S.sourceProfileSucc h).terminalValue i) := by
  apply S.sourceProfile.castComponentCount_terminalGenerator h
  intro j
  exact S.toStrictJordanEndpointAlignment.sourceTerminalGenerator_fundamentalLattice j

theorem sourceNormGenerator_order_eq_fundamental
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1) (i : Fin (t + 1)) :
    ordUnit K ((S.sourceJordanSucc h).normGenerator i) =
      ordUnit K ((S.sourceJordanSucc h).fundamentalNormGenerator i) := by
  apply S.sourceProfile.castComponentCount_normOrder h
  intro j
  have heffective :=
    S.weakAlignment.endpoint.sourceEndpoints.normOrder_eq_effective j
  rw [S.sourceJordan.fundamentalNormGenerator_order_eq_effective]
  change ordUnit K
      (S.weakAlignment.endpoint.sourceWeak.normGeneratorUnit j) =
    JordanProfileOrder.effectiveAt
      (fun k ↦ ordUnit K
        (S.weakAlignment.endpoint.sourceWeak.scaleGenerator k))
      (fun k ↦ ordUnit K
        (S.weakAlignment.endpoint.sourceWeak.normGeneratorUnit k)) j
      (ordUnit K
        (S.weakAlignment.endpoint.sourceWeak.scaleGenerator j)) at heffective
  change ordUnit K
      (S.weakAlignment.endpoint.sourceWeak.normGeneratorUnit j) =
    JordanProfileOrder.effectiveAt
      (fun k ↦ ordUnit K
        (S.weakAlignment.endpoint.sourceWeak.scaleGenerator k))
      (fun k ↦ ordUnit K
        (S.weakAlignment.endpoint.sourceWeak.normGeneratorUnit k)) j
      (ordUnit K
        (S.weakAlignment.endpoint.sourceWeak.scaleGenerator j))
  exact heffective

noncomputable def targetJordanSucc
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1) :
    Lattice.JordanDecomposition r M (t + 1) :=
  S.targetJordan.castComponentCount h

noncomputable def targetProfileSucc
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1) :
    JordanOrderProfileWitness b.toBONG (S.targetJordanSucc h) :=
  S.targetProfile.castComponentCount h

theorem targetTerminalValue_isNormGeneratorValue
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1) (i : Fin (t + 1)) :
    Lattice.IsNormGeneratorValue r
      ((S.targetJordanSucc h).fundamentalLattice i)
      ((S.targetProfileSucc h).terminalValue i) := by
  apply S.targetProfile.castComponentCount_terminalGenerator h
  intro j
  exact S.toStrictJordanEndpointAlignment.targetTerminalGenerator_fundamentalLattice j

theorem targetNormGenerator_order_eq_fundamental
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1) (i : Fin (t + 1)) :
    ordUnit K ((S.targetJordanSucc h).normGenerator i) =
      ordUnit K ((S.targetJordanSucc h).fundamentalNormGenerator i) := by
  apply S.targetProfile.castComponentCount_normOrder h
  intro j
  have heffective :=
    S.weakAlignment.endpoint.targetEndpoints.normOrder_eq_effective j
  rw [S.targetJordan.fundamentalNormGenerator_order_eq_effective]
  change ordUnit K
      (S.weakAlignment.endpoint.targetWeak.normGeneratorUnit j) =
    JordanProfileOrder.effectiveAt
      (fun k ↦ ordUnit K
        (S.weakAlignment.endpoint.targetWeak.scaleGenerator k))
      (fun k ↦ ordUnit K
        (S.weakAlignment.endpoint.targetWeak.normGeneratorUnit k)) j
      (ordUnit K
        (S.weakAlignment.endpoint.targetWeak.scaleGenerator j)) at heffective
  change ordUnit K
      (S.weakAlignment.endpoint.targetWeak.normGeneratorUnit j) =
    JordanProfileOrder.effectiveAt
      (fun k ↦ ordUnit K
        (S.weakAlignment.endpoint.targetWeak.scaleGenerator k))
      (fun k ↦ ordUnit K
        (S.weakAlignment.endpoint.targetWeak.normGeneratorUnit k)) j
      (ordUnit K
        (S.weakAlignment.endpoint.targetWeak.scaleGenerator j))
  exact heffective

end BONG.StrictJordanAdaptedAlignment

namespace Lattice.JordanDecomposition

variable {J : JordanDecomposition q L (t + 1)}

/-- The actual O'Meara fundamental ideal, packaged with its explicit order
in the odd boundary branch. -/
noncomputable def oddOrderedFundamentalIdeal
    (J : JordanDecomposition q L (t + 1)) (i : Fin t)
    (hodd : Odd (J.boundaryNormOrderSum i)) :
    OrderedFractionalIdeal K where
  carrier := J.fundamentalIdeal i
  order := J.boundaryNormOrderSum i -
    2 * J.fundamentalScaleOrder (boundaryLeftIndex i)
  carrier_eq_powerIdeal := by
    rw [J.fundamentalIdeal_eq_principalIdeal_of_odd i hodd,
      principalIdeal_eq_powerIdeal]
    congr 1
    rw [ordUnit_mul, ordUnit_mul, ordUnit_pow, ordUnit_inv]
    unfold boundaryNormOrderSum fundamentalScaleOrder
    ring

end Lattice.JordanDecomposition

namespace BONG.JordanOrderProfileWitness

variable {a : GoodBONG q L (m + 1)}
  {J : Lattice.JordanDecomposition q L (t + 1)}

/-- The concrete boundary record tied to an actual profiled Jordan
decomposition in the odd branch. -/
noncomputable def oddBoundaryAlphaData
    (P : JordanOrderProfileWitness a.toBONG J) (i : Fin t)
    (hodd : Odd (J.boundaryNormOrderSum i)) :
    a.BoundaryJordanAlphaData where
  index := P.boundaryIndex i
  fundamental := J.oddOrderedFundamentalIdeal i hodd

/-- Concrete odd branch of Beli (2009), Lemma 2.16(ii): the order of the
actual O'Meara ideal equals the actual good-BONG boundary gap. -/
theorem oddBoundaryAlphaData_order_eq_orderGap
    (P : JordanOrderProfileWitness a.toBONG J) (i : Fin t)
    (hodd : Odd (J.boundaryNormOrderSum i))
    (hterminal : Lattice.IsNormGeneratorValue q
      (J.fundamentalLattice
        (Lattice.JordanDecomposition.boundaryLeftIndex i))
      (P.terminalValue
        (Lattice.JordanDecomposition.boundaryLeftIndex i)))
    (hnorm : ordUnit K
        (J.normGenerator
          (Lattice.JordanDecomposition.boundaryLeftIndex i)) =
      ordUnit K
        (J.fundamentalNormGenerator
          (Lattice.JordanDecomposition.boundaryLeftIndex i))) :
    (P.oddBoundaryAlphaData i hodd).fundamental.order =
      a.orderGap (P.oddBoundaryAlphaData i hodd).index := by
  change J.boundaryNormOrderSum i -
      2 * J.fundamentalScaleOrder
        (Lattice.JordanDecomposition.boundaryLeftIndex i) =
    a.orderGap (P.boundaryIndex i)
  exact (P.orderGap_boundaryIndex i hterminal hnorm).symm

theorem odd_orderGap
    (P : JordanOrderProfileWitness a.toBONG J) (i : Fin t)
    (hodd : Odd (J.boundaryNormOrderSum i))
    (hterminal : Lattice.IsNormGeneratorValue q
      (J.fundamentalLattice
        (Lattice.JordanDecomposition.boundaryLeftIndex i))
      (P.terminalValue
        (Lattice.JordanDecomposition.boundaryLeftIndex i)))
    (hnorm : ordUnit K
        (J.normGenerator
          (Lattice.JordanDecomposition.boundaryLeftIndex i)) =
      ordUnit K
        (J.fundamentalNormGenerator
          (Lattice.JordanDecomposition.boundaryLeftIndex i))) :
    Odd (a.orderGap (P.boundaryIndex i)) := by
  rw [P.orderGap_boundaryIndex i hterminal hnorm]
  rcases hodd with ⟨z, hz⟩
  refine ⟨z - J.fundamentalScaleOrder
    (Lattice.JordanDecomposition.boundaryLeftIndex i), ?_⟩
  omega

/-- Full odd-boundary branch of Beli (2009), Lemma 2.16(ii), now stated
only for the boundary record generated by the actual Jordan profile. -/
theorem oddBoundaryAlphaData_lemma216
    (P : JordanOrderProfileWitness a.toBONG J) (i : Fin t)
    (hodd : Odd (J.boundaryNormOrderSum i))
    (hterminal : Lattice.IsNormGeneratorValue q
      (J.fundamentalLattice
        (Lattice.JordanDecomposition.boundaryLeftIndex i))
      (P.terminalValue
        (Lattice.JordanDecomposition.boundaryLeftIndex i)))
    (hnorm : ordUnit K
        (J.normGenerator
          (Lattice.JordanDecomposition.boundaryLeftIndex i)) =
      ordUnit K
        (J.fundamentalNormGenerator
          (Lattice.JordanDecomposition.boundaryLeftIndex i))) :
    ((Even (a.orderGap (P.oddBoundaryAlphaData i hodd).index) ∨
        a.orderGap (P.oddBoundaryAlphaData i hodd).index ≤
          2 * (ramificationIndex K : Int)) →
      a.alphaValue (P.oddBoundaryAlphaData i hodd).index =
        ((P.oddBoundaryAlphaData i hodd).fundamental.order : ℚ)) ∧
    (¬(Even (a.orderGap (P.oddBoundaryAlphaData i hodd).index) ∨
        a.orderGap (P.oddBoundaryAlphaData i hodd).index ≤
          2 * (ramificationIndex K : Int)) →
      a.alphaValue (P.oddBoundaryAlphaData i hodd).index =
          a.halfGapValue (P.oddBoundaryAlphaData i hodd).index ∧
      (P.oddBoundaryAlphaData i hodd).fundamental.order =
          a.orderGap (P.oddBoundaryAlphaData i hodd).index ∧
      ((P.oddBoundaryAlphaData i hodd).fundamental.order : ℚ) =
          2 * a.alphaValue (P.oddBoundaryAlphaData i hodd).index -
            2 * (ramificationIndex K : ℚ) ∧
      2 * (ramificationIndex K : ℚ) <
          a.alphaValue (P.oddBoundaryAlphaData i hodd).index ∧
      2 * (ramificationIndex K : ℚ) <
          ((P.oddBoundaryAlphaData i hodd).fundamental.order : ℚ)) := by
  let D := P.oddBoundaryAlphaData i hodd
  have hfund : D.fundamental.order = a.orderGap D.index :=
    P.oddBoundaryAlphaData_order_eq_orderGap i hodd hterminal hnorm
  have hgapOdd : Odd (a.orderGap D.index) :=
    P.odd_orderGap i hodd hterminal hnorm
  constructor
  · rintro (hgapEven | hgapLe)
    · rcases hgapEven with ⟨x, hx⟩
      rcases hgapOdd with ⟨y, hy⟩
      exact False.elim ((Int.not_even_iff_odd.mpr ⟨y, hy⟩) ⟨x, hx⟩)
    · rw [hfund]
      exact a.alphaValue_eq_orderGap_of_odd_of_le_twoE
        D.index hgapLe hgapOdd
  · intro hexceptional
    have hgapLarge : 2 * (ramificationIndex K : Int) <
        a.orderGap D.index := by
      by_contra hnot
      exact hexceptional (Or.inr (le_of_not_gt hnot))
    have halpha : a.alphaValue D.index = a.halfGapValue D.index :=
      a.satisfiesAlphaP4_proved D.index hgapLarge.le
    have hgapLargeQ : 2 * (ramificationIndex K : ℚ) <
        (a.orderGap D.index : ℚ) := by
      exact_mod_cast hgapLarge
    have halphaLarge : 2 * (ramificationIndex K : ℚ) <
        a.alphaValue D.index := by
      rw [halpha]
      unfold GoodBONG.halfGapValue
      push_cast
      linarith
    have hfundLarge : 2 * (ramificationIndex K : ℚ) <
        (D.fundamental.order : ℚ) := by
      rw [hfund]
      exact hgapLargeQ
    refine ⟨halpha, hfund, ?_, halphaLarge, hfundLarge⟩
    rw [hfund, halpha]
    unfold GoodBONG.halfGapValue
    push_cast
    ring

end BONG.JordanOrderProfileWitness

namespace BONG.StrictJordanAdaptedAlignment

variable {W : Type w} [AddCommGroup W] [Module K W]
  {r : QuadraticSpace K W} {M : Lattice K W}
  {a : GoodBONG q L (m + 1)} {b : GoodBONG r M (m + 1)}

noncomputable def sourceOddBoundaryAlphaData
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1) (i : Fin t)
    (hodd : Odd ((S.sourceJordanSucc h).boundaryNormOrderSum i)) :
    a.BoundaryJordanAlphaData :=
  (S.sourceProfileSucc h).oddBoundaryAlphaData i hodd

theorem sourceOddBoundaryAlphaData_order_eq_orderGap
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1) (i : Fin t)
    (hodd : Odd ((S.sourceJordanSucc h).boundaryNormOrderSum i)) :
    (S.sourceOddBoundaryAlphaData h i hodd).fundamental.order =
      a.orderGap (S.sourceOddBoundaryAlphaData h i hodd).index := by
  apply (S.sourceProfileSucc h).oddBoundaryAlphaData_order_eq_orderGap
  · exact S.sourceTerminalValue_isNormGeneratorValue h _
  · exact S.sourceNormGenerator_order_eq_fundamental h _

theorem sourceOddBoundaryAlphaData_orderGap_odd
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1) (i : Fin t)
    (hodd : Odd ((S.sourceJordanSucc h).boundaryNormOrderSum i)) :
    Odd (a.orderGap (S.sourceOddBoundaryAlphaData h i hodd).index) := by
  apply (S.sourceProfileSucc h).odd_orderGap i hodd
  · exact S.sourceTerminalValue_isNormGeneratorValue h _
  · exact S.sourceNormGenerator_order_eq_fundamental h _

/-- The complete odd case of Lemma 2.16(ii) for an actual source Jordan
boundary of the aligned pair. -/
theorem sourceOddBoundaryAlphaData_lemma216
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1) (i : Fin t)
    (hodd : Odd ((S.sourceJordanSucc h).boundaryNormOrderSum i)) :
    ((Even (a.orderGap (S.sourceOddBoundaryAlphaData h i hodd).index) ∨
        a.orderGap (S.sourceOddBoundaryAlphaData h i hodd).index ≤
          2 * (ramificationIndex K : Int)) →
      a.alphaValue (S.sourceOddBoundaryAlphaData h i hodd).index =
        ((S.sourceOddBoundaryAlphaData h i hodd).fundamental.order : ℚ)) ∧
    (¬(Even (a.orderGap (S.sourceOddBoundaryAlphaData h i hodd).index) ∨
        a.orderGap (S.sourceOddBoundaryAlphaData h i hodd).index ≤
          2 * (ramificationIndex K : Int)) →
      a.alphaValue (S.sourceOddBoundaryAlphaData h i hodd).index =
          a.halfGapValue (S.sourceOddBoundaryAlphaData h i hodd).index ∧
      (S.sourceOddBoundaryAlphaData h i hodd).fundamental.order =
          a.orderGap (S.sourceOddBoundaryAlphaData h i hodd).index ∧
      ((S.sourceOddBoundaryAlphaData h i hodd).fundamental.order : ℚ) =
          2 * a.alphaValue (S.sourceOddBoundaryAlphaData h i hodd).index -
            2 * (ramificationIndex K : ℚ) ∧
      2 * (ramificationIndex K : ℚ) <
          a.alphaValue (S.sourceOddBoundaryAlphaData h i hodd).index ∧
      2 * (ramificationIndex K : ℚ) <
          ((S.sourceOddBoundaryAlphaData h i hodd).fundamental.order : ℚ)) := by
  apply (S.sourceProfileSucc h).oddBoundaryAlphaData_lemma216 i hodd
  · exact S.sourceTerminalValue_isNormGeneratorValue h _
  · exact S.sourceNormGenerator_order_eq_fundamental h _

noncomputable def targetOddBoundaryAlphaData
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1) (i : Fin t)
    (hodd : Odd ((S.targetJordanSucc h).boundaryNormOrderSum i)) :
    b.BoundaryJordanAlphaData :=
  (S.targetProfileSucc h).oddBoundaryAlphaData i hodd

theorem targetOddBoundaryAlphaData_order_eq_orderGap
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1) (i : Fin t)
    (hodd : Odd ((S.targetJordanSucc h).boundaryNormOrderSum i)) :
    (S.targetOddBoundaryAlphaData h i hodd).fundamental.order =
      b.orderGap (S.targetOddBoundaryAlphaData h i hodd).index := by
  apply (S.targetProfileSucc h).oddBoundaryAlphaData_order_eq_orderGap
  · exact S.targetTerminalValue_isNormGeneratorValue h _
  · exact S.targetNormGenerator_order_eq_fundamental h _

theorem targetOddBoundaryAlphaData_orderGap_odd
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1) (i : Fin t)
    (hodd : Odd ((S.targetJordanSucc h).boundaryNormOrderSum i)) :
    Odd (b.orderGap (S.targetOddBoundaryAlphaData h i hodd).index) := by
  apply (S.targetProfileSucc h).odd_orderGap i hodd
  · exact S.targetTerminalValue_isNormGeneratorValue h _
  · exact S.targetNormGenerator_order_eq_fundamental h _

/-- The complete odd case of Lemma 2.16(ii) for an actual target Jordan
boundary of the aligned pair. -/
theorem targetOddBoundaryAlphaData_lemma216
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1) (i : Fin t)
    (hodd : Odd ((S.targetJordanSucc h).boundaryNormOrderSum i)) :
    ((Even (b.orderGap (S.targetOddBoundaryAlphaData h i hodd).index) ∨
        b.orderGap (S.targetOddBoundaryAlphaData h i hodd).index ≤
          2 * (ramificationIndex K : Int)) →
      b.alphaValue (S.targetOddBoundaryAlphaData h i hodd).index =
        ((S.targetOddBoundaryAlphaData h i hodd).fundamental.order : ℚ)) ∧
    (¬(Even (b.orderGap (S.targetOddBoundaryAlphaData h i hodd).index) ∨
        b.orderGap (S.targetOddBoundaryAlphaData h i hodd).index ≤
          2 * (ramificationIndex K : Int)) →
      b.alphaValue (S.targetOddBoundaryAlphaData h i hodd).index =
          b.halfGapValue (S.targetOddBoundaryAlphaData h i hodd).index ∧
      (S.targetOddBoundaryAlphaData h i hodd).fundamental.order =
          b.orderGap (S.targetOddBoundaryAlphaData h i hodd).index ∧
      ((S.targetOddBoundaryAlphaData h i hodd).fundamental.order : ℚ) =
          2 * b.alphaValue (S.targetOddBoundaryAlphaData h i hodd).index -
            2 * (ramificationIndex K : ℚ) ∧
      2 * (ramificationIndex K : ℚ) <
          b.alphaValue (S.targetOddBoundaryAlphaData h i hodd).index ∧
      2 * (ramificationIndex K : ℚ) <
          ((S.targetOddBoundaryAlphaData h i hodd).fundamental.order : ℚ)) := by
  apply (S.targetProfileSucc h).oddBoundaryAlphaData_lemma216 i hodd
  · exact S.targetTerminalValue_isNormGeneratorValue h _
  · exact S.targetNormGenerator_order_eq_fundamental h _

end BONG.StrictJordanAdaptedAlignment

end Bong
