/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma716TypeIGeometry
import Bong.Bong.AlternatingEndpointTowerRepresentation
import Bong.Bong.Beli2019Lemma75EndpointClass
import Bong.Bong.DiagonalHasseSymbol

/-!
# Beli (2019), Lemma 7.16: the type-II geometric obstruction

After the alternating blocks are removed, the paper's type-II obstruction
is the ternary form `[a₁, a₂, aₛ₊₁]`.  Its first signed adjacent product is
in the unramified discriminant class, whereas its second signed adjacent
product has odd valuation.  The adjacent-product Hilbert criterion therefore
makes this ternary form anisotropic.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L N : Lattice K V} {n : Nat}

variable [Beli2006AlphaLaws.{u, v} K]
variable [laws : DyadicDiscriminantClassLaws K]
variable [DyadicUnramifiedNormLaws K]
variable [HilbertSymbolLaws K]

/-- The three coefficients left after the type-II alternating cancellation:
the initial unramified binary plane and the coefficient at paper index
`s + 1`. -/
noncomputable def lemma716TypeIIResidualTernary
    (a : GoodBONG q L (n + 3)) (s : Nat) (hs : s < n + 3) :
    Fin 3 → Kˣ :=
  ![a.valueUnit (0 : Fin (n + 3)),
    a.valueUnit (1 : Fin (n + 3)),
    a.valueUnit ⟨s, hs⟩]

omit [Beli2006AlphaLaws.{u, v} K] in
/-- The residual ternary form in type II is anisotropic. -/
theorem lemma716_typeII_residualTernary_anisotropic
    (a : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (hsecond : a.order 1 =
      R - 2 * (ramificationIndex K : Int))
    (hdiscriminant : a.toBONG.adjacentUnitSquareClass
      (0 : Fin (n + 3)) (by simp) = unitSquareClass K
        (lemma712DiscriminantParameter (K := K)))
    (hII : Lemma714IsTypeII a R s) :
    DiagonalAnisotropic
      (diagonalUnitCoefficients
        (lemma716TypeIIResidualTernary a s (Classical.choose hII))) := by
  have hII' : ∃ hs : s < n + 3, a.order ⟨s, hs⟩ = R + 1 := hII
  have hnextOrder :
      a.order ⟨s, Classical.choose hII'⟩ = R + 1 :=
    Classical.choose_spec hII'
  let residual :=
    lemma716TypeIIResidualTernary a s (Classical.choose hII')
  change DiagonalAnisotropic (diagonalUnitCoefficients residual)
  apply (not_diagonalIsotropic_iff_diagonalAnisotropic
    (diagonalUnitCoefficients residual)).mp
  intro hisotropic
  have hhilbert :=
    (diagonalUnitTernary_isotropic_iff_adjacentHilbertOne residual).mp
      hisotropic
  have hfirst : IsSquare
      (-(residual 0 * residual 1) * laws.discriminantUnit) := by
    simpa only [residual, lemma716TypeIIResidualTernary,
      Matrix.cons_val_zero, Matrix.cons_val_one] using
      a.lemma716_initialSignedProduct_mul_discriminant_isSquare hdiscriminant
  have hsecondOrder :
      ordUnit K (-(residual 1 * residual 2)) =
        (R - 2 * (ramificationIndex K : Int)) + (R + 1) := by
    rw [ordUnit_neg, ordUnit_mul]
    change ordUnit K (a.valueUnit (1 : Fin (n + 3))) +
        ordUnit K (a.valueUnit ⟨s, Classical.choose hII'⟩) = _
    unfold GoodBONG.valueUnit
    have hsecond' : a.toBONG.order (1 : Fin (n + 3)) =
        R - 2 * (ramificationIndex K : Int) := hsecond
    have hnextOrder' : a.toBONG.order ⟨s, Classical.choose hII'⟩ =
        R + 1 := hnextOrder
    rw [← a.toBONG.order_eq_ordUnit (1 : Fin (n + 3)),
      ← a.toBONG.order_eq_ordUnit ⟨s, Classical.choose hII'⟩,
      hsecond', hnextOrder']
  have hsecondOdd : Odd (ordUnit K (-(residual 1 * residual 2))) := by
    rw [hsecondOrder]
    apply Int.not_even_iff_odd.mp
    rintro ⟨k, hk⟩
    omega
  exact
    (hilbertSymbol_ne_one_of_isSquare_mul_discriminant_of_odd_order
      hfirst hsecondOdd) hhilbert

/-- Every rigid type-II failure profile is impossible.  Lemma 7.5 cancels
the comparison tower against the middle source tower; the remaining
ternary form is isotropic by representation theory but anisotropic by the
adjacent-product Hilbert criterion above. -/
theorem lemma716_typeII_failureProfile_false
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    (a : GoodBONG q L (n + 3)) (c : GoodBONG q N (n + 3))
    (R : Int) (s : Nat) (D : Lemma714StoppingData a R s)
    (hfirst : a.order 0 = R)
    (hsecond : a.order 1 =
      R - 2 * (ramificationIndex K : Int))
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (hdiscriminant : a.toBONG.adjacentUnitSquareClass
      (0 : Fin (n + 3)) (by simp) = unitSquareClass K
        (lemma712DiscriminantParameter (K := K)))
    (hII : Lemma714IsTypeII a R s)
    (P : Beli2019Lemma716TypeIIFailureProfile c R s D.two_le
      (Classical.choose hII))
    (hrep : DiagonalRepresents
      (c.prefixValues s (Nat.le_of_lt (Classical.choose hII)))
      (a.prefixValues (s + 1) (by
        have := Classical.choose hII
        omega))) : False := by
  rcases D.even with ⟨d, hd⟩
  let pairs := d - 1
  have hsTwo := D.two_le
  have hsEq : s = 2 * (pairs + 1) := by
    dsimp only [pairs]
    omega
  have D' : Lemma714StoppingData a R (2 * (pairs + 1)) := by
    rw [← hsEq]
    exact D
  have hRank : 2 * (pairs + 1) ≤ n + 3 := D'.le_rank
  have hInterior : 2 * (pairs + 1) < n + 3 := by
    rw [← hsEq]
    exact Classical.choose hII
  have hrepEq : DiagonalRepresents
      (c.prefixValues (2 * (pairs + 1)) (Nat.le_of_lt hInterior))
      (a.prefixValues (2 * (pairs + 1) + 1) (by omega)) := by
    exact prefixRepresents_cast c a hsEq (by omega) hrep
  let initial : Fin 2 → Kˣ := a.prefixValueUnits 2 (by omega)
  let source : Fin (2 * pairs) → Kˣ := fun i =>
    a.valueUnit ⟨i.val + 2, by omega⟩
  let comparison : Fin (2 * (pairs + 1)) → Kˣ :=
    c.prefixValueUnits (2 * (pairs + 1)) (Nat.le_of_lt hInterior)
  let extra : Kˣ := a.valueUnit ⟨2 * (pairs + 1), hInterior⟩
  have hextraOrder : ordUnit K extra = R + 1 := by
    have hindex : (⟨2 * (pairs + 1), hInterior⟩ : Fin (n + 3)) =
        ⟨s, Classical.choose hII⟩ := by
      apply Fin.ext
      simp only [Fin.val_mk]
      omega
    calc
      ordUnit K extra = a.order ⟨2 * (pairs + 1), hInterior⟩ := by
        exact (a.toBONG.order_eq_ordUnit _).symm
      _ = a.order ⟨s, Classical.choose hII⟩ := by rw [hindex]
      _ = R + 1 := Classical.choose_spec hII
  let comparisonFirst : Fin (n + 2) := ⟨0, by omega⟩
  let comparisonLast : Fin (n + 2) :=
    ⟨2 * (pairs + 1) - 2, by omega⟩
  have hcomparisonFirstLast : comparisonFirst ≤ comparisonLast := by
    exact Fin.mk_le_mk.mpr (by omega)
  have hcomparisonSegmentEven :
      Even (comparisonLast.val - comparisonFirst.val) := by
    exact ⟨pairs, by
      simp only [comparisonLast, comparisonFirst, Nat.sub_zero]
      omega⟩
  have hcomparisonInitial : c.order comparisonFirst.castSucc = R + 1 := by
    change c.order (0 : Fin (n + 3)) = R + 1
    exact P.first
  have hcomparisonTerminal : c.order comparisonLast.succ =
      R + 1 - 2 * (ramificationIndex K : Int) := by
    have hterminalIndex : comparisonLast.succ =
        (⟨2 * (pairs + 1) - 1, by omega⟩ : Fin (n + 3)) := by
      apply Fin.ext
      simp only [comparisonLast, Fin.val_succ]
      omega
    have hprofileIndex :
        (⟨2 * (pairs + 1) - 1, by omega⟩ : Fin (n + 3)) =
          ⟨s - 1, by omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_mk]
      omega
    rw [hterminalIndex, hprofileIndex, P.low]
    ring
  let comparisonArithmetic := c.beli2019Lemma75_arithmetic
    comparisonFirst comparisonLast (R + 1) hcomparisonFirstLast
      hcomparisonSegmentEven hcomparisonInitial hcomparisonTerminal
  have hcomparisonClasses : AlternatingEndpointPairClasses comparison := by
    intro t
    let k : Fin (n + 2) := ⟨2 * t.val, by omega⟩
    have hcomparisonFirstK : comparisonFirst ≤ k := Fin.zero_le k
    have hkComparisonLast : k ≤ comparisonLast := by
      exact Fin.mk_le_mk.mpr (by omega)
    have hkEven : Even (k.val - comparisonFirst.val) := by
      exact ⟨t.val, by
        simp only [k, comparisonFirst, Nat.sub_zero]
        omega⟩
    have hclasses := c.beli2019Lemma75_pairBlock_endpointClass
      comparisonFirst comparisonLast k (R + 1) hcomparisonFirstLast
        hcomparisonSegmentEven hcomparisonInitial hcomparisonTerminal
        hcomparisonFirstK hkComparisonLast hkEven
    have hpair := c.toBONG.adjacentSignedProduct_endpoint_cases
      k.castSucc (Nat.succ_lt_succ k.isLt) hclasses
    simpa only [comparison, prefixValueUnits, GoodBONG.valueUnit, k,
      Fin.castSucc_mk] using hpair
  have hcomparisonOrders : ∀ t : Fin (pairs + 1),
      ordUnit K (comparison ⟨2 * t.val, by omega⟩) = ordUnit K extra := by
    intro t
    let k : Fin (n + 2) := ⟨2 * t.val, by omega⟩
    have hkOrder := comparisonArithmetic.even_order k
      (Fin.zero_le k) (Fin.mk_le_mk.mpr (by omega))
      ⟨t.val, by
        simp only [k, comparisonFirst, Nat.sub_zero]
        omega⟩
    calc
      ordUnit K (comparison ⟨2 * t.val, by omega⟩) =
          c.order k.castSucc := by
        simpa only [comparison, prefixValueUnits, GoodBONG.valueUnit,
          GoodBONG.order, k, Fin.castSucc_mk] using
            (c.toBONG.order_eq_ordUnit k.castSucc).symm
      _ = R + 1 := hkOrder
      _ = ordUnit K extra := hextraOrder.symm
  have hsourceFacts : ∀ t : Fin pairs,
      (IsSquare (-(source ⟨2 * t.val, by omega⟩ *
          source ⟨2 * t.val + 1, by omega⟩)) ∨
        IsSquare (-(source ⟨2 * t.val, by omega⟩ *
            source ⟨2 * t.val + 1, by omega⟩) * laws.discriminantUnit)) ∧
      ordUnit K (source ⟨2 * t.val, by omega⟩) = ordUnit K extra := by
    intro t
    have ht := t.isLt
    have hpairsPos : 0 < pairs := by omega
    let sourceFirst : Fin (n + 2) := ⟨2, by omega⟩
    let sourceLast : Fin (n + 2) := ⟨2 * pairs, by omega⟩
    have hsourceFirstLast : sourceFirst ≤ sourceLast := by
      exact Fin.mk_le_mk.mpr (by omega)
    have hsourceSegmentEven : Even (sourceLast.val - sourceFirst.val) := by
      exact ⟨pairs - 1, by simp only [sourceLast, sourceFirst]; omega⟩
    have hsFour : 4 ≤ 2 * (pairs + 1) := by omega
    have hplateau := a.beli2019Lemma714_i R (2 * (pairs + 1))
      D'.toLemma714MinimalityData hsFour hthird
    have hsourceInitial : a.order sourceFirst.castSucc = R + 1 := by
      simpa only [sourceFirst, Fin.castSucc_mk] using
        hplateau.high_positions 2 (by omega) (by omega) (by simp)
    have hsourceTerminal : a.order sourceLast.succ =
        R + 1 - 2 * (ramificationIndex K : Int) := by
      have h := hplateau.low_positions (2 * pairs + 1)
        (by omega) (by omega) (by exact ⟨pairs, by omega⟩)
      have hindex : sourceLast.succ =
          (⟨2 * pairs + 1, by omega⟩ : Fin (n + 3)) := by
        apply Fin.ext
        rfl
      rw [hindex, h]
      ring
    let sourceArithmetic := a.beli2019Lemma75_arithmetic
      sourceFirst sourceLast (R + 1) hsourceFirstLast hsourceSegmentEven
        hsourceInitial hsourceTerminal
    let k : Fin (n + 2) := ⟨2 + 2 * t.val, by omega⟩
    have hsourceFirstK : sourceFirst ≤ k := by
      exact Fin.mk_le_mk.mpr (by omega)
    have hkSourceLast : k ≤ sourceLast := by
      exact Fin.mk_le_mk.mpr (by omega)
    have hkEven : Even (k.val - sourceFirst.val) := by
      exact ⟨t.val, by simp only [k, sourceFirst]; omega⟩
    have hclasses := a.beli2019Lemma75_pairBlock_endpointClass
      sourceFirst sourceLast k (R + 1) hsourceFirstLast
        hsourceSegmentEven hsourceInitial hsourceTerminal
        hsourceFirstK hkSourceLast hkEven
    have hpair := a.toBONG.adjacentSignedProduct_endpoint_cases
      k.castSucc (Nat.succ_lt_succ k.isLt) hclasses
    have hkOrder := sourceArithmetic.even_order k hsourceFirstK hkSourceLast
      hkEven
    constructor
    · simpa only [source, GoodBONG.valueUnit, k, Fin.castSucc_mk,
        Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hpair
    · calc
        ordUnit K (source ⟨2 * t.val, by omega⟩) =
            a.order k.castSucc := by
          simpa only [source, k, GoodBONG.valueUnit, GoodBONG.order,
            Fin.castSucc_mk, Nat.add_comm] using
              (a.toBONG.order_eq_ordUnit k.castSucc).symm
        _ = R + 1 := hkOrder
        _ = ordUnit K extra := hextraOrder.symm
  have hsourceClasses : AlternatingEndpointPairClasses source :=
    fun t => (hsourceFacts t).1
  have hsourceOrders : ∀ t : Fin pairs,
      ordUnit K (source ⟨2 * t.val, by omega⟩) = ordUnit K extra :=
    fun t => (hsourceFacts t).2
  have hinitial : IsSquare
      (-(initial 0 * initial 1) * laws.discriminantUnit) := by
    simpa [initial, prefixValueUnits] using
      a.lemma716_initialSignedProduct_mul_discriminant_isSquare
        hdiscriminant
  have hinitialZeroOrder : ordUnit K (initial 0) = R := by
    simpa [initial, prefixValueUnits, GoodBONG.order, GoodBONG.valueUnit] using hfirst
  have hodd : Odd (ordUnit K (extra * (initial 0)⁻¹)) := by
    rw [ordUnit_mul, ordUnit_inv, hextraOrder, hinitialZeroOrder]
    exact ⟨0, by omega⟩
  have hcomparisonCoefficients :
      diagonalUnitCoefficients comparison =
        c.prefixValues (2 * (pairs + 1)) (Nat.le_of_lt hInterior) := by
    funext i
    simp [comparison, diagonalUnitCoefficients, prefixValues,
      prefixValueUnits, GoodBONG.valueUnit, GoodBONG.value]
  have hrep' : DiagonalRepresents
      (c.prefixValues (2 * (pairs + 1)) (Nat.le_of_lt hInterior))
      (a.prefixValues (2 + 2 * pairs + 1) (by omega)) :=
    prefixRepresents_cast c a rfl (by omega) hrepEq
  have htargetCoefficients :
      diagonalUnitCoefficients (Fin.snoc (Fin.append initial source) extra) =
        a.prefixValues (2 + 2 * pairs + 1) (by omega) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [diagonalUnitCoefficients]
      rw [Fin.snoc_last]
      simp only [extra, prefixValues,
        GoodBONG.valueUnit, GoodBONG.value]
      rw [BONG.coe_valueUnit]
      apply congrArg a.toBONG.value
      apply Fin.ext
      simp only [Fin.val_last]
      omega
    · simp only [diagonalUnitCoefficients]
      rw [Fin.snoc_castSucc]
      refine Fin.addCases (fun k => ?_) (fun k => ?_) j
      · rw [Fin.append_left]
        simp [initial, prefixValues,
          prefixValueUnits, GoodBONG.valueUnit, GoodBONG.value]
      · rw [Fin.append_right]
        simp only [source, prefixValues,
          GoodBONG.valueUnit, GoodBONG.value]
        rw [BONG.coe_valueUnit]
        apply congrArg a.toBONG.value
        apply Fin.ext
        simp only [Fin.val_natAdd, Fin.val_castSucc]
        omega
  have hisotropic := alternatingEndpointTower_residualTernaryIsotropic
    initial source comparison extra hinitial hodd hsourceClasses
      hcomparisonClasses hsourceOrders hcomparisonOrders (by
        rw [hcomparisonCoefficients, htargetCoefficients]
        exact hrep')
  have hanisotropic :=
    a.lemma716_typeII_residualTernary_anisotropic R s hsecond
      hdiscriminant hII
  apply (not_diagonalIsotropic_iff_diagonalAnisotropic _).mpr hanisotropic
  convert hisotropic using 1
  funext i
  fin_cases i
  · rfl
  · rfl
  · simp only [initial, extra, prefixValueUnits, lemma716TypeIIResidualTernary,
      diagonalUnitCoefficients, Matrix.cons_val_zero, Matrix.cons_val_one,
      GoodBONG.valueUnit, GoodBONG.value]
    congr

end BONG.GoodBONG

end Bong
