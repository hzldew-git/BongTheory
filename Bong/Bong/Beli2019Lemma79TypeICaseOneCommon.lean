/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.AlternatingEndpointTowerRepresentation
import Bong.Bong.Beli2019CanonicalApproximation
import Bong.Bong.Beli2019Lemma75EndpointClass
import Bong.Bong.Beli2019Lemma79TypeICaseOneProfile
import Bong.Bong.BinaryEndpointProduct

/-!
# Beli (2019), Lemma 7.9(ii), case 1: common odd subform

The two exceptional even prefixes are alternating endpoint towers with the
same high order.  The generic dyadic tower theorem therefore embeds the
prefix of `c` obtained by deleting its last coefficient into the full prefix
of `b`.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The two Lemma 7.5 towers in case 1 have a common codimension-one
diagonal subform. -/
theorem beli2019Lemma79_typeI_caseOne_commonPrefix
    [Beli2006AlphaLaws.{u, v} K]
    [discriminant : DyadicDiscriminantClassLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (D : Lemma67TypeI a b) (C : Lemma67TypeICanonicalData a b D)
    (hnorm : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (i : RepresentationIndex (n + 2) (n + 2))
    (hleft : i.val = C.leftSwitch)
    (hgap : b.orderGap ⟨i.val - 1, by
        have hiBound := i.lt_large
        omega⟩ = 2 * (ramificationIndex K : Int) + 1)
    (hprevious : c.order ⟨i.val - 1, by
        have hiBound := i.lt_large
        omega⟩ = b.order ⟨i.val - 1, by
        have hiBound := i.lt_large
        omega⟩) :
    DiagonalRepresents
      (c.prefixValues (i.val - 1)
        ((Nat.sub_le i.val 1).trans i.lt_large.le))
      (b.prefixValues i.val i.lt_large.le) := by
  have hiEven : Even i.val := by
    simpa only [hleft] using C.left_even
  have hiTwo : 2 ≤ i.val := by
    have hiPos := i.pos
    rcases hiEven with ⟨d, hd⟩
    omega
  rcases hiEven with ⟨pairs, hpairs⟩
  have hpairsEq : 2 * pairs = i.val := by omega
  have hpairsPos : 0 < pairs := by omega
  have hpairsBound : 2 * pairs ≤ n + 1 := by
    have hiBound := i.lt_large
    omega
  let first : Fin (n + 1) := ⟨0, by omega⟩
  let lastPair : Fin (n + 1) := ⟨2 * pairs - 2, by omega⟩
  have hfirstLast : first ≤ lastPair := by
    exact Fin.mk_le_mk.mpr (Nat.zero_le _)
  have hsegmentEven : Even (lastPair.val - first.val) := by
    refine ⟨pairs - 1, ?_⟩
    simp only [first, lastPair]
    omega
  rcases beli2019Lemma79_typeI_caseOne_endpointOrders
      a b c D C hnorm i hleft hgap hprevious with
    ⟨hfirstOrders, hbLast, hcLast⟩
  have hbInitial : b.order first.castSucc = b.order 0 := by
    congr 1
  have hcInitial : c.order first.castSucc = b.order 0 := by
    have hindex : first.castSucc = (0 : Fin (n + 2)) := by
      apply Fin.ext
      rfl
    rw [hindex, ← hfirstOrders]
  have hlastSucc : lastPair.succ =
      (⟨i.val - 1, by omega⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp only [lastPair, Fin.val_succ]
    omega
  have hbTerminal : b.order lastPair.succ =
      b.order 0 - 2 * (ramificationIndex K : Int) := by
    rw [hlastSucc]
    exact hbLast
  have hcTerminal : c.order lastPair.succ =
      b.order 0 - 2 * (ramificationIndex K : Int) := by
    rw [hlastSucc, hcLast, ← hfirstOrders]
  let hbArithmetic := b.beli2019Lemma75_arithmetic first lastPair
    (b.order 0) hfirstLast hsegmentEven hbInitial hbTerminal
  let hcArithmetic := c.beli2019Lemma75_arithmetic first lastPair
    (b.order 0) hfirstLast hsegmentEven hcInitial hcTerminal
  let bu := b.prefixValueUnits (2 * pairs) (by omega)
  let cu := c.prefixValueUnits (2 * pairs) (by omega)
  have hbClasses : AlternatingEndpointPairClasses bu := by
    intro t
    let k : Fin (n + 1) := ⟨2 * t.val, by omega⟩
    have hik : first ≤ k := Fin.zero_le k
    have hkj : k ≤ lastPair := by
      change 2 * t.val ≤ 2 * pairs - 2
      omega
    have hkEven : Even (k.val - first.val) := by
      refine ⟨t.val, ?_⟩
      simp only [k, first, Nat.sub_zero]
      omega
    have hclasses := b.beli2019Lemma75_pairBlock_endpointClass
      first lastPair k (b.order 0) hfirstLast hsegmentEven hbInitial
        hbTerminal hik hkj hkEven
    have hpair := b.toBONG.adjacentSignedProduct_endpoint_cases
      k.castSucc (Nat.succ_lt_succ k.isLt) hclasses
    simpa only [bu, prefixValueUnits, GoodBONG.valueUnit, k,
      Fin.castSucc_mk] using hpair
  have hcClasses : AlternatingEndpointPairClasses cu := by
    intro t
    let k : Fin (n + 1) := ⟨2 * t.val, by omega⟩
    have hik : first ≤ k := Fin.zero_le k
    have hkj : k ≤ lastPair := by
      change 2 * t.val ≤ 2 * pairs - 2
      omega
    have hkEven : Even (k.val - first.val) := by
      refine ⟨t.val, ?_⟩
      simp only [k, first, Nat.sub_zero]
      omega
    have hclasses := c.beli2019Lemma75_pairBlock_endpointClass
      first lastPair k (b.order 0) hfirstLast hsegmentEven hcInitial
        hcTerminal hik hkj hkEven
    have hpair := c.toBONG.adjacentSignedProduct_endpoint_cases
      k.castSucc (Nat.succ_lt_succ k.isLt) hclasses
    simpa only [cu, prefixValueUnits, GoodBONG.valueUnit, k,
      Fin.castSucc_mk] using hpair
  let scale : Kˣ := uniformizerPowerUnit K (b.order 0)
  have hscaleOrder : ordUnit K scale = b.order 0 := by
    simp only [scale, ordUnit_uniformizerPowerUnit]
  have hbOrders : AlternatingEndpointLeadingOrdersAt bu scale := by
    intro t
    let k : Fin (n + 1) := ⟨2 * t.val, by omega⟩
    have hik : first ≤ k := Fin.zero_le k
    have hkj : k ≤ lastPair := by
      change 2 * t.val ≤ 2 * pairs - 2
      omega
    have hkEven : Even (k.val - first.val) := by
      refine ⟨t.val, ?_⟩
      simp only [k, first, Nat.sub_zero]
      omega
    have hbOrder := hbArithmetic.even_order k hik hkj hkEven
    change ordUnit K (b.toBONG.valueUnit ⟨2 * t.val, by omega⟩) =
      ordUnit K scale
    calc
      ordUnit K (b.toBONG.valueUnit ⟨2 * t.val, by omega⟩) =
          b.toBONG.order ⟨2 * t.val, by omega⟩ :=
        (b.toBONG.order_eq_ordUnit ⟨2 * t.val, by omega⟩).symm
      _ = b.toBONG.order 0 := by
        simpa only [GoodBONG.order, k, Fin.castSucc_mk] using hbOrder
      _ = ordUnit K scale := hscaleOrder.symm
  have hcOrders : AlternatingEndpointLeadingOrdersAt cu scale := by
    intro t
    let k : Fin (n + 1) := ⟨2 * t.val, by omega⟩
    have hik : first ≤ k := Fin.zero_le k
    have hkj : k ≤ lastPair := by
      change 2 * t.val ≤ 2 * pairs - 2
      omega
    have hkEven : Even (k.val - first.val) := by
      refine ⟨t.val, ?_⟩
      simp only [k, first, Nat.sub_zero]
      omega
    have hcOrder := hcArithmetic.even_order k hik hkj hkEven
    change ordUnit K (c.toBONG.valueUnit ⟨2 * t.val, by omega⟩) =
      ordUnit K scale
    calc
      ordUnit K (c.toBONG.valueUnit ⟨2 * t.val, by omega⟩) =
          c.toBONG.order ⟨2 * t.val, by omega⟩ :=
        (c.toBONG.order_eq_ordUnit ⟨2 * t.val, by omega⟩).symm
      _ = b.toBONG.order 0 := by
        simpa only [GoodBONG.order, k, Fin.castSucc_mk] using hcOrder
      _ = ordUnit K scale := hscaleOrder.symm
  have htower := alternatingEndpointTower_commonCodimensionOne
    bu cu scale hbClasses hcClasses hbOrders hcOrders
  have hrep : DiagonalRepresents
      (c.prefixValues (2 * pairs - 1) (by omega))
      (b.prefixValues (2 * pairs) (by omega)) := by
    simpa only [bu, cu, diagonalUnitTake_prefixValueUnits,
      diagonalUnitCoefficients_prefixValueUnits] using htower
  exact prefixRepresents_cast c b (by omega) hpairsEq hrep

end BONG.GoodBONG

end Bong
