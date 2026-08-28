/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.AlternatingEndpointTowerRepresentation
import Bong.Bong.Beli2019Lemma75EndpointClass
import Bong.Bong.BinaryEndpointProduct

/-!
# Beli (2019), Lemma 7.9(iii): reusable endpoint-tower geometry

Cases 1 and 5 use the same two consequences of Lemma 7.5 several times.
An even prefix whose first order is `R` and whose last order is `R - 2e`
is an alternating endpoint tower.  Such towers admit either an equal-length
unary extension or a one-pair extension.  This file packages those arguments
independently of the normalized type-I/II/III profiles.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The order endpoints in Lemma 7.5 force every pair of an even prefix into
one of the two unramified endpoint classes. -/
theorem lemma79_endpointTower_pairClasses
    [Beli2006AlphaLaws.{u, v} K]
    [laws : DyadicDiscriminantClassLaws K]
    (x : GoodBONG q L (n + 2)) (R : Int) (pairs : Nat)
    (hpairs : 0 < pairs) (hbound : 2 * pairs ≤ n + 2)
    (hfirst : x.order 0 = R)
    (hlast : x.order ⟨2 * pairs - 1, by omega⟩ =
      R - 2 * (ramificationIndex K : Int)) :
    AlternatingEndpointPairClasses
      (x.prefixValueUnits (2 * pairs) hbound) := by
  let first : Fin (n + 1) := ⟨0, by omega⟩
  let last : Fin (n + 1) := ⟨2 * pairs - 2, by omega⟩
  have hfirstLast : first ≤ last := Fin.zero_le last
  have hsegmentEven : Even (last.val - first.val) := by
    exact ⟨pairs - 1, by dsimp only [first, last]; omega⟩
  have hfirstOrder : x.order first.castSucc = R := by
    have hindex : first.castSucc = (0 : Fin (n + 2)) := by
      apply Fin.ext
      rfl
    rw [hindex]
    exact hfirst
  have hterminal : x.order last.succ =
      R - 2 * (ramificationIndex K : Int) := by
    have hindex : last.succ =
        (⟨2 * pairs - 1, by omega⟩ : Fin (n + 2)) := by
      apply Fin.ext
      simp only [last, Fin.val_succ]
      omega
    simpa only [hindex] using hlast
  intro t
  let k : Fin (n + 1) := ⟨2 * t.val, by omega⟩
  have hfirstK : first ≤ k := Fin.zero_le k
  have hkLast : k ≤ last := by
    change 2 * t.val ≤ 2 * pairs - 2
    omega
  have hkEven : Even (k.val - first.val) := by
    exact ⟨t.val, by dsimp only [k, first]; omega⟩
  have hclasses := x.beli2019Lemma75_pairBlock_endpointClass
    first last k R hfirstLast hsegmentEven hfirstOrder hterminal
      hfirstK hkLast hkEven
  have hpair := x.toBONG.adjacentSignedProduct_endpoint_cases
    k.castSucc (Nat.succ_lt_succ k.isLt) hclasses
  simpa only [prefixValueUnits, GoodBONG.valueUnit, k, Fin.castSucc_mk]
    using hpair

/-- Every leading entry of a Lemma 7.5 endpoint tower has the common high
order. -/
theorem lemma79_endpointTower_leadingOrders
    [Beli2006AlphaLaws.{u, v} K]
    (x : GoodBONG q L (n + 2)) (R : Int) (pairs : Nat)
    (hpairs : 0 < pairs) (hbound : 2 * pairs ≤ n + 2)
    (hfirst : x.order 0 = R)
    (hlast : x.order ⟨2 * pairs - 1, by omega⟩ =
      R - 2 * (ramificationIndex K : Int)) :
    ∀ t : Fin pairs,
      ordUnit K ((x.prefixValueUnits (2 * pairs) hbound)
        ⟨2 * t.val, by omega⟩) = R := by
  let first : Fin (n + 1) := ⟨0, by omega⟩
  let last : Fin (n + 1) := ⟨2 * pairs - 2, by omega⟩
  have hfirstLast : first ≤ last := Fin.zero_le last
  have hsegmentEven : Even (last.val - first.val) := by
    exact ⟨pairs - 1, by dsimp only [first, last]; omega⟩
  have hfirstOrder : x.order first.castSucc = R := by
    have hindex : first.castSucc = (0 : Fin (n + 2)) := by
      apply Fin.ext
      rfl
    rw [hindex]
    exact hfirst
  have hterminal : x.order last.succ =
      R - 2 * (ramificationIndex K : Int) := by
    have hindex : last.succ =
        (⟨2 * pairs - 1, by omega⟩ : Fin (n + 2)) := by
      apply Fin.ext
      simp only [last, Fin.val_succ]
      omega
    simpa only [hindex] using hlast
  have A := x.beli2019Lemma75_arithmetic first last R hfirstLast
    hsegmentEven hfirstOrder hterminal
  intro t
  let k : Fin (n + 1) := ⟨2 * t.val, by omega⟩
  have hkOrder := A.even_order k (Fin.zero_le k) (by
      change 2 * t.val ≤ 2 * pairs - 2
      omega) (by
        exact ⟨t.val, by dsimp only [k, first]; omega⟩)
  calc
    ordUnit K ((x.prefixValueUnits (2 * pairs) hbound)
        ⟨2 * t.val, by omega⟩) = x.order k.castSucc := by
      simpa only [prefixValueUnits, k, GoodBONG.valueUnit,
        Fin.castSucc_mk, GoodBONG.order] using
          (x.toBONG.order_eq_ordUnit k.castSucc).symm
    _ = R := hkOrder

/-- Two equal-length endpoint towers at the same scale give the direct
representation used at odd indices in case 1. -/
theorem lemma79_endpointTower_representationInUnaryExtension
    [Beli2006AlphaLaws.{u, v} K]
    [DyadicDiscriminantClassLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    (target : GoodBONG q M (n + 2))
    (comparison : GoodBONG q N (n + 2))
    (R : Int) (pairs : Nat) (hpairs : 0 < pairs)
    (hbound : 2 * pairs + 1 ≤ n + 2)
    (htargetFirst : target.order 0 = R)
    (htargetLast : target.order ⟨2 * pairs - 1, by omega⟩ =
      R - 2 * (ramificationIndex K : Int))
    (hcomparisonFirst : comparison.order 0 = R)
    (hcomparisonLast : comparison.order ⟨2 * pairs - 1, by omega⟩ =
      R - 2 * (ramificationIndex K : Int))
    (hextraOrder : target.order ⟨2 * pairs, by omega⟩ = R) :
    DiagonalRepresents
      (comparison.prefixValues (2 * pairs) (by omega))
      (target.prefixValues (2 * pairs + 1) hbound) := by
  let targetTower : Fin (2 * pairs) → Kˣ :=
    target.prefixValueUnits (2 * pairs) (by omega)
  let comparisonTower : Fin (2 * pairs) → Kˣ :=
    comparison.prefixValueUnits (2 * pairs) (by omega)
  let extraIndex : Fin (n + 2) := ⟨2 * pairs, by omega⟩
  let extra : Kˣ := target.valueUnit extraIndex
  have htargetClasses : AlternatingEndpointPairClasses targetTower := by
    simpa only [targetTower] using target.lemma79_endpointTower_pairClasses
      R pairs hpairs (by omega) htargetFirst htargetLast
  have hcomparisonClasses :
      AlternatingEndpointPairClasses comparisonTower := by
    simpa only [comparisonTower] using
      comparison.lemma79_endpointTower_pairClasses R pairs hpairs
        (by omega) hcomparisonFirst hcomparisonLast
  have hextra : ordUnit K extra = R := by
    calc
      ordUnit K extra = target.order extraIndex :=
        (target.toBONG.order_eq_ordUnit extraIndex).symm
      _ = R := by simpa only [extraIndex] using hextraOrder
  have htargetOrders : ∀ t : Fin pairs,
      ordUnit K (targetTower ⟨2 * t.val, by omega⟩) =
        ordUnit K extra := by
    intro t
    calc
      ordUnit K (targetTower ⟨2 * t.val, by omega⟩) = R := by
        simpa only [targetTower] using
          target.lemma79_endpointTower_leadingOrders R pairs hpairs
            (by omega) htargetFirst htargetLast t
      _ = ordUnit K extra := hextra.symm
  have hcomparisonOrders : ∀ t : Fin pairs,
      ordUnit K (comparisonTower ⟨2 * t.val, by omega⟩) =
        ordUnit K extra := by
    intro t
    calc
      ordUnit K (comparisonTower ⟨2 * t.val, by omega⟩) = R := by
        simpa only [comparisonTower] using
          comparison.lemma79_endpointTower_leadingOrders R pairs hpairs
            (by omega) hcomparisonFirst hcomparisonLast t
      _ = ordUnit K extra := hextra.symm
  have hrep := alternatingEndpointTower_representationInUnaryExtension
    targetTower comparisonTower extra htargetClasses hcomparisonClasses
      htargetOrders hcomparisonOrders
  have hcomparisonCoefficients :
      diagonalUnitCoefficients comparisonTower =
        comparison.prefixValues (2 * pairs) (by omega) := by
    simpa only [comparisonTower, diagonalUnitCoefficients_prefixValueUnits]
  have htargetCoefficients :
      diagonalUnitCoefficients (Fin.snoc targetTower extra) =
        target.prefixValues (2 * pairs + 1) hbound := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [targetTower, extra, extraIndex, diagonalUnitCoefficients,
        prefixValues, prefixValueUnits, GoodBONG.valueUnit, GoodBONG.value]
    · simp [targetTower, diagonalUnitCoefficients, prefixValues,
        prefixValueUnits, GoodBONG.valueUnit, GoodBONG.value]
  rwa [hcomparisonCoefficients, htargetCoefficients] at hrep

/-- A Lemma 7.5 tower with one additional pair represents a shorter tower
followed by a line at the common high scale.  The shorter tower may be empty. -/
theorem lemma79_endpointTower_onePairExtension
    [Beli2006AlphaLaws.{u, v} K]
    [DyadicDiscriminantClassLaws K]
    [DyadicAlternatingEndpointTowerRepresentationLaws K]
    (large : GoodBONG q M (n + 2))
    (small : GoodBONG q N (n + 2))
    (R : Int) (pairs : Nat)
    (hlargeBound : 2 * (pairs + 1) ≤ n + 2)
    (hlargeFirst : large.order 0 = R)
    (hlargeLast : large.order ⟨2 * (pairs + 1) - 1, by omega⟩ =
      R - 2 * (ramificationIndex K : Int))
    (hsmallClasses : AlternatingEndpointPairClasses
      (small.prefixValueUnits (2 * pairs) (by omega)))
    (hsmallOrders : ∀ t : Fin pairs,
      ordUnit K ((small.prefixValueUnits (2 * pairs) (by omega))
        ⟨2 * t.val, by omega⟩) = R)
    (hextraOrder : small.order ⟨2 * pairs, by omega⟩ = R) :
    DiagonalRepresents
      (small.prefixValues (2 * pairs + 1) (by omega))
      (large.prefixValues (2 * (pairs + 1)) hlargeBound) := by
  let largeTower : Fin (2 * (pairs + 1)) → Kˣ :=
    large.prefixValueUnits (2 * (pairs + 1)) hlargeBound
  let smallTower : Fin (2 * pairs) → Kˣ :=
    small.prefixValueUnits (2 * pairs) (by omega)
  let extraIndex : Fin (n + 2) := ⟨2 * pairs, by omega⟩
  let extra : Kˣ := small.valueUnit extraIndex
  have hlargeClasses : AlternatingEndpointPairClasses largeTower := by
    simpa only [largeTower] using large.lemma79_endpointTower_pairClasses
      R (pairs + 1) (Nat.succ_pos pairs) hlargeBound hlargeFirst hlargeLast
  have hextra : ordUnit K extra = R := by
    calc
      ordUnit K extra = small.order extraIndex :=
        (small.toBONG.order_eq_ordUnit extraIndex).symm
      _ = R := by simpa only [extraIndex] using hextraOrder
  have hlargeOrders : ∀ t : Fin (pairs + 1),
      ordUnit K (largeTower ⟨2 * t.val, by omega⟩) =
        ordUnit K extra := by
    intro t
    calc
      ordUnit K (largeTower ⟨2 * t.val, by omega⟩) = R := by
        simpa only [largeTower] using
          large.lemma79_endpointTower_leadingOrders R (pairs + 1)
            (Nat.succ_pos pairs) hlargeBound hlargeFirst hlargeLast t
      _ = ordUnit K extra := hextra.symm
  have hsmallOrders' : ∀ t : Fin pairs,
      ordUnit K (smallTower ⟨2 * t.val, by omega⟩) =
        ordUnit K extra := by
    intro t
    calc
      ordUnit K (smallTower ⟨2 * t.val, by omega⟩) = R := by
        simpa only [smallTower] using hsmallOrders t
      _ = ordUnit K extra := hextra.symm
  have hrep := alternatingEndpointTower_onePairExtensionRepresentation
    largeTower smallTower extra hlargeClasses
      (by simpa only [smallTower] using hsmallClasses)
      hlargeOrders hsmallOrders'
  have hsmallCoefficients :
      diagonalUnitCoefficients (Fin.snoc smallTower extra) =
        small.prefixValues (2 * pairs + 1) (by omega) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [smallTower, extra, extraIndex, diagonalUnitCoefficients,
        prefixValues, prefixValueUnits, GoodBONG.valueUnit, GoodBONG.value]
    · simp [smallTower, diagonalUnitCoefficients, prefixValues,
        prefixValueUnits, GoodBONG.valueUnit, GoodBONG.value]
  have hlargeCoefficients : diagonalUnitCoefficients largeTower =
      large.prefixValues (2 * (pairs + 1)) hlargeBound := by
    simpa only [largeTower, diagonalUnitCoefficients_prefixValueUnits]
  rwa [hsmallCoefficients, hlargeCoefficients] at hrep

end BONG.GoodBONG

end Bong
