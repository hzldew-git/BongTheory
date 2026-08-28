/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009JordanAdaptedSymmetry

/-!
# Transport of Beli's alpha invariants across aligned Jordan splittings

This file assembles the internal, even-boundary, and odd-boundary parts of
Beli (2009), Lemma 2.16.  It proves that equality of the complete Jordan
fundamental type and of the BONG order sequence forces equality of every
alpha invariant, without a residual local-law interface.
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

namespace BONG.StrictJordanAdaptedAlignment

variable {m : Nat} {a : GoodBONG q L (m + 1)}
  {b : GoodBONG r M (m + 1)}

end BONG.StrictJordanAdaptedAlignment

namespace Lattice.JordanDecomposition.SameFundamentalType

/-- Simultaneously reindex two same-length decompositions along the same
equality of their component count. -/
noncomputable def castComponentCount
    {c d : Nat}
    {J : Lattice.JordanDecomposition q L c}
    {H : Lattice.JordanDecomposition r M c}
    (F : Lattice.JordanDecomposition.SameFundamentalType J H)
    (h : c = d) :
    Lattice.JordanDecomposition.SameFundamentalType
      (J.castComponentCount h) (H.castComponentCount h) := by
  subst d
  exact F

end Lattice.JordanDecomposition.SameFundamentalType

namespace Lattice.OrderedFractionalIdeal

/-- The integral order attached to a nonzero fractional power ideal is
uniquely determined by its carrier. -/
theorem order_eq_of_carrier_eq
    (I J : Lattice.OrderedFractionalIdeal K)
    (h : I.carrier = J.carrier) : I.order = J.order := by
  apply Lattice.powerIdeal_order_eq_of_eq (K := K)
  rw [← I.carrier_eq_powerIdeal, ← J.carrier_eq_powerIdeal]
  exact h

end Lattice.OrderedFractionalIdeal

namespace BONG.StrictJordanAdaptedAlignment

variable {m : Nat} {a : GoodBONG q L (m + 1)}
  {b : GoodBONG r M (m + 1)}

theorem componentStart_eq_targetComponentStart
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) :
    S.componentStart k = S.targetComponentStart k := by
  unfold componentStart targetComponentStart
  apply Finset.sum_congr rfl
  intro i hi
  exact S.componentRank_eq i

theorem componentStop_eq_targetComponentStop
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) :
    S.componentStop k = S.targetComponentStop k := by
  unfold componentStop targetComponentStop
  rw [S.componentStart_eq_targetComponentStart k]
  exact congrArg (fun x ↦ S.targetComponentStart k + x)
    (S.componentRank_eq k)

/-- Cast a same-fundamental-type witness along the common component-count
identification used by the boundary API. -/
noncomputable def sameFundamentalTypeSucc
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (F : Lattice.JordanDecomposition.SameFundamentalType
      S.sourceJordan S.targetJordan)
    {t : Nat} (h : S.componentCount = t + 1) :
    Lattice.JordanDecomposition.SameFundamentalType
      (S.sourceJordanSucc h) (S.targetJordanSucc h) :=
  F.castComponentCount h

/-- Target counterpart of the concrete source boundary-coordinate formula. -/
theorem targetBoundaryIndex_succ_val_eq_componentStart
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1) (i : Fin t) :
    ((S.targetProfileSucc h).boundaryIndex i).val + 1 =
      S.targetComponentStart (Fin.cast h.symm
        (Lattice.JordanDecomposition.boundaryRightIndex i)) := by
  exact S.symm.sourceBoundaryIndex_succ_val_eq_componentStart h i

/-- Source and target use the same global alpha index at each aligned
Jordan boundary. -/
theorem sourceBoundaryIndex_eq_targetBoundaryIndex
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    {t : Nat} (h : S.componentCount = t + 1) (i : Fin t) :
    (S.sourceProfileSucc h).boundaryIndex i =
      (S.targetProfileSucc h).boundaryIndex i := by
  apply Fin.ext
  have hs := S.sourceBoundaryIndex_succ_val_eq_componentStart h i
  have ht := S.targetBoundaryIndex_succ_val_eq_componentStart h i
  rw [← S.componentStart_eq_targetComponentStart] at ht
  omega

theorem target_component_internal
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount)
    (i : Nat)
    (hstart : S.targetComponentStart k ≤ i)
    (hnext : i + 1 < S.targetComponentStop k) :
    let D := S.symm.sourceInternalAlphaData k i hstart hnext
    ((b.order D.leftIndex : ℚ) + b.alphaValue D.alphaIndex =
        (D.weight.order : ℚ)) ∧
      (-(b.order D.rightIndex : ℚ) + b.alphaValue D.alphaIndex =
        (D.dualWeight.order : ℚ)) := by
  exact S.symm.source_component_internal k i hstart hnext

/-- The source and target profiles assign every global coordinate to the
same component and to the same numerical local coordinate. -/
theorem source_target_profile_coordinates_eq
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (i : Fin (m + 1)) :
    (S.sourceProfile.indexEquiv i).1 =
        (S.targetProfile.indexEquiv i).1 ∧
      (S.sourceProfile.indexEquiv i).2.val =
        (S.targetProfile.indexEquiv i).2.val := by
  apply S.sourceProfile.indexEquiv_coordinates_eq_of_componentRank_eq
    S.targetProfile
  funext k
  exact S.componentRank_eq k

/-- On an adjacent pair lying strictly inside one aligned Jordan component,
equality of the BONG orders and equality of the fundamental type force
equality of the corresponding Beli alpha invariant. -/
theorem alphaValue_eq_of_component_internal
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (F : Lattice.JordanDecomposition.SameFundamentalType
      S.sourceJordan S.targetJordan)
    (horders : a.SameOrders b)
    (i : Fin m)
    (hlocal : (S.sourceProfile.indexEquiv i.castSucc).2.val + 1 <
      S.sourceJordan.componentRank
        (S.sourceProfile.indexEquiv i.castSucc).1) :
    a.alphaValue i = b.alphaValue i := by
  let k : Fin S.componentCount :=
    (S.sourceProfile.indexEquiv i.castSucc).1
  have hindex := S.sourceProfile.index_val_eq_componentStart_add_local
    i.castSucc
  change i.val =
      (∑ k ∈ Finset.Iio (S.sourceProfile.indexEquiv i.castSucc).1,
        S.sourceJordan.componentRank k) +
        (S.sourceProfile.indexEquiv i.castSucc).2.val at hindex
  have hstart0 : S.componentStart
      (S.sourceProfile.indexEquiv i.castSucc).1 ≤ i.val := by
    change (∑ k ∈ Finset.Iio
      (S.sourceProfile.indexEquiv i.castSucc).1,
        S.sourceJordan.componentRank k) ≤ i.val
    rw [hindex]
    omega
  have hnext0 : i.val + 1 < S.componentStop
      (S.sourceProfile.indexEquiv i.castSucc).1 := by
    change i.val + 1 <
      (∑ k ∈ Finset.Iio
        (S.sourceProfile.indexEquiv i.castSucc).1,
          S.sourceJordan.componentRank k) +
        S.sourceJordan.componentRank
          (S.sourceProfile.indexEquiv i.castSucc).1
    calc
      i.val + 1 =
          (∑ k ∈ Finset.Iio
            (S.sourceProfile.indexEquiv i.castSucc).1,
              S.sourceJordan.componentRank k) +
            ((S.sourceProfile.indexEquiv i.castSucc).2.val + 1) := by
        rw [hindex]
        omega
      _ < _ := Nat.add_lt_add_left hlocal _
  have hstart : S.componentStart k ≤ i.val := by
    simpa only [k] using hstart0
  have hnext : i.val + 1 < S.componentStop k := by
    simpa only [k] using hnext0
  have htargetStart : S.targetComponentStart k ≤ i.val := by
    rw [← S.componentStart_eq_targetComponentStart k]
    exact hstart
  have htargetNext : i.val + 1 < S.targetComponentStop k := by
    rw [← S.componentStop_eq_targetComponentStop k]
    exact hnext
  let Ds := S.sourceInternalAlphaData k i.val hstart hnext
  let Dt := S.symm.sourceInternalAlphaData k i.val htargetStart htargetNext
  have hs := (S.source_component_internal k i.val hstart hnext).1
  have ht := (S.target_component_internal k i.val
    htargetStart htargetNext).1
  have hsAlpha : Ds.alphaIndex = i := by
    apply Fin.ext
    rfl
  have htAlpha : Dt.alphaIndex = i := by
    apply Fin.ext
    rfl
  have hsLeft : Ds.leftIndex = i.castSucc := by
    apply Fin.ext
    rfl
  have htLeft : Dt.leftIndex = i.castSucc := by
    apply Fin.ext
    rfl
  have hweight := F.fundamentalWeightOrder_eq k
  rw [F.indexEquiv_apply_eq_self k] at hweight
  rw [hsLeft, hsAlpha] at hs
  rw [htLeft, htAlpha] at ht
  have hs' : (a.order i.castSucc : ℚ) + a.alphaValue i =
      (S.sourceJordan.fundamentalWeightOrder k : ℚ) := by
    change (a.order i.castSucc : ℚ) + a.alphaValue i =
      (S.sourceJordan.fundamentalWeightOrder k : ℚ) at hs
    exact hs
  have ht' : (b.order i.castSucc : ℚ) + b.alphaValue i =
      (S.targetJordan.fundamentalWeightOrder k : ℚ) := by
    change (b.order i.castSucc : ℚ) + b.alphaValue i =
      (S.targetJordan.fundamentalWeightOrder k : ℚ) at ht
    exact ht
  have hweightQ :
      (S.targetJordan.fundamentalWeightOrder k : ℚ) =
        (S.sourceJordan.fundamentalWeightOrder k : ℚ) := by
    exact_mod_cast hweight
  have horderQ : (b.order i.castSucc : ℚ) =
      (a.order i.castSucc : ℚ) := by
    exact_mod_cast (horders i.castSucc).symm
  linarith

/-- At an aligned Jordan boundary, equality of the complete fundamental
type and of the BONG order sequence forces equality of the boundary alpha.
This combines the even and odd branches of Beli's Lemma 2.16. -/
theorem alphaValue_eq_at_boundary
    {n : Nat}
    {a : GoodBONG q L (n + 2)} {b : GoodBONG r M (n + 2)}
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (F : Lattice.JordanDecomposition.SameFundamentalType
      S.sourceJordan S.targetJordan)
    (horders : a.SameOrders b)
    {t : Nat} (h : S.componentCount = t + 1) (z : Fin t) :
    a.alphaValue ((S.sourceProfileSucc h).boundaryIndex z) =
      b.alphaValue ((S.targetProfileSucc h).boundaryIndex z) := by
  let Js := S.sourceJordanSucc h
  let Jt := S.targetJordanSucc h
  let Ps := S.sourceProfileSucc h
  let Pt := S.targetProfileSucc h
  let Fs := S.sameFundamentalTypeSucc F h
  have hidx : Ps.boundaryIndex z = Pt.boundaryIndex z := by
    exact S.sourceBoundaryIndex_eq_targetBoundaryIndex h z
  have hsum : Jt.boundaryNormOrderSum z =
      Js.boundaryNormOrderSum z := by
    exact Fs.boundaryNormOrderSum_eq z
  by_cases heven : Even (Js.boundaryNormOrderSum z)
  · have hevenT : Even (Jt.boundaryNormOrderSum z) := by
      rw [hsum]
      exact heven
    let Is := Js.evenOrderedFundamentalIdeal z
      (Ps.boundaryLeftValue z) (Ps.boundaryRightValue z)
      (S.sourceBoundaryLeftValue_isNormGeneratorValue h z)
      (S.sourceBoundaryRightValue_isNormGeneratorValue h z) heven
    let It := Jt.evenOrderedFundamentalIdeal z
      (Pt.boundaryLeftValue z) (Pt.boundaryRightValue z)
      (S.targetBoundaryLeftValue_isNormGeneratorValue h z)
      (S.targetBoundaryRightValue_isNormGeneratorValue h z) hevenT
    have hs := S.sourceEvenBoundaryFundamentalOrder_eq_alpha h z heven
    have ht := S.targetEvenBoundaryFundamentalOrder_eq_alpha h z hevenT
    have hcarrier : It.carrier = Is.carrier := by
      change Jt.fundamentalIdeal z = Js.fundamentalIdeal z
      exact Fs.fundamentalIdeal_eq z
    have hidealOrder : It.order = Is.order :=
      Lattice.OrderedFractionalIdeal.order_eq_of_carrier_eq It Is hcarrier
    have hs' : (Is.order : ℚ) = a.alphaValue (Ps.boundaryIndex z) := by
      simpa only [Is, Js, Ps] using hs
    have ht' : (It.order : ℚ) = b.alphaValue (Pt.boundaryIndex z) := by
      simpa only [It, Jt, Pt] using ht
    have hidealOrderQ : (It.order : ℚ) = (Is.order : ℚ) := by
      exact_mod_cast hidealOrder
    linarith
  · have hodd : Odd (Js.boundaryNormOrderSum z) :=
      Int.not_even_iff_odd.mp heven
    have hoddT : Odd (Jt.boundaryNormOrderSum z) := by
      rw [hsum]
      exact hodd
    let Ds := S.sourceOddBoundaryAlphaData h z hodd
    let Dt := S.targetOddBoundaryAlphaData h z hoddT
    have hs := S.sourceOddBoundaryAlphaData_lemma216 h z hodd
    have ht := S.targetOddBoundaryAlphaData_lemma216 h z hoddT
    have hDsIndex : Ds.index = Ps.boundaryIndex z := rfl
    have hDtIndex : Dt.index = Pt.boundaryIndex z := rfl
    have hgap : b.orderGap Dt.index = a.orderGap Ds.index := by
      rw [hDtIndex, ← hidx, ← hDsIndex]
      unfold GoodBONG.orderGap
      rw [← horders Ds.index.succ, ← horders Ds.index.castSucc]
    by_cases hordinary :
        Even (a.orderGap Ds.index) ∨
          a.orderGap Ds.index ≤ 2 * (ramificationIndex K : Int)
    · have hordinaryT :
          Even (b.orderGap Dt.index) ∨
            b.orderGap Dt.index ≤ 2 * (ramificationIndex K : Int) := by
        rw [hgap]
        exact hordinary
      have hsAlpha := hs.1 hordinary
      have htAlpha := ht.1 hordinaryT
      change a.alphaValue Ds.index =
        (Ds.fundamental.order : ℚ) at hsAlpha
      change b.alphaValue Dt.index =
        (Dt.fundamental.order : ℚ) at htAlpha
      have hcarrier : Dt.fundamental.carrier = Ds.fundamental.carrier := by
        change Jt.fundamentalIdeal z = Js.fundamentalIdeal z
        exact Fs.fundamentalIdeal_eq z
      have hfundOrder : Dt.fundamental.order = Ds.fundamental.order :=
        Lattice.OrderedFractionalIdeal.order_eq_of_carrier_eq
          Dt.fundamental Ds.fundamental hcarrier
      have hfundOrderQ : (Dt.fundamental.order : ℚ) =
          (Ds.fundamental.order : ℚ) := by
        exact_mod_cast hfundOrder
      rw [hDsIndex] at hsAlpha
      rw [hDtIndex] at htAlpha
      linarith
    · have hnotOrdinaryT :
          ¬(Even (b.orderGap Dt.index) ∨
            b.orderGap Dt.index ≤ 2 * (ramificationIndex K : Int)) := by
        rw [hgap]
        exact hordinary
      have hsAlpha := (hs.2 hordinary).1
      have htAlpha := (ht.2 hnotOrdinaryT).1
      change a.alphaValue Ds.index =
        a.halfGapValue Ds.index at hsAlpha
      change b.alphaValue Dt.index =
        b.halfGapValue Dt.index at htAlpha
      have hhalf : b.halfGapValue Dt.index =
          a.halfGapValue Ds.index := by
        unfold GoodBONG.halfGapValue
        rw [hgap]
      rw [hDsIndex] at hsAlpha
      rw [hDtIndex] at htAlpha
      rw [hDtIndex, hDsIndex] at hhalf
      change a.alphaValue (Ps.boundaryIndex z) =
        b.alphaValue (Pt.boundaryIndex z)
      exact hsAlpha.trans (hhalf.symm.trans htAlpha.symm)

/-- Beli (2009), Lemma 2.16 in transport form: equal orders together with
equal complete Jordan fundamental type determine the entire alpha sequence. -/
theorem sameAlphas_of_sameOrders_of_fundamentalType
    {n : Nat}
    {a : GoodBONG q L (n + 2)} {b : GoodBONG r M (n + 2)}
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (F : Lattice.JordanDecomposition.SameFundamentalType
      S.sourceJordan S.targetJordan)
    (horders : a.SameOrders b) :
    a.SameAlphas b := by
  intro i
  by_cases hlocal :
      (S.sourceProfile.indexEquiv i.castSucc).2.val + 1 <
        S.sourceJordan.componentRank
          (S.sourceProfile.indexEquiv i.castSucc).1
  · exact S.alphaValue_eq_of_component_internal F horders i hlocal
  · let k : Fin S.componentCount :=
      (S.sourceProfile.indexEquiv i.castSucc).1
    have hindex := S.sourceProfile.index_val_eq_componentStart_add_local
      i.castSucc
    change i.val =
        (∑ x ∈ Finset.Iio (S.sourceProfile.indexEquiv i.castSucc).1,
          S.sourceJordan.componentRank x) +
          (S.sourceProfile.indexEquiv i.castSucc).2.val at hindex
    have hlast :
        (S.sourceProfile.indexEquiv i.castSucc).2.val + 1 =
          S.sourceJordan.componentRank
            (S.sourceProfile.indexEquiv i.castSucc).1 := by
      have hlt := (S.sourceProfile.indexEquiv i.castSucc).2.isLt
      apply le_antisymm
      · exact Nat.succ_le_iff.mpr hlt
      · exact Nat.le_of_not_gt hlocal
    have hstopEq : S.componentStop k = i.val + 1 := by
      change
        (∑ x ∈ Finset.Iio (S.sourceProfile.indexEquiv i.castSucc).1,
          S.sourceJordan.componentRank x) +
            S.sourceJordan.componentRank
              (S.sourceProfile.indexEquiv i.castSucc).1 = i.val + 1
      calc
        _ = (∑ x ∈ Finset.Iio
              (S.sourceProfile.indexEquiv i.castSucc).1,
              S.sourceJordan.componentRank x) +
              ((S.sourceProfile.indexEquiv i.castSucc).2.val + 1) := by
            rw [hlast]
        _ = i.val + 1 := by rw [hindex]; omega
    have hstopLt : S.componentStop k < n + 2 := by
      rw [hstopEq]
      omega
    have hsucc : k.val + 1 < S.componentCount :=
      S.source_component_has_successor_of_stop_lt k hstopLt
    let t := S.componentCount - 1
    have hc : S.componentCount = t + 1 := by
      dsimp only [t]
      omega
    let z : Fin t := ⟨k.val, by
      dsimp only [t]
      omega⟩
    let l : Fin S.componentCount := ⟨k.val + 1, hsucc⟩
    have hright :
        Fin.cast hc.symm
            (Lattice.JordanDecomposition.boundaryRightIndex z) = l := by
      apply Fin.ext
      rfl
    have hstopStart : S.componentStop k = S.componentStart l :=
      S.componentStop_eq_componentStart_of_val_succ k l rfl
    have hboundaryStart :=
      S.sourceBoundaryIndex_succ_val_eq_componentStart hc z
    rw [hright] at hboundaryStart
    have hboundaryIndex :
        (S.sourceProfileSucc hc).boundaryIndex z = i := by
      apply Fin.ext
      omega
    have halpha := S.alphaValue_eq_at_boundary F horders hc z
    have htarget := S.sourceBoundaryIndex_eq_targetBoundaryIndex hc z
    rw [← htarget, hboundaryIndex] at halpha
    exact halpha

end BONG.StrictJordanAdaptedAlignment

namespace BONG.GoodBONG

/-- Beli (2003), Lemma 4.7 transported along an integral isometry: the
orders of arbitrary good BONGs on isometric lattices agree coordinatewise. -/
theorem sameOrders_of_latticeIsometry
    {n : Nat}
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (f : Lattice.Isometry q r L M) :
    a.SameOrders b := by
  let c : GoodBONG q L (n + 1) := b.mapLatticeIsometry f.symm
  have hac := a.toBONG.beliLemma47_orders_eq
    c.toBONG a.good c.good
  intro i
  calc
    a.order i = c.order i := hac i
    _ = b.order i := by simp only [c, order_mapLatticeIsometry]

/-- The first two conditions of Beli's classification theorem are necessary
for integral isometry, with the alpha assertion now derived from the complete
proof of Lemma 2.16 rather than supplied as a law instance. -/
theorem sameAlphas_of_latticeIsometry
    {n : Nat}
    (a : GoodBONG q L (n + 1)) (b : GoodBONG r M (n + 1))
    (f : Lattice.Isometry q r L M) :
    a.SameAlphas b := by
  have horders : a.SameOrders b := a.sameOrders_of_latticeIsometry b f
  cases n with
  | zero =>
      intro i
      exact Fin.elim0 i
  | succ n =>
      obtain ⟨S⟩ := a.nonempty_strictJordanAdaptedAlignment b horders
      let F := Lattice.JordanDecomposition.sameFundamentalTypeOfIsometry
        S.sourceJordan S.targetJordan f
      exact S.sameAlphas_of_sameOrders_of_fundamentalType F horders

end BONG.GoodBONG

end Bong
