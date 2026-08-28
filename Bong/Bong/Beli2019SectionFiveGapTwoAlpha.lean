/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFiveGapTwo

/-!
# The alpha bound in the gap-two reverse branch of Beli (2019), Section 5

The effective-norm gap-two calculation gives equality of the relevant
fundamental weight ideals.  This file transports that equality to the
preceding internal BONG coordinate and proves the source-alpha bound required
by condition 2.1(ii).
-/

namespace Bong

open Dyadic Module

universe u v

namespace Lattice.Beli2019Lemma51Data

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V}

/-- A positive local coordinate has an internal predecessor in the same
Jordan component. -/
theorem previous_profile_coordinate_internal_of_current_local_pos
    {L : Lattice K V} {n t : Nat}
    (c : BONG.GoodBONG q L (n + 2))
    {J : Lattice.JordanDecomposition q L t}
    (P : BONG.JordanOrderProfileWitness c.toBONG J)
    (i : Fin (n + 1))
    (hlocalPos : 0 < (P.indexEquiv i.castSucc).2.val) :
    ∃ hpos : 0 < i.val,
      (P.indexEquiv
        (⟨i.val - 1, by omega⟩ : Fin (n + 1)).castSucc).1 =
          (P.indexEquiv i.castSucc).1 ∧
      (P.indexEquiv
          (⟨i.val - 1, by omega⟩ : Fin (n + 1)).castSucc).2.val + 1 <
        J.componentRank
          (P.indexEquiv
            (⟨i.val - 1, by omega⟩ : Fin (n + 1)).castSucc).1 := by
  have hipos : 0 < i.val := by
    have hindex := P.index_val_eq_componentStart_add_local i.castSucc
    change i.val =
      (∑ k ∈ Finset.Iio (P.indexEquiv i.castSucc).1,
        J.componentRank k) + (P.indexEquiv i.castSucc).2.val at hindex
    omega
  let j : Fin (n + 1) := ⟨i.val - 1, by omega⟩
  let k : Fin t := (P.indexEquiv i.castSucc).1
  let ell : Fin (J.componentRank k) := (P.indexEquiv i.castSucc).2
  let previousLocal : Fin (J.componentRank k) :=
    ⟨ell.val - 1, by
      have := ell.isLt
      omega⟩
  have hinverse := P.inverse_index_val_local_pred k ell hlocalPos
  change (P.indexEquiv.symm ⟨k, previousLocal⟩).val + 1 =
    (P.indexEquiv.symm ⟨k, ell⟩).val at hinverse
  have hcurrent : P.indexEquiv.symm ⟨k, ell⟩ = i.castSucc := by
    exact P.indexEquiv.symm_apply_apply i.castSucc
  have hpreviousVal :
      (P.indexEquiv.symm ⟨k, previousLocal⟩).val + 1 = i.val := by
    calc
      (P.indexEquiv.symm ⟨k, previousLocal⟩).val + 1 =
          (P.indexEquiv.symm ⟨k, ell⟩).val := by
        simpa only [previousLocal] using hinverse
      _ = i.val := by simpa using congrArg Fin.val hcurrent
  have hj : j.castSucc = P.indexEquiv.symm ⟨k, previousLocal⟩ := by
    apply Fin.ext
    dsimp only [j, Fin.val_mk, Fin.castSucc_mk]
    omega
  have hcoordinates : P.indexEquiv j.castSucc =
      ⟨k, previousLocal⟩ := by
    rw [hj, P.indexEquiv.apply_symm_apply]
  refine ⟨hipos, ?_, ?_⟩
  · simpa only [j, k] using congrArg Sigma.fst hcoordinates
  · rw [show (⟨i.val - 1, by omega⟩ : Fin (n + 1)) = j by rfl,
      hcoordinates]
    change previousLocal.val + 1 < J.componentRank k
    have hellLt := ell.isLt
    have hellPos : 0 < ell.val := by
      simpa only [ell] using hlocalPos
    have hprevious : previousLocal.val + 1 < J.componentRank k := by
      dsimp only [previousLocal, Fin.val_mk]
      omega
    exact hprevious

/-- A reverse strict inequality can occur only at a positive odd local
coordinate of the aligned Jordan profiles. -/
theorem noCollision_current_local_pos_of_current_gt
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : Fin (n + 1))
    (hbefore :
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv
        i.castSucc).1 < D.largeSelectedPosition)
    (hcurrent : b.order i.castSucc < a.order i.castSucc) :
    0 < ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv
      i.castSucc).2.val := by
  let I : Fin (n + 2) := i.castSucc
  let Psource := D.largeNoCollisionProfileWitness hlarge a
  let Ptarget := D.smallNoCollisionProfileWitness hsmall b
  let p := (Psource.indexEquiv I).1
  let r := (Ptarget.indexEquiv I).1
  let localIndex := (Psource.indexEquiv I).2.val
  let scale := ordUnit K (D.largeAlmostJordan.scaleGenerator p)
  let sourceEffective := D.largeAlmostJordan.effectiveNormOrderAt p scale
  let targetEffective := D.smallAlmostJordan.effectiveNormOrderAt r
    (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
  have hcoordinates := D.noCollision_profile_coordinates_eq
    hsmall hlarge hselected a b I
  have hrp : p = r := hcoordinates.1
  have hlocal : localIndex = (Ptarget.indexEquiv I).2.val :=
    hcoordinates.2
  have hscaleRaw := D.weakAligned_scaleOrder_eq_before_selected
    hselected p hbefore
  have hscaleTarget :
      ordUnit K (D.smallAlmostJordan.scaleGenerator r) = scale := by
    rw [← hrp]
    exact hscaleRaw.symm
  have heffective : sourceEffective ≤ targetEffective := by
    change D.largeAlmostJordan.effectiveNormOrderAt p
        (ordUnit K (D.largeAlmostJordan.scaleGenerator p)) ≤
      D.smallAlmostJordan.effectiveNormOrderAt r
        (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
    rw [← hrp]
    exact D.weakAligned_effectiveNormOrderAt_le_before_selected
      hselected p hbefore
  have hsourceScale : scale ≤ sourceEffective :=
    D.largeAlmostJordan.targetScale_le_effectiveNormOrderAt p scale
  have htargetScale : scale ≤ targetEffective := by
    rw [← hscaleTarget]
    exact D.smallAlmostJordan.targetScale_le_effectiveNormOrderAt r
      (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
  have hsourceLocal := D.largeNoCollision_order_eq_localOrder hlarge a I
  have htargetLocal := D.smallNoCollision_order_eq_localOrder hsmall b I
  have htargetLocalNormalized :
      b.order I =
        JordanProfileOrder.localOrder scale targetEffective localIndex := by
    calc
      b.order I = JordanProfileOrder.localOrder
          (ordUnit K (D.smallAlmostJordan.scaleGenerator r)) targetEffective
            (Ptarget.indexEquiv I).2.val := by
        simpa only [Ptarget, r] using htargetLocal
      _ = JordanProfileOrder.localOrder scale targetEffective localIndex := by
        rw [hscaleTarget, ← hlocal]
  have hlocalCurrent :
      JordanProfileOrder.localOrder scale targetEffective localIndex <
        JordanProfileOrder.localOrder scale sourceEffective localIndex := by
    change a.order I =
      JordanProfileOrder.localOrder scale sourceEffective localIndex at hsourceLocal
    calc
      JordanProfileOrder.localOrder scale targetEffective localIndex =
          b.order I := htargetLocalNormalized.symm
      _ < a.order I := by simpa only [I] using hcurrent
      _ = JordanProfileOrder.localOrder scale sourceEffective localIndex :=
        hsourceLocal
  have hodd : ¬Even localIndex :=
    JordanProfileOrder.odd_of_effective_le_of_localOrder_gt
      hsourceScale htargetScale heffective hlocalCurrent
  have hpos : 0 < localIndex := by
    by_contra hnot
    have hz : localIndex = 0 := by omega
    apply hodd
    rw [hz]
    simp
  simpa only [localIndex, Psource, I] using hpos

/-- A current order drop of two is exactly the effective-norm gap-two branch,
so the corresponding fundamental weight ideals agree. -/
theorem noCollision_fundamentalWeightIdeal_eq_of_current_eq_target_add_two
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : Fin (n + 1))
    (hbefore :
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv
        i.castSucc).1 < D.largeSelectedPosition)
    (hcurrent : a.order i.castSucc = b.order i.castSucc + 2) :
    Lattice.weightIdeal q
        ((D.largeNoCollisionJordan hlarge).fundamentalLattice
          ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv
            i.castSucc).1) =
      Lattice.weightIdeal q
        ((D.smallNoCollisionJordan hsmall).fundamentalLattice
          ((D.smallNoCollisionProfileWitness hsmall b).indexEquiv
            i.castSucc).1) := by
  let I : Fin (n + 2) := i.castSucc
  let Psource := D.largeNoCollisionProfileWitness hlarge a
  let Ptarget := D.smallNoCollisionProfileWitness hsmall b
  let p := (Psource.indexEquiv I).1
  let r := (Ptarget.indexEquiv I).1
  let localIndex := (Psource.indexEquiv I).2.val
  let scale := ordUnit K (D.largeAlmostJordan.scaleGenerator p)
  let sourceEffective := D.largeAlmostJordan.effectiveNormOrderAt p scale
  let targetEffective := D.smallAlmostJordan.effectiveNormOrderAt r
    (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
  have hcoordinates := D.noCollision_profile_coordinates_eq
    hsmall hlarge hselected a b I
  have hrp : p = r := hcoordinates.1
  have hlocal : localIndex = (Ptarget.indexEquiv I).2.val :=
    hcoordinates.2
  have hscaleRaw := D.weakAligned_scaleOrder_eq_before_selected
    hselected p hbefore
  have hscaleTarget :
      ordUnit K (D.smallAlmostJordan.scaleGenerator r) = scale := by
    rw [← hrp]
    exact hscaleRaw.symm
  have heffective : sourceEffective ≤ targetEffective := by
    change D.largeAlmostJordan.effectiveNormOrderAt p
        (ordUnit K (D.largeAlmostJordan.scaleGenerator p)) ≤
      D.smallAlmostJordan.effectiveNormOrderAt r
        (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
    rw [← hrp]
    exact D.weakAligned_effectiveNormOrderAt_le_before_selected
      hselected p hbefore
  have hsourceScale : scale ≤ sourceEffective :=
    D.largeAlmostJordan.targetScale_le_effectiveNormOrderAt p scale
  have htargetScale : scale ≤ targetEffective := by
    rw [← hscaleTarget]
    exact D.smallAlmostJordan.targetScale_le_effectiveNormOrderAt r
      (ordUnit K (D.smallAlmostJordan.scaleGenerator r))
  have hsourceLocal := D.largeNoCollision_order_eq_localOrder hlarge a I
  have htargetLocal := D.smallNoCollision_order_eq_localOrder hsmall b I
  have htargetLocalNormalized :
      b.order I =
        JordanProfileOrder.localOrder scale targetEffective localIndex := by
    calc
      b.order I = JordanProfileOrder.localOrder
          (ordUnit K (D.smallAlmostJordan.scaleGenerator r)) targetEffective
            (Ptarget.indexEquiv I).2.val := by
        simpa only [Ptarget, r] using htargetLocal
      _ = JordanProfileOrder.localOrder scale targetEffective localIndex := by
        rw [hscaleTarget, ← hlocal]
  have hlocalCurrent :
      JordanProfileOrder.localOrder scale targetEffective localIndex <
        JordanProfileOrder.localOrder scale sourceEffective localIndex := by
    change a.order I =
      JordanProfileOrder.localOrder scale sourceEffective localIndex at hsourceLocal
    calc
      JordanProfileOrder.localOrder scale targetEffective localIndex =
          b.order I := htargetLocalNormalized.symm
      _ < a.order I := by
        change b.order i.castSucc < a.order i.castSucc
        omega
      _ = JordanProfileOrder.localOrder scale sourceEffective localIndex :=
        hsourceLocal
  have hodd : ¬Even localIndex :=
    JordanProfileOrder.odd_of_effective_le_of_localOrder_gt
      hsourceScale htargetScale heffective hlocalCurrent
  have heffectiveGap : targetEffective = sourceEffective + 2 := by
    change a.order I =
      JordanProfileOrder.localOrder scale sourceEffective localIndex at hsourceLocal
    rw [JordanProfileOrder.localOrder_odd_of_scale_le hsourceScale hodd]
      at hsourceLocal
    rw [JordanProfileOrder.localOrder_odd_of_scale_le htargetScale hodd]
      at htargetLocalNormalized
    change a.order I = b.order I + 2 at hcurrent
    omega
  have heffectiveGap' :
      D.smallAlmostJordan.effectiveNormOrderAt p
          (ordUnit K (D.largeAlmostJordan.scaleGenerator p)) =
        D.largeAlmostJordan.effectiveNormOrderAt p
          (ordUnit K (D.largeAlmostJordan.scaleGenerator p)) + 2 := by
    change D.smallAlmostJordan.effectiveNormOrderAt p scale =
      sourceEffective + 2
    calc
      D.smallAlmostJordan.effectiveNormOrderAt p scale =
          targetEffective := by
        dsimp only [targetEffective]
        rw [hrp, hscaleTarget]
      _ = sourceEffective + 2 := heffectiveGap
  have hweight := D.noCollision_fundamentalWeightIdeal_eq_of_effective_gapTwo
    hsmall hlarge p hbefore hscaleRaw heffectiveGap'
  change Lattice.weightIdeal q
      ((D.largeNoCollisionJordan hlarge).fundamentalLattice p) =
    Lattice.weightIdeal q
      ((D.smallNoCollisionJordan hsmall).fundamentalLattice r)
  rw [← hrp]
  exact hweight

/-- In the gap-two reverse branch, the common fundamental weight gives the
equality of the two preceding alpha endpoints. -/
theorem noCollision_previous_order_add_alpha_eq_of_current_eq_target_add_two
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : Fin (n + 1))
    (hbefore :
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv
        i.castSucc).1 < D.largeSelectedPosition)
    (hcurrent : a.order i.castSucc = b.order i.castSucc + 2) :
    ∃ hpos : 0 < i.val,
      (a.order (⟨i.val - 1, by omega⟩ : Fin (n + 1)).castSucc : ℚ) +
          a.alphaValue (⟨i.val - 1, by omega⟩ : Fin (n + 1)) =
        (b.order (⟨i.val - 1, by omega⟩ : Fin (n + 1)).castSucc : ℚ) +
          b.alphaValue (⟨i.val - 1, by omega⟩ : Fin (n + 1)) := by
  let Psource := D.largeNoCollisionProfileWitness hlarge a
  let Ptarget := D.smallNoCollisionProfileWitness hsmall b
  let I : Fin (n + 2) := i.castSucc
  let p := (Psource.indexEquiv I).1
  let r := (Ptarget.indexEquiv I).1
  have hgt : b.order i.castSucc < a.order i.castSucc := by omega
  have hsourceLocalPos := D.noCollision_current_local_pos_of_current_gt
    hsmall hlarge hselected a b i hbefore hgt
  have hcoordinates := D.noCollision_profile_coordinates_eq
    hsmall hlarge hselected a b I
  have htargetLocalPos : 0 < (Ptarget.indexEquiv I).2.val := by
    rw [← hcoordinates.2]
    simpa only [Psource, I] using hsourceLocalPos
  rcases previous_profile_coordinate_internal_of_current_local_pos
      a Psource i hsourceLocalPos with
    ⟨hipos, hsourceComponent, hsourceInternal⟩
  rcases previous_profile_coordinate_internal_of_current_local_pos
      b Ptarget i htargetLocalPos with
    ⟨_, htargetComponent, htargetInternal⟩
  let previous : Fin (n + 1) := ⟨i.val - 1, by omega⟩
  have hweightIdeal :=
    D.noCollision_fundamentalWeightIdeal_eq_of_current_eq_target_add_two
      hsmall hlarge hselected a b i hbefore hcurrent
  have hweightOrder :
      (D.largeNoCollisionJordan hlarge).fundamentalWeightOrder p =
        (D.smallNoCollisionJordan hsmall).fundamentalWeightOrder r := by
    unfold Lattice.JordanDecomposition.fundamentalWeightOrder
    apply Lattice.powerIdeal_injective (K := K)
    rw [← Lattice.weightIdeal_eq_powerIdeal,
      ← Lattice.weightIdeal_eq_powerIdeal]
    simpa only [p, r, Psource, Ptarget, I] using hweightIdeal
  have hsourceFormula :=
    Psource.internal_weightOrder_eq_order_add_alpha previous hsourceInternal
  have htargetFormula :=
    Ptarget.internal_weightOrder_eq_order_add_alpha previous htargetInternal
  have hsourceComponent' :
      (Psource.indexEquiv previous.castSucc).1 = p := by
    simpa only [previous, p, I] using hsourceComponent
  have htargetComponent' :
      (Ptarget.indexEquiv previous.castSucc).1 = r := by
    simpa only [previous, r, I] using htargetComponent
  rw [hsourceComponent'] at hsourceFormula
  rw [htargetComponent'] at htargetFormula
  have hweightQ :
      ((D.largeNoCollisionJordan hlarge).fundamentalWeightOrder p : ℚ) =
        ((D.smallNoCollisionJordan hsmall).fundamentalWeightOrder r : ℚ) := by
    exact_mod_cast hweightOrder
  refine ⟨hipos, ?_⟩
  change (a.order previous.castSucc : ℚ) + a.alphaValue previous =
    (b.order previous.castSucc : ℚ) + b.alphaValue previous
  linarith

/-- In the two-step reverse-order branch `R_i = S_i + 2`, equality of the
preceding fundamental weights, the source two-step equality, and alpha
endpoint monotonicity give `A_i ≤ alpha_i`. -/
theorem noCollision_representationAlphaValue_le_sourceAlpha_of_current_eq_target_add_two
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hbefore :
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv
        (BONG.GoodBONG.representationAlphaIndex i).castSucc).1 <
          D.largeSelectedPosition)
    (hcurrent : a.order
        (BONG.GoodBONG.representationAlphaIndex i).castSucc =
      b.order (BONG.GoodBONG.representationAlphaIndex i).castSucc + 2) :
    a.representationAlphaValue b i ≤
      a.alphaValue (BONG.GoodBONG.representationAlphaIndex i) := by
  let g := BONG.GoodBONG.representationAlphaIndex i
  change a.representationAlphaValue b i ≤ a.alphaValue g
  change a.order g.castSucc = b.order g.castSucc + 2 at hcurrent
  have hgt : b.order g.castSucc < a.order g.castSucc := by omega
  rcases D.noCollision_source_previous_twoStep_eq_before_selected_of_current_gt
      hsmall hlarge hselected a b g hbefore hgt with
    ⟨hpos, hnext, htwo, hpreviousStrict, hcurrentCases,
      hgapEquality, hevenPair, hgapEven, hgapLt⟩
  have hiPrevious : 1 < i.val := by
    change 0 < i.val - 1 at hpos
    omega
  let previousAlpha : Fin (n + 1) := ⟨i.val - 2, by
    have := i.lt_large
    omega⟩
  have hpreviousLe : previousAlpha ≤ g := by
    change i.val - 2 ≤ i.val - 1
    omega
  have hendpoint := a.alphaLeftEndpoint_monotone hpreviousLe
  change (a.order previousAlpha.castSucc : ℚ) +
      a.alphaValue previousAlpha ≤
    (a.order g.castSucc : ℚ) + a.alphaValue g at hendpoint
  have hweightData :=
    D.noCollision_previous_order_add_alpha_eq_of_current_eq_target_add_two
      hsmall hlarge hselected a b g hbefore hcurrent
  rcases hweightData with ⟨_, hweightSum⟩
  have hpreviousAlphaIndex :
      (⟨g.val - 1, by omega⟩ : Fin (n + 1)) = previousAlpha := by
    apply Fin.ext
    change (i.val - 1) - 1 = i.val - 2
    omega
  rw [hpreviousAlphaIndex] at hweightSum
  have hnextIndex :
      (⟨g.val + 1, hnext⟩ : Fin (n + 2)) =
        ⟨i.val, i.lt_large⟩ := by
    apply Fin.ext
    change i.val - 1 + 1 = i.val
    omega
  have hpreviousIndex :
      (⟨g.val - 1, by omega⟩ : Fin (n + 2)) =
        previousAlpha.castSucc := by
    apply Fin.ext
    change (i.val - 1) - 1 = i.val - 2
    omega
  have htwoNormalized :
      a.order previousAlpha.castSucc =
        a.order ⟨i.val, i.lt_large⟩ := by
    rw [← hpreviousIndex, ← hnextIndex]
    exact htwo
  have hgapNormalized :
      b.order previousAlpha.castSucc - a.order previousAlpha.castSucc =
        a.order g.castSucc - b.order g.castSucc := by
    rw [← hpreviousIndex]
    exact hgapEquality
  have hcandidate :=
    a.representationAlphaValue_le_primary_previousAlpha b i hiPrevious
  have hcurrentMathIndex :
      (⟨i.val - 1, by have := i.le_small; omega⟩ : Fin (n + 2)) =
        g.castSucc := by
    apply Fin.ext
    rfl
  have hcandidate' : a.representationAlphaValue b i ≤
      (a.order ⟨i.val, i.lt_large⟩ : ℚ) -
        (b.order g.castSucc : ℚ) + b.alphaValue previousAlpha := by
    push_cast at hcandidate
    rw [hcurrentMathIndex,
      show (⟨i.val - 2, by have := i.lt_large; omega⟩ : Fin (n + 1)) =
        previousAlpha by rfl] at hcandidate
    exact hcandidate
  have htwoQ :
      (a.order previousAlpha.castSucc : ℚ) =
        (a.order ⟨i.val, i.lt_large⟩ : ℚ) := by
    exact_mod_cast htwoNormalized
  have hgapQ :
      (b.order previousAlpha.castSucc : ℚ) -
          (a.order previousAlpha.castSucc : ℚ) =
        (a.order g.castSucc : ℚ) - (b.order g.castSucc : ℚ) := by
    exact_mod_cast hgapNormalized
  have hcurrentQ : (a.order g.castSucc : ℚ) =
      (b.order g.castSucc : ℚ) + 2 := by
    exact_mod_cast hcurrent
  linarith

/-- Attach Lemma 5.13's common approximation to both alpha-cap estimates in
the reverse strict-order branch. -/
theorem noCollision_commonCertificate_before_selected_of_current_gt
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : D.Lemma517Range i)
    (hbefore :
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv
        (BONG.GoodBONG.representationAlphaIndex i).castSucc).1 <
          D.largeSelectedPosition)
    (hcurrent : b.order
        (BONG.GoodBONG.representationAlphaIndex i).castSucc <
      a.order (BONG.GoodBONG.representationAlphaIndex i).castSucc) :
    BONG.GoodBONG.Beli2019SectionFiveDefectCertificate a b i := by
  let g := BONG.GoodBONG.representationAlphaIndex i
  change b.order g.castSucc < a.order g.castSucc at hcurrent
  have hnotSucc : b.orderSequence.entryOrZero (i.val - 1) ≠
      a.orderSequence.entryOrZero (i.val - 1) + 1 := by
    rw [BeliOrderSequence.entryOrZero_of_lt b.orderSequence
        (by have := i.lt_large; omega),
      BeliOrderSequence.entryOrZero_of_lt a.orderSequence
        (by have := i.lt_large; omega)]
    simp only [BONG.GoodBONG.orderSequence_at]
    have hindex :
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2)) =
          g.castSucc := by
      apply Fin.ext
      rfl
    rw [hindex]
    omega
  let localData := D.noCollision_aligned_lemma513LocalData
    hsmall hlarge hselected a b
  obtain ⟨X, hsource, htarget⟩ :=
    localData.commonApproximation i hi hnotSucc
  have hcases :=
    D.noCollision_source_previous_twoStep_eq_before_selected_of_current_gt
      hsmall hlarge hselected a b g hbefore hcurrent
  rcases hcases with
    ⟨_hpos, _hnext, _htwo, _hpreviousStrict, hcurrentCases,
      _hgapEquality, _hevenPair, _hgapEven, _hgapLt⟩
  have hsourceBound : a.representationAlphaValue b i ≤
      a.alphaValue g := by
    rcases hcurrentCases with hgapOne | hgapTwo
    · exact D.noCollision_representationAlphaValue_le_sourceAlpha_of_current_eq_target_add_one
        hsmall hlarge hselected a b i hi hbefore hgapOne
    · exact D.noCollision_representationAlphaValue_le_sourceAlpha_of_current_eq_target_add_two
        hsmall hlarge hselected a b i hbefore hgapTwo
  have htargetBound : a.representationAlphaValue b i ≤
      b.alphaValue g :=
    D.noCollision_representationAlphaValue_le_targetAlpha_of_current_gt
      hsmall hlarge hselected a b i hcurrent
  apply BONG.GoodBONG.Beli2019SectionFiveDefectCertificate.common
    X hsource htarget
  rw [a.prefixAlphaCap_of_internal i.pos i.lt_large,
    b.prefixAlphaCap_of_internal i.pos i.lt_large,
    ← a.coe_representationAlphaValue b i]
  apply le_min
  · exact_mod_cast hsourceBound
  · exact_mod_cast htargetBound

/-- Complete defect certificate at every collision-free aligned boundary
strictly before the distinguished component. -/
theorem noCollision_defectCertificate_before_selected
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [Beli2019OrderNecessityLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hsmall : ¬D.SmallScaleCollision)
    (hlarge : ¬D.LargeScaleCollision)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hi : D.Lemma517Range i)
    (hbefore :
      ((D.largeNoCollisionProfileWitness hlarge a).indexEquiv
        (BONG.GoodBONG.representationAlphaIndex i).castSucc).1 <
          D.largeSelectedPosition) :
    BONG.GoodBONG.Beli2019SectionFiveDefectCertificate a b i := by
  let g := BONG.GoodBONG.representationAlphaIndex i
  let localData := D.noCollision_aligned_lemma513LocalData
    hsmall hlarge hselected a b
  by_cases hlt : a.order g.castSucc < b.order g.castSucc
  · by_cases hsucc : b.orderSequence.entryOrZero (i.val - 1) =
        a.orderSequence.entryOrZero (i.val - 1) + 1
    · exact D.noCollision_oddCertificate_before_selected
        hsmall hlarge hselected a b i hi hbefore hsucc
    · have hcurrentLt : a.order
            ⟨i.val - 1, (Nat.sub_le _ _).trans_lt i.lt_large⟩ <
          b.order ⟨i.val - 1,
            (Nat.sub_le _ _).trans_lt i.lt_large⟩ := by
        have hindex :
            (⟨i.val - 1,
              (Nat.sub_le _ _).trans_lt i.lt_large⟩ : Fin (n + 2)) =
                g.castSucc := by
          apply Fin.ext
          rfl
        rw [hindex]
        exact hlt
      exact D.noCollision_commonCertificate_before_selected_of_current_lt
        hsmall hlarge hselected a b i hi hbefore hcurrentLt hsucc
  · by_cases heq : a.order g.castSucc = b.order g.castSucc
    · have hentryEq : a.orderSequence.entryOrZero (i.val - 1) =
          b.orderSequence.entryOrZero (i.val - 1) := by
        rw [BeliOrderSequence.entryOrZero_of_lt a.orderSequence
            (by have := i.lt_large; omega),
          BeliOrderSequence.entryOrZero_of_lt b.orderSequence
            (by have := i.lt_large; omega)]
        simp only [BONG.GoodBONG.orderSequence_at]
        have hindex :
            (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2)) =
              g.castSucc := by
          apply Fin.ext
          rfl
        rw [hindex]
        exact heq
      exact localData.equalCertificate a b D.smallLattice_le_large
        (D.lemma517Data_proved a b) i hi hentryEq
    · have hgt : b.order g.castSucc < a.order g.castSucc := by omega
      exact D.noCollision_commonCertificate_before_selected_of_current_gt
        hsmall hlarge hselected a b i hi hbefore hgt

end Lattice.Beli2019Lemma51Data

end Bong
