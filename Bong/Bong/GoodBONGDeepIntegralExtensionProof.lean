/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.GoodBONGDeepIntegralExtension
import Bong.Bong.Beli2019Lemma710BONGProduct
import Bong.Bong.GoodExistence
import Bong.Bong.Rescale
import Bong.Bong.Beli2006AlphaP4P6Proof
import Bong.Lattice.DeepRescale
import Bong.Lattice.ModularSplitting
import Mathlib.Data.Finset.Order

/-!
# Constructing deep integral extensions

This file proves the deep-complement construction used in Beli (2019),
Lemmas 2.20--2.21.  The image of an integral representation is split from
its nondegenerate orthogonal complement, an arbitrary good BONG is chosen on
that complement, and the complement is multiplied by a sufficiently high
uniformizer power.  O'Meara, Proposition 81:1, enters only through
`Lattice.exists_uniformizerPower_rescale_le`.
-/

namespace Bong

open Dyadic Module

universe u v w

namespace Lattice.Representation

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W}

/-- The source space is linearly equivalent to the range of an injective
lattice representation. -/
noncomputable def rangeEquiv
    (f : Lattice.Representation r q M L) :
    W ≃ₗ[K] LinearMap.range f.toLinearMap :=
  LinearEquiv.ofBijective f.toLinearMap.rangeRestrict ⟨by
    intro x y hxy
    apply f.injective
    exact congrArg Subtype.val hxy, LinearMap.surjective_rangeRestrict _⟩

@[simp]
theorem coe_rangeEquiv_apply
    (f : Lattice.Representation r q M L) (x : W) :
    ((f.rangeEquiv x : LinearMap.range f.toLinearMap) : V) =
      f.toLinearMap x :=
  rfl

/-- The image of a quadratic-space representation is nondegenerate. -/
theorem range_nondegenerate
    (f : Lattice.Representation r q M L) :
    (q.bilin.restrict (LinearMap.range f.toLinearMap)).Nondegenerate := by
  let e := f.rangeEquiv
  have hform :
      q.bilin.restrict (LinearMap.range f.toLinearMap) =
        LinearMap.BilinForm.congr e r.bilin := by
    ext x y
    change q.bilin (x : V) (y : V) =
      r.bilin (e.symm x) (e.symm y)
    rw [← f.map_bilin]
    congr 2
    · exact (congrArg Subtype.val (e.apply_symm_apply x)).symm
    · exact (congrArg Subtype.val (e.apply_symm_apply y)).symm
  rw [hform]
  exact r.nondegenerate.congr e

/-- The represented source, regarded as a nondegenerate quadratic
sublattice of the target space. -/
noncomputable def imageComponent
    (f : Lattice.Representation r q M L) :
    Lattice.QuadraticSublattice q where
  carrier := LinearMap.range f.toLinearMap
  nondegenerate := f.range_nondegenerate
  lattice := Lattice.map f.rangeEquiv M

@[simp]
theorem imageComponent_space_bilin
    (f : Lattice.Representation r q M L)
    (x y : (f.imageComponent).carrier) :
    f.imageComponent.space.bilin x y = q.bilin (x : V) (y : V) :=
  rfl

/-- The source quadratic space is isometric to its image component. -/
noncomputable def imageIsometry
    (f : Lattice.Representation r q M L) :
    QuadraticSpace.Isometry r f.imageComponent.space where
  toLinearEquiv := f.rangeEquiv
  map_bilin := by
    intro x y
    exact f.map_bilin x y

/-- A chosen full lattice on the orthogonal complement of the represented
source space. -/
noncomputable def complementComponent
    (f : Lattice.Representation r q M L) [FiniteDimensional K V] :
    Lattice.QuadraticSublattice q where
  carrier := f.imageComponent.orthogonalCarrier
  nondegenerate := f.imageComponent.orthogonalCarrier_nondegenerate
  lattice := Lattice.basisLattice (Module.Free.chooseBasis K
    f.imageComponent.orthogonalCarrier)

/-- Orthogonal addition identifies the source plus its complement with the
target quadratic space. -/
noncomputable def ambientIsometry
    (f : Lattice.Representation r q M L) [FiniteDimensional K V] :
    QuadraticSpace.Isometry
      (r.orthogonalSum f.complementComponent.space) q where
  toLinearEquiv :=
    (f.rangeEquiv.prodCongr
      (LinearEquiv.refl K f.imageComponent.orthogonalCarrier)).trans
      (f.imageComponent.carrier.prodEquivOfIsCompl
        f.imageComponent.orthogonalCarrier
        f.imageComponent.carrier_isCompl_orthogonalCarrier)
  map_bilin := by
    intro x y
    change q.bilin
      ((f.toLinearMap x.1 : V) + (x.2 : V))
      ((f.toLinearMap y.1 : V) + (y.2 : V)) =
        r.bilin x.1 y.1 + q.bilin (x.2 : V) (y.2 : V)
    simp only [map_add, LinearMap.add_apply]
    rw [f.map_bilin]
    have hxy : q.bilin (f.toLinearMap x.1) (y.2 : V) = 0 :=
      y.2.property (f.toLinearMap x.1) ⟨x.1, rfl⟩
    have hyx : q.bilin (x.2 : V) (f.toLinearMap y.1) = 0 := by
      rw [q.isSymm.eq]
      exact x.2.property (f.toLinearMap y.1) ⟨y.1, rfl⟩
    rw [hxy, hyx]
    simp

@[simp]
theorem ambientIsometry_apply
    (f : Lattice.Representation r q M L) [FiniteDimensional K V]
    (x : W × f.imageComponent.orthogonalCarrier) :
    f.ambientIsometry.toLinearEquiv x =
      f.toLinearMap x.1 + (x.2 : V) :=
  rfl

end Lattice.Representation

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {m n : Nat}

/-- Internal alpha values of an old prefix are unchanged when all new tail
orders lie beyond a uniform cross-candidate bound. -/
theorem alphaValue_eq_of_prefix_values_of_deep_tail
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (hRank : n < m)
    (hvalues : ∀ i : Fin (n + 1),
      a.valueUnit ⟨i.val, by omega⟩ = b.valueUnit i)
    (T : Int)
    (htail : ∀ j : Fin (m + 1), n + 1 ≤ j.val → T ≤ a.order j)
    (i : Fin n)
    (hcross : (b.alphaValue i : WithTop ℚ) ≤
      ((((T - b.order i.castSucc : Int) : ℚ) : WithTop ℚ))) :
    a.alphaValue ⟨i.val, by omega⟩ = b.alphaValue i := by
  let ia : Fin m := ⟨i.val, by omega⟩
  have horder (k : Fin (n + 1)) :
      a.order ⟨k.val, by omega⟩ = b.order k := by
    unfold order
    rw [a.toBONG.order_eq_ordUnit, b.toBONG.order_eq_ordUnit]
    exact congrArg (ordUnit K) (hvalues k)
  have hadjacent (j : Fin n) :
      a.adjacentDefect ⟨j.val, by omega⟩ = b.adjacentDefect j := by
    unfold adjacentDefect adjacentProduct
    have hcast :
        (⟨j.val, by omega⟩ : Fin m).castSucc =
          (⟨j.val, by omega⟩ : Fin (m + 1)) := Fin.ext rfl
    have hsucc :
        (⟨j.val, by omega⟩ : Fin m).succ =
          (⟨j.val + 1, by omega⟩ : Fin (m + 1)) := Fin.ext rfl
    rw [hcast, hsucc]
    have h₀ := hvalues j.castSucc
    have h₁ := hvalues j.succ
    have hprod := congrArg₂ (fun x y : Kˣ ↦ x * y) h₀ h₁
    exact congrArg (fun z : Kˣ ↦ defectOrder (K := K) (-z)) hprod
  have hhalf : a.halfGapCandidate ia = b.halfGapCandidate i := by
    unfold halfGapCandidate
    have hcast :
        ia.castSucc = (⟨i.val, by omega⟩ : Fin (m + 1)) := Fin.ext rfl
    have hsucc :
        ia.succ = (⟨i.val + 1, by omega⟩ : Fin (m + 1)) := Fin.ext rfl
    rw [hcast, hsucc]
    have h₀ := horder i.castSucc
    have h₁ := horder i.succ
    simpa only [ia, Fin.val_castSucc, Fin.val_succ] using
      congrArg₂ (fun x y : Int ↦
        (((((y - x : Int) : ℚ) / 2 + (ramificationIndex K : ℚ) : ℚ) :
          WithTop ℚ))) h₀ h₁
  have hleft (j : Fin n) :
      a.leftDefectCandidate ia ⟨j.val, by omega⟩ =
        b.leftDefectCandidate i j := by
    unfold leftDefectCandidate
    have hiSucc :
        ia.succ = (⟨i.val + 1, by omega⟩ : Fin (m + 1)) := Fin.ext rfl
    have hjCast :
        (⟨j.val, by omega⟩ : Fin m).castSucc =
          (⟨j.val, by omega⟩ : Fin (m + 1)) := Fin.ext rfl
    rw [hiSucc, hjCast]
    have hi := horder i.succ
    have hj := horder j.castSucc
    rw [hadjacent]
    have hdiff := congrArg₂ (fun x y : Int ↦
      ((((x - y : Int) : ℚ) : WithTop ℚ))) hi hj
    exact congrArg (fun z : WithTop ℚ ↦ z + b.adjacentDefect j) hdiff
  have hright (j : Fin n) :
      a.rightDefectCandidate ia ⟨j.val, by omega⟩ =
        b.rightDefectCandidate i j := by
    unfold rightDefectCandidate
    have hjSucc :
        (⟨j.val, by omega⟩ : Fin m).succ =
          (⟨j.val + 1, by omega⟩ : Fin (m + 1)) := Fin.ext rfl
    have hiCast :
        ia.castSucc = (⟨i.val, by omega⟩ : Fin (m + 1)) := Fin.ext rfl
    rw [hjSucc, hiCast]
    have hj := horder j.succ
    have hi := horder i.castSucc
    rw [hadjacent]
    have hdiff := congrArg₂ (fun x y : Int ↦
      ((((x - y : Int) : ℚ) : WithTop ℚ))) hj hi
    exact congrArg (fun z : WithTop ℚ ↦ z + b.adjacentDefect j) hdiff
  apply WithTop.coe_injective
  rw [a.coe_alphaValue, b.coe_alphaValue]
  apply le_antisymm
  · have hmem := Finset.min'_mem (b.alphaCandidates i)
      (b.alphaCandidates_nonempty i)
    have hcandidate : b.alpha i ∈ b.alphaCandidates i := hmem
    simp only [alphaCandidates, Finset.mem_insert, Finset.mem_union,
      Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hcandidate
    rcases hcandidate with hhalfEq | hleftEq | hrightEq
    · apply (a.alpha_le_halfGapCandidate ia).trans_eq
        (hhalf.trans hhalfEq.symm)
    · rcases hleftEq with ⟨j, hji, hj⟩
      have hja : (⟨j.val, by omega⟩ : Fin m) ≤ ia := hji
      apply (a.alpha_le_leftDefectCandidate hja).trans_eq
      exact (hleft j).trans hj
    · rcases hrightEq with ⟨j, hij, hj⟩
      have hja : ia ≤ (⟨j.val, by omega⟩ : Fin m) := hij
      apply (a.alpha_le_rightDefectCandidate hja).trans_eq
      exact (hright j).trans hj
  · apply Finset.le_min'
    intro x hx
    simp only [alphaCandidates, Finset.mem_insert, Finset.mem_union,
      Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rcases hx with hhalfEq | hleftEq | hrightEq
    · rw [hhalfEq, hhalf]
      exact Finset.min'_le _ _ (b.halfGapCandidate_mem_alphaCandidates i)
    · rcases hleftEq with ⟨j, hji, hj⟩
      have hjn : j.val < n := by
        have hle : j.val ≤ i.val := hji
        exact lt_of_le_of_lt hle i.isLt
      let jb : Fin n := ⟨j.val, hjn⟩
      have hjb : jb ≤ i := hji
      rw [← hj, hleft jb]
      exact b.alpha_le_leftDefectCandidate hjb
    · rcases hrightEq with ⟨j, hij, hj⟩
      by_cases hjPrefix : j.val < n
      · let jb : Fin n := ⟨j.val, hjPrefix⟩
        have hjb : i ≤ jb := hij
        rw [← hj, hright jb]
        exact b.alpha_le_rightDefectCandidate hjb
      · rw [← hj]
        unfold rightDefectCandidate
        have htailOrder : T ≤ a.order j.succ := by
          apply htail
          simp only [Fin.val_succ]
          omega
        have hbase :
            (b.alphaValue i : WithTop ℚ) ≤
              ((((a.order j.succ - a.order ia.castSucc : Int) : ℚ) :
                WithTop ℚ)) := by
          have hiOrder : a.order ia.castSucc = b.order i.castSucc := by
            have hiCast :
                ia.castSucc = (⟨i.val, by omega⟩ : Fin (m + 1)) := Fin.ext rfl
            rw [hiCast]
            exact horder i.castSucc
          rw [hiOrder]
          exact hcross.trans (by exact_mod_cast sub_le_sub_right htailOrder _)
        rw [← b.coe_alphaValue]
        exact hbase.trans (le_add_of_nonneg_right
          (defectOrder_nonneg_for_alpha (K := K) (a.adjacentProduct j)))

/-- Prefix alpha caps below the old rank are unchanged after adjoining a
sufficiently deep tail. -/
theorem prefixAlphaCap_eq_of_prefix_values_of_deep_tail
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (hRank : n < m)
    (hvalues : ∀ i : Fin (n + 1),
      a.valueUnit ⟨i.val, by omega⟩ = b.valueUnit i)
    (T : Int)
    (htail : ∀ j : Fin (m + 1), n + 1 ≤ j.val → T ≤ a.order j)
    (hcross : ∀ i : Fin n, (b.alphaValue i : WithTop ℚ) ≤
      ((((T - b.order i.castSucc : Int) : ℚ) : WithTop ℚ)))
    (k : Nat) (hk : k ≤ n) :
    a.prefixAlphaCap k = b.prefixAlphaCap k := by
  by_cases hk0 : k = 0
  · subst k
    simp
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    rw [a.prefixAlphaCap_of_internal hkpos (by omega),
      b.prefixAlphaCap_of_internal hkpos (by omega)]
    let i : Fin n := ⟨k - 1, by omega⟩
    have halpha := a.alphaValue_eq_of_prefix_values_of_deep_tail b hRank
      hvalues T htail i (hcross i)
    exact congrArg (fun z : ℚ ↦ (z : WithTop ℚ)) halpha

/-- Every strict lower-rank integral representation admits a good-BONG
completion with an arbitrarily deep orthogonal tail. -/
theorem exists_deepIntegralExtension [BONGGoodExistenceLaws.{u, v} K]
    (a : GoodBONG q L (m + 1)) (b : GoodBONG r M (n + 1))
    (hRank : n < m) (f : Lattice.Representation r q M L)
    (orderBound : Int) (alphaBound : ℚ) :
    Nonempty (GoodBONGDeepIntegralExtensionData
      a b hRank f orderBound alphaBound) := by
  classical
  letI : Module.Finite K V := L.moduleFinite
  letI : Module.Finite K W := M.moduleFinite
  let C := f.complementComponent
  have hCompRank : Module.finrank K C.carrier = m - n := by
    change Module.finrank K
        (q.bilin.orthogonal (LinearMap.range f.toLinearMap)) = m - n
    rw [q.bilin.finrank_orthogonal q.nondegenerate,
      LinearMap.finrank_range_of_inj f.injective,
      ← b.toBONG.length_eq_finrank,
      ← a.toBONG.length_eq_finrank]
    omega
  have hTailLen : Module.finrank K C.carrier = (m - n - 1) + 1 := by
    rw [hCompRank]
    omega
  rcases exists_good_bong C.space C.lattice with ⟨cRaw⟩
  let c₀ : GoodBONG C.space C.lattice ((m - n - 1) + 1) :=
    cRaw.castLength hTailLen
  let bOrders : Finset Int := Finset.univ.image b.order
  obtain ⟨bMax, hbMax⟩ := Finset.exists_le bOrders
  have hbOrder (i : Fin (n + 1)) : b.order i ≤ bMax := by
    apply hbMax
    simp [bOrders]
  let bAlphas : Finset ℚ := Finset.univ.image b.alphaValue
  obtain ⟨alphaMax, hAlphaMax⟩ := Finset.exists_le bAlphas
  have hbAlpha (i : Fin n) : b.alphaValue i ≤ alphaMax := by
    apply hAlphaMax
    simp [bAlphas]
  obtain ⟨alphaInteger, hAlphaInteger⟩ :=
    exists_int_gt (max (max alphaBound alphaMax) 0)
  have hAlphaBound : alphaBound < (alphaInteger : ℚ) :=
    lt_of_le_of_lt (le_max_left _ _) (lt_of_le_of_lt (le_max_left _ _)
      hAlphaInteger)
  have hAlphaMaxInt : alphaMax < (alphaInteger : ℚ) :=
    lt_of_le_of_lt (le_max_right _ _) (lt_of_le_of_lt (le_max_left _ _)
      hAlphaInteger)
  have hAlphaIntegerPos : 0 < alphaInteger := by
    have hzeroQ : (0 : ℚ) < (alphaInteger : ℚ) :=
      lt_of_le_of_lt (le_max_right _ _) hAlphaInteger
    exact_mod_cast hzeroQ
  let gapBound : Int := max (2 * (ramificationIndex K : Int))
    (2 * alphaInteger)
  let T : Int := max orderBound
    (max (bMax + alphaInteger)
      (b.order (Fin.last n) + gapBound))
  have hTOrder : orderBound ≤ T := le_max_left _ _
  have hTBAlpha : bMax + alphaInteger ≤ T :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hTGap : b.order (Fin.last n) + gapBound ≤ T :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have hGapTwoE : 2 * (ramificationIndex K : Int) ≤ gapBound :=
    le_max_left _ _
  have hGapAlpha : 2 * alphaInteger ≤ gapBound :=
    le_max_right _ _
  let shifts : Finset Int := Finset.univ.image (fun j => T - c₀.order j)
  obtain ⟨shiftMax, hShiftMax⟩ := Finset.exists_le shifts
  have hShift (j : Fin ((m - n - 1) + 1)) :
      T - c₀.order j ≤ shiftMax := by
    apply hShiftMax
    simp [shifts]
  let k₀ : Int := max 0 shiftMax
  let A : Lattice K V := Lattice.map f.ambientIsometry.toLinearEquiv
    (Lattice.product M C.lattice)
  obtain ⟨k, hk, hDeep⟩ :=
    Lattice.exists_uniformizerPower_rescale_le A L k₀
  let s : Kˣ := uniformizerPowerUnit K k
  let c : GoodBONG C.space (Lattice.rescale s C.lattice)
      ((m - n - 1) + 1) := c₀.rescale s
  have hkNonneg : 0 ≤ k :=
    le_trans (le_max_left _ _) hk
  have hcDeep (j : Fin ((m - n - 1) + 1)) : T ≤ c.order j := by
    rw [order_rescale, show ordUnit K s = k by
      simp [s, ordUnit_uniformizerPowerUnit]]
    have hj := hShift j
    have hshiftLe : shiftMax ≤ k :=
      le_trans (le_max_right _ _) hk
    omega
  have hbMaxT : bMax ≤ T := by
    have : bMax ≤ bMax + alphaInteger := by omega
    exact this.trans hTBAlpha
  have hConcatOrder (i : Fin (n + 1)) : b.order i ≤ c.order 0 :=
    (hbOrder i).trans (hbMaxT.trans (hcDeep 0))
  have hLastSecond : ∀ (hn : 0 < n + 1)
      (hm : 1 < (m - n - 1) + 1),
      b.order ⟨(n + 1) - 1, by omega⟩ ≤ c.order ⟨1, hm⟩ := by
    intro hn hm
    exact (hbOrder _).trans (hbMaxT.trans (hcDeep _))
  let dProduct := b.orthogonalProductRight_of_orderBounds c
    hConcatOrder hLastSecond
  let Dlat : Lattice K V := Lattice.map f.ambientIsometry.toLinearEquiv
    (Lattice.product M (Lattice.rescale s C.lattice))
  let dMapped : GoodBONG q Dlat
      (((m - n - 1) + 1) + (n + 1)) :=
    dProduct.map f.ambientIsometry
  have hTotalLen : ((m - n - 1) + 1) + (n + 1) = m + 1 := by omega
  let d : GoodBONG q Dlat (m + 1) := dMapped.castLength hTotalLen
  have hCompletedLe : Dlat ≤ L := by
    intro z hz
    let x := f.ambientIsometry.toLinearEquiv.symm z
    have hx : x ∈ Lattice.product M (Lattice.rescale s C.lattice) := by
      exact (Lattice.mem_map_iff f.ambientIsometry.toLinearEquiv _ z).1 hz
    have hxSource : x.1 ∈ M := Lattice.fst_mem_of_mem_product hx
    have hxComplement : x.2 ∈ Lattice.rescale s C.lattice :=
      Lattice.snd_mem_of_mem_product hx
    have hsource : f.toLinearMap x.1 ∈ L := f.map_mem hxSource
    have hcomplement : (x.2 : V) ∈ L := by
      rcases (Lattice.mem_rescale_iff s C.lattice x.2).1 hxComplement with
        ⟨y, hy, hyx⟩
      apply hDeep
      apply (Lattice.mem_rescale_iff s A (x.2 : V)).2
      refine ⟨f.ambientIsometry.toLinearEquiv (0, y), ?_, ?_⟩
      · apply (Lattice.map_mem_map_iff f.ambientIsometry.toLinearEquiv
          (Lattice.product M C.lattice) (0, y)).2
        exact Lattice.inr_mem_product_iff.mpr hy
      · simpa only [Lattice.Representation.ambientIsometry_apply,
          map_zero, zero_add, Submodule.coe_smul] using
          congrArg Subtype.val hyx
    have hiso := f.ambientIsometry.toLinearEquiv.apply_symm_apply z
    change f.toLinearMap x.1 + (x.2 : V) = z at hiso
    rw [← hiso]
    exact L.add_mem hsource hcomplement
  have hdTail (j : Fin (m + 1)) (hj : n + 1 ≤ j.val) :
      T ≤ d.order j := by
    rw [order_castLength, BONG.GoodBONG.order_map]
    let jc : Fin ((m - n - 1) + 1) := ⟨j.val - (n + 1), by omega⟩
    have hidx :
        (⟨j.val, by omega⟩ :
          Fin (((m - n - 1) + 1) + (n + 1))) =
        BONG.orthogonalProductRightIndex (n + 1) jc := by
      apply Fin.ext
      simp [jc, BONG.orthogonalProductRightIndex]
      omega
    rw [hidx]
    change T ≤
      (b.toBONG.orthogonalProductRight c.toBONG hConcatOrder).order
        (BONG.orthogonalProductRightIndex (n + 1) jc)
    rw [BONG.order_orthogonalProductRight_right]
    exact hcDeep jc
  have hdPrefix (i : Fin (n + 1)) :
      d.toBONG.ambientVector ⟨i.val, by omega⟩ =
        f.toLinearMap (b.toBONG.ambientVector i) := by
    rw [ambientVector_castLength_eq]
    change ((dProduct.map f.ambientIsometry).toBONG.ambientVector
      ⟨i.val, by omega⟩) = _
    change (dProduct.toBONG.map f.ambientIsometry).ambientVector
      ⟨i.val, by omega⟩ = _
    rw [BONG.ambientVector_map]
    have hidx :
        (⟨i.val, by omega⟩ :
          Fin (((m - n - 1) + 1) + (n + 1))) =
        BONG.orthogonalProductLeftIndex ((m - n - 1) + 1) i := by
      apply Fin.ext
      rfl
    rw [hidx]
    change f.ambientIsometry.toLinearEquiv
      ((b.toBONG.orthogonalProductRight c.toBONG hConcatOrder).ambientVector
        (BONG.orthogonalProductLeftIndex ((m - n - 1) + 1) i)) = _
    rw [BONG.ambientVector_orthogonalProductRight_left]
    simp
  have hdValues (i : Fin (n + 1)) :
      d.valueUnit ⟨i.val, by omega⟩ = b.valueUnit i := by
    apply Units.ext
    simp only [coe_valueUnit]
    change d.value ⟨i.val, by omega⟩ = b.value i
    unfold value
    rw [← d.toBONG.quadratic_ambientVector, hdPrefix,
      f.map_quadratic, b.toBONG.quadratic_ambientVector]
  have hdPrefixOrder (i : Fin (n + 1)) :
      d.order ⟨i.val, by omega⟩ = b.order i := by
    unfold order
    rw [d.toBONG.order_eq_ordUnit, b.toBONG.order_eq_ordUnit]
    exact congrArg (ordUnit K) (hdValues i)
  have hCross (i : Fin n) :
      (b.alphaValue i : WithTop ℚ) ≤
        ((((T - b.order i.castSucc : Int) : ℚ) : WithTop ℚ)) := by
    have hAlphaLt : b.alphaValue i < (alphaInteger : ℚ) :=
      (hbAlpha i).trans_lt hAlphaMaxInt
    have hInt : alphaInteger ≤ T - b.order i.castSucc := by
      have hi := hbOrder i.castSucc
      omega
    have hIntQ : (alphaInteger : ℚ) ≤
        ((T - b.order i.castSucc : Int) : ℚ) := by
      exact_mod_cast hInt
    exact_mod_cast hAlphaLt.le.trans hIntQ
  have hdPrefixCaps (i : Nat) (hi : i ≤ n) :
      d.prefixAlphaCap i = b.prefixAlphaCap i :=
    d.prefixAlphaCap_eq_of_prefix_values_of_deep_tail b hRank hdValues
      T hdTail hCross i hi
  have hBoundaryOrder :
      orderBound ≤ d.order ⟨n + 1, by omega⟩ :=
    hTOrder.trans (hdTail _ (by exact le_rfl))
  let boundary : Fin m := ⟨n, hRank⟩
  have hBoundaryLast : d.order boundary.castSucc = b.order (Fin.last n) := by
    have hindex : boundary.castSucc =
        (⟨(Fin.last n).val, by omega⟩ : Fin (m + 1)) := by
      apply Fin.ext
      rfl
    rw [hindex]
    exact hdPrefixOrder (Fin.last n)
  have hBoundaryNext : T ≤ d.order boundary.succ := by
    apply hdTail
    change n + 1 ≤ n + 1
    exact le_rfl
  have hBoundaryGap : gapBound ≤ d.orderGap boundary := by
    unfold orderGap
    rw [hBoundaryLast]
    omega
  have hBoundaryAlpha : alphaBound < d.alphaValue boundary := by
    have hTwoE : 2 * (ramificationIndex K : Int) ≤
        d.orderGap boundary := hGapTwoE.trans hBoundaryGap
    rw [d.satisfiesAlphaP4_proved boundary hTwoE]
    unfold halfGapValue
    have hGapQ : 2 * (alphaInteger : ℚ) ≤
        (d.orderGap boundary : ℚ) := by
      exact_mod_cast hGapAlpha.trans hBoundaryGap
    have heNonneg : 0 ≤ (ramificationIndex K : ℚ) := by positivity
    have hAlphaLe : (alphaInteger : ℚ) ≤
        (d.orderGap boundary : ℚ) / 2 +
          (ramificationIndex K : ℚ) := by
      linarith
    exact hAlphaBound.trans_le hAlphaLe
  refine ⟨
    { completedLattice := Dlat
      completedBONG := d
      completed_le := hCompletedLe
      prefixAmbient_eq := hdPrefix
      prefixAlphaCap_eq := hdPrefixCaps
      tailOrder := fun i hi => hTOrder.trans (hdTail i hi)
      boundaryOrder := hBoundaryOrder
      boundaryAlpha := hBoundaryAlpha }⟩


end BONG.GoodBONG

/-- Good-BONG existence on the target universe supplies the full deep
integral-extension law by the concrete orthogonal-complement construction. -/
theorem goodBONGDeepIntegralExtensionLaws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    [BONGGoodExistenceLaws.{u, v} K] :
    GoodBONGDeepIntegralExtensionLaws.{u, v, w} K where
  extension := fun a b hRank f orderBound alphaBound =>
    BONG.GoodBONG.exists_deepIntegralExtension
      a b hRank f orderBound alphaBound

end Bong
