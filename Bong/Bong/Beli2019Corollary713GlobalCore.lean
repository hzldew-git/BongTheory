/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Corollary713Local
import Bong.Bong.Beli2019Lemma710ArbitraryReverseDualSeed
import Bong.Bong.Beli2019Lemma710General
import Bong.Bong.Beli2019Lemma710Swap
import Bong.Bong.Beli2006SectionTwo

namespace Bong

open Dyadic
open Module

universe u v w z

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {J : Lattice K V} {T : Lattice K W} {s m : Nat}
  {j : GoodBONG q J s} {R : Int}

noncomputable def corollary713HeadSegment
    (t : GoodBONG r T (m + 1)) :
    BONG.SegmentWitness t.toBONG 0 1 (by omega) :=
  t.toBONG.segmentWitness 0 1 (by omega)

noncomputable def corollary713Head
    (t : GoodBONG r T (m + 1)) :
    GoodBONG
      (r.restrict (t.corollary713HeadSegment).carrier
        (t.corollary713HeadSegment).nondegenerate)
      (t.corollary713HeadSegment).lattice 1 :=
  (t.corollary713HeadSegment).toGoodBONG t.good

noncomputable def corollary713EmbedLocal
    (t : GoodBONG r T (m + 1)) :
    (V × (t.corollary713HeadSegment).carrier) →ₗ[K] (V × W) where
  toFun z := (z.1, z.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem corollary713EmbedLocal_apply
    (t : GoodBONG r T (m + 1))
    (z : V × (t.corollary713HeadSegment).carrier) :
    corollary713EmbedLocal (V := V) t z = (z.1, (z.2 : W)) := rfl

theorem quadratic_corollary713EmbedLocal
    (t : GoodBONG r T (m + 1))
    (z : V × (t.corollary713HeadSegment).carrier) :
    (q.orthogonalSum r).quadratic
        (corollary713EmbedLocal (V := V) t z) =
      (q.orthogonalSum
        (r.restrict (t.corollary713HeadSegment).carrier
          (t.corollary713HeadSegment).nondegenerate)).quadratic z := by
  rfl

theorem bilin_corollary713EmbedLocal
    (t : GoodBONG r T (m + 1))
    (z y : V × (t.corollary713HeadSegment).carrier) :
    (q.orthogonalSum r).bilin
        (corollary713EmbedLocal (V := V) t z)
        (corollary713EmbedLocal (V := V) t y) =
      (q.orthogonalSum
        (r.restrict (t.corollary713HeadSegment).carrier
          (t.corollary713HeadSegment).nondegenerate)).bilin z y := by
  rfl

theorem corollary713Head_bilin_suffix_eq_zero
    (t : GoodBONG r T (m + 1))
    (i : Fin (m + 1)) (hi : 0 < i.val)
    (z : (t.corollary713HeadSegment).carrier) :
    r.bilin (z : W) (t.toBONG.ambientVector i) = 0 := by
  let H := t.corollary713HeadSegment
  have hz : z ∈ Submodule.span K (Set.range H.bong.ambientVector) := by
    rw [H.bong.span_ambientVector_eq_top]
    trivial
  refine Submodule.span_induction
    (p := fun (y : (t.corollary713HeadSegment).carrier) _ =>
      r.bilin (y : W) (t.toBONG.ambientVector i) = 0)
    ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨j, rfl⟩
    rw [H.ambientVector_eq]
    apply (LinearMap.BilinForm.iIsOrtho_def.mp
      t.toBONG.ambientVector_iIsOrtho)
    intro heq
    have hval := congrArg Fin.val heq
    simp only [BONG.SegmentWitness.sourceIndex_val] at hval
    omega
  · simp
  · intro x y _ _ hx hy
    simpa only [Submodule.coe_add, LinearMap.BilinForm.add_left,
      hx, hy, add_zero]
  · intro a x _ hx
    simpa only [SetLike.val_smul, LinearMap.BilinForm.smul_left, hx,
      smul_zero, mul_zero]

theorem corollary713Suffix_bilin_head_eq_zero
    (t : GoodBONG r T (m + 1))
    (i : Fin (m + 1)) (hi : 0 < i.val)
    (z : (t.corollary713HeadSegment).carrier) :
    r.bilin (t.toBONG.ambientVector i) (z : W) = 0 := by
  rw [r.isSymm.eq]
  exact t.corollary713Head_bilin_suffix_eq_zero i hi z

noncomputable def corollary713TargetVector
    (t : GoodBONG r T (m + 1))
    (E : Corollary713LocalRealization
      (s := s) (j := j) (x := t.corollary713Head) R)
    (i : Fin ((m + 1) + s)) : V × W :=
  if h : i.val < s + 1 then
    corollary713EmbedLocal (V := V) t
      (E.bong.toBONG.ambientVector ⟨i.val, h⟩)
  else
    (0, t.toBONG.ambientVector ⟨i.val - s, by omega⟩)

@[simp] theorem corollary713TargetVector_local
    (t : GoodBONG r T (m + 1))
    (E : Corollary713LocalRealization
      (s := s) (j := j) (x := t.corollary713Head) R)
    (i : Fin ((m + 1) + s)) (hi : i.val < s + 1) :
    corollary713TargetVector t E i =
      corollary713EmbedLocal (V := V) t
        (E.bong.toBONG.ambientVector ⟨i.val, hi⟩) := by
  simp [corollary713TargetVector, hi]

@[simp] theorem corollary713TargetVector_suffix
    (t : GoodBONG r T (m + 1))
    (E : Corollary713LocalRealization
      (s := s) (j := j) (x := t.corollary713Head) R)
    (i : Fin ((m + 1) + s)) (hi : s + 1 ≤ i.val) :
    corollary713TargetVector t E i =
      (0, t.toBONG.ambientVector ⟨i.val - s, by omega⟩) := by
  simp [corollary713TargetVector, not_lt.mpr hi]

theorem corollary713TargetVector_bilin_eq_zero_of_lt
    (t : GoodBONG r T (m + 1))
    (E : Corollary713LocalRealization
      (s := s) (j := j) (x := t.corollary713Head) R)
    (i k : Fin ((m + 1) + s)) (hik : i.val < k.val) :
    (q.orthogonalSum r).bilin
      (corollary713TargetVector t E i)
      (corollary713TargetVector t E k) = 0 := by
  by_cases hi : i.val < s + 1
  · rw [corollary713TargetVector_local t E i hi]
    by_cases hk : k.val < s + 1
    · rw [corollary713TargetVector_local t E k hk,
        bilin_corollary713EmbedLocal]
      exact (LinearMap.BilinForm.iIsOrtho_def.mp
        E.bong.toBONG.ambientVector_iIsOrtho)
          ⟨i.val, hi⟩ ⟨k.val, hk⟩ (Fin.ne_of_lt hik)
    · have hk' : s + 1 ≤ k.val := Nat.le_of_not_gt hk
      let kk : Fin (m + 1) := ⟨k.val - s, by omega⟩
      have hkk : 0 < kk.val := by
        dsimp only [kk]
        omega
      rw [corollary713TargetVector_suffix t E k hk',
        QuadraticSpace.orthogonalSum_bilin_apply]
      change q.bilin _ 0 + r.bilin
        ((E.bong.toBONG.ambientVector ⟨i.val, hi⟩).2 : W)
        (t.toBONG.ambientVector kk) = 0
      simp only [map_zero, zero_add]
      exact t.corollary713Head_bilin_suffix_eq_zero kk hkk
        (E.bong.toBONG.ambientVector ⟨i.val, hi⟩).2
  · have hi' : s + 1 ≤ i.val := Nat.le_of_not_gt hi
    have hk' : s + 1 ≤ k.val := by omega
    let ii : Fin (m + 1) := ⟨i.val - s, by omega⟩
    let kk : Fin (m + 1) := ⟨k.val - s, by omega⟩
    have hiik : ii.val < kk.val := by
      dsimp only [ii, kk]
      omega
    rw [corollary713TargetVector_suffix t E i hi',
      corollary713TargetVector_suffix t E k hk',
      QuadraticSpace.orthogonalSum_bilin_apply]
    simp only [map_zero, zero_add]
    exact (LinearMap.BilinForm.iIsOrtho_def.mp
      t.toBONG.ambientVector_iIsOrtho)
        ii kk (Fin.ne_of_lt hiik)

theorem corollary713TargetVector_iIsOrtho
    (t : GoodBONG r T (m + 1))
    (E : Corollary713LocalRealization
      (s := s) (j := j) (x := t.corollary713Head) R) :
    (q.orthogonalSum r).bilin.iIsOrtho
      (corollary713TargetVector t E) := by
  rw [LinearMap.BilinForm.iIsOrtho_def]
  intro i k hik
  have hval : i.val ≠ k.val := fun h => hik (Fin.ext h)
  rcases lt_or_gt_of_ne hval with hlt | hgt
  · exact corollary713TargetVector_bilin_eq_zero_of_lt t E i k hlt
  · rw [(q.orthogonalSum r).isSymm.eq]
    exact corollary713TargetVector_bilin_eq_zero_of_lt t E k i hgt

noncomputable def corollary713TargetBasis
    (t : GoodBONG r T (m + 1))
    (E : Corollary713LocalRealization
      (s := s) (j := j) (x := t.corollary713Head) R) :
    Basis (Fin ((m + 1) + s)) K (V × W) := by
  letI : FiniteDimensional K V := j.toBONG.basis.finiteDimensional_of_finite
  letI : FiniteDimensional K W := t.toBONG.basis.finiteDimensional_of_finite
  let family := corollary713TargetVector t E
  have horthogonal := corollary713TargetVector_iIsOrtho t E
  have hself : ∀ i, (q.orthogonalSum r).bilin (family i) (family i) ≠ 0 := by
    intro i
    change (q.orthogonalSum r).quadratic
      (corollary713TargetVector t E i) ≠ 0
    by_cases hi : i.val < s + 1
    · rw [corollary713TargetVector_local t E i hi,
        quadratic_corollary713EmbedLocal]
      rw [E.bong.toBONG.quadratic_ambientVector]
      exact E.bong.toBONG.value_ne_zero ⟨i.val, hi⟩
    · have hi' : s + 1 ≤ i.val := Nat.le_of_not_gt hi
      rw [corollary713TargetVector_suffix t E i hi',
        QuadraticSpace.orthogonalSum_quadratic_apply]
      simp only [q.quadratic_zero, zero_add]
      rw [t.toBONG.quadratic_ambientVector]
      exact t.toBONG.value_ne_zero ⟨i.val - s, by omega⟩
  have hlinear : LinearIndependent K family :=
    LinearMap.BilinForm.linearIndependent_of_iIsOrtho horthogonal hself
  have hcard : Fintype.card (Fin ((m + 1) + s)) =
      Module.finrank K (V × W) := by
    rw [Fintype.card_fin, Module.finrank_prod]
    have hj := j.toBONG.length_eq_finrank
    have ht := t.toBONG.length_eq_finrank
    omega
  exact basisOfLinearIndependentOfCardEqFinrank' family hlinear hcard

@[simp] theorem corollary713TargetBasis_apply
    (t : GoodBONG r T (m + 1))
    (E : Corollary713LocalRealization
      (s := s) (j := j) (x := t.corollary713Head) R)
    (i : Fin ((m + 1) + s)) :
    corollary713TargetBasis t E i = corollary713TargetVector t E i := by
  simp [corollary713TargetBasis]

noncomputable def corollary713OrthogonalBasisData
    (t : GoodBONG r T (m + 1))
    (E : Corollary713LocalRealization
      (s := s) (j := j) (x := t.corollary713Head) R) :
    OrthogonalBasisData (q.orthogonalSum r) ((m + 1) + s) where
  basis := corollary713TargetBasis t E
  orthogonal := by
    rw [LinearMap.BilinForm.iIsOrtho_def]
    intro i k hik
    rw [corollary713TargetBasis_apply, corollary713TargetBasis_apply]
    exact (LinearMap.BilinForm.iIsOrtho_def.mp
      (corollary713TargetVector_iIsOrtho t E)) i k hik

@[simp] theorem corollary713Head_valueUnit
    (t : GoodBONG r T (m + 1)) :
    (t.corollary713Head).valueUnit 0 = t.valueUnit 0 := by
  change (t.corollary713HeadSegment).bong.valueUnit 0 = _
  rw [BONG.SegmentWitness.valueUnit_eq]
  congr 1

@[simp] theorem corollary713Head_order
    (t : GoodBONG r T (m + 1)) :
    (t.corollary713Head).order 0 = t.order 0 := by
  change (t.corollary713HeadSegment).bong.order 0 = _
  rw [BONG.SegmentWitness.order_eq]
  congr 1

@[simp] theorem corollary713OrthogonalBasisData_valueUnit_local
    (t : GoodBONG r T (m + 1))
    (E : Corollary713LocalRealization
      (s := s) (j := j) (x := t.corollary713Head) R)
    (i : Fin ((m + 1) + s)) (hi : i.val < s + 1) :
    (corollary713OrthogonalBasisData t E).valueUnit i =
      E.bong.valueUnit ⟨i.val, hi⟩ := by
  apply Units.ext
  change (q.orthogonalSum r).quadratic
      (corollary713TargetBasis t E i) =
    ((E.bong.valueUnit ⟨i.val, hi⟩ : Kˣ) : K)
  rw [corollary713TargetBasis_apply,
    corollary713TargetVector_local t E i hi,
    quadratic_corollary713EmbedLocal,
    E.bong.toBONG.quadratic_ambientVector]
  rfl

@[simp] theorem corollary713OrthogonalBasisData_valueUnit_suffix
    (t : GoodBONG r T (m + 1))
    (E : Corollary713LocalRealization
      (s := s) (j := j) (x := t.corollary713Head) R)
    (i : Fin ((m + 1) + s)) (hi : s + 1 ≤ i.val) :
    (corollary713OrthogonalBasisData t E).valueUnit i =
      t.valueUnit ⟨i.val - s, by omega⟩ := by
  apply Units.ext
  change (q.orthogonalSum r).quadratic
      (corollary713TargetBasis t E i) =
    ((t.valueUnit ⟨i.val - s, by omega⟩ : Kˣ) : K)
  rw [corollary713TargetBasis_apply,
    corollary713TargetVector_suffix t E i hi,
    QuadraticSpace.orthogonalSum_quadratic_apply,
    q.quadratic_zero, zero_add,
    t.toBONG.quadratic_ambientVector]
  rfl

theorem corollary713OrthogonalBasisData_order_local
    (t : GoodBONG r T (m + 1))
    (E : Corollary713LocalRealization
      (s := s) (j := j) (x := t.corollary713Head) R)
    (i : Fin ((m + 1) + s)) (hi : i.val < s + 1) :
    (corollary713OrthogonalBasisData t E).order i =
      E.bong.order ⟨i.val, hi⟩ := by
  unfold OrthogonalBasisData.order GoodBONG.order
  rw [corollary713OrthogonalBasisData_valueUnit_local]
  exact (E.bong.toBONG.order_eq_ordUnit ⟨i.val, hi⟩).symm

theorem corollary713OrthogonalBasisData_valueUnit_right
    (t : GoodBONG r T (m + 1))
    (E : Corollary713LocalRealization
      (s := s) (j := j) (x := t.corollary713Head) R)
    (i : Fin ((m + 1) + s)) (hi : s ≤ i.val) :
    (corollary713OrthogonalBasisData t E).valueUnit i =
      t.valueUnit ⟨i.val - s, by omega⟩ := by
  by_cases his : i.val = s
  · have hilocal : i.val < s + 1 := by omega
    rw [corollary713OrthogonalBasisData_valueUnit_local t E i hilocal]
    have hidxE : (⟨i.val, hilocal⟩ : Fin (s + 1)) =
        ⟨s, by omega⟩ := Fin.ext his
    have hidxT : (⟨i.val - s, by omega⟩ : Fin (m + 1)) = 0 := by
      apply Fin.ext
      simp [his]
    rw [hidxE, hidxT, E.valueUnit_last,
      corollary713Head_valueUnit]
  · have hisuffix : s + 1 ≤ i.val := by omega
    exact corollary713OrthogonalBasisData_valueUnit_suffix t E i hisuffix

theorem corollary713OrthogonalBasisData_order_right
    (t : GoodBONG r T (m + 1))
    (E : Corollary713LocalRealization
      (s := s) (j := j) (x := t.corollary713Head) R)
    (i : Fin ((m + 1) + s)) (hi : s ≤ i.val) :
    (corollary713OrthogonalBasisData t E).order i =
      t.order ⟨i.val - s, by omega⟩ := by
  unfold OrthogonalBasisData.order GoodBONG.order
  rw [corollary713OrthogonalBasisData_valueUnit_right t E i hi]
  exact (t.toBONG.order_eq_ordUnit ⟨i.val - s, by omega⟩).symm

theorem corollary713OrthogonalBasisData_satisfiesCriteria
    (t : GoodBONG r T (m + 1))
    (E : Corollary713LocalRealization
      (s := s) (j := j) (x := t.corollary713Head) R)
    (hsEven : Even s)
    (hsecond : ∀ hm : 0 < m,
      R - 2 * (ramificationIndex K : Int) + 2 ≤
        t.order ⟨1, by omega⟩) :
    (corollary713OrthogonalBasisData t E).SatisfiesGoodBONGCriteria := by
  constructor
  · intro i hi
    let k : Fin ((m + 1) + s) := ⟨i.val + 2, hi⟩
    by_cases hlocal : i.val + 2 < s + 1
    · rw [corollary713OrthogonalBasisData_order_local t E i (by omega),
        corollary713OrthogonalBasisData_order_local t E k hlocal]
      exact E.bong.good ⟨i.val, by omega⟩ (by omega)
    by_cases hright : s ≤ i.val
    · let ii : Fin (m + 1) := ⟨i.val - s, by omega⟩
      let kk : Fin (m + 1) := ⟨k.val - s, by
        dsimp only [k]
        omega⟩
      have hkRight : s ≤ k.val := by
        dsimp only [k]
        omega
      rw [corollary713OrthogonalBasisData_order_right t E i hright,
        corollary713OrthogonalBasisData_order_right t E k hkRight]
      change t.order ii ≤ t.order kk
      have hii : ii.val + 2 < m + 1 := by
        dsimp only [ii]
        omega
      have hkk : (⟨ii.val + 2, hii⟩ : Fin (m + 1)) = kk := by
        apply Fin.ext
        dsimp only [ii, kk, k]
        omega
      rw [← hkk]
      exact t.good ii hii
    · have his : i.val = s - 1 := by omega
      have hsPos : 0 < s := by omega
      have hm : 0 < m := by omega
      have hkRight : s ≤ k.val := by
        dsimp only [k]
        omega
      rw [corollary713OrthogonalBasisData_order_local t E i (by omega),
        corollary713OrthogonalBasisData_order_right t E k hkRight]
      have hiE : (⟨i.val, by omega⟩ : Fin (s + 1)) =
          ⟨s - 1, by omega⟩ := Fin.ext his
      have hkT : (⟨k.val - s, by omega⟩ : Fin (m + 1)) =
          ⟨1, by omega⟩ := by
        apply Fin.ext
        dsimp only [k]
        omega
      rw [hiE, hkT]
      change ordUnit K (E.bong.valueUnit ⟨s - 1, by omega⟩) ≤
        t.order ⟨1, by omega⟩
      rw [E.valueUnit_prefix ⟨s - 1, by omega⟩]
      have hsOdd : Odd (s - 1) := by
        rcases hsEven with ⟨a, ha⟩
        exact ⟨a - 1, by omega⟩
      rw [corollary713PrefixValues_eq_low R ⟨s - 1, by omega⟩
        (Nat.not_even_iff_odd.mpr hsOdd)]
      rw [ordUnit_corollary713Low]
      exact hsecond hm
  · intro i hi
    unfold OrthogonalBasisData.adjacentParameter
    by_cases hlocal : i.val < s
    · have hi0 : i.val < s + 1 := by omega
      have hi1 : i.val + 1 < s + 1 := by omega
      rw [corollary713OrthogonalBasisData_valueUnit_local t E i hi0,
        corollary713OrthogonalBasisData_valueUnit_local t E
          ⟨i.val + 1, hi⟩ hi1]
      exact E.bong.toBONG.adjacentParameter_isBinaryParameterAdmissible
        ⟨i.val, by omega⟩ (by omega)
    · have hright : s ≤ i.val := Nat.le_of_not_gt hlocal
      have hright1 : s ≤ i.val + 1 := by omega
      let ii : Fin (m + 1) := ⟨i.val - s, by omega⟩
      let next : Fin (m + 1) := ⟨i.val + 1 - s, by omega⟩
      rw [corollary713OrthogonalBasisData_valueUnit_right t E i hright,
        corollary713OrthogonalBasisData_valueUnit_right t E
          ⟨i.val + 1, hi⟩ hright1]
      change IsBinaryParameterAdmissible (t.valueUnit next / t.valueUnit ii)
      have hii : ii.val + 1 < m + 1 := by
        dsimp only [ii]
        omega
      have hnext : (⟨ii.val + 1, hii⟩ : Fin (m + 1)) = next := by
        apply Fin.ext
        dsimp only [ii, next]
        omega
      rw [← hnext]
      exact t.toBONG.adjacentParameter_isBinaryParameterAdmissible ii hii

theorem exists_corollary713Candidate
    [BeliLemma43ConstructionLaws.{u, max v w} K]
    [Beli2006SectionTwoLaws.{u, max v w} K]
    (t : GoodBONG r T (m + 1))
    (E : Corollary713LocalRealization
      (s := s) (j := j) (x := t.corollary713Head) R)
    (hsEven : Even s)
    (hsecond : ∀ hm : 0 < m,
      R - 2 * (ramificationIndex K : Int) + 2 ≤
        t.order ⟨1, by omega⟩) :
    ∃ (N : Lattice K (V × W))
        (target : GoodBONG (q.orthogonalSum r) N ((m + 1) + s)),
      (∀ i, target.valueUnit i =
        (corollary713OrthogonalBasisData t E).valueUnit i) ∧
      ∀ i, target.toBONG.ambientVector i =
        corollary713TargetVector t E i := by
  let X := corollary713OrthogonalBasisData t E
  have hcriteria : X.SatisfiesGoodBONGCriteria :=
    corollary713OrthogonalBasisData_satisfiesCriteria t E hsEven hsecond
  rcases (X.hasGoodRealization_iff_beli2006Criteria).2 hcriteria with
    ⟨N, raw, hreal, hgood⟩
  let target : GoodBONG (q.orthogonalSum r) N ((m + 1) + s) :=
    ⟨raw, hgood⟩
  refine ⟨N, target, ?_, ?_⟩
  · intro i
    apply Units.ext
    change raw.value i = ((X.valueUnit i : Kˣ) : K)
    rw [← X.value_eq_of_isRealizedBy hreal i]
    rfl
  · intro i
    calc
      target.toBONG.ambientVector i = X.basis i := hreal i
      _ = corollary713TargetVector t E i := by
        exact corollary713TargetBasis_apply t E i

theorem corollary713Target_reverseDualVector_suffix
    {N : Lattice K (V × W)}
    (t : GoodBONG r T (m + 1))
    (E : Corollary713LocalRealization
      (s := s) (j := j) (x := t.corollary713Head) R)
    (target : GoodBONG (q.orthogonalSum r) N ((m + 1) + s))
    (htarget : ∀ i, target.toBONG.ambientVector i =
      corollary713TargetVector t E i)
    (i : Fin m) :
    target.toBONG.reverseDualVector
        ⟨i.val, by omega⟩ =
      (0, t.toBONG.reverseDualVector ⟨i.val, by omega⟩) := by
  let targetIndex : Fin ((m + 1) + s) := ⟨i.val, by omega⟩
  let tIndex : Fin (m + 1) := ⟨i.val, by omega⟩
  let targetRev : Fin ((m + 1) + s) := Fin.rev targetIndex
  let tRev : Fin (m + 1) := Fin.rev tIndex
  have htargetRev : s + 1 ≤ targetRev.val := by
    dsimp only [targetRev, targetIndex, Fin.rev]
    omega
  have hsource : (⟨targetRev.val - s, by omega⟩ : Fin (m + 1)) =
      tRev := by
    apply Fin.ext
    dsimp only [targetRev, targetIndex, tRev, tIndex, Fin.rev]
    omega
  have hv : target.toBONG.ambientVector targetRev =
      (0, t.toBONG.ambientVector tRev) := by
    rw [htarget targetRev,
      corollary713TargetVector_suffix t E targetRev htargetRev,
      hsource]
  have hunit : target.valueUnit targetRev = t.valueUnit tRev := by
    apply Units.ext
    change target.toBONG.value targetRev = t.toBONG.value tRev
    rw [← target.toBONG.quadratic_ambientVector targetRev,
      ← t.toBONG.quadratic_ambientVector tRev, hv]
    simp [QuadraticSpace.orthogonalSum_quadratic_apply]
  change target.toBONG.reverseDualVector targetIndex =
    (0, t.toBONG.reverseDualVector tIndex)
  simp only [BONG.reverseDualVector, BONG.dualVector]
  change ((target.valueUnit targetRev)⁻¹ : K) •
      target.toBONG.ambientVector targetRev =
    (0, ((t.valueUnit tRev)⁻¹ : K) • t.toBONG.ambientVector tRev)
  rw [hv, hunit]
  simp

theorem corollary713Target_reverseDualVector_local
    {N : Lattice K (V × W)}
    (t : GoodBONG r T (m + 1))
    (E : Corollary713LocalRealization
      (s := s) (j := j) (x := t.corollary713Head) R)
    (target : GoodBONG (q.orthogonalSum r) N ((m + 1) + s))
    (htarget : ∀ i, target.toBONG.ambientVector i =
      corollary713TargetVector t E i)
    (a : Fin (s + 1)) :
    target.toBONG.reverseDualVector
        ⟨m + a.val, by omega⟩ =
      corollary713EmbedLocal (V := V) t
        (E.bong.toBONG.reverseDualVector a) := by
  let targetIndex : Fin ((m + 1) + s) := ⟨m + a.val, by omega⟩
  let localRev : Fin (s + 1) := Fin.rev a
  let targetRev : Fin ((m + 1) + s) := Fin.rev targetIndex
  have htargetRev : targetRev.val < s + 1 := by
    dsimp only [targetRev, targetIndex, Fin.rev]
    omega
  have hsource : (⟨targetRev.val, htargetRev⟩ : Fin (s + 1)) =
      localRev := by
    apply Fin.ext
    dsimp only [targetRev, targetIndex, localRev, Fin.rev]
    omega
  have hv : target.toBONG.ambientVector targetRev =
      corollary713EmbedLocal (V := V) t
        (E.bong.toBONG.ambientVector localRev) := by
    rw [htarget targetRev,
      corollary713TargetVector_local t E targetRev htargetRev,
      hsource]
  have hunit : target.valueUnit targetRev = E.bong.valueUnit localRev := by
    apply Units.ext
    change target.toBONG.value targetRev = E.bong.toBONG.value localRev
    rw [← target.toBONG.quadratic_ambientVector targetRev,
      ← E.bong.toBONG.quadratic_ambientVector localRev, hv,
      quadratic_corollary713EmbedLocal]
  change target.toBONG.reverseDualVector targetIndex =
    corollary713EmbedLocal (V := V) t
      (E.bong.toBONG.reverseDualVector a)
  simp only [BONG.reverseDualVector, BONG.dualVector]
  change ((target.valueUnit targetRev)⁻¹ : K) •
      target.toBONG.ambientVector targetRev =
    corollary713EmbedLocal (V := V) t
      (((E.bong.valueUnit localRev)⁻¹ : K) •
        E.bong.toBONG.ambientVector localRev)
  rw [hv, hunit, LinearMap.map_smul]

theorem corollary713Value_eq_inv_reverse_of_ambientVector_eq
    {X : Type z} [AddCommGroup X] [Module K X]
    {form : QuadraticSpace K X} {L LD : Lattice K X}
    {length : Nat}
    (source : BONG X form L length)
    (dual : BONG X form LD length)
    (vectors : ∀ i, dual.ambientVector i = source.reverseDualVector i)
    (i : Fin length) :
    dual.value i = ((source.valueUnit (Fin.rev i))⁻¹ : K) := by
  rw [← dual.quadratic_ambientVector i, vectors i,
    source.quadratic_reverseDualVector]

theorem corollary713Order_eq_neg_reverse_of_ambientVector_eq
    {X : Type z} [AddCommGroup X] [Module K X]
    {form : QuadraticSpace K X} {L LD : Lattice K X}
    {length : Nat}
    (source : BONG X form L length)
    (dual : GoodBONG form LD length)
    (vectors : ∀ i, dual.toBONG.ambientVector i =
      source.reverseDualVector i)
    (i : Fin length) :
    dual.order i = -source.order (Fin.rev i) := by
  change dual.toBONG.order i = -source.order (Fin.rev i)
  apply WithTop.coe_injective
  rw [BONG.coe_order, ← dual.toBONG.quadratic_ambientVector i,
    vectors i, source.ord_quadratic_reverseDualVector]

theorem corollary713Candidate_lattice_eq_product
    [lawsV : BONGReverseDualLaws.{u, v} K]
    [lawsW : BONGReverseDualLaws.{u, w} K]
    [lawsProduct : BONGReverseDualLaws.{u, max v w} K]
    {N : Lattice K (V × W)}
    (j : GoodBONG q J s) (t : GoodBONG r T (m + 1))
    (E : Corollary713LocalRealization j t.corollary713Head R)
    (hsTwo : 2 ≤ s)
    (hlast : ∀ hm : 0 < m,
      j.order ⟨s - 1, by omega⟩ ≤ t.order ⟨1, by omega⟩)
    (target : GoodBONG (q.orthogonalSum r) N ((m + 1) + s))
    (htarget : ∀ i, target.toBONG.ambientVector i =
      corollary713TargetVector t E i) :
    N = Lattice.product J T := by
  rcases (@BONG.GoodBONG.exists_reverseDual.{u, w}
      K _ _ _ _ _ W _ _ r T _ lawsW t) with ⟨tDual, htDual⟩
  rcases (@BONG.GoodBONG.exists_reverseDual.{u, w}
      K _ _ _ _ _ _ _ _ _ _ _ lawsW t.corollary713Head) with
    ⟨headDual, hheadDual⟩
  rcases (@BONG.GoodBONG.exists_reverseDual.{u, v}
      K _ _ _ _ _ V _ _ q J _ lawsV j) with ⟨jDual, hjDual⟩
  rcases (@BONG.GoodBONG.exists_reverseDual.{u, max v w}
      K _ _ _ _ _ _ _ _ _ _ _ lawsProduct E.bong) with
    ⟨blockDual, hblockDual⟩
  rcases target.exists_swappedReverseDual_with_values with
    ⟨targetDual, htargetDual, _, _⟩
  have hlastValue : tDual.toBONG.value ⟨m, by omega⟩ =
      headDual.toBONG.value 0 := by
    rw [corollary713Value_eq_inv_reverse_of_ambientVector_eq
        t.toBONG tDual.toBONG htDual,
      corollary713Value_eq_inv_reverse_of_ambientVector_eq
        t.corollary713Head.toBONG headDual.toBONG hheadDual]
    have htIndex : Fin.rev (⟨m, by omega⟩ : Fin (m + 1)) = 0 := by
      apply Fin.ext
      simp [Fin.rev]
    have hheadIndex : Fin.rev (0 : Fin 1) = 0 := Subsingleton.elim _ _
    rw [htIndex, hheadIndex]
    have hunit : (t.toBONG.valueUnit 0 : K) =
        (t.corollary713Head.toBONG.valueUnit 0 : K) := by
      exact congrArg Units.val (corollary713Head_valueUnit t).symm
    rw [hunit]
  let seed := BONG.arbitraryReverseDualProductPrefixSeed
    tDual.toBONG headDual.toBONG jDual.toBONG blockDual.toBONG hlastValue
  have hterminal : ∀ z : (t.corollary713HeadSegment).carrier,
      BONG.arbitraryReverseDualProductTerminalEmbedding
          tDual.toBONG headDual.toBONG jDual.toBONG blockDual.toBONG
          hlastValue z = (z : W) := by
    let terminal := BONG.arbitraryReverseDualProductTerminalEmbedding
      tDual.toBONG headDual.toBONG jDual.toBONG blockDual.toBONG hlastValue
    have hmaps : terminal = (t.corollary713HeadSegment).carrier.subtype := by
      apply Module.Basis.ext headDual.toBONG.basis
      intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      change terminal (headDual.toBONG.ambientVector 0) =
        ((headDual.toBONG.ambientVector 0 :
          (t.corollary713HeadSegment).carrier) : W)
      rw [show terminal = BONG.arbitraryReverseDualProductTerminalEmbedding
          tDual.toBONG headDual.toBONG jDual.toBONG blockDual.toBONG
          hlastValue by rfl,
        BONG.arbitraryReverseDualProductTerminalEmbedding_ambientVector,
        htDual ⟨m, by omega⟩, hheadDual 0]
      have hsegment :=
        BONG.SegmentWitness.coe_reverseDualVector_prefix_eq
          (m := 0) (start := 0) (dualStart := 0)
          (n := m + 1) (length := 1) (b := t.toBONG)
          t.corollary713HeadSegment (0 : Fin 1)
      have hidx :
          (⟨m + 1 - 1 + (0 : Fin 1).val, by omega⟩ : Fin (m + 1)) =
            ⟨m, by omega⟩ := by
        apply Fin.ext
        simp
      rw [hidx] at hsegment
      exact hsegment.symm
    intro z
    change terminal z = (z : W)
    exact DFunLike.congr_fun hmaps z
  have hendpoint : ∀ hm : 0 < m,
      tDual.order ⟨m - 1, by omega⟩ ≤
        jDual.order ⟨0, by omega⟩ := by
    intro hm
    let ti : Fin (m + 1) := ⟨m - 1, by omega⟩
    let ji : Fin s := ⟨0, by omega⟩
    have htRev : Fin.rev ti = (⟨1, by omega⟩ : Fin (m + 1)) := by
      apply Fin.ext
      dsimp only [ti, Fin.rev]
      omega
    have hjRev : Fin.rev ji = (⟨s - 1, by omega⟩ : Fin s) := by
      apply Fin.ext
      dsimp only [ji, Fin.rev]
    calc
      tDual.order ti = -t.order (Fin.rev ti) :=
        corollary713Order_eq_neg_reverse_of_ambientVector_eq
          t.toBONG tDual htDual ti
      _ = -t.order ⟨1, by omega⟩ := by rw [htRev]
      _ ≤ -j.order ⟨s - 1, by omega⟩ := by
        have := hlast hm
        omega
      _ = jDual.order ji := by
        symm
        rw [corollary713Order_eq_neg_reverse_of_ambientVector_eq
          j.toBONG jDual hjDual ji, hjRev]
        rfl
  have hleftLength : s = (s - 1) + 1 := by omega
  let leftDual := jDual.castLength hleftLength
  let targetDual' := targetDual.castLength
    (show (m + 1) + s = (s + 1) + m by omega)
  have hleftVectors : ∀ i : Fin m,
      targetDual'.toBONG.ambientVector
          (BONG.orthogonalProductLeftIndex (s + 1) i) =
        (tDual.toBONG.ambientVector (seed.sourceIndex i), 0) := by
    intro i
    rw [BONG.GoodBONG.ambientVector_castLength]
    change targetDual.toBONG.ambientVector ⟨i.val, by omega⟩ = _
    rw [htargetDual]
    change (target.toBONG.reverseDualVector ⟨i.val, by omega⟩).swap = _
    rw [corollary713Target_reverseDualVector_suffix t E target htarget i]
    have hsource : seed.sourceIndex i =
        (⟨i.val, by omega⟩ : Fin (m + 1)) := by
      apply Fin.ext
      rfl
    rw [hsource, ← htDual]
    rfl
  have hrightVectors : ∀ a : Fin (s + 1),
      targetDual'.toBONG.ambientVector
          (BONG.orthogonalProductRightIndex m a) =
        seed.baseAmbientVector a := by
    intro a
    rw [BONG.GoodBONG.ambientVector_castLength]
    change targetDual.toBONG.ambientVector ⟨m + a.val, by omega⟩ = _
    rw [htargetDual]
    change (target.toBONG.reverseDualVector
      ⟨m + a.val, by omega⟩).swap = _
    rw [corollary713Target_reverseDualVector_local t E target htarget a]
    rw [show seed = BONG.arbitraryReverseDualProductPrefixSeed
        tDual.toBONG headDual.toBONG jDual.toBONG blockDual.toBONG
        hlastValue by rfl,
      BONG.arbitraryReverseDualProductPrefixSeed_baseAmbientVector,
      hblockDual a, hterminal]
    rfl
  have hleftOrder :
      leftDual.toBONG.order (0 : Fin ((s - 1) + 1)) =
        jDual.order ⟨0, by omega⟩ := by
    change (jDual.castLength hleftLength).order 0 = _
    exact BONG.GoodBONG.order_castLength jDual hleftLength 0
  apply tDual.beli2019Lemma710SwappedDualRightEnd_steps_of_good
    (q := q) (r := r) (L := J) (M := T)
    (steps := m) (baseTail := s) (dualRightLength := s - 1)
    (by omega) leftDual.toBONG
    seed (fun hm => by
      rw [hleftOrder]
      exact hendpoint hm)
    targetDual' hleftVectors hrightVectors

end BONG.GoodBONG

end Bong
