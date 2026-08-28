/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.AsymmetricBinaryModular
import Bong.Lattice.ModularPrimitivePairing

/-!
# Beli (2019), Lemma 5.1: the adapted modular block

This file formalizes the geometric core of Lemma 5.1.  Starting from a
primitive vector `x` of a lattice `L`, it recursively removes minimal-scale
modular components on which the projection of `x` is divisible by the
uniformizer.  The ambient dimension strictly decreases at every recursive
call.  At the first primitive projection, O'Meara 82:14a and 91C produce a
unary or binary modular block containing a representative congruent to `x`
modulo `πL`.

The result also records the mixed-pairing condition needed by O'Meara 82:15,
so the block splits the original lattice without any additional law instance.
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

namespace Lattice

variable {q : QuadraticSpace K V} {L : Lattice K V} {x : V}

/-- The unary or binary modular block selected in the proof of Beli's
Lemma 5.1.  The first vector is congruent to the prescribed primitive vector
modulo `πL`. -/
inductive Beli2019Lemma51BlockData
    (q : QuadraticSpace K V) (L : Lattice K V) (x : V) : Type (max u v)
  | unary
      (z : V)
      (mem : z ∈ L)
      (congruent : x - z ∈ rescale (uniformizerUnit K) L)
      (anisotropic : q.IsAnisotropic z)
      (pairing : ∀ w : V, w ∈ L →
        q.bilin z w ∈ principalIdeal (K := K) (q.quadratic z))
  | binary
      (z y : V)
      (mem_left : z ∈ L)
      (mem_right : y ∈ L)
      (congruent : x - z ∈ rescale (uniformizerUnit K) L)
      (mixed_ne : q.bilin z y ≠ 0)
      (left_strict : ord K (q.bilin z y) < ord K (q.quadratic z))
      (right_weak : ord K (q.bilin z y) ≤ ord K (q.quadratic y))
      (pairing_left : ∀ w : V, w ∈ L →
        q.bilin z w ∈ principalIdeal (K := K) (q.bilin z y))
      (pairing_right : ∀ w : V, w ∈ L →
        q.bilin y w ∈ principalIdeal (K := K) (q.bilin z y))

namespace Beli2019Lemma51BlockData

/-- The representative of the original primitive class carried by the block. -/
def representative (D : Beli2019Lemma51BlockData q L x) : V :=
  match D with
  | .unary z _ _ _ _ => z
  | .binary z _ _ _ _ _ _ _ _ _ => z

/-- Whether the selected modular block is the unary branch. -/
def IsUnary (D : Beli2019Lemma51BlockData q L x) : Prop :=
  match D with
  | .unary _ _ _ _ _ => True
  | .binary _ _ _ _ _ _ _ _ _ _ => False

/-- Whether the selected modular block is the binary branch. -/
def IsBinary (D : Beli2019Lemma51BlockData q L x) : Prop :=
  match D with
  | .unary _ _ _ _ _ => False
  | .binary _ _ _ _ _ _ _ _ _ _ => True

/-- The block constructor exhausts the two alternatives occurring in
Beli's Lemma 5.1. -/
theorem isUnary_or_isBinary (D : Beli2019Lemma51BlockData q L x) :
    D.IsUnary ∨ D.IsBinary := by
  cases D <;> simp [IsUnary, IsBinary]

@[simp]
theorem isUnary_unary (z : V) (hz : z ∈ L)
    (hcongruent : x - z ∈ rescale (uniformizerUnit K) L)
    (hanisotropic : q.IsAnisotropic z)
    (hpair : ∀ w : V, w ∈ L →
      q.bilin z w ∈ principalIdeal (K := K) (q.quadratic z)) :
    (Beli2019Lemma51BlockData.unary z hz hcongruent hanisotropic hpair).IsUnary :=
  trivial

@[simp]
theorem not_isUnary_binary (z y : V) (hz : z ∈ L) (hy : y ∈ L)
    (hcongruent : x - z ∈ rescale (uniformizerUnit K) L)
    (hzy : q.bilin z y ≠ 0)
    (hleft : ord K (q.bilin z y) < ord K (q.quadratic z))
    (hright : ord K (q.bilin z y) ≤ ord K (q.quadratic y))
    (hpairZ : ∀ w : V, w ∈ L →
      q.bilin z w ∈ principalIdeal (K := K) (q.bilin z y))
    (hpairY : ∀ w : V, w ∈ L →
      q.bilin y w ∈ principalIdeal (K := K) (q.bilin z y)) :
    ¬(Beli2019Lemma51BlockData.binary z y hz hy hcongruent hzy
      hleft hright hpairZ hpairY).IsUnary := by
  simp [IsUnary]

/-- The representative belongs to the ambient lattice. -/
theorem representative_mem (D : Beli2019Lemma51BlockData q L x) :
    D.representative ∈ L := by
  cases D with
  | unary _ hz _ _ _ => exact hz
  | binary _ _ hz _ _ _ _ _ _ _ => exact hz

/-- The representative differs from the prescribed vector by an element of
`πL`. -/
theorem sub_representative_mem_rescale
    (D : Beli2019Lemma51BlockData q L x) :
    x - D.representative ∈ rescale (uniformizerUnit K) L := by
  cases D with
  | unary _ _ hcongruent _ _ => exact hcongruent
  | binary _ _ _ _ hcongruent _ _ _ _ _ => exact hcongruent

/-- The modular quadratic sublattice underlying the selected block. -/
noncomputable def component (D : Beli2019Lemma51BlockData q L x) :
    QuadraticSublattice q :=
  match D with
  | .unary z _ _ hz _ => unaryScaleComponent (q := q) z hz
  | .binary z y _ _ _ hzy hz hy _ _ =>
      asymmetricBinaryScaleComponent (q := q) hzy hz hy

/-- The chosen generator of the block scale. -/
noncomputable def scaleGenerator (D : Beli2019Lemma51BlockData q L x) : Kˣ :=
  match D with
  | .unary z _ _ hz _ => Units.mk0 (q.quadratic z) hz
  | .binary z y _ _ _ hzy _ _ _ _ => Units.mk0 (q.bilin z y) hzy

/-- The selected block has rank one or two. -/
theorem component_rank_one_or_two (D : Beli2019Lemma51BlockData q L x) :
    finrank K D.component.carrier = 1 ∨ finrank K D.component.carrier = 2 := by
  cases D with
  | unary z _ _ hz _ =>
      left
      change finrank K (K ∙ z) = 1
      simpa using Module.finrank_eq_card_basis
        (unarySpanBasis (K := K) z hz.ne_zero)
  | binary z y _ _ _ hzy hz hy _ _ =>
      right
      change finrank K (BONG.binaryPairSpan (K := K) z y) = 2
      simpa using Module.finrank_eq_card_basis
        (BONG.binaryPairBasis (K := K) z y
          (binaryPair_linearIndependent_of_left_strict hzy hz hy))

/-- The selected block is contained in the ambient lattice. -/
theorem component_contained (D : Beli2019Lemma51BlockData q L x) :
    D.component.ambientSubmodule ≤ L.toSubmodule := by
  cases D with
  | unary z hz _ hanisotropic _ =>
      exact unaryScaleComponent_ambientSubmodule_le hanisotropic hz
  | binary z y hz hy _ hzy hleft hright _ _ =>
      exact asymmetricBinaryScaleComponent_ambientSubmodule_le
        hzy hleft hright hz hy

/-- The selected block is modular at its chosen scale. -/
theorem component_modular (D : Beli2019Lemma51BlockData q L x) :
    IsModular D.component.space D.component.lattice D.scaleGenerator := by
  cases D with
  | unary _ _ _ hz _ => exact unaryScaleComponent_isModular hz
  | binary _ _ _ _ _ hzy hz hy _ _ =>
      exact asymmetricBinaryScaleComponent_isModular hzy hz hy

private theorem pairing_basisSpan_of_pairing_basis
    {P : Submodule K V} (_hP : (q.bilin.restrict P).Nondegenerate)
    {ι : Type*} [Finite ι] (b : Basis ι K P) (a : Kˣ)
    (hpair : ∀ i, ∀ w : V, w ∈ L →
      q.bilin (b i : V) w ∈ principalIdeal (K := K) (a : K))
    (y : P) (hy : y ∈ basisLattice b) (w : V) (hw : w ∈ L) :
    q.bilin (y : V) w ∈ principalIdeal (K := K) (a : K) := by
  change y ∈ Submodule.span (IntegerRing K) (Set.range b) at hy
  refine Submodule.span_induction (R := IntegerRing K) (M := P)
    (s := Set.range b)
    (p := fun y _ ↦ q.bilin (y : V) w ∈
      principalIdeal (K := K) (a : K)) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨i, rfl⟩
    exact hpair i w hw
  · simp
  · intro y z _ _ hy hz
    simpa only [Submodule.coe_add, LinearMap.BilinForm.add_left] using
      (principalIdeal (K := K) (a : K)).add_mem hy hz
  · intro c y _ hy
    have hmem := (principalIdeal (K := K) (a : K)).smul_mem c hy
    rw [← IsScalarTower.algebraMap_smul K c y,
      Submodule.coe_smul_of_tower, LinearMap.BilinForm.smul_left]
    simpa only [Algebra.smul_def] using hmem

/-- Every mixed pairing between the selected block and the ambient lattice
is divisible by the block scale. -/
theorem component_pairing
    (D : Beli2019Lemma51BlockData q L x)
    (y : D.component.carrier) (hy : y ∈ D.component.lattice)
    (w : V) (hw : w ∈ L) :
    q.bilin (y : V) w ∈
      principalIdeal (K := K) (D.scaleGenerator : K) := by
  cases D with
  | unary z hz hcongruent hanisotropic hpair =>
      let b := unarySpanBasis (K := K) z hanisotropic.ne_zero
      change y ∈ basisLattice b at hy
      apply pairing_basisSpan_of_pairing_basis
        (unarySpan_restrict_nondegenerate hanisotropic) b
        (Units.mk0 (q.quadratic z) hanisotropic) _ y hy w hw
      intro i w hw
      change q.bilin (b i : V) w ∈
        principalIdeal (K := K) (q.quadratic z)
      simpa only [b, coe_unarySpanBasis] using hpair w hw
  | binary z t hz ht hcongruent hzt hleft hright hpairZ hpairT =>
      let hli := binaryPair_linearIndependent_of_left_strict hzt hleft hright
      let b := BONG.binaryPairBasis (K := K) z t hli
      change y ∈ basisLattice b at hy
      apply pairing_basisSpan_of_pairing_basis
        (binaryPair_restrict_nondegenerate_of_left_strict hzt hleft hright)
        b (Units.mk0 (q.bilin z t) hzt) _ y hy w hw
      intro i w hw
      rw [BONG.coe_binaryPairBasis]
      fin_cases i
      · exact hpairZ w hw
      · exact hpairT w hw

/-- O'Meara 82:15 splits the selected block from the original lattice. -/
noncomputable def splitting (D : Beli2019Lemma51BlockData q L x) :
    OrthogonalDecomposition q L 2 :=
  omearaModularSplitting D.component D.component_contained
    D.component_modular D.component_pairing

end Beli2019Lemma51BlockData

private theorem rescale_mem_of_subspace_rescale_mem
    {P : Submodule K V} {LP : Lattice K P} {z : P}
    (hLP : ∀ y : P, y ∈ LP → (y : V) ∈ L)
    (hz : z ∈ rescale (uniformizerUnit K) LP) :
    (z : V) ∈ rescale (uniformizerUnit K) L := by
  rw [mem_rescale_iff] at hz ⊢
  obtain ⟨y, hy, hzy⟩ := hz
  exact ⟨(y : V), hLP y hy, by simpa using congrArg Subtype.val hzy⟩

/-- The adapted block in Beli (2019), Lemma 5.1 exists for every primitive
vector.  The recursion is the constructive content of the Jordan-splitting
argument used in the paper. -/
noncomputable def beli2019Lemma51BlockData
    {W : Type v} [AddCommGroup W] [Module K W]
    (q : QuadraticSpace K W) (L : Lattice K W) (x : W)
    (hx : x ∈ L) (hprimitive : x ∉ rescale (uniformizerUnit K) L) :
    Beli2019Lemma51BlockData q L x := by
  letI : Module.Finite K W := L.moduleFinite
  have hxne : x ≠ 0 := by
    intro hzero
    apply hprimitive
    rw [hzero]
    exact (rescale (uniformizerUnit K) L).zero_mem
  have hpos : 0 < finrank K W :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨x, hxne⟩
  let hexists := exists_isScaleGenerator_of_finrank_pos q L hpos
  let s := Classical.choose hexists
  let t := Classical.choose (Classical.choose_spec hexists)
  have hgenerator : IsScaleGenerator q L s t :=
    (Classical.choose_spec (Classical.choose_spec hexists)).1
  have hst : q.bilin s t ≠ 0 :=
    (Classical.choose_spec (Classical.choose_spec hexists)).2
  let D := minimalScaleComponentDataOfScaleGenerator hgenerator hst
  let C := D.component
  have hpairC : ∀ y : C.carrier, y ∈ C.lattice →
      ∀ w : W, w ∈ L →
        q.bilin (y : W) w ∈
          principalIdeal (K := K) (D.scaleGenerator : K) := by
    intro y hy w hw
    exact D.ambientScale_le
      (bilin_mem_scaleIdeal_of_mem q L
        (D.contained ⟨y, hy, rfl⟩) hw)
  let p := C.carrierProjection x
  let z := C.orthogonalProjection x
  have hp : p ∈ C.lattice :=
    C.carrierProjection_mem_lattice_of_pairing D.modular hpairC hx
  have hz : (z : W) ∈ L :=
    C.orthogonalProjection_mem_lattice D.contained D.modular hpairC hx
  by_cases hpPrimitive : p ∉ rescale (uniformizerUnit K) C.lattice
  · let hexistsPair :=
      D.modular.exists_pairing_eq_of_not_mem_rescale hp hpPrimitive
    let y := Classical.choose hexistsPair
    have hy : y ∈ C.lattice := (Classical.choose_spec hexistsPair).1
    have hpy : C.space.bilin p y = (D.scaleGenerator : K) :=
      (Classical.choose_spec hexistsPair).2
    have hyL : (y : W) ∈ L := D.contained ⟨y, hy, rfl⟩
    have hxy : q.bilin x (y : W) = (D.scaleGenerator : K) := by
      have horth : q.bilin (z : W) (y : W) = 0 := by
        rw [q.isSymm.eq (z : W) (y : W)]
        exact z.property (y : W) y.property
      calc
        q.bilin x (y : W) =
            q.bilin ((p : W) + (z : W)) (y : W) := by
          rw [C.carrierProjection_add_orthogonalProjection]
        _ = q.bilin (p : W) (y : W) + q.bilin (z : W) (y : W) := by
          rw [LinearMap.BilinForm.add_left]
        _ = (D.scaleGenerator : K) := by
          change C.space.bilin p y + _ = _
          rw [hpy, horth, add_zero]
    have hscaleX : q.quadratic x ∈
        principalIdeal (K := K) (D.scaleGenerator : K) :=
      D.ambientScale_le (bilin_mem_scaleIdeal_of_mem q L hx hx)
    have horder : ord K (D.scaleGenerator : K) ≤ ord K (q.quadratic x) :=
      ord_le_of_mem_principalIdeal (Units.ne_zero D.scaleGenerator) hscaleX
    by_cases heq : ord K (D.scaleGenerator : K) = ord K (q.quadratic x)
    · have hxanisotropic : q.IsAnisotropic x := by
        intro hzero
        rw [hzero, ord_zero] at heq
        exact (ord_eq_top_iff K).not.mpr
          (Units.ne_zero D.scaleGenerator) heq
      refine .unary x hx (by simp) hxanisotropic ?_
      intro w hw
      have hmem := D.ambientScale_le
        (bilin_mem_scaleIdeal_of_mem q L hx hw)
      have hideal : principalIdeal (K := K) (q.quadratic x) =
          principalIdeal (K := K) (D.scaleGenerator : K) := by
        apply le_antisymm
        · exact (principalIdeal_le_iff_ord_ge hxanisotropic
            (Units.ne_zero D.scaleGenerator)).2 heq.le
        · exact (principalIdeal_le_iff_ord_ge
            (Units.ne_zero D.scaleGenerator) hxanisotropic).2 heq.ge
      rwa [hideal]
    · have hstrict : ord K (D.scaleGenerator : K) < ord K (q.quadratic x) :=
        lt_of_le_of_ne horder heq
      have hscaleY : q.quadratic (y : W) ∈
          principalIdeal (K := K) (D.scaleGenerator : K) :=
        D.ambientScale_le (bilin_mem_scaleIdeal_of_mem q L hyL hyL)
      have hweak : ord K (D.scaleGenerator : K) ≤
          ord K (q.quadratic (y : W)) :=
        ord_le_of_mem_principalIdeal (Units.ne_zero D.scaleGenerator) hscaleY
      have hxyne : q.bilin x (y : W) ≠ 0 := by
        rw [hxy]
        exact Units.ne_zero D.scaleGenerator
      refine .binary x (y : W) hx hyL (by simp) hxyne ?_ ?_ ?_ ?_
      · rwa [hxy]
      · rwa [hxy]
      · intro w hw
        rw [hxy]
        exact D.ambientScale_le (bilin_mem_scaleIdeal_of_mem q L hx hw)
      · intro w hw
        rw [hxy]
        exact D.ambientScale_le (bilin_mem_scaleIdeal_of_mem q L hyL hw)
  · push Not at hpPrimitive
    let O := C.orthogonalLattice D.contained D.modular hpairC
    have hzO : z ∈ O := by
      change (z : W) ∈ L
      exact hz
    have hzPrimitive : z ∉ rescale (uniformizerUnit K) O := by
      intro hzScaled
      apply hprimitive
      have hpScaled : (p : W) ∈ rescale (uniformizerUnit K) L :=
        rescale_mem_of_subspace_rescale_mem
          (fun y hy ↦ D.contained ⟨y, hy, rfl⟩) hpPrimitive
      have hzScaledAmbient : (z : W) ∈ rescale (uniformizerUnit K) L :=
        rescale_mem_of_subspace_rescale_mem
          (fun y hy ↦ show (y : W) ∈ L from hy) hzScaled
      have hsum := (rescale (uniformizerUnit K) L).add_mem
        hpScaled hzScaledAmbient
      rw [C.carrierProjection_add_orthogonalProjection] at hsum
      exact hsum
    let R := beli2019Lemma51BlockData
      (q.restrict C.orthogonalCarrier C.orthogonalCarrier_nondegenerate)
      O z hzO hzPrimitive
    cases R with
    | unary u hu hcongruent huanisotropic hpairU =>
        have huL : (u : W) ∈ L := hu
        have hpScaled : (p : W) ∈ rescale (uniformizerUnit K) L :=
          rescale_mem_of_subspace_rescale_mem
            (fun y hy ↦ D.contained ⟨y, hy, rfl⟩) hpPrimitive
        have htailScaled : ((z : W) - (u : W)) ∈
            rescale (uniformizerUnit K) L :=
          rescale_mem_of_subspace_rescale_mem
            (fun y hy ↦ show (y : W) ∈ L from hy) hcongruent
        have hcongruentAmbient : x - (u : W) ∈
            rescale (uniformizerUnit K) L := by
          have hsum := (rescale (uniformizerUnit K) L).add_mem
            hpScaled htailScaled
          have hdecomp := C.carrierProjection_add_orthogonalProjection x
          change (p : W) + ((z : W) - (u : W)) ∈ _ at hsum
          rw [add_sub, hdecomp] at hsum
          exact hsum
        have huanisotropicAmbient : q.IsAnisotropic (u : W) := huanisotropic
        refine .unary (u : W) huL hcongruentAmbient
          huanisotropicAmbient ?_
        intro w hw
        have hwO : C.orthogonalProjection w ∈ O := by
          change (C.orthogonalProjection w : W) ∈ L
          exact C.orthogonalProjection_mem_lattice D.contained D.modular
            hpairC hw
        have hrec := hpairU (C.orthogonalProjection w) hwO
        change q.bilin (u : W) (C.orthogonalProjection w : W) ∈ _ at hrec
        have horth : q.bilin (u : W) (C.carrierProjection w : W) = 0 := by
          rw [q.isSymm.eq]
          exact u.property (C.carrierProjection w : W)
            (C.carrierProjection w).property
        rw [← C.carrierProjection_add_orthogonalProjection w,
          LinearMap.BilinForm.add_right, horth, zero_add]
        exact hrec
    | binary u y hu hy hcongruent huy hleft hright hpairU hpairY =>
        have huL : (u : W) ∈ L := hu
        have hyL : (y : W) ∈ L := hy
        have hpScaled : (p : W) ∈ rescale (uniformizerUnit K) L :=
          rescale_mem_of_subspace_rescale_mem
            (fun t ht ↦ D.contained ⟨t, ht, rfl⟩) hpPrimitive
        have htailScaled : ((z : W) - (u : W)) ∈
            rescale (uniformizerUnit K) L :=
          rescale_mem_of_subspace_rescale_mem
            (fun t ht ↦ show (t : W) ∈ L from ht) hcongruent
        have hcongruentAmbient : x - (u : W) ∈
            rescale (uniformizerUnit K) L := by
          have hsum := (rescale (uniformizerUnit K) L).add_mem
            hpScaled htailScaled
          have hdecomp := C.carrierProjection_add_orthogonalProjection x
          change (p : W) + ((z : W) - (u : W)) ∈ _ at hsum
          rw [add_sub, hdecomp] at hsum
          exact hsum
        refine .binary (u : W) (y : W) huL hyL hcongruentAmbient
          huy hleft hright ?_ ?_
        · intro w hw
          have hwO : C.orthogonalProjection w ∈ O := by
            change (C.orthogonalProjection w : W) ∈ L
            exact C.orthogonalProjection_mem_lattice D.contained D.modular
              hpairC hw
          have hrec := hpairU (C.orthogonalProjection w) hwO
          change q.bilin (u : W) (C.orthogonalProjection w : W) ∈ _ at hrec
          have horth : q.bilin (u : W) (C.carrierProjection w : W) = 0 := by
            rw [q.isSymm.eq]
            exact u.property (C.carrierProjection w : W)
              (C.carrierProjection w).property
          rw [← C.carrierProjection_add_orthogonalProjection w,
            LinearMap.BilinForm.add_right, horth, zero_add]
          exact hrec
        · intro w hw
          have hwO : C.orthogonalProjection w ∈ O := by
            change (C.orthogonalProjection w : W) ∈ L
            exact C.orthogonalProjection_mem_lattice D.contained D.modular
              hpairC hw
          have hrec := hpairY (C.orthogonalProjection w) hwO
          change q.bilin (y : W) (C.orthogonalProjection w : W) ∈ _ at hrec
          have horth : q.bilin (y : W) (C.carrierProjection w : W) = 0 := by
            rw [q.isSymm.eq]
            exact y.property (C.carrierProjection w : W)
              (C.carrierProjection w).property
          rw [← C.carrierProjection_add_orthogonalProjection w,
            LinearMap.BilinForm.add_right, horth, zero_add]
          exact hrec
termination_by finrank K W
decreasing_by
  letI : FiniteDimensional K W := L.moduleFinite
  change finrank K (q.bilin.orthogonal C.carrier) < finrank K W
  rw [q.bilin.finrank_orthogonal q.nondegenerate]
  have hcomponent : 0 < finrank K C.carrier := by
    rcases D.rank_one_or_two with h | h
    · simpa [C, h]
    · simpa [C, h]
  exact Nat.sub_lt hpos hcomponent

end Lattice

end Bong
