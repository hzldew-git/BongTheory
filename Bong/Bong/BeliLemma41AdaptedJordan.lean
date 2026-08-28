/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma41AdaptedStep
import Bong.Bong.JordanPropertyAInvariant
import Bong.Lattice.JordanAmalgamation
import Bong.Lattice.OmearaJordan
import Bong.Lattice.OrthogonalDecompositionCons
import Bong.Lattice.RankOneNormScale

/-!
# A Jordan decomposition adapted to the first vector of a BONG

This file carries out the Jordan-decomposition change used in Beli (2003),
Lemma 4.1(ii).  The exact unary or binary block containing the prescribed
first BONG vector is put in front of a Jordan decomposition of its orthogonal
complement.  At most the first two equal-scale components can then have to be
amalgamated.
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n t : Nat}

namespace BONG

/-- The adapted first block has the scale of the first component of the
given property-A Jordan decomposition. -/
theorem firstJordanAdaptedBlockData_scaleOrder_eq_first
    [FiniteDimensional K V]
    (b : BONG V q L (n + 1))
    (J : Lattice.JordanDecomposition q L t) (hA : J.HasPropertyA)
    (ht : 0 < t) :
    ordUnit K (b.firstJordanAdaptedBlockData J hA ht).scaleGenerator =
      ordUnit K (J.scaleGenerator ⟨0, ht⟩) := by
  classical
  let i0 : Fin t := ⟨0, ht⟩
  let C := J.component i0
  let p : C.carrier := C.carrierProjection b.head
  let z : C.orthogonalCarrier := C.orthogonalProjection b.head
  have hp : p ∈ C.lattice := by
    simpa [i0, C, p] using
      J.firstCarrierProjection_mem_lattice ht b.head
        b.head_isNormGenerator.mem
  have hpPrimitive : p ∉
      Lattice.rescale (uniformizerUnit K) C.lattice := by
    simpa [i0, C, p] using
      b.firstJordanProjection_not_mem_rescale J hA ht
  let hexistsPair :=
    (J.modular i0).exists_pairing_eq_of_not_mem_rescale hp hpPrimitive
  let y : C.carrier := Classical.choose hexistsPair
  have hpy : C.space.bilin p y = (J.scaleGenerator i0 : K) :=
    (Classical.choose_spec hexistsPair).2
  have hxy : q.bilin b.head (y : V) = (J.scaleGenerator i0 : K) := by
    have horth : q.bilin (z : V) (y : V) = 0 := by
      rw [q.isSymm.eq (z : V) (y : V)]
      exact z.property (y : V) y.property
    calc
      q.bilin b.head (y : V) =
          q.bilin ((p : V) + (z : V)) (y : V) := by
        rw [C.carrierProjection_add_orthogonalProjection]
      _ = q.bilin (p : V) (y : V) + q.bilin (z : V) (y : V) := by
        rw [LinearMap.BilinForm.add_left]
      _ = (J.scaleGenerator i0 : K) := by
        change C.space.bilin p y + _ = _
        rw [hpy, horth, add_zero]
  simp only [firstJordanAdaptedBlockData]
  split <;> rename_i heq
  · apply WithTop.coe_injective
    simpa only [Lattice.Beli2019Lemma51BlockData.scaleGenerator,
      coe_ordUnit, Units.val_mk0] using heq.symm
  · apply WithTop.coe_injective
    simpa only [Lattice.Beli2019Lemma51BlockData.scaleGenerator,
      coe_ordUnit, Units.val_mk0, i0, C, p, z, hexistsPair, y] using
        congrArg (ord K) hxy

/-- The orthogonal complement of the exact first adapted block. -/
noncomputable def firstJordanAdaptedComplement
    [FiniteDimensional K V]
    (b : BONG V q L (n + 1))
    (J : Lattice.JordanDecomposition q L t) (hA : J.HasPropertyA)
    (ht : 0 < t) : Lattice.QuadraticSublattice q :=
  (b.firstJordanAdaptedBlockData J hA ht).splitting.component 1

/-- A chosen Jordan decomposition of the complement of the adapted block. -/
noncomputable def firstJordanAdaptedComplementJordanWitness
    [FiniteDimensional K V]
    (b : BONG V q L (n + 1))
    (J : Lattice.JordanDecomposition q L t) (hA : J.HasPropertyA)
    (ht : 0 < t) :
    Σ s : Nat, Lattice.JordanDecomposition
      (b.firstJordanAdaptedComplement J hA ht).space
      (b.firstJordanAdaptedComplement J hA ht).lattice s :=
  Lattice.omearaJordanDecomposition
    (b.firstJordanAdaptedComplement J hA ht).space
    (b.firstJordanAdaptedComplement J hA ht).lattice

/-- The number of strict-scale Jordan components in the complement. -/
noncomputable def firstJordanAdaptedComplementCount
    [FiniteDimensional K V]
    (b : BONG V q L (n + 1))
    (J : Lattice.JordanDecomposition q L t) (hA : J.HasPropertyA)
    (ht : 0 < t) : Nat :=
  (b.firstJordanAdaptedComplementJordanWitness J hA ht).1

/-- The selected Jordan decomposition of the complement. -/
noncomputable def firstJordanAdaptedComplementJordan
    [FiniteDimensional K V]
    (b : BONG V q L (n + 1))
    (J : Lattice.JordanDecomposition q L t) (hA : J.HasPropertyA)
    (ht : 0 < t) :
    Lattice.JordanDecomposition
      (b.firstJordanAdaptedComplement J hA ht).space
      (b.firstJordanAdaptedComplement J hA ht).lattice
      (b.firstJordanAdaptedComplementCount J hA ht) :=
  (b.firstJordanAdaptedComplementJordanWitness J hA ht).2

/-- Every scale in the orthogonal complement is no smaller than the scale
of the adapted first block. -/
theorem firstJordanAdaptedBlock_scaleOrder_le_complement
    [FiniteDimensional K V]
    (b : BONG V q L (n + 1))
    (J : Lattice.JordanDecomposition q L t) (hA : J.HasPropertyA)
    (ht : 0 < t)
    (i : Fin (b.firstJordanAdaptedComplementCount J hA ht)) :
    ordUnit K (b.firstJordanAdaptedBlockData J hA ht).scaleGenerator ≤
      ordUnit K
        ((b.firstJordanAdaptedComplementJordan J hA ht).scaleGenerator i) := by
  let D := b.firstJordanAdaptedBlockData J hA ht
  let C := b.firstJordanAdaptedComplement J hA ht
  let H := b.firstJordanAdaptedComplementJordan J hA ht
  let P := D.splitting.prependNested H.toOrthogonalDecomposition
  have hcontained :
      (C.liftNested (H.component i)).ambientSubmodule ≤ L.toSubmodule := by
    change (P.component i.succ).ambientSubmodule ≤ L.toSubmodule
    exact P.component_ambientSubmodule_le i.succ
  have hscaleLe :
      Lattice.scaleIdeal
          (C.liftNested (H.component i)).space
          (C.liftNested (H.component i)).lattice ≤
        Lattice.scaleIdeal q L :=
    Lattice.QuadraticSublattice.scaleIdeal_le_of_ambientSubmodule_le
      (C.liftNested (H.component i)) hcontained
  have hpos : 0 < Module.finrank K
      (C.liftNested (H.component i)).carrier := by
    rw [C.finrank_liftNested]
    exact H.component_finrank_pos i
  have hscaleLift :
      Lattice.scaleIdeal
          (C.liftNested (H.component i)).space
          (C.liftNested (H.component i)).lattice =
        Lattice.principalIdeal (K := K) (H.scaleGenerator i : K) :=
    (Lattice.QuadraticSublattice.IsModular.liftNested C (H.component i)
      (H.modular i)).scaleIdeal_eq_principal hpos
  rw [hscaleLift, J.scaleIdeal_eq_first ht] at hscaleLe
  have hord := (Lattice.principalIdeal_le_iff_ord_ge
    (Units.ne_zero (H.scaleGenerator i))
    (Units.ne_zero (J.scaleGenerator ⟨0, ht⟩))).mp hscaleLe
  have hfirst : ordUnit K (J.scaleGenerator ⟨0, ht⟩) ≤
      ordUnit K (H.scaleGenerator i) := by
    apply WithTop.coe_le_coe.mp
    simpa only [coe_ordUnit] using hord
  rw [b.firstJordanAdaptedBlockData_scaleOrder_eq_first J hA ht]
  exact hfirst

/-- The modular decomposition obtained by putting the exact adapted block
in front of the chosen strict Jordan decomposition of its complement. -/
noncomputable def firstJordanAdaptedWeakJordan
    [FiniteDimensional K V]
    (b : BONG V q L (n + 1))
    (J : Lattice.JordanDecomposition q L t) (hA : J.HasPropertyA)
    (ht : 0 < t) :
    Lattice.WeakJordanDecomposition q L
      (b.firstJordanAdaptedComplementCount J hA ht + 1) := by
  let D := b.firstJordanAdaptedBlockData J hA ht
  let C := b.firstJordanAdaptedComplement J hA ht
  let H := b.firstJordanAdaptedComplementJordan J hA ht
  let P := D.splitting.prependNested H.toOrthogonalDecomposition
  exact {
    toOrthogonalDecomposition := P
    scaleGenerator := Fin.cases D.scaleGenerator H.scaleGenerator
    modular := by
      intro i
      cases i using Fin.cases with
      | zero =>
          change Lattice.IsModular D.component.space D.component.lattice
            D.scaleGenerator
          exact D.component_modular
      | succ i =>
          change Lattice.IsModular
            (C.liftNested (H.component i)).space
            (C.liftNested (H.component i)).lattice
            (H.scaleGenerator i)
          exact Lattice.QuadraticSublattice.IsModular.liftNested
            C (H.component i) (H.modular i)
    component_finrank_pos := by
      intro i
      cases i using Fin.cases with
      | zero =>
          change 0 < finrank K D.component.carrier
          rcases D.component_rank_one_or_two with h | h <;> omega
      | succ i =>
          change 0 < finrank K (C.liftNested (H.component i)).carrier
          rw [C.finrank_liftNested]
          exact H.component_finrank_pos i
    scaleOrder_mono := by
      intro i j hij
      cases i using Fin.cases with
      | zero =>
          cases j using Fin.cases with
          | zero => exact le_rfl
          | succ j =>
              exact b.firstJordanAdaptedBlock_scaleOrder_le_complement
                J hA ht j
      | succ i =>
          cases j using Fin.cases with
          | zero =>
              change i.val + 1 ≤ 0 at hij
              omega
          | succ j =>
              have hij' : i ≤ j := by simpa using hij
              have hstrict : StrictMono
                  (fun k ↦ ordUnit K (H.scaleGenerator k)) :=
                fun _ _ h ↦ H.scaleOrder_strict h
              exact hstrict.monotone hij'
  }

@[simp]
theorem firstJordanAdaptedWeakJordan_component_zero
    [FiniteDimensional K V]
    (b : BONG V q L (n + 1))
    (J : Lattice.JordanDecomposition q L t) (hA : J.HasPropertyA)
    (ht : 0 < t) :
    (b.firstJordanAdaptedWeakJordan J hA ht).component 0 =
      (b.firstJordanAdaptedBlockData J hA ht).component :=
  rfl

@[simp]
theorem firstJordanAdaptedWeakJordan_component_succ
    [FiniteDimensional K V]
    (b : BONG V q L (n + 1))
    (J : Lattice.JordanDecomposition q L t) (hA : J.HasPropertyA)
    (ht : 0 < t)
    (i : Fin (b.firstJordanAdaptedComplementCount J hA ht)) :
    (b.firstJordanAdaptedWeakJordan J hA ht).component i.succ =
      (b.firstJordanAdaptedComplement J hA ht).liftNested
        ((b.firstJordanAdaptedComplementJordan J hA ht).component i) :=
  rfl

@[simp]
theorem firstJordanAdaptedWeakJordan_scaleGenerator_zero
    [FiniteDimensional K V]
    (b : BONG V q L (n + 1))
    (J : Lattice.JordanDecomposition q L t) (hA : J.HasPropertyA)
    (ht : 0 < t) :
    (b.firstJordanAdaptedWeakJordan J hA ht).scaleGenerator 0 =
      (b.firstJordanAdaptedBlockData J hA ht).scaleGenerator :=
  rfl

@[simp]
theorem firstJordanAdaptedWeakJordan_scaleGenerator_succ
    [FiniteDimensional K V]
    (b : BONG V q L (n + 1))
    (J : Lattice.JordanDecomposition q L t) (hA : J.HasPropertyA)
    (ht : 0 < t)
    (i : Fin (b.firstJordanAdaptedComplementCount J hA ht)) :
    (b.firstJordanAdaptedWeakJordan J hA ht).scaleGenerator i.succ =
      (b.firstJordanAdaptedComplementJordan J hA ht).scaleGenerator i :=
  rfl

/-- The norm order chosen on a lifted complement component agrees with the
norm order in the complement Jordan decomposition. -/
theorem firstJordanAdaptedWeakJordan_normOrder_succ_eq_complement
    [FiniteDimensional K V]
    (b : BONG V q L (n + 1))
    (J : Lattice.JordanDecomposition q L t) (hA : J.HasPropertyA)
    (ht : 0 < t)
    (i : Fin (b.firstJordanAdaptedComplementCount J hA ht)) :
    ordUnit K
        ((b.firstJordanAdaptedWeakJordan J hA ht).normGeneratorUnit i.succ) =
      ordUnit K
        ((b.firstJordanAdaptedComplementJordan J hA ht).normGenerator i) := by
  let W := b.firstJordanAdaptedWeakJordan J hA ht
  let C := b.firstJordanAdaptedComplement J hA ht
  let H := b.firstJordanAdaptedComplementJordan J hA ht
  apply (Lattice.principalIdeal_eq_iff_ordUnit_eq _ _).mp
  calc
    Lattice.principalIdeal (K := K) (W.normGeneratorUnit i.succ : K) =
        Lattice.normIdeal (W.component i.succ).space
          (W.component i.succ).lattice :=
      (W.normIdeal_eq_normGeneratorUnit i.succ).symm
    _ = Lattice.normIdeal
          (C.liftNested (H.component i)).space
          (C.liftNested (H.component i)).lattice := by
      rw [show W.component i.succ = C.liftNested (H.component i) by rfl]
    _ = Lattice.normIdeal (H.component i).space
          (H.component i).lattice :=
      Lattice.normIdeal_map_isometry
        (C.liftNestedIsometry (H.component i)).toQuadraticSpaceIsometry
        (H.component i).lattice
    _ = Lattice.principalIdeal (K := K) (H.normGenerator i : K) :=
      H.normIdeal_eq i

/-- An equal-scale collision exists precisely when the adapted first block
has the scale of a component in the chosen complement decomposition. -/
def FirstJordanAdaptedScaleCollision
    [FiniteDimensional K V]
    (b : BONG V q L (n + 1))
    (J : Lattice.JordanDecomposition q L t) (hA : J.HasPropertyA)
    (ht : 0 < t) : Prop :=
  ∃ i : Fin (b.firstJordanAdaptedComplementCount J hA ht),
    ordUnit K (b.firstJordanAdaptedBlockData J hA ht).scaleGenerator =
      ordUnit K
        ((b.firstJordanAdaptedComplementJordan J hA ht).scaleGenerator i)

/-- If no complement component has the selected scale, the prepended weak
decomposition is already a genuine strict-scale decomposition. -/
theorem firstJordanAdaptedWeakJordan_scaleOrder_strict_of_noCollision
    [FiniteDimensional K V]
    (b : BONG V q L (n + 1))
    (J : Lattice.JordanDecomposition q L t) (hA : J.HasPropertyA)
    (ht : 0 < t)
    (hcollision : ¬b.FirstJordanAdaptedScaleCollision J hA ht) :
    StrictMono (fun i ↦ ordUnit K
      ((b.firstJordanAdaptedWeakJordan J hA ht).scaleGenerator i)) := by
  let W := b.firstJordanAdaptedWeakJordan J hA ht
  let H := b.firstJordanAdaptedComplementJordan J hA ht
  apply W.scaleOrder_mono.strictMono_of_injective
  intro i j heq
  cases i using Fin.cases with
  | zero =>
      cases j using Fin.cases with
      | zero => rfl
      | succ j =>
          exfalso
          apply hcollision
          refine ⟨j, ?_⟩
          simpa only [W, firstJordanAdaptedWeakJordan_scaleGenerator_zero,
            firstJordanAdaptedWeakJordan_scaleGenerator_succ] using heq
  | succ i =>
      cases j using Fin.cases with
      | zero =>
          exfalso
          apply hcollision
          refine ⟨i, ?_⟩
          simpa only [W, firstJordanAdaptedWeakJordan_scaleGenerator_zero,
            firstJordanAdaptedWeakJordan_scaleGenerator_succ] using heq.symm
      | succ j =>
          have hstrict : StrictMono
              (fun k ↦ ordUnit K (H.scaleGenerator k)) :=
            fun _ _ h ↦ H.scaleOrder_strict h
          have hij : i = j := hstrict.injective (by
            simpa only [W, H,
              firstJordanAdaptedWeakJordan_scaleGenerator_succ] using heq)
          subst j
          rfl

/-- Because all complement scales are strictly increasing and the selected
scale is minimal, any collision is necessarily with the first complement
component. -/
theorem firstJordanAdaptedCollision_index_eq_zero
    [FiniteDimensional K V]
    (b : BONG V q L (n + 1))
    (J : Lattice.JordanDecomposition q L t) (hA : J.HasPropertyA)
    (ht : 0 < t)
    (i : Fin (b.firstJordanAdaptedComplementCount J hA ht))
    (hscale :
      ordUnit K (b.firstJordanAdaptedBlockData J hA ht).scaleGenerator =
        ordUnit K
          ((b.firstJordanAdaptedComplementJordan J hA ht).scaleGenerator i)) :
    i.val = 0 := by
  let H := b.firstJordanAdaptedComplementJordan J hA ht
  by_contra hi
  have hcountPos : 0 < b.firstJordanAdaptedComplementCount J hA ht := by
    omega
  let i0 : Fin (b.firstJordanAdaptedComplementCount J hA ht) :=
    ⟨0, hcountPos⟩
  have hzero_lt : i0 < i := by
    change 0 < i.val
    omega
  have hstrict : ordUnit K (H.scaleGenerator i0) <
      ordUnit K (H.scaleGenerator i) := H.scaleOrder_strict hzero_lt
  have hle := b.firstJordanAdaptedBlock_scaleOrder_le_complement
    J hA ht i0
  change ordUnit K (b.firstJordanAdaptedBlockData J hA ht).scaleGenerator ≤
      ordUnit K (H.scaleGenerator i0) at hle
  change ordUnit K (b.firstJordanAdaptedBlockData J hA ht).scaleGenerator =
      ordUnit K (H.scaleGenerator i) at hscale
  omega

/-- After identifying the first collision, it is the only equality between
distinct scale positions in the prepended weak decomposition. -/
theorem firstJordanAdaptedOnlyScaleCollisionAt
    [FiniteDimensional K V]
    (b : BONG V q L (n + 1))
    (J : Lattice.JordanDecomposition q L t) (hA : J.HasPropertyA)
    (ht : 0 < t)
    (k : Fin (b.firstJordanAdaptedComplementCount J hA ht))
    (hk : k.val = 0)
    (heq : ordUnit K
        ((b.firstJordanAdaptedWeakJordan J hA ht).scaleGenerator k.castSucc) =
      ordUnit K
        ((b.firstJordanAdaptedWeakJordan J hA ht).scaleGenerator k.succ)) :
    Lattice.WeakJordanDecomposition.OnlyScaleCollisionAt
      (b.firstJordanAdaptedWeakJordan J hA ht) k := by
  let W := b.firstJordanAdaptedWeakJordan J hA ht
  let H := b.firstJordanAdaptedComplementJordan J hA ht
  intro p r hpr hscale
  cases p using Fin.cases with
  | zero =>
      cases r using Fin.cases with
      | zero => exact (lt_irrefl _ hpr).elim
      | succ r =>
          have hrScale :
              ordUnit K
                  (b.firstJordanAdaptedBlockData J hA ht).scaleGenerator =
                ordUnit K (H.scaleGenerator r) := by
            simpa only [W, H,
              firstJordanAdaptedWeakJordan_scaleGenerator_zero,
              firstJordanAdaptedWeakJordan_scaleGenerator_succ] using hscale
          have hr0 := b.firstJordanAdaptedCollision_index_eq_zero
            J hA ht r hrScale
          constructor
          · apply Fin.ext
            exact hk.symm
          · apply Fin.ext
            change r.val + 1 = k.val + 1
            omega
  | succ p =>
      cases r using Fin.cases with
      | zero =>
          change p.val + 1 < 0 at hpr
          omega
      | succ r =>
          have hpr' : p < r := by simpa using hpr
          have hstrict : ordUnit K (H.scaleGenerator p) <
              ordUnit K (H.scaleGenerator r) := H.scaleOrder_strict hpr'
          have heq' : ordUnit K (H.scaleGenerator p) =
              ordUnit K (H.scaleGenerator r) := by
            simpa only [W, H,
              firstJordanAdaptedWeakJordan_scaleGenerator_succ] using hscale
          exact (ne_of_lt hstrict heq').elim

/-- The genuine Jordan decomposition obtained by performing the unique
possible first amalgamation. -/
noncomputable def firstJordanAdaptedJordanWitness
    [FiniteDimensional K V]
    (b : BONG V q L (n + 1))
    (J : Lattice.JordanDecomposition q L t) (hA : J.HasPropertyA)
    (ht : 0 < t) :
    Σ s : Nat, Lattice.JordanDecomposition q L s := by
  classical
  let W := b.firstJordanAdaptedWeakJordan J hA ht
  by_cases hcollision : b.FirstJordanAdaptedScaleCollision J hA ht
  · let i := Classical.choose hcollision
    have hscale := Classical.choose_spec hcollision
    have hi : i.val = 0 :=
      b.firstJordanAdaptedCollision_index_eq_zero J hA ht i hscale
    have hcountPos : 0 < b.firstJordanAdaptedComplementCount J hA ht := by
      omega
    let k : Fin (b.firstJordanAdaptedComplementCount J hA ht) :=
      ⟨0, hcountPos⟩
    have hk : k.val = 0 := rfl
    have hik : i = k := by
      apply Fin.ext
      exact hi
    have heq : ordUnit K (W.scaleGenerator k.castSucc) =
        ordUnit K (W.scaleGenerator k.succ) := by
      change ordUnit K
          (b.firstJordanAdaptedBlockData J hA ht).scaleGenerator =
        ordUnit K
          ((b.firstJordanAdaptedComplementJordan J hA ht).scaleGenerator i)
        at hscale
      rw [hik] at hscale
      have hkcast : k.castSucc =
          (0 : Fin (b.firstJordanAdaptedComplementCount J hA ht + 1)) := by
        apply Fin.ext
        rfl
      rw [hkcast]
      simpa only [W,
        firstJordanAdaptedWeakJordan_scaleGenerator_zero,
        firstJordanAdaptedWeakJordan_scaleGenerator_succ] using hscale
    let S := W.mergeAdjacentAt k heq
    have hstrict : StrictMono
        (fun j ↦ ordUnit K (S.scaleGenerator j)) :=
      Lattice.WeakJordanDecomposition.mergeAdjacentAt_scaleOrder_strict
        W k heq
          (b.firstJordanAdaptedOnlyScaleCollisionAt J hA ht k hk heq)
    exact ⟨b.firstJordanAdaptedComplementCount J hA ht,
      S.toJordan hstrict⟩
  · exact ⟨b.firstJordanAdaptedComplementCount J hA ht + 1,
      W.toJordan
        (b.firstJordanAdaptedWeakJordan_scaleOrder_strict_of_noCollision
          J hA ht hcollision)⟩

/-- The adapted decomposition inherits property A from the original Jordan
decomposition of the same lattice. -/
theorem firstJordanAdaptedJordanWitness_hasPropertyA
    [FiniteDimensional K V]
    (b : BONG V q L (n + 1))
    (J : Lattice.JordanDecomposition q L t) (hA : J.HasPropertyA)
    (ht : 0 < t) :
    (b.firstJordanAdaptedJordanWitness J hA ht).2.HasPropertyA :=
  J.hasPropertyA_of_hasPropertyA
    (b.firstJordanAdaptedJordanWitness J hA ht).2 hA

/-- Without a first-scale collision, the complement Jordan decomposition is
literally the positive-index suffix of the adapted property-A decomposition. -/
theorem firstJordanAdaptedComplementJordan_hasPropertyA_of_noCollision
    [FiniteDimensional K V]
    (b : BONG V q L (n + 1))
    (J : Lattice.JordanDecomposition q L t) (hA : J.HasPropertyA)
    (ht : 0 < t)
    (hcollision : ¬b.FirstJordanAdaptedScaleCollision J hA ht) :
    (b.firstJordanAdaptedComplementJordan J hA ht).HasPropertyA := by
  let W := b.firstJordanAdaptedWeakJordan J hA ht
  let C := b.firstJordanAdaptedComplement J hA ht
  let H := b.firstJordanAdaptedComplementJordan J hA ht
  let hstrict :=
    b.firstJordanAdaptedWeakJordan_scaleOrder_strict_of_noCollision
      J hA ht hcollision
  let G := W.toJordan hstrict
  have hG : G.HasPropertyA := J.hasPropertyA_of_hasPropertyA G hA
  constructor
  · intro i
    change finrank K (H.component i).carrier = 1 ∨
      finrank K (H.component i).carrier = 2
    have hrank := hG.1 i.succ
    change finrank K (W.component i.succ).carrier = 1 ∨
        finrank K (W.component i.succ).carrier = 2 at hrank
    change finrank K (C.liftNested (H.component i)).carrier = 1 ∨
        finrank K (C.liftNested (H.component i)).carrier = 2 at hrank
    simpa only [C.finrank_liftNested] using hrank
  · intro i j hij
    have hij' : i.succ < j.succ := by simpa using hij
    have hgap := hG.2 hij'
    change
      0 < ordUnit K (W.normGeneratorUnit j.succ) -
          ordUnit K (W.normGeneratorUnit i.succ) ∧
        ordUnit K (W.normGeneratorUnit j.succ) -
            ordUnit K (W.normGeneratorUnit i.succ) <
          2 * (ordUnit K (W.scaleGenerator j.succ) -
            ordUnit K (W.scaleGenerator i.succ)) at hgap
    have hni :=
      b.firstJordanAdaptedWeakJordan_normOrder_succ_eq_complement
        J hA ht i
    have hnj :=
      b.firstJordanAdaptedWeakJordan_normOrder_succ_eq_complement
        J hA ht j
    change ordUnit K (W.normGeneratorUnit i.succ) =
      ordUnit K (H.normGenerator i) at hni
    change ordUnit K (W.normGeneratorUnit j.succ) =
      ordUnit K (H.normGenerator j) at hnj
    rw [hni, hnj] at hgap
    change
      0 < ordUnit K (H.normGenerator j) -
          ordUnit K (H.normGenerator i) ∧
        ordUnit K (H.normGenerator j) -
            ordUnit K (H.normGenerator i) <
          2 * (ordUnit K (H.scaleGenerator j) -
            ordUnit K (H.scaleGenerator i)) at hgap
    exact hgap

/-- In the collision branch the selected block and the first complement
component both have rank one.  Their amalgamation therefore has rank two,
and its scale and norm orders agree with those of the removed first
complement component.  Consequently the complement itself still has
property A. -/
theorem firstJordanAdaptedComplementJordan_hasPropertyA_of_collision
    [FiniteDimensional K V]
    (b : BONG V q L (n + 1))
    (J : Lattice.JordanDecomposition q L t) (hA : J.HasPropertyA)
    (ht : 0 < t)
    (hcollision : b.FirstJordanAdaptedScaleCollision J hA ht) :
    (b.firstJordanAdaptedComplementJordan J hA ht).HasPropertyA := by
  classical
  let D := b.firstJordanAdaptedBlockData J hA ht
  let C := b.firstJordanAdaptedComplement J hA ht
  let H := b.firstJordanAdaptedComplementJordan J hA ht
  let W := b.firstJordanAdaptedWeakJordan J hA ht
  let i := Classical.choose hcollision
  have hscaleRaw := Classical.choose_spec hcollision
  have hi : i.val = 0 :=
    b.firstJordanAdaptedCollision_index_eq_zero J hA ht i hscaleRaw
  have hcountPos : 0 < b.firstJordanAdaptedComplementCount J hA ht := by
    omega
  let k : Fin (b.firstJordanAdaptedComplementCount J hA ht) :=
    ⟨0, hcountPos⟩
  have hk : k.val = 0 := rfl
  have hik : i = k := by
    apply Fin.ext
    exact hi
  have hscale : ordUnit K D.scaleGenerator =
      ordUnit K (H.scaleGenerator k) := by
    change ordUnit K
        (b.firstJordanAdaptedBlockData J hA ht).scaleGenerator =
      ordUnit K
        ((b.firstJordanAdaptedComplementJordan J hA ht).scaleGenerator i)
      at hscaleRaw
    rw [hik] at hscaleRaw
    exact hscaleRaw
  have hkcast : k.castSucc =
      (0 : Fin (b.firstJordanAdaptedComplementCount J hA ht + 1)) := by
    apply Fin.ext
    exact hk
  have heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ) := by
    rw [hkcast]
    simpa only [W, D, H,
      firstJordanAdaptedWeakJordan_scaleGenerator_zero,
      firstJordanAdaptedWeakJordan_scaleGenerator_succ] using hscale
  let S := W.mergeAdjacentAt k heq
  have hstrict : StrictMono (fun a ↦ ordUnit K (S.scaleGenerator a)) :=
    Lattice.WeakJordanDecomposition.mergeAdjacentAt_scaleOrder_strict
      W k heq
        (b.firstJordanAdaptedOnlyScaleCollisionAt J hA ht k hk heq)
  let G := S.toJordan hstrict
  have hG : G.HasPropertyA := J.hasPropertyA_of_hasPropertyA G hA

  have hmergedRank := hG.1 k
  change finrank K (S.component k).carrier = 1 ∨
      finrank K (S.component k).carrier = 2 at hmergedRank
  have hrankSum :=
    W.mergeAdjacentAt_componentRank_self k heq
  change finrank K (S.component k).carrier =
      finrank K (W.component k.castSucc).carrier +
        finrank K (W.component k.succ).carrier at hrankSum
  have hleftPos := W.component_finrank_pos k.castSucc
  have hrightPos := W.component_finrank_pos k.succ
  have hleftRank : finrank K (W.component k.castSucc).carrier = 1 := by
    rcases hmergedRank with h | h <;> omega
  have hrightRank : finrank K (W.component k.succ).carrier = 1 := by
    rcases hmergedRank with h | h <;> omega
  have hDrank : finrank K D.component.carrier = 1 := by
    rw [hkcast] at hleftRank
    change finrank K
      (b.firstJordanAdaptedBlockData J hA ht).component.carrier = 1
    change finrank K
      (b.firstJordanAdaptedBlockData J hA ht).component.carrier = 1
      at hleftRank
    exact hleftRank
  have hHrank : finrank K (H.component k).carrier = 1 := by
    change finrank K (C.liftNested (H.component k)).carrier = 1 at hrightRank
    simpa only [C.finrank_liftNested] using hrightRank

  have hDNormIdeal :
      Lattice.normIdeal D.component.space D.component.lattice =
        Lattice.principalIdeal (K := K)
          (W.normGeneratorUnit k.castSucc : K) := by
    rw [hkcast]
    have h := W.normIdeal_eq_normGeneratorUnit
      (0 : Fin (b.firstJordanAdaptedComplementCount J hA ht + 1))
    change Lattice.normIdeal
        (b.firstJordanAdaptedBlockData J hA ht).component.space
        (b.firstJordanAdaptedBlockData J hA ht).component.lattice =
      Lattice.principalIdeal (K := K)
        ((b.firstJordanAdaptedWeakJordan J hA ht).normGeneratorUnit 0 : K)
      at h
    exact h
  have hleftNorm : ordUnit K (W.normGeneratorUnit k.castSucc) =
      ordUnit K D.scaleGenerator :=
    Lattice.ordUnit_normGenerator_eq_scaleGenerator_of_finrank_eq_one
      D.component.space D.component.lattice D.scaleGenerator
      (W.normGeneratorUnit k.castSucc) hDrank D.component_modular hDNormIdeal
  have hHNorm : ordUnit K (H.normGenerator k) =
      ordUnit K (H.scaleGenerator k) :=
    Lattice.ordUnit_normGenerator_eq_scaleGenerator_of_finrank_eq_one
      (H.component k).space (H.component k).lattice
      (H.scaleGenerator k) (H.normGenerator k) hHrank
      (H.modular k) (H.normIdeal_eq k)
  have hrightNorm : ordUnit K (W.normGeneratorUnit k.succ) =
      ordUnit K (H.normGenerator k) := by
    simpa only [W, H] using
      b.firstJordanAdaptedWeakJordan_normOrder_succ_eq_complement
        J hA ht k
  have hleftNormH : ordUnit K (W.normGeneratorUnit k.castSucc) =
      ordUnit K (H.normGenerator k) :=
    hleftNorm.trans (hscale.trans hHNorm.symm)
  have hnormAtK : ordUnit K (G.normGenerator k) =
      ordUnit K (H.normGenerator k) := by
    change ordUnit K (S.normGeneratorUnit k) =
      ordUnit K (H.normGenerator k)
    rw [W.ordUnit_normGeneratorUnit_mergeAdjacentAt_self k heq,
      hleftNormH, hrightNorm, min_self]

  have hk_le (a : Fin (b.firstJordanAdaptedComplementCount J hA ht)) :
      k ≤ a := by
    change k.val ≤ a.val
    omega
  have hscaleProfile
      (a : Fin (b.firstJordanAdaptedComplementCount J hA ht)) :
      ordUnit K (G.scaleGenerator a) =
        ordUnit K (H.scaleGenerator a) := by
    change ordUnit K (S.scaleGenerator a) =
      ordUnit K (H.scaleGenerator a)
    rw [W.mergeAdjacentAt_scaleGenerator k heq a]
    by_cases ha : a = k
    · subst a
      rw [Fin.succAbove_succ_self]
      change ordUnit K (W.scaleGenerator k.castSucc) =
        ordUnit K (H.scaleGenerator k)
      exact heq.trans (by rfl)
    · have hka : k < a := lt_of_le_of_ne (hk_le a) (Ne.symm ha)
      rw [Fin.succAbove_succ_of_lt k a hka]
      rfl
  have hnormProfile
      (a : Fin (b.firstJordanAdaptedComplementCount J hA ht)) :
      ordUnit K (G.normGenerator a) =
        ordUnit K (H.normGenerator a) := by
    by_cases ha : a = k
    · subst a
      exact hnormAtK
    · have hka : k < a := lt_of_le_of_ne (hk_le a) (Ne.symm ha)
      change ordUnit K (S.normGeneratorUnit a) =
        ordUnit K (H.normGenerator a)
      rw [W.ordUnit_normGeneratorUnit_mergeAdjacentAt_of_ne k heq a ha,
        Fin.succAbove_succ_of_lt k a hka]
      simpa only [W, H] using
        b.firstJordanAdaptedWeakJordan_normOrder_succ_eq_complement
          J hA ht a

  constructor
  · intro a
    change finrank K (H.component a).carrier = 1 ∨
      finrank K (H.component a).carrier = 2
    by_cases ha : a = k
    · subst a
      exact Or.inl hHrank
    · have hka : k < a := lt_of_le_of_ne (hk_le a) (Ne.symm ha)
      have hrank := hG.1 a
      change finrank K (S.component a).carrier = 1 ∨
        finrank K (S.component a).carrier = 2 at hrank
      rw [W.mergeAdjacentAt_component_of_ne k heq a ha,
        Fin.succAbove_succ_of_lt k a hka] at hrank
      change finrank K (C.liftNested (H.component a)).carrier = 1 ∨
        finrank K (C.liftNested (H.component a)).carrier = 2 at hrank
      simpa only [C.finrank_liftNested] using hrank
  · intro a d had
    have hgap := hG.2 had
    change
      0 < ordUnit K (G.normGenerator d) -
          ordUnit K (G.normGenerator a) ∧
        ordUnit K (G.normGenerator d) -
            ordUnit K (G.normGenerator a) <
          2 * (ordUnit K (G.scaleGenerator d) -
            ordUnit K (G.scaleGenerator a)) at hgap
    rw [hnormProfile a, hnormProfile d,
      hscaleProfile a, hscaleProfile d] at hgap
    exact hgap

/-- The exact orthogonal complement selected at the first BONG vector has
property A in both the strict and equal-scale branches. -/
theorem firstJordanAdaptedComplementJordan_hasPropertyA
    [FiniteDimensional K V]
    (b : BONG V q L (n + 1))
    (J : Lattice.JordanDecomposition q L t) (hA : J.HasPropertyA)
    (ht : 0 < t) :
    (b.firstJordanAdaptedComplementJordan J hA ht).HasPropertyA := by
  by_cases hcollision : b.FirstJordanAdaptedScaleCollision J hA ht
  · exact b.firstJordanAdaptedComplementJordan_hasPropertyA_of_collision
      J hA ht hcollision
  · exact b.firstJordanAdaptedComplementJordan_hasPropertyA_of_noCollision
      J hA ht hcollision

/-- Lattice-level form of the preceding result. -/
theorem firstJordanAdaptedComplement_hasJordanPropertyA
    [FiniteDimensional K V]
    (b : BONG V q L (n + 1))
    (J : Lattice.JordanDecomposition q L t) (hA : J.HasPropertyA)
    (ht : 0 < t) :
    Lattice.HasJordanPropertyA
      (b.firstJordanAdaptedComplement J hA ht).space
      (b.firstJordanAdaptedComplement J hA ht).lattice :=
  ⟨b.firstJordanAdaptedComplementCount J hA ht,
    b.firstJordanAdaptedComplementJordan J hA ht,
    b.firstJordanAdaptedComplementJordan_hasPropertyA J hA ht⟩

/-- If the line `O x` splits integrally, its complementary intersection
lattice is exactly the recursively projected lattice used by `BONG.tail`. -/
theorem Lattice.projectedLattice_eq_unaryOrthogonalLattice
    [FiniteDimensional K V]
    {x : V} (hxL : x ∈ L) (hx : q.IsAnisotropic x)
    (hpair : ∀
      (y : (Lattice.unaryScaleComponent (q := q) x hx).carrier),
      y ∈ (Lattice.unaryScaleComponent (q := q) x hx).lattice →
      ∀ w : V, w ∈ L →
        q.bilin (y : V) w ∈
          Lattice.principalIdeal (K := K) (q.quadratic x))
    (hprojectedIntegral : ∀ y : q.vectorOrthogonal x,
      y ∈ L.projectedLattice q x hx → (y : V) ∈ L) :
    L.projectedLattice q x hx =
      (Lattice.unaryScaleComponent (q := q) x hx).orthogonalLattice
        (Lattice.unaryScaleComponent_ambientSubmodule_le hx hxL)
        (Lattice.unaryScaleComponent_isModular hx) hpair := by
  apply Lattice.ext
  ext y
  constructor
  · intro hy
    change (y : V) ∈ L
    exact hprojectedIntegral y hy
  · intro hy
    change (y : V) ∈ L at hy
    apply (Lattice.mem_projectedLattice_iff q L x hx y).2
    refine ⟨(y : V), hy, ?_⟩
    apply Subtype.ext
    exact q.orthogonalProjection_eq_self y.property

/-- In the unary branch, the next BONG order is the first norm order of the
adapted orthogonal complement.  This is the numerical form of the exact
identification of that complement with the recursively projected lattice. -/
theorem order_one_eq_firstJordanAdaptedComplementNorm_of_isUnary
    [FiniteDimensional K V]
    (b : BONG V q L (n + 2))
    (J : Lattice.JordanDecomposition q L t) (hA : J.HasPropertyA)
    (ht : 0 < t)
    (hUnary : (b.firstJordanAdaptedBlockData J hA ht).IsUnary)
    (hcount : 0 < b.firstJordanAdaptedComplementCount J hA ht) :
    b.order 1 = ordUnit K
      ((b.firstJordanAdaptedComplementJordan J hA ht).normGenerator
        ⟨0, hcount⟩) := by
  let D := b.firstJordanAdaptedBlockData J hA ht
  let H := b.firstJordanAdaptedComplementJordan J hA ht
  have hrep : D.representative = b.head := by
    simpa only [D] using
      b.firstJordanAdaptedBlockData_representative J hA ht
  have hH : H.HasPropertyA := by
    exact b.firstJordanAdaptedComplementJordan_hasPropertyA J hA ht
  cases hD : D with
  | unary z hz hcongruent hanisotropic hpair =>
      have hzhead : z = b.head := by
        simpa [Lattice.Beli2019Lemma51BlockData.representative, hD] using hrep
      subst z
      have hpairC : ∀
          (y : (Lattice.unaryScaleComponent
            (q := q) b.head b.head_isAnisotropic).carrier),
          y ∈ (Lattice.unaryScaleComponent
            (q := q) b.head b.head_isAnisotropic).lattice →
          ∀ w : V, w ∈ L →
            q.bilin (y : V) w ∈
              Lattice.principalIdeal (K := K) (q.quadratic b.head) := by
        intro y hy w hw
        exact
          (Lattice.Beli2019Lemma51BlockData.unary b.head hz hcongruent
            hanisotropic hpair).component_pairing y hy w hw
      have hprojectedIntegral : ∀ y : q.vectorOrthogonal b.head,
          y ∈ L.projectedLattice q b.head b.head_isAnisotropic →
            (y : V) ∈ L := by
        intro y hy
        exact Lattice.coe_mem_of_mem_projectedLattice_of_pairing_divisible
          b.head_isNormGenerator.mem b.head_isAnisotropic hpair hy
      have heq := Lattice.projectedLattice_eq_unaryOrthogonalLattice
        b.head_isNormGenerator.mem b.head_isAnisotropic hpairC
        hprojectedIntegral
      have hHfirst := H.normIdeal_eq_first hH hcount
      change Lattice.normIdeal (D.splitting.component 1).space
          (D.splitting.component 1).lattice =
        Lattice.principalIdeal (K := K)
          (H.normGenerator ⟨0, hcount⟩ : K) at hHfirst
      rw [hD] at hHfirst
      change Lattice.normIdeal
          (q.orthogonalSpace b.head b.head_isAnisotropic)
          ((Lattice.unaryScaleComponent
            (q := q) b.head b.head_isAnisotropic).orthogonalLattice
              (Lattice.unaryScaleComponent_ambientSubmodule_le
                b.head_isAnisotropic b.head_isNormGenerator.mem)
              (Lattice.unaryScaleComponent_isModular b.head_isAnisotropic)
              hpairC) =
        Lattice.principalIdeal (K := K)
          (H.normGenerator ⟨0, hcount⟩ : K) at hHfirst
      have hideal :
          Lattice.principalIdeal (K := K) (b.tail.valueUnit 0 : K) =
            Lattice.principalIdeal (K := K)
              (H.normGenerator ⟨0, hcount⟩ : K) := by
        calc
          Lattice.principalIdeal (K := K) (b.tail.valueUnit 0 : K) =
              Lattice.normIdeal
                (q.orthogonalSpace b.head b.head_isAnisotropic)
                (L.projectedLattice q b.head b.head_isAnisotropic) := by
            rw [b.tail.coe_valueUnit, b.tail.value_zero_eq_quadratic_head]
            exact b.tail.head_isNormGenerator.normIdeal_eq.symm
          _ = Lattice.normIdeal
              (q.orthogonalSpace b.head b.head_isAnisotropic)
              ((Lattice.unaryScaleComponent
                (q := q) b.head b.head_isAnisotropic).orthogonalLattice
                  (Lattice.unaryScaleComponent_ambientSubmodule_le
                    b.head_isAnisotropic b.head_isNormGenerator.mem)
                  (Lattice.unaryScaleComponent_isModular
                    b.head_isAnisotropic) hpairC) := by rw [heq]
          _ = Lattice.principalIdeal (K := K)
              (H.normGenerator ⟨0, hcount⟩ : K) := hHfirst
      have horder := (Lattice.principalIdeal_eq_iff_ordUnit_eq
        (b.tail.valueUnit 0) (H.normGenerator ⟨0, hcount⟩)).mp hideal
      rw [← b.tail.order_eq_ordUnit, b.order_tail] at horder
      exact horder
  | binary z y hz hy hcongruent hzy hleft hright hpairZ hpairY =>
      exact False.elim (by
        have : ¬D.IsUnary := by
          rw [hD]
          exact Lattice.Beli2019Lemma51BlockData.not_isUnary_binary
            z y hz hy hcongruent hzy hleft hright hpairZ hpairY
        exact this hUnary)

/-- In the unary branch, the complement constructed from the adapted block
is exactly the recursive lattice underlying `b.tail`; hence the tail lattice
inherits property A. -/
theorem tailLattice_hasJordanPropertyA_of_firstJordanAdaptedBlock_isUnary
    [FiniteDimensional K V]
    (b : BONG V q L (n + 1))
    (J : Lattice.JordanDecomposition q L t) (hA : J.HasPropertyA)
    (ht : 0 < t)
    (hUnary : (b.firstJordanAdaptedBlockData J hA ht).IsUnary) :
    Lattice.HasJordanPropertyA
      (q.orthogonalSpace b.head b.head_isAnisotropic)
      (L.projectedLattice q b.head b.head_isAnisotropic) := by
  let D := b.firstJordanAdaptedBlockData J hA ht
  have hrep : D.representative = b.head := by
    simpa only [D] using
      b.firstJordanAdaptedBlockData_representative J hA ht
  have hcomplement :=
    b.firstJordanAdaptedComplement_hasJordanPropertyA J hA ht
  change Lattice.HasJordanPropertyA
      (D.splitting.component 1).space
      (D.splitting.component 1).lattice at hcomplement
  cases hD : D with
  | unary z hz hcongruent hanisotropic hpair =>
      have hzhead : z = b.head := by
        simpa [Lattice.Beli2019Lemma51BlockData.representative, hD] using hrep
      subst z
      rw [hD] at hcomplement
      have hpairC : ∀
          (y : (Lattice.unaryScaleComponent
            (q := q) b.head b.head_isAnisotropic).carrier),
          y ∈ (Lattice.unaryScaleComponent
            (q := q) b.head b.head_isAnisotropic).lattice →
          ∀ w : V, w ∈ L →
            q.bilin (y : V) w ∈
              Lattice.principalIdeal (K := K) (q.quadratic b.head) := by
        intro y hy w hw
        exact
          (Lattice.Beli2019Lemma51BlockData.unary b.head hz hcongruent
            hanisotropic hpair).component_pairing y hy w hw
      have hprojectedIntegral : ∀ y : q.vectorOrthogonal b.head,
          y ∈ L.projectedLattice q b.head b.head_isAnisotropic →
            (y : V) ∈ L := by
        intro y hy
        exact Lattice.coe_mem_of_mem_projectedLattice_of_pairing_divisible
          b.head_isNormGenerator.mem b.head_isAnisotropic hpair hy
      have heq := Lattice.projectedLattice_eq_unaryOrthogonalLattice
        b.head_isNormGenerator.mem b.head_isAnisotropic hpairC
        hprojectedIntegral
      change Lattice.HasJordanPropertyA
          (q.orthogonalSpace b.head b.head_isAnisotropic)
          ((Lattice.unaryScaleComponent
            (q := q) b.head b.head_isAnisotropic).orthogonalLattice
              (Lattice.unaryScaleComponent_ambientSubmodule_le
                b.head_isAnisotropic b.head_isNormGenerator.mem)
              (Lattice.unaryScaleComponent_isModular b.head_isAnisotropic)
              hpairC) at hcomplement
      rw [← heq] at hcomplement
      exact hcomplement
  | binary z y hz hy hcongruent hzy hleft hright hpairZ hpairY =>
      exact False.elim (by
        have : ¬D.IsUnary := by
          rw [hD]
          exact Lattice.Beli2019Lemma51BlockData.not_isUnary_binary
            z y hz hy hcongruent hzy hleft hright hpairZ hpairY
        exact this hUnary)

end BONG

end Bong
