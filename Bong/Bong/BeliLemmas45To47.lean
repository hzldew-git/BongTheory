/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliCorollary44

/-!
# Beli (2003), Lemmas 4.5--4.7

This file records the modular-pair replacement in Lemma 4.5, derives good
BONG existence from a maximal norm splitting as in Lemma 4.6, and encodes the
Jordan/order profile correspondence of Lemma 4.7.
-/

namespace Bong

open Dyadic
open Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n t : Nat}

namespace Lattice

/-- A two-component modular orthogonal splitting with binary first block. -/
structure ModularPairSplitting (q : QuadraticSpace K V)
    (L : Lattice K V) extends OrthogonalDecomposition q L 2 where
  /-- Chosen scale generators. -/
  scaleGenerator : Fin 2 → Kˣ
  /-- Chosen norm generators. -/
  normGenerator : Fin 2 → Kˣ
  /-- Both components are modular at their chosen scales. -/
  modular : ∀ i,
    IsModular (component i).space (component i).lattice
      (scaleGenerator i)
  /-- Exact component scale ideals. -/
  scaleIdeal_eq : ∀ i,
    scaleIdeal (component i).space (component i).lattice =
      principalIdeal (K := K) (scaleGenerator i : K)
  /-- Exact component norm ideals. -/
  normIdeal_eq : ∀ i,
    normIdeal (component i).space (component i).lattice =
      principalIdeal (K := K) (normGenerator i : K)
  /-- The first component is binary. -/
  first_rank : finrank K (component 0).carrier = 2

namespace ModularPairSplitting

variable (P : ModularPairSplitting q L)

/-- Rank of a modular component. -/
noncomputable def componentRank (i : Fin 2) : Nat :=
  finrank K (P.component i).carrier

/-- Valuation order of a component scale. -/
noncomputable def scaleOrder (i : Fin 2) : Int :=
  ordUnit K (P.scaleGenerator i)

/-- Valuation order of a component norm. -/
noncomputable def normOrder (i : Fin 2) : Int :=
  ordUnit K (P.normGenerator i)

/-- For a modular component, the dual norm order is `u - 2r`. -/
noncomputable def dualNormOrder (i : Fin 2) : Int :=
  P.normOrder i - 2 * P.scaleOrder i

/-- A replacement preserves both component ranks and exact scale ideals. -/
def PreservesRanksAndScales (P' : ModularPairSplitting q L) : Prop :=
  ∀ i,
    P'.componentRank i = P.componentRank i ∧
      scaleIdeal (P'.component i).space (P'.component i).lattice =
        scaleIdeal (P.component i).space (P.component i).lattice

/-- Both replacement components acquire the old second norm ideal. -/
def NormsEqualOldSecond (P' : ModularPairSplitting q L) : Prop :=
  ∀ i,
    normIdeal (P'.component i).space (P'.component i).lattice =
      normIdeal (P.component 1).space (P.component 1).lattice

/-- Both replacement dual norm orders acquire the old second dual norm order. -/
def DualNormOrdersEqualOldSecond (P' : ModularPairSplitting q L) : Prop :=
  ∀ i, P'.dualNormOrder i = P.dualNormOrder 1

end ModularPairSplitting

end Lattice

/-- The two modular replacement assertions of Beli (2003), Lemma 4.5. -/
class BeliLemma45Laws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  /-- Lemma 4.5(i), in exact ideal form. -/
  rebalance_norms
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    (P : Lattice.ModularPairSplitting q L) :
    P.scaleOrder 0 ≤ P.scaleOrder 1 →
      P.normOrder 1 < P.normOrder 0 →
        ∃ P' : Lattice.ModularPairSplitting q L,
          P.PreservesRanksAndScales P' ∧ P.NormsEqualOldSecond P'
  /-- Lemma 4.5(ii), the dual replacement. -/
  rebalance_dualNorms
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    (P : Lattice.ModularPairSplitting q L) :
    P.scaleOrder 1 ≤ P.scaleOrder 0 →
      P.dualNormOrder 1 < P.dualNormOrder 0 →
        ∃ P' : Lattice.ModularPairSplitting q L,
          P.PreservesRanksAndScales P' ∧
            P.DualNormOrdersEqualOldSecond P'

namespace Lattice.ModularPairSplitting

variable [BeliLemma45Laws.{u, v} K]

/-- Beli (2003), Lemma 4.5(i). -/
theorem beliLemma45_i (P : Lattice.ModularPairSplitting q L)
    (hscale : P.scaleOrder 0 ≤ P.scaleOrder 1)
    (hnorm : P.normOrder 1 < P.normOrder 0) :
    ∃ P' : Lattice.ModularPairSplitting q L,
      P.PreservesRanksAndScales P' ∧ P.NormsEqualOldSecond P' :=
  BeliLemma45Laws.rebalance_norms P hscale hnorm

/-- Beli (2003), Lemma 4.5(ii). -/
theorem beliLemma45_ii (P : Lattice.ModularPairSplitting q L)
    (hscale : P.scaleOrder 1 ≤ P.scaleOrder 0)
    (hnorm : P.dualNormOrder 1 < P.dualNormOrder 0) :
    ∃ P' : Lattice.ModularPairSplitting q L,
      P.PreservesRanksAndScales P' ∧
        P.DualNormOrdersEqualOldSecond P' :=
  BeliLemma45Laws.rebalance_dualNorms P hscale hnorm

end Lattice.ModularPairSplitting

/-- The terminating replacement argument in Beli (2003), Lemma 4.6. -/
class BeliLemma46Laws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  /-- Every lattice has a maximal norm splitting. -/
  exists_maximalNormSplitting
    {V : Type v} [AddCommGroup V] [Module K V]
    (q : QuadraticSpace K V) (L : Lattice K V) :
    ∃ (t : Nat), Nonempty (Lattice.MaximalNormSplitting q L t)

/-- Beli (2003), Lemma 4.6, first assertion. -/
theorem Lattice.exists_maximalNormSplitting
    [BeliLemma46Laws.{u, v} K]
    (q : QuadraticSpace K V) (L : Lattice K V) :
    ∃ (t : Nat), Nonempty (Lattice.MaximalNormSplitting q L t) :=
  BeliLemma46Laws.exists_maximalNormSplitting q L

/--
Beli (2003), Lemma 4.6, second assertion: a maximal norm splitting and
Lemma 4.1 construct a good BONG.
-/
theorem exists_good_bong_of_sectionFour
    [BeliLemma46Laws.{u, v} K] [BeliSectionFourLaws.{u, v} K]
    (q : QuadraticSpace K V) (L : Lattice K V) :
    Nonempty (BONG.GoodBONG q L (finrank K V)) := by
  rcases Lattice.exists_maximalNormSplitting q L with ⟨t, ⟨M⟩⟩
  let c : M.toOrthogonalDecomposition.ComponentBONGFamily := fun i ↦
    Classical.choice
      (BONG.exists_ofLattice (M.component i).space (M.component i).lattice)
  rcases BONG.beliLemma41_i M c with ⟨b, hb⟩
  exact ⟨⟨b, BONG.beliCorollary42_ii M c b hb⟩⟩

namespace JordanProfileOrder

/-- Adjust one component's norm order to an arbitrary target scale. -/
def adjustedAt {t : Nat} (scale norm : Fin t → Int)
    (r : Int) (source : Fin t) : Int :=
  if scale source < r then
    norm source + 2 * (r - scale source)
  else norm source

/-- The minimum adjusted norm order of a nonempty finite component family. -/
def effectiveAt {t : Nat} (scale norm : Fin t → Int)
    (anchor : Fin t) (r : Int) : Int :=
  Finset.univ.inf' ⟨anchor, Finset.mem_univ anchor⟩
    (adjustedAt scale norm r)

end JordanProfileOrder

namespace BONG

/-- The contribution of one Jordan component to the norm of the lattice at
an arbitrary target scale order.  Components of smaller scale are rescaled
up to the target scale; components of at least the target scale are left
unchanged. -/
noncomputable def jordanAdjustedNormOrderAt
    (J : Lattice.JordanDecomposition q L t) (r : Int) (source : Fin t) : Int :=
  JordanProfileOrder.adjustedAt
    (fun j ↦ ordUnit K (J.scaleGenerator j))
    (fun j ↦ ordUnit K (J.normGenerator j)) r source

/-- The contribution of one Jordan component at the scale of another
component. -/
noncomputable def jordanAdjustedNormOrder
    (J : Lattice.JordanDecomposition q L t) (target source : Fin t) : Int :=
  jordanAdjustedNormOrderAt J (ordUnit K (J.scaleGenerator target)) source

/-- The effective norm order at an arbitrary target scale. -/
noncomputable def jordanEffectiveNormOrderAt
    (J : Lattice.JordanDecomposition q L t) (anchor : Fin t)
    (r : Int) : Int :=
  JordanProfileOrder.effectiveAt
    (fun j ↦ ordUnit K (J.scaleGenerator j))
    (fun j ↦ ordUnit K (J.normGenerator j)) anchor r

/-- The order of the norm of the scale truncation `L^{s_k}`.  This is the
minimum of the adjusted norm orders of all Jordan components and is the
quantity denoted `u_k = ord n(L^{s_k})` in Beli (2003), Lemma 4.7, and
Beli (2019), Section 5.4. -/
noncomputable def jordanEffectiveNormOrder
    (J : Lattice.JordanDecomposition q L t) (k : Fin t) : Int :=
  jordanEffectiveNormOrderAt J k (ordUnit K (J.scaleGenerator k))

/-- The order prescribed by one Jordan component at a local position.  Its
norm parameter is the norm of the whole lattice at that component's scale,
not merely the norm of the isolated component. -/
noncomputable def jordanExpectedOrder
    (J : Lattice.JordanDecomposition q L t) (k : Fin t)
    (i : Fin (J.toOrthogonalDecomposition.componentRank k)) : Int :=
  let r := ordUnit K (J.scaleGenerator k)
  let u := jordanEffectiveNormOrder J k
  if r = u then r else if Even i.1 then u else 2 * r - u

/--
The BONG order sequence is the lexicographic concatenation of the alternating
profiles prescribed by the Jordan components.
-/
structure JordanOrderProfileWitness (b : BONG V q L n)
    (J : Lattice.JordanDecomposition q L t) where
  /-- Global positions correspond to local positions in Jordan components. -/
  indexEquiv : Fin n ≃
    Σ k : Fin t, Fin (J.toOrthogonalDecomposition.componentRank k)
  /-- The correspondence is lexicographically order preserving. -/
  order_iff : ∀ i j : Fin n,
    i < j ↔ ComponentIndexBefore J.toOrthogonalDecomposition
      (indexEquiv i) (indexEquiv j)
  /-- Every order is the value prescribed by its Jordan component. -/
  order_eq : ∀ i : Fin n,
    b.order i = jordanExpectedOrder J (indexEquiv i).1 (indexEquiv i).2

end BONG

/-- The Jordan-profile correspondence and invariance in Beli (2003), Lemma 4.7. -/
class BeliLemma47Laws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  /-- A good BONG has the exact profile prescribed by every Jordan splitting. -/
  jordanOrderProfile
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n t : Nat}
    (b : BONG V q L n) (hgood : b.IsGood)
    (J : Lattice.JordanDecomposition q L t) :
    Nonempty (BONG.JordanOrderProfileWitness b J)
  /-- In particular, good BONG orders are independent of the chosen BONG. -/
  goodBONG_orders_eq
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (b c : BONG V q L n) (hb : b.IsGood) (hc : c.IsGood) :
    ∀ i, b.order i = c.order i

namespace BONG

variable [BeliLemma47Laws.{u, v} K]

/-- Beli (2003), Lemma 4.7, profile form. -/
theorem beliLemma47_profile (b : BONG V q L n) (hgood : b.IsGood)
    (J : Lattice.JordanDecomposition q L t) :
    Nonempty (JordanOrderProfileWitness b J) :=
  BeliLemma47Laws.jordanOrderProfile b hgood J

/-- Beli (2003), Lemma 4.7, invariance consequence. -/
theorem beliLemma47_orders_eq (b c : BONG V q L n)
    (hb : b.IsGood) (hc : c.IsGood) :
    ∀ i, b.order i = c.order i :=
  BeliLemma47Laws.goodBONG_orders_eq b c hb hc

end BONG

end Bong
