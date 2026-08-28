/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009ConcreteJordanChain
import Bong.Bong.BeliLemma47Proof
import Bong.Bong.Beli2009OrthogonalIdealProof
import Bong.Lattice.OrthogonalSupScale

/-!
# Endpoint norm generators under Jordan amalgamation

Beli (2009), Lemma 2.13 starts from a maximal norm splitting and then
amalgamates consecutive components of equal scale.  The order-profile proof
already performs this amalgamation, but an order profile alone does not retain
the first and last scalar norm generators.  This file supplies the missing
value-level layer.

The basic observation is intrinsic: if two orthogonal components have the same
norm ideal, a scalar norm generator of either component remains a scalar norm
generator after they are amalgamated.  The maximal-norm inequalities imply
that equal-scale components do have the same norm order.
-/

namespace Bong

open Dyadic Module

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n t : Nat}

namespace Lattice

section OrthogonalProduct

variable {W : Type w} [AddCommGroup W] [Module K W]
  {r : QuadraticSpace K W} {M₀ : Lattice K W}

/-- The left error ideal `2sL` embeds in that of an orthogonal product. -/
theorem twoScaleIdeal_le_orthogonalProduct_left :
    twoScaleIdeal q L ≤
      twoScaleIdeal (q.orthogonalSum r) (product L M₀) := by
  unfold twoScaleIdeal twiceIdeal
  apply Submodule.map_mono
  rw [scaleIdeal_orthogonalProduct]
  exact _root_.le_sup_left

/-- The right error ideal `2sM` embeds in that of an orthogonal product. -/
theorem twoScaleIdeal_le_orthogonalProduct_right :
    twoScaleIdeal r M₀ ≤
      twoScaleIdeal (q.orthogonalSum r) (product L M₀) := by
  unfold twoScaleIdeal twiceIdeal
  apply Submodule.map_mono
  rw [scaleIdeal_orthogonalProduct]
  exact _root_.le_sup_right

/-- A scalar norm generator of the left factor remains one for an orthogonal
product when the right norm ideal is contained in the left norm ideal. -/
theorem IsNormGeneratorValue.orthogonalProduct_left
    {a : Kˣ} (ha : IsNormGeneratorValue q L a)
    (hM : normIdeal r M₀ ≤ normIdeal q L) :
    IsNormGeneratorValue (q.orthogonalSum r) (product L M₀) a := by
  constructor
  · rcases ha.1 with ⟨x, hx, y, hy, hvalue⟩
    refine ⟨(x, 0), mem_product_iff.2 ⟨hx, Submodule.zero_mem _⟩,
      y, twoScaleIdeal_le_orthogonalProduct_left hy, ?_⟩
    simpa only [QuadraticSpace.orthogonalSum_quadratic_apply,
      QuadraticSpace.quadratic_zero, add_zero] using hvalue
  · rw [normIdeal_orthogonalProduct, sup_eq_left.mpr hM]
    exact ha.2

/-- The symmetric right-factor form of
`IsNormGeneratorValue.orthogonalProduct_left`. -/
theorem IsNormGeneratorValue.orthogonalProduct_right
    {a : Kˣ} (ha : IsNormGeneratorValue r M₀ a)
    (hL : normIdeal q L ≤ normIdeal r M₀) :
    IsNormGeneratorValue (q.orthogonalSum r) (product L M₀) a := by
  constructor
  · rcases ha.1 with ⟨x, hx, y, hy, hvalue⟩
    refine ⟨(0, x), mem_product_iff.2 ⟨Submodule.zero_mem _, hx⟩,
      y, twoScaleIdeal_le_orthogonalProduct_right hy, ?_⟩
    simpa only [QuadraticSpace.orthogonalSum_quadratic_apply,
      QuadraticSpace.quadratic_zero, zero_add] using hvalue
  · rw [normIdeal_orthogonalProduct, sup_eq_right.mpr hL]
    exact ha.2

end OrthogonalProduct

/-- A scalar norm generator of the left component remains one for the
orthogonal amalgamation when the two component norm ideals agree. -/
theorem IsNormGeneratorValue.orthogonalSup_left
    (D : OrthogonalDecomposition q L t) {i j : Fin t} (hij : i ≠ j)
    {a : Kˣ}
    (ha : IsNormGeneratorValue
      (D.component i).space (D.component i).lattice a)
    (hnorm : normIdeal (D.component j).space (D.component j).lattice =
      normIdeal (D.component i).space (D.component i).lattice) :
    IsNormGeneratorValue
      (D.orthogonalSup hij).space (D.orthogonalSup hij).lattice a :=
  (ha.orthogonalProduct_left hnorm.le).mapLatticeIsometry
    (D.orthogonalSupLatticeIsometry hij)

/-- The symmetric right-component form of
`IsNormGeneratorValue.orthogonalSup_left`. -/
theorem IsNormGeneratorValue.orthogonalSup_right
    (D : OrthogonalDecomposition q L t) {i j : Fin t} (hij : i ≠ j)
    {a : Kˣ}
    (ha : IsNormGeneratorValue
      (D.component j).space (D.component j).lattice a)
    (hnorm : normIdeal (D.component i).space (D.component i).lattice =
      normIdeal (D.component j).space (D.component j).lattice) :
    IsNormGeneratorValue
      (D.orthogonalSup hij).space (D.orthogonalSup hij).lattice a :=
  (ha.orthogonalProduct_right hnorm.le).mapLatticeIsometry
    (D.orthogonalSupLatticeIsometry hij)

namespace JordanDecomposition

/-- A scalar norm generator of a Jordan component also generates the
intrinsic scale layer when the component norm order is the effective norm
order at that scale.  This is the general form of the second half of Beli
(2009), Lemma 2.13(iii); property A is only one way to prove the displayed
effective-norm equality. -/
theorem isNormGeneratorValue_fundamentalLattice
    (J : JordanDecomposition q L t) (i : Fin t) {a : Kˣ}
    (ha : IsNormGeneratorValue
      (J.component i).space (J.component i).lattice a)
    (heffective : BONG.jordanEffectiveNormOrder J i =
      ordUnit K (J.normGenerator i)) :
    IsNormGeneratorValue q (J.fundamentalLattice i) a := by
  let D := J.scaleTruncationDecomposition (J.fundamentalScaleOrder i)
  have hcomponentD : IsNormGeneratorValue
      (D.component i).space (D.component i).lattice a := by
    have hDi : D.component i = J.component i := by
      simpa only [D, fundamentalScaleOrder] using
        J.scaleTruncationDecomposition_component_self i
    rw [hDi]
    exact ha
  have hmember : (a : K) ∈ normGroupSet q (J.fundamentalLattice i) := by
    have hsubset := D.component_normGroupSet_subset i hcomponentD.1
    simpa only [D, fundamentalLattice, fundamentalScaleOrder,
      scaleTruncationDecomposition_component_self] using hsubset
  have hprincipal : principalIdeal (K := K) (a : K) =
      principalIdeal (K := K) (J.normGenerator i : K) := by
    calc
      principalIdeal (K := K) (a : K) =
          normIdeal (J.component i).space (J.component i).lattice :=
        ha.2.symm
      _ = principalIdeal (K := K) (J.normGenerator i : K) :=
        J.normIdeal_eq i
  have horder : ordUnit K a = ordUnit K (J.normGenerator i) :=
    (principalIdeal_eq_iff_ordUnit_eq a (J.normGenerator i)).mp hprincipal
  refine ⟨hmember, ?_⟩
  calc
    normIdeal q (J.fundamentalLattice i) =
        powerIdeal (K := K) (BONG.jordanEffectiveNormOrder J i) := by
      exact J.normIdeal_scaleTruncation_eq_powerIdeal i
        (J.fundamentalScaleOrder i)
    _ = powerIdeal (K := K) (ordUnit K (J.normGenerator i)) := by
      rw [heffective]
    _ = powerIdeal (K := K) (ordUnit K a) := by rw [horder]
    _ = principalIdeal (K := K) (a : K) :=
      (principalIdeal_eq_powerIdeal a).symm

end JordanDecomposition

end Lattice

namespace Lattice.MaximalNormSplitting

variable (M : MaximalNormSplitting q L t)
  (c : M.toOrthogonalDecomposition.ComponentBONGFamily)

/-- Equal scale orders in a maximal norm splitting force equal norm orders.
This is the equality case of the two norm-gap inequalities in Definition 8. -/
theorem normGeneratorOrder_eq_of_scaleOrder_eq (i j : Fin t)
    (hscale : ordUnit K (M.scaleGenerator i) =
      ordUnit K (M.scaleGenerator j)) :
    ordUnit K (M.normGenerator i) = ordUnit K (M.normGenerator j) := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · have h := M.normGap_bounds hij
    omega
  · rfl
  · have h := M.normGap_bounds hji
    omega

/-- Beli's rescaled terminal scalar for one component of a maximal norm
splitting. -/
noncomputable def componentTerminalNormValue (i : Fin t) : Kˣ :=
  uniformizerPowerUnit K
      (2 * ordUnit K (M.normGenerator i) -
        2 * ordUnit K (M.scaleGenerator i)) *
    (c i).valueUnit (M.componentLastIndex i)

/-- The rescaled last value of every unary-or-modular-binary component is an
actual scalar norm generator of that component. -/
theorem componentTerminalNormValue_isNormGeneratorValue (i : Fin t) :
    Lattice.IsNormGeneratorValue
      (M.component i).space (M.component i).lattice
      (M.componentTerminalNormValue c i) := by
  rcases M.unary_or_modular_binary i with hOne | ⟨hTwo, hmodular⟩
  · have hlast : M.componentLastIndex i = M.componentFirstIndex i := by
      apply Fin.ext
      simp only [componentLastIndex, componentFirstIndex]
      change M.componentRank i - 1 = 0
      change M.componentRank i = 1 at hOne
      omega
    have hmodular := M.component_isModular c i
    have hnormScale : ordUnit K (M.normGenerator i) =
        ordUnit K (M.scaleGenerator i) :=
      Lattice.ordUnit_normGenerator_eq_scaleGenerator_of_finrank_eq_one
        (M.component i).space (M.component i).lattice
        (M.scaleGenerator i) (M.normGenerator i) hOne hmodular
        (M.normIdeal_eq i)
    have hgenerator := M.componentFirst_isNormGenerator c i
    have hne : (M.component i).space.quadratic
        ((c i).ambientVector (M.componentFirstIndex i)) ≠ 0 := by
      rw [(c i).quadratic_ambientVector]
      exact (c i).value_ne_zero _
    have hvalue := hgenerator.isNormGeneratorValue hne
    convert hvalue using 1
    apply Units.ext
    simp only [componentTerminalNormValue, hnormScale, sub_self,
      uniformizerPowerUnit, zpow_zero, one_mul, hlast,
      BONG.coe_valueUnit, Units.val_mk0, (c i).quadratic_ambientVector]
  · let b₂ := (c i).castLength hTwo
    have hterminal := b₂.modularTerminalNormValue_isNormGeneratorValue
      (M.scaleGenerator i) hmodular
    have hfirstOrder : b₂.order 0 = ordUnit K (M.normGenerator i) := by
      calc
        b₂.order 0 = (c i).order (M.componentFirstIndex i) := by
          rw [BONG.order_castLength]
          apply congrArg (c i).order
          apply Fin.ext
          rfl
        _ = ordUnit K (M.normGenerator i) :=
          M.componentFirst_order_eq_normGeneratorOrder c i
    have hlast : M.componentLastIndex i =
        (⟨1, by change M.componentRank i = 2 at hTwo
                change 1 < M.componentRank i
                omega⟩ :
          Fin (M.toOrthogonalDecomposition.componentRank i)) := by
      apply Fin.ext
      simp only [componentLastIndex]
      change M.componentRank i - 1 = 1
      change M.componentRank i = 2 at hTwo
      omega
    convert hterminal using 1
    apply Units.ext
    simp only [componentTerminalNormValue, BONG.modularTerminalNormValue,
      Units.val_mul]
    rw [hfirstOrder]
    congr 1
    rw [BONG.coe_valueUnit, BONG.coe_valueUnit, BONG.value_castLength]
    congr 1

end Lattice.MaximalNormSplitting

namespace Lattice.WeakJordanDecomposition

variable (W : WeakJordanDecomposition q L t)

/-- The first local coordinate of a positive-rank weak Jordan component. -/
noncomputable def endpointFirstIndex (i : Fin t) :
    Fin (finrank K (W.component i).carrier) :=
  ⟨0, W.component_finrank_pos i⟩

/-- The last local coordinate of a positive-rank weak Jordan component. -/
noncomputable def endpointLastIndex (i : Fin t) :
    Fin (finrank K (W.component i).carrier) :=
  ⟨finrank K (W.component i).carrier - 1, by
    exact Nat.sub_lt (W.component_finrank_pos i) Nat.zero_lt_one⟩

@[simp]
theorem endpointLastIndex_val_add_one (i : Fin t) :
    (W.endpointLastIndex i).val + 1 =
      finrank K (W.component i).carrier := by
  rw [endpointLastIndex]
  exact Nat.sub_add_cancel (Nat.succ_le_iff.mpr (W.component_finrank_pos i))

end Lattice.WeakJordanDecomposition

namespace BONG

namespace WeakJordanOrderProfileWitness

variable {b : BONG V q L n} {W : Lattice.WeakJordanDecomposition q L t}

/-- The global BONG value occupying the first coordinate of a weak Jordan
component. -/
noncomputable def endpointFirstValue
    (w : WeakJordanOrderProfileWitness b W) (i : Fin t) : Kˣ :=
  b.valueUnit (w.indexEquiv.symm ⟨i, W.endpointFirstIndex i⟩)

/-- The unscaled global BONG value occupying the last coordinate of a weak
Jordan component. -/
noncomputable def endpointLastValue
    (w : WeakJordanOrderProfileWitness b W) (i : Fin t) : Kˣ :=
  b.valueUnit (w.indexEquiv.symm ⟨i, W.endpointLastIndex i⟩)

/-- The rescaled global BONG value occupying the last coordinate of a weak
Jordan component. -/
noncomputable def endpointTerminalValue
    (w : WeakJordanOrderProfileWitness b W) (i : Fin t) : Kˣ :=
  uniformizerPowerUnit K
      (2 * ordUnit K (W.normGeneratorUnit i) -
        2 * ordUnit K (W.scaleGenerator i)) *
    w.endpointLastValue i

/-- The inverse global index after amalgamation is obtained by first splitting
the new component coordinate back into the old weak family. -/
theorem inverse_indexEquiv_mergeAdjacentAt {s : Nat}
    {W : Lattice.WeakJordanDecomposition q L (s + 1)}
    (hW : W.HasImproperEvenRank)
    (w : WeakJordanOrderProfileWitness b W) (k : Fin s)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ))
    (z : Σ i : Fin s,
      Fin (finrank K ((W.mergeAdjacentAt k heq).component i).carrier)) :
    (w.mergeAdjacentAt W hW k heq).indexEquiv.symm z =
      w.indexEquiv.symm (W.mergeIndexEquiv k heq z) := by
  rfl

/-- The first global value of the amalgamated component is the first global
value of its old left neighbour. -/
theorem endpointFirstValue_mergeAdjacentAt_self {s : Nat}
    {W : Lattice.WeakJordanDecomposition q L (s + 1)}
    (hW : W.HasImproperEvenRank)
    (w : WeakJordanOrderProfileWitness b W) (k : Fin s)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ)) :
    (w.mergeAdjacentAt W hW k heq).endpointFirstValue k =
      w.endpointFirstValue k.castSucc := by
  unfold endpointFirstValue
  rw [w.inverse_indexEquiv_mergeAdjacentAt hW k heq]
  apply congrArg b.valueUnit
  apply congrArg w.indexEquiv.symm
  let oldFirst := W.endpointFirstIndex k.castSucc
  let mergedFirst := (W.mergeAdjacentAt k heq).endpointFirstIndex k
  have hcanonical : mergedFirst =
      (⟨oldFirst.val, by
        rw [W.mergeAdjacentAt_componentRank_self k heq]
        exact oldFirst.isLt.trans_le (Nat.le_add_right _ _)⟩ :
        Fin (finrank K ((W.mergeAdjacentAt k heq).component k).carrier)) :=
    Fin.ext rfl
  rw [show (W.mergeAdjacentAt k heq).endpointFirstIndex k =
      mergedFirst by rfl, hcanonical]
  exact W.mergeIndexEquiv_left k heq oldFirst

/-- A component away from the merge keeps its first global endpoint value. -/
theorem endpointFirstValue_mergeAdjacentAt_of_ne {s : Nat}
    {W : Lattice.WeakJordanDecomposition q L (s + 1)}
    (hW : W.HasImproperEvenRank)
    (w : WeakJordanOrderProfileWitness b W) (k : Fin s)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ))
    (j : Fin s) (hjk : j ≠ k) :
    (w.mergeAdjacentAt W hW k heq).endpointFirstValue j =
      w.endpointFirstValue (k.succ.succAbove j) := by
  unfold endpointFirstValue
  rw [w.inverse_indexEquiv_mergeAdjacentAt hW k heq]
  apply congrArg b.valueUnit
  apply congrArg w.indexEquiv.symm
  rcases lt_trichotomy j k with hjkLt | hjkEq | hkjLt
  · have hmap := W.mergeIndexEquiv_of_lt k heq j hjkLt
      ((W.mergeAdjacentAt k heq).endpointFirstIndex j)
    have hold : k.succ.succAbove j = j.castSucc := by
      rw [Fin.succAbove_of_castSucc_lt]
      exact Fin.castSucc_lt_succ_iff.mpr hjkLt.le
    rw [hold]
    convert hmap using 1
    apply Sigma.ext
    · rfl
    · simp [Lattice.WeakJordanDecomposition.endpointFirstIndex]
  · exact (hjk hjkEq).elim
  · have hmap := W.mergeIndexEquiv_of_gt k heq j hkjLt
      ((W.mergeAdjacentAt k heq).endpointFirstIndex j)
    have hold : k.succ.succAbove j = j.succ := by
      rw [Fin.succAbove_of_le_castSucc]
      exact Fin.succ_le_castSucc_iff.mpr hkjLt
    rw [hold]
    convert hmap using 1
    apply Sigma.ext
    · rfl
    · simp [Lattice.WeakJordanDecomposition.endpointFirstIndex]

/-- The last global value of the amalgamated component is the last global
value of its old right neighbour. -/
theorem endpointLastValue_mergeAdjacentAt_self {s : Nat}
    {W : Lattice.WeakJordanDecomposition q L (s + 1)}
    (hW : W.HasImproperEvenRank)
    (w : WeakJordanOrderProfileWitness b W) (k : Fin s)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ)) :
    (w.mergeAdjacentAt W hW k heq).endpointLastValue k =
      w.endpointLastValue k.succ := by
  unfold endpointLastValue
  rw [w.inverse_indexEquiv_mergeAdjacentAt hW k heq]
  apply congrArg b.valueUnit
  apply congrArg w.indexEquiv.symm
  let rightLast := W.endpointLastIndex k.succ
  let mergedLast := (W.mergeAdjacentAt k heq).endpointLastIndex k
  let canonicalRight : Fin
      (finrank K ((W.mergeAdjacentAt k heq).component k).carrier) :=
    ⟨finrank K (W.component k.castSucc).carrier + rightLast.val, by
      rw [W.mergeAdjacentAt_componentRank_self k heq]
      exact Nat.add_lt_add_left rightLast.isLt _⟩
  have hcanonical : mergedLast = canonicalRight := by
    apply Fin.ext
    have hright := W.endpointLastIndex_val_add_one k.succ
    have hmerged :=
      (W.mergeAdjacentAt k heq).endpointLastIndex_val_add_one k
    have hrank := W.mergeAdjacentAt_componentRank_self k heq
    dsimp only [mergedLast, canonicalRight, Fin.val_mk]
    omega
  rw [show (W.mergeAdjacentAt k heq).endpointLastIndex k =
      mergedLast by rfl, hcanonical]
  exact W.mergeIndexEquiv_right k heq rightLast

/-- A component away from the merge keeps its last global endpoint value. -/
theorem endpointLastValue_mergeAdjacentAt_of_ne {s : Nat}
    {W : Lattice.WeakJordanDecomposition q L (s + 1)}
    (hW : W.HasImproperEvenRank)
    (w : WeakJordanOrderProfileWitness b W) (k : Fin s)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ))
    (j : Fin s) (hjk : j ≠ k) :
    (w.mergeAdjacentAt W hW k heq).endpointLastValue j =
      w.endpointLastValue (k.succ.succAbove j) := by
  unfold endpointLastValue
  rw [w.inverse_indexEquiv_mergeAdjacentAt hW k heq]
  apply congrArg b.valueUnit
  apply congrArg w.indexEquiv.symm
  rcases lt_trichotomy j k with hjkLt | hjkEq | hkjLt
  · have hmap := W.mergeIndexEquiv_of_lt k heq j hjkLt
      ((W.mergeAdjacentAt k heq).endpointLastIndex j)
    have hold : k.succ.succAbove j = j.castSucc := by
      rw [Fin.succAbove_of_castSucc_lt]
      exact Fin.castSucc_lt_succ_iff.mpr hjkLt.le
    have hrank : finrank K ((W.mergeAdjacentAt k heq).component j).carrier =
        finrank K (W.component j.castSucc).carrier := by
      rw [W.mergeAdjacentAt_component_of_ne k heq j (Fin.ne_of_lt hjkLt),
        hold]
    rw [hold]
    convert hmap using 1
    apply Sigma.ext
    · rfl
    · simp [Lattice.WeakJordanDecomposition.endpointLastIndex, hrank]
  · exact (hjk hjkEq).elim
  · have hmap := W.mergeIndexEquiv_of_gt k heq j hkjLt
      ((W.mergeAdjacentAt k heq).endpointLastIndex j)
    have hold : k.succ.succAbove j = j.succ := by
      rw [Fin.succAbove_of_le_castSucc]
      exact Fin.succ_le_castSucc_iff.mpr hkjLt
    have hrank : finrank K ((W.mergeAdjacentAt k heq).component j).carrier =
        finrank K (W.component j.succ).carrier := by
      rw [W.mergeAdjacentAt_component_of_ne k heq j (Fin.ne_of_gt hkjLt),
        hold]
    rw [hold]
    convert hmap using 1
    apply Sigma.ext
    · rfl
    · simp [Lattice.WeakJordanDecomposition.endpointLastIndex, hrank]

end WeakJordanOrderProfileWitness

/-- A weak Jordan order profile enhanced with the two value-level facts used
in Beli (2009), Lemma 2.13(iii).  The effective-norm equality is retained
because it is exactly the invariant needed when equal-scale neighbours are
amalgamated. -/
structure WeakJordanEndpointWitness
    (b : BONG V q L n) {t : Nat}
    (W : Lattice.WeakJordanDecomposition q L t) where
  profile : WeakJordanOrderProfileWitness b W
  normOrder_eq_effective : ∀ i,
    ordUnit K (W.normGeneratorUnit i) =
      W.effectiveNormOrderAt i (ordUnit K (W.scaleGenerator i))
  firstGenerator : ∀ i,
    Lattice.IsNormGeneratorValue
      (W.component i).space (W.component i).lattice
      (profile.endpointFirstValue i)
  terminalGenerator : ∀ i,
    Lattice.IsNormGeneratorValue
      (W.component i).space (W.component i).lattice
      (profile.endpointTerminalValue i)

namespace WeakJordanEndpointWitness

variable {b : BONG V q L n} {W : Lattice.WeakJordanDecomposition q L t}

/-- Components at the same scale in an endpoint witness have the same norm
order. -/
theorem normOrder_eq_of_scaleOrder_eq
    (E : WeakJordanEndpointWitness b W) (i j : Fin t)
    (hscale : ordUnit K (W.scaleGenerator i) =
      ordUnit K (W.scaleGenerator j)) :
    ordUnit K (W.normGeneratorUnit i) =
      ordUnit K (W.normGeneratorUnit j) := by
  rw [E.normOrder_eq_effective i, E.normOrder_eq_effective j]
  calc
    W.effectiveNormOrderAt i (ordUnit K (W.scaleGenerator i)) =
        W.effectiveNormOrderAt j (ordUnit K (W.scaleGenerator i)) :=
      W.effectiveNormOrderAt_anchor_irrel i j _
    _ = W.effectiveNormOrderAt j
        (ordUnit K (W.scaleGenerator j)) := by rw [hscale]

/-- The effective-norm equality is preserved by one equal-scale adjacent
amalgamation. -/
theorem normOrder_eq_effective_mergeAdjacentAt {s : Nat}
    {W : Lattice.WeakJordanDecomposition q L (s + 1)}
    (E : WeakJordanEndpointWitness b W) (k : Fin s)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ)) (j : Fin s) :
    ordUnit K ((W.mergeAdjacentAt k heq).normGeneratorUnit j) =
      (W.mergeAdjacentAt k heq).effectiveNormOrderAt j
        (ordUnit K ((W.mergeAdjacentAt k heq).scaleGenerator j)) := by
  by_cases hjk : j = k
  · subst j
    have hnorm := E.normOrder_eq_of_scaleOrder_eq
      k.castSucc k.succ heq
    rw [W.ordUnit_normGeneratorUnit_mergeAdjacentAt_self k heq,
      hnorm, min_self]
    rw [W.effectiveNormOrderAt_mergeAdjacentAt k heq k k.castSucc]
    simp only [W.mergeAdjacentAt_scaleGenerator, Fin.succAbove_succ_self]
    rw [← hnorm]
    exact E.normOrder_eq_effective k.castSucc
  · let old := k.succ.succAbove j
    rw [W.ordUnit_normGeneratorUnit_mergeAdjacentAt_of_ne k heq j hjk]
    rw [W.effectiveNormOrderAt_mergeAdjacentAt k heq j old]
    simp only [W.mergeAdjacentAt_scaleGenerator]
    exact E.normOrder_eq_effective old

/-- The rescaled terminal value of the merged component is exactly that of
the old right neighbour. -/
theorem endpointTerminalValue_mergeAdjacentAt_self {s : Nat}
    {W : Lattice.WeakJordanDecomposition q L (s + 1)}
    (E : WeakJordanEndpointWitness b W) (hW : W.HasImproperEvenRank)
    (k : Fin s)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ)) :
    (E.profile.mergeAdjacentAt W hW k heq).endpointTerminalValue k =
      E.profile.endpointTerminalValue k.succ := by
  unfold WeakJordanOrderProfileWitness.endpointTerminalValue
  rw [E.profile.endpointLastValue_mergeAdjacentAt_self hW k heq]
  rw [W.ordUnit_normGeneratorUnit_mergeAdjacentAt_self k heq]
  have hnorm := E.normOrder_eq_of_scaleOrder_eq
    k.castSucc k.succ heq
  rw [hnorm, min_self]
  simp only [W.mergeAdjacentAt_scaleGenerator, Fin.succAbove_succ_self]
  rw [heq]

/-- A component away from the merge keeps its rescaled terminal value. -/
theorem endpointTerminalValue_mergeAdjacentAt_of_ne {s : Nat}
    {W : Lattice.WeakJordanDecomposition q L (s + 1)}
    (E : WeakJordanEndpointWitness b W) (hW : W.HasImproperEvenRank)
    (k : Fin s)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ))
    (j : Fin s) (hjk : j ≠ k) :
    (E.profile.mergeAdjacentAt W hW k heq).endpointTerminalValue j =
      E.profile.endpointTerminalValue (k.succ.succAbove j) := by
  unfold WeakJordanOrderProfileWitness.endpointTerminalValue
  rw [E.profile.endpointLastValue_mergeAdjacentAt_of_ne hW k heq j hjk]
  rw [W.ordUnit_normGeneratorUnit_mergeAdjacentAt_of_ne k heq j hjk]
  simp only [W.mergeAdjacentAt_scaleGenerator]

/-- The first endpoint generator property is preserved by one equal-scale
amalgamation. -/
theorem firstGenerator_mergeAdjacentAt {s : Nat}
    {W : Lattice.WeakJordanDecomposition q L (s + 1)}
    (E : WeakJordanEndpointWitness b W) (hW : W.HasImproperEvenRank)
    (k : Fin s)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ)) (j : Fin s) :
    Lattice.IsNormGeneratorValue
      ((W.mergeAdjacentAt k heq).component j).space
      ((W.mergeAdjacentAt k heq).component j).lattice
      ((E.profile.mergeAdjacentAt W hW k heq).endpointFirstValue j) := by
  by_cases hjk : j = k
  · subst j
    have horder := E.normOrder_eq_of_scaleOrder_eq
      k.castSucc k.succ heq
    have hnorm :
        Lattice.normIdeal (W.component k.succ).space
            (W.component k.succ).lattice =
          Lattice.normIdeal (W.component k.castSucc).space
            (W.component k.castSucc).lattice := by
      rw [W.normIdeal_eq_normGeneratorUnit,
        W.normIdeal_eq_normGeneratorUnit]
      exact (Lattice.principalIdeal_eq_iff_ordUnit_eq _ _).2 horder.symm
    have hgen := (E.firstGenerator k.castSucc).orthogonalSup_left
      W.toOrthogonalDecomposition k.castSucc_lt_succ.ne hnorm
    rw [W.mergeAdjacentAt_component_self k heq,
      E.profile.endpointFirstValue_mergeAdjacentAt_self hW k heq]
    exact hgen
  · rw [W.mergeAdjacentAt_component_of_ne k heq j hjk,
      E.profile.endpointFirstValue_mergeAdjacentAt_of_ne hW k heq j hjk]
    exact E.firstGenerator (k.succ.succAbove j)

/-- The terminal endpoint generator property is preserved by one equal-scale
amalgamation. -/
theorem terminalGenerator_mergeAdjacentAt {s : Nat}
    {W : Lattice.WeakJordanDecomposition q L (s + 1)}
    (E : WeakJordanEndpointWitness b W) (hW : W.HasImproperEvenRank)
    (k : Fin s)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ)) (j : Fin s) :
    Lattice.IsNormGeneratorValue
      ((W.mergeAdjacentAt k heq).component j).space
      ((W.mergeAdjacentAt k heq).component j).lattice
      ((E.profile.mergeAdjacentAt W hW k heq).endpointTerminalValue j) := by
  by_cases hjk : j = k
  · subst j
    have horder := E.normOrder_eq_of_scaleOrder_eq
      k.castSucc k.succ heq
    have hnorm :
        Lattice.normIdeal (W.component k.castSucc).space
            (W.component k.castSucc).lattice =
          Lattice.normIdeal (W.component k.succ).space
            (W.component k.succ).lattice := by
      rw [W.normIdeal_eq_normGeneratorUnit,
        W.normIdeal_eq_normGeneratorUnit]
      exact (Lattice.principalIdeal_eq_iff_ordUnit_eq _ _).2 horder
    have hgen := (E.terminalGenerator k.succ).orthogonalSup_right
      W.toOrthogonalDecomposition k.castSucc_lt_succ.ne hnorm
    rw [W.mergeAdjacentAt_component_self k heq,
      E.endpointTerminalValue_mergeAdjacentAt_self hW k heq]
    exact hgen
  · rw [W.mergeAdjacentAt_component_of_ne k heq j hjk,
      E.endpointTerminalValue_mergeAdjacentAt_of_ne hW k heq j hjk]
    exact E.terminalGenerator (k.succ.succAbove j)

/-- One equal-scale adjacent amalgamation preserves the full endpoint
witness. -/
noncomputable def mergeAdjacentAt {s : Nat}
    {W : Lattice.WeakJordanDecomposition q L (s + 1)}
    (E : WeakJordanEndpointWitness b W) (hW : W.HasImproperEvenRank)
    (k : Fin s)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ)) :
    WeakJordanEndpointWitness b (W.mergeAdjacentAt k heq) where
  profile := E.profile.mergeAdjacentAt W hW k heq
  normOrder_eq_effective := E.normOrder_eq_effective_mergeAdjacentAt k heq
  firstGenerator := E.firstGenerator_mergeAdjacentAt hW k heq
  terminalGenerator := E.terminalGenerator_mergeAdjacentAt hW k heq

end WeakJordanEndpointWitness

/-- A strict weak Jordan decomposition together with the value-level endpoint
witness obtained by amalgamating equal-scale maximal-norm components. -/
structure StrictJordanEndpointWitness (b : BONG V q L n) where
  componentCount : Nat
  weak : Lattice.WeakJordanDecomposition q L componentCount
  strict : StrictMono (fun i ↦ ordUnit K (weak.scaleGenerator i))
  endpoints : WeakJordanEndpointWitness b weak

namespace WeakJordanEndpointWitness

/-- Repeated equal-scale amalgamation terminates while preserving both
endpoint norm generators. -/
theorem exists_strict :
    ∀ (s : Nat) (W : Lattice.WeakJordanDecomposition q L s),
      W.HasImproperEvenRank → WeakJordanEndpointWitness b W →
        Nonempty (StrictJordanEndpointWitness b) := by
  intro s
  induction s using Nat.strong_induction_on with
  | h s ih =>
      intro W hparity E
      let f : Fin s → Int := fun i ↦ ordUnit K (W.scaleGenerator i)
      by_cases hstrict : StrictMono f
      · exact ⟨{
          componentCount := s
          weak := W
          strict := hstrict
          endpoints := E
        }⟩
      · cases s with
        | zero =>
            exfalso
            apply hstrict
            exact fun i ↦ Fin.elim0 i
        | succ s =>
            cases s with
            | zero =>
                exfalso
                apply hstrict
                intro i j hij
                omega
            | succ m =>
                have hadj : ¬∀ k : Fin (m + 1),
                    f k.castSucc < f k.succ := by
                  intro hall
                  exact hstrict ((Fin.strictMono_iff_lt_succ).2 hall)
                push Not at hadj
                obtain ⟨k, hk⟩ := hadj
                have hle : f k.castSucc ≤ f k.succ :=
                  W.scaleOrder_mono k.castSucc_lt_succ.le
                have heq : ordUnit K (W.scaleGenerator k.castSucc) =
                    ordUnit K (W.scaleGenerator k.succ) :=
                  le_antisymm hle hk
                let W' := W.mergeAdjacentAt k heq
                have hparity' : W'.HasImproperEvenRank :=
                  Lattice.WeakJordanDecomposition.HasImproperEvenRank.mergeAdjacentAt
                    W hparity k heq
                let E' : WeakJordanEndpointWitness b W' :=
                  E.mergeAdjacentAt hparity k heq
                exact ih (m + 1) (by omega) W' hparity' E'

end WeakJordanEndpointWitness

namespace StrictJordanEndpointWitness

variable {b : BONG V q L n} (S : StrictJordanEndpointWitness b)

/-- The strict weak family gives the genuine Jordan decomposition used in
Beli (2009), Lemma 2.13. -/
noncomputable def jordan :
    Lattice.JordanDecomposition q L S.componentCount :=
  S.weak.toJordan S.strict

/-- The selected first endpoint is a norm generator of the intrinsic scale
layer as well as of the actual Jordan component. -/
theorem firstGenerator_fundamentalLattice (i : Fin S.componentCount) :
    Lattice.IsNormGeneratorValue q (S.jordan.fundamentalLattice i)
      (S.endpoints.profile.endpointFirstValue i) := by
  apply S.jordan.isNormGeneratorValue_fundamentalLattice i
  · exact S.endpoints.firstGenerator i
  · change S.weak.effectiveNormOrderAt i
        (ordUnit K (S.weak.scaleGenerator i)) =
      ordUnit K (S.weak.normGeneratorUnit i)
    exact (S.endpoints.normOrder_eq_effective i).symm

/-- The selected rescaled terminal endpoint is a norm generator of the
intrinsic scale layer as well as of the actual Jordan component. -/
theorem terminalGenerator_fundamentalLattice (i : Fin S.componentCount) :
    Lattice.IsNormGeneratorValue q (S.jordan.fundamentalLattice i)
      (S.endpoints.profile.endpointTerminalValue i) := by
  apply S.jordan.isNormGeneratorValue_fundamentalLattice i
  · exact S.endpoints.terminalGenerator i
  · change S.weak.effectiveNormOrderAt i
        (ordUnit K (S.weak.scaleGenerator i)) =
      ordUnit K (S.weak.normGeneratorUnit i)
    exact (S.endpoints.normOrder_eq_effective i).symm

/-- Beli (2009), Lemma 2.13(iii), for the general Jordan component obtained
by amalgamating any number of equal-scale maximal-norm blocks. -/
theorem beli2009Lemma213_iii_general (i : Fin S.componentCount) :
    Lattice.BothSignsNormGeneratorValue
        (S.jordan.component i).space (S.jordan.component i).lattice
        (S.endpoints.profile.endpointFirstValue i) ∧
      Lattice.BothSignsNormGeneratorValue q
        (S.jordan.fundamentalLattice i)
        (S.endpoints.profile.endpointFirstValue i) ∧
      Lattice.BothSignsNormGeneratorValue
        (S.jordan.component i).space (S.jordan.component i).lattice
        (S.endpoints.profile.endpointTerminalValue i) ∧
      Lattice.BothSignsNormGeneratorValue q
        (S.jordan.fundamentalLattice i)
        (S.endpoints.profile.endpointTerminalValue i) := by
  exact ⟨(S.endpoints.firstGenerator i).bothSigns,
    (S.firstGenerator_fundamentalLattice i).bothSigns,
    (S.endpoints.terminalGenerator i).bothSigns,
    (S.terminalGenerator_fundamentalLattice i).bothSigns⟩

end StrictJordanEndpointWitness

/-- The exact weak Jordan order profile obtained from a specified
put-together witness.  Keeping the specified witness, rather than choosing one
from a `Nonempty`, makes the later value identities definitional. -/
noncomputable def weakJordanOrderProfileOfPutTogether
    (M : Lattice.MaximalNormSplitting q L t)
    (c : M.toOrthogonalDecomposition.ComponentBONGFamily)
    (b : BONG V q L n)
    (h : PutTogetherWitness b M.toOrthogonalDecomposition c) :
    WeakJordanOrderProfileWitness b (M.toWeakJordan c) where
  indexEquiv := h.indexEquiv
  order_iff := by
    intro i j
    exact (h.order_iff i j).trans
      (JordanOrderProfileWitness.componentIndexBefore_iff_lex_lt
        M.toOrthogonalDecomposition (h.indexEquiv i) (h.indexEquiv j))
  order_eq := by
    intro i
    exact (h.order_eq i).trans
      (M.componentOrder_eq_weakJordanExpectedOrder c
        (h.indexEquiv i).1 (h.indexEquiv i).2)

namespace PutTogetherWitness

variable {M : Lattice.MaximalNormSplitting q L t}
  {c : M.toOrthogonalDecomposition.ComponentBONGFamily}
  {b : BONG V q L n}

/-- At an inverse component coordinate, the global value unit is the
corresponding local component value unit. -/
theorem valueUnit_inverse_indexEquiv
    (h : PutTogetherWitness b M.toOrthogonalDecomposition c)
    (i : Fin t) (j : Fin (M.toOrthogonalDecomposition.componentRank i)) :
    b.valueUnit (h.indexEquiv.symm ⟨i, j⟩) = (c i).valueUnit j := by
  apply Units.ext
  simp only [BONG.coe_valueUnit]
  have hv := h.ambientVector_eq (h.indexEquiv.symm ⟨i, j⟩)
  have heq : h.indexEquiv (h.indexEquiv.symm ⟨i, j⟩) = ⟨i, j⟩ :=
    h.indexEquiv.apply_symm_apply ⟨i, j⟩
  change b.value (h.indexEquiv.symm ⟨i, j⟩) = _
  rw [← b.quadratic_ambientVector,
    ← (c i).quadratic_ambientVector]
  rw [heq] at hv
  exact congrArg q.quadratic hv

end PutTogetherWitness

end BONG

namespace Lattice.MaximalNormSplitting

/-- The specified maximal norm splitting and concatenation witness carry the
full endpoint information before equal-scale amalgamation begins. -/
noncomputable def weakJordanEndpointWitness
    (M : Lattice.MaximalNormSplitting q L t)
    (c : M.toOrthogonalDecomposition.ComponentBONGFamily)
    (b : BONG V q L n)
    (h : BONG.PutTogetherWitness b M.toOrthogonalDecomposition c) :
    BONG.WeakJordanEndpointWitness b (M.toWeakJordan c) := by
  let w := BONG.weakJordanOrderProfileOfPutTogether M c b h
  refine {
    profile := w
    normOrder_eq_effective := ?_
    firstGenerator := ?_
    terminalGenerator := ?_
  }
  · intro i
    exact (M.toWeakJordan_normGeneratorOrder c i).trans
      (M.toWeakJordan_effectiveNormOrderAt_eq c i).symm
  · intro i
    have hlocal := M.componentFirst_isNormGenerator c i
    have hne : (M.component i).space.quadratic
        ((c i).ambientVector (M.componentFirstIndex i)) ≠ 0 := by
      rw [(c i).quadratic_ambientVector]
      exact (c i).value_ne_zero _
    have hvalue := hlocal.isNormGeneratorValue hne
    have hunit := h.valueUnit_inverse_indexEquiv i
      (M.componentFirstIndex i)
    change Lattice.IsNormGeneratorValue
      (M.component i).space (M.component i).lattice
      (b.valueUnit (h.indexEquiv.symm
        ⟨i, M.componentFirstIndex i⟩))
    rw [hunit]
    convert hvalue using 1
    apply Units.ext
    simp only [BONG.coe_valueUnit, Units.val_mk0,
      (c i).quadratic_ambientVector]
  · intro i
    have hlocal := M.componentTerminalNormValue_isNormGeneratorValue c i
    have hunit := h.valueUnit_inverse_indexEquiv i
      (M.componentLastIndex i)
    change Lattice.IsNormGeneratorValue
      (M.component i).space (M.component i).lattice
      (uniformizerPowerUnit K
          (2 * ordUnit K ((M.toWeakJordan c).normGeneratorUnit i) -
            2 * ordUnit K (M.scaleGenerator i)) *
        b.valueUnit (h.indexEquiv.symm
          ⟨i, M.componentLastIndex i⟩))
    rw [M.toWeakJordan_normGeneratorOrder c i, hunit]
    exact hlocal

/-- Amalgamate the endpoint witness of a specified maximal norm splitting to
a strict Jordan endpoint witness. -/
noncomputable def strictJordanEndpointWitness
    (M : Lattice.MaximalNormSplitting q L t)
    (c : M.toOrthogonalDecomposition.ComponentBONGFamily)
    (b : BONG V q L n)
    (h : BONG.PutTogetherWitness b M.toOrthogonalDecomposition c) :
    BONG.StrictJordanEndpointWitness b :=
  Classical.choice <|
    (M.weakJordanEndpointWitness c b h).exists_strict t (M.toWeakJordan c)
      (M.toWeakJordan_hasImproperEvenRank c)

end Lattice.MaximalNormSplitting

namespace BONG

namespace GoodBONG

/-- The genuine strict Jordan endpoint witness canonically selected from the
improper maximal norm splitting of a good BONG.  No Jordan-coordinate law
interface is used. -/
theorem nonempty_strictJordanEndpointWitness (b : GoodBONG q L n) :
    Nonempty (StrictJordanEndpointWitness b.toBONG) := by
  rcases b.toBONG.beliLemma43_iii b.good with
    ⟨t, M, c, hput, _⟩
  let h := Classical.choice hput
  exact ⟨M.strictJordanEndpointWitness c b.toBONG h⟩

noncomputable def strictJordanEndpointWitness (b : GoodBONG q L n) :
    StrictJordanEndpointWitness b.toBONG :=
  Classical.choice b.nonempty_strictJordanEndpointWitness

/-- Unconditional general-rank form of Beli (2009), Lemma 2.13(iii), for the
Jordan decomposition obtained from the good BONG's maximal norm splitting. -/
theorem beli2009Lemma213_iii_general (b : GoodBONG q L n)
    (i : Fin b.strictJordanEndpointWitness.componentCount) :
    Lattice.BothSignsNormGeneratorValue
        (b.strictJordanEndpointWitness.jordan.component i).space
        (b.strictJordanEndpointWitness.jordan.component i).lattice
        (b.strictJordanEndpointWitness.endpoints.profile.endpointFirstValue i) ∧
      Lattice.BothSignsNormGeneratorValue q
        (b.strictJordanEndpointWitness.jordan.fundamentalLattice i)
        (b.strictJordanEndpointWitness.endpoints.profile.endpointFirstValue i) ∧
      Lattice.BothSignsNormGeneratorValue
        (b.strictJordanEndpointWitness.jordan.component i).space
        (b.strictJordanEndpointWitness.jordan.component i).lattice
        (b.strictJordanEndpointWitness.endpoints.profile.endpointTerminalValue i) ∧
      Lattice.BothSignsNormGeneratorValue q
        (b.strictJordanEndpointWitness.jordan.fundamentalLattice i)
        (b.strictJordanEndpointWitness.endpoints.profile.endpointTerminalValue i) :=
  b.strictJordanEndpointWitness.beli2009Lemma213_iii_general i

end GoodBONG

end BONG

end Bong
