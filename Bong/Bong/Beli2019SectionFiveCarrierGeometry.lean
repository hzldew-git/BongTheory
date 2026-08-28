/- Carrier geometry of the two almost-Jordan decompositions in Section 5. -/
import Bong.Bong.Beli2019Lemma513Approximation
import Bong.Lattice.OrthogonalDecompositionPrefixCarrier

namespace Bong

open Dyadic Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V}

namespace Lattice.Beli2019Lemma51Data

/-- Enlarging the selected lattice in Lemma 5.1 does not change its ambient
quadratic subspace. -/
theorem selectedComponent_carrier_eq
    (D : Beli2019Lemma51Data q M N) :
    (D.largeAlmostJordan.component D.largeSelectedPosition).carrier =
      (D.smallAlmostJordan.component D.smallSelectedPosition).carrier := by
  rw [D.largeAlmostJordan_component_selected,
    D.smallAlmostJordan_component_selected]
  rfl

/-- When the selected positions are aligned, corresponding almost-Jordan
components have the same ambient carrier, including the selected component
whose integral lattice has changed. -/
theorem aligned_component_carrier_eq
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    (p : Fin (D.complementComponentCount + 1)) :
    (D.largeAlmostJordan.component p).carrier =
      (D.smallAlmostJordan.component p).carrier := by
  by_cases hp : p = D.largeSelectedPosition
  · subst p
    exact D.selectedComponent_carrier_eq.trans <|
      congrArg (fun j ↦ (D.smallAlmostJordan.component j).carrier) hselected
  · exact congrArg QuadraticSublattice.carrier
      (D.aligned_component_eq hselected p hp)

/-- In the aligned case every common numerical component prefix is the same
ambient subspace on the two sides. -/
theorem aligned_prefixCarrier_eq
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    (k : Nat) :
    D.largeAlmostJordan.toOrthogonalDecomposition.prefixCarrier k =
      D.smallAlmostJordan.toOrthogonalDecomposition.prefixCarrier k := by
  apply Lattice.OrthogonalDecomposition.prefixCarrier_eq_of_component_carrier_eq
  intro p _hp
  exact D.aligned_component_carrier_eq hselected p

/-- At the first slot of the unary adjacent transposition, the large side
contains the selected carrier and the small side contains the intermediate
common carrier. -/
theorem unaryShift_components_at_largeSelected
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1) :
    (D.largeAlmostJordan.component D.largeSelectedPosition).carrier =
        D.input.block.component.carrier ∧
      (D.smallAlmostJordan.component D.largeSelectedPosition).carrier =
        (D.complement.liftNested
          (D.complementStrictWeak.component i₀)).carrier := by
  constructor
  · rw [D.largeAlmostJordan_component_selected]
    rfl
  · rw [← D.smallCommonPosition_eq_largeSelectedPosition_of_intermediate
      hfin i₀ hi₀, D.smallAlmostJordan_component_common]

/-- At the second slot of the unary adjacent transposition, the two carriers
occur in the opposite order. -/
theorem unaryShift_components_at_smallSelected
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1) :
    (D.largeAlmostJordan.component D.smallSelectedPosition).carrier =
        (D.complement.liftNested
          (D.complementStrictWeak.component i₀)).carrier ∧
      (D.smallAlmostJordan.component D.smallSelectedPosition).carrier =
        D.input.block.component.carrier := by
  constructor
  · rw [← D.largeCommonPosition_eq_smallSelectedPosition_of_intermediate
      hfin i₀ hi₀, D.largeAlmostJordan_component_common]
  · rw [D.smallAlmostJordan_component_selected]

/-- The common carrier crossing the unary adjacent transposition is the
same on the two sides. -/
theorem unaryShift_crossCommon_carrier_eq
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1) :
    (D.largeAlmostJordan.component D.smallSelectedPosition).carrier =
      (D.smallAlmostJordan.component D.largeSelectedPosition).carrier := by
  exact (D.unaryShift_components_at_smallSelected hfin i₀ hi₀).1.trans
    (D.unaryShift_components_at_largeSelected hfin i₀ hi₀).2.symm

/-- Outside the two exchanged slots, corresponding components in the unary
exceptional case are literally the same lifted common component. -/
theorem unaryShift_component_eq_outside
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    (p : Fin (D.complementComponentCount + 1))
    (hlarge : p ≠ D.largeSelectedPosition)
    (hsmall : p ≠ D.smallSelectedPosition) :
    D.largeAlmostJordan.component p =
      D.smallAlmostJordan.component p := by
  rcases D.largePosition_eq_selected_or_common p with hp | ⟨j, hp⟩
  · exact (hlarge hp).elim
  · subst p
    have hj : j ≠ i₀ := by
      intro h
      subst j
      exact hsmall (D.largeCommonPosition_eq_smallSelectedPosition_of_intermediate
        hfin i₀ hi₀)
    have hposition :=
      D.commonPositions_eq_of_intermediate_of_ne hfin i₀ j hi₀ hj
    rw [D.largeAlmostJordan_component_common, ← hposition,
      D.smallAlmostJordan_component_common]

/-- Prefixes ending before the unary adjacent transposition have identical
ambient carriers. -/
theorem unaryShift_prefixCarrier_eq_before
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    (k : Nat) (hk : k ≤ D.largeSelectedPosition.val) :
    D.largeAlmostJordan.toOrthogonalDecomposition.prefixCarrier k =
      D.smallAlmostJordan.toOrthogonalDecomposition.prefixCarrier k := by
  apply Lattice.OrthogonalDecomposition.prefixCarrier_eq_of_component_carrier_eq
  intro p hp
  exact congrArg QuadraticSublattice.carrier
    (D.unaryShift_component_eq_before hfin i₀ hi₀ p (by omega))

/-- Once both exchanged slots are included, the unary adjacent transposition
again gives the same ambient prefix carrier. -/
theorem unaryShift_prefixCarrier_eq_after
    (D : Beli2019Lemma51Data q M N)
    (hfin : finrank K D.input.block.component.carrier = 1)
    (i₀ : Fin D.complementComponentCount)
    (hi₀ : ordUnit K (D.complementStrictWeak.scaleGenerator i₀) =
      ordUnit K D.input.block.enlargedScaleGenerator + 1)
    (k : Nat) (hk : D.smallSelectedPosition.val < k) :
    D.largeAlmostJordan.toOrthogonalDecomposition.prefixCarrier k =
      D.smallAlmostJordan.toOrthogonalDecomposition.prefixCarrier k := by
  let P := D.largeAlmostJordan.toOrthogonalDecomposition
  let Q := D.smallAlmostJordan.toOrthogonalDecomposition
  apply le_antisymm
  · apply P.prefixCarrier_le_of_component_le Q k k
    intro p hp
    by_cases hpl : p = D.largeSelectedPosition
    · subst p
      rw [D.selectedComponent_carrier_eq]
      exact Q.component_carrier_le_prefixCarrier
        D.smallSelectedPosition hk
    · by_cases hps : p = D.smallSelectedPosition
      · subst p
        rw [D.unaryShift_crossCommon_carrier_eq hfin i₀ hi₀]
        exact Q.component_carrier_le_prefixCarrier
          D.largeSelectedPosition (by
            have hadj := D.smallSelectedPosition_val_eq_large_add_one_of_rank_one
              hfin i₀ hi₀
            omega)
      · rw [congrArg QuadraticSublattice.carrier
          (D.unaryShift_component_eq_outside hfin i₀ hi₀ p hpl hps)]
        exact Q.component_carrier_le_prefixCarrier p hp
  · apply Q.prefixCarrier_le_of_component_le P k k
    intro p hp
    by_cases hpl : p = D.largeSelectedPosition
    · subst p
      rw [← D.unaryShift_crossCommon_carrier_eq hfin i₀ hi₀]
      exact P.component_carrier_le_prefixCarrier
        D.smallSelectedPosition hk
    · by_cases hps : p = D.smallSelectedPosition
      · subst p
        rw [← D.selectedComponent_carrier_eq]
        exact P.component_carrier_le_prefixCarrier
          D.largeSelectedPosition (by
            have hadj := D.smallSelectedPosition_val_eq_large_add_one_of_rank_one
              hfin i₀ hi₀
            omega)
      · rw [← congrArg QuadraticSublattice.carrier
          (D.unaryShift_component_eq_outside hfin i₀ hi₀ p hpl hps)]
        exact P.component_carrier_le_prefixCarrier p hp

end Lattice.Beli2019Lemma51Data

end Bong
