/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009NormGroupCongruence
import Bong.Bong.Beli2009JordanAlphaTransport

/-!
# Beli's component congruences and O'Meara fundamental type

This file packages the endpoint norm generators retained by a strict aligned
Jordan decomposition and proves the exact bridge needed in Beli (2009),
Lemma 3.3: equality of the fundamental weights together with the normalized
component congruences gives equality of the complete O'Meara fundamental
type.
-/

namespace Bong

open Dyadic

namespace BONG.StrictJordanAdaptedAlignment

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {m : Nat}
  {a : GoodBONG q L (m + 1)} {b : GoodBONG r M (m + 1)}

/-- The first retained source endpoint, used by Beli as the fundamental norm
generator `a_k`. -/
noncomputable def sourceFundamentalGenerator
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) : Kˣ :=
  S.weakAlignment.endpoint.sourceEndpoints.profile.endpointFirstValue k

/-- The corresponding target endpoint `b_k`. -/
noncomputable def targetFundamentalGenerator
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) : Kˣ :=
  S.weakAlignment.endpoint.targetEndpoints.profile.endpointFirstValue k

/-- The retained weak endpoint profile and the concrete source component
BONG family use the same ordered sigma indexing. -/
theorem sourceEndpointProfile_indexEquiv_eq_putTogether
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG) :
    S.weakAlignment.endpoint.sourceEndpoints.profile.indexEquiv =
      S.weakAlignment.sourceAdapted.putTogether.indexEquiv := by
  apply Equiv.ext
  intro i
  let p := S.weakAlignment.endpoint.sourceEndpoints.profile
  let h := S.weakAlignment.sourceAdapted.putTogether
  have hi : p.indexOrderIso i = h.indexOrderIso i :=
    congrArg (fun e ↦ e i) (Subsingleton.elim p.indexOrderIso h.indexOrderIso)
  change toLex (p.indexEquiv i) = toLex (h.indexEquiv i) at hi
  exact toLex_inj.mp hi

/-- Target analogue of
`sourceEndpointProfile_indexEquiv_eq_putTogether`. -/
theorem targetEndpointProfile_indexEquiv_eq_putTogether
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG) :
    S.weakAlignment.endpoint.targetEndpoints.profile.indexEquiv =
      S.weakAlignment.targetAdapted.putTogether.indexEquiv := by
  apply Equiv.ext
  intro i
  let p := S.weakAlignment.endpoint.targetEndpoints.profile
  let h := S.weakAlignment.targetAdapted.putTogether
  have hi : p.indexOrderIso i = h.indexOrderIso i :=
    congrArg (fun e ↦ e i) (Subsingleton.elim p.indexOrderIso h.indexOrderIso)
  change toLex (p.indexEquiv i) = toLex (h.indexEquiv i) at hi
  exact toLex_inj.mp hi

theorem sourceFundamentalGenerator_spec
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) :
    Lattice.IsNormGeneratorValue q (S.sourceJordan.fundamentalLattice k)
      (S.sourceFundamentalGenerator k) := by
  unfold sourceFundamentalGenerator
  exact S.toStrictJordanEndpointAlignment.sourceFirstGenerator_fundamentalLattice k

theorem targetFundamentalGenerator_spec
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (k : Fin S.componentCount) :
    Lattice.IsNormGeneratorValue r (S.targetJordan.fundamentalLattice k)
      (S.targetFundamentalGenerator k) := by
  unfold targetFundamentalGenerator
  exact S.toStrictJordanEndpointAlignment.targetFirstGenerator_fundamentalLattice k

/-- Equal global BONG orders give equal orders for the two retained
fundamental norm generators. -/
theorem fundamentalGenerator_order_eq
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (horders : a.SameOrders b) (k : Fin S.componentCount) :
    ordUnit K (S.sourceFundamentalGenerator k) =
      ordUnit K (S.targetFundamentalGenerator k) := by
  let first : Fin
      (S.weakAlignment.endpoint.sourceWeak.componentRank k) :=
    S.weakAlignment.endpoint.sourceWeak.endpointFirstIndex k
  let targetFirst : Fin
      (S.weakAlignment.endpoint.targetWeak.componentRank k) :=
    S.weakAlignment.endpoint.targetWeak.endpointFirstIndex k
  have htargetFirst : S.targetLocalIndex k first = targetFirst := by
    apply Fin.ext
    rfl
  have hindex := S.inverse_indexEquiv_eq k first
  unfold sourceFundamentalGenerator targetFundamentalGenerator
    WeakJordanOrderProfileWitness.endpointFirstValue
  rw [S.sourceEndpointProfile_indexEquiv_eq_putTogether,
    S.targetEndpointProfile_indexEquiv_eq_putTogether]
  change ordUnit K
      (a.toBONG.valueUnit
        (S.weakAlignment.sourceAdapted.putTogether.indexEquiv.symm
          ⟨k, first⟩)) =
    ordUnit K
      (b.toBONG.valueUnit
        (S.weakAlignment.targetAdapted.putTogether.indexEquiv.symm
          ⟨k, targetFirst⟩))
  rw [← htargetFirst, ← hindex]
  change a.order
      (S.weakAlignment.sourceAdapted.putTogether.indexEquiv.symm
        ⟨k, first⟩) =
    b.order
      (S.weakAlignment.sourceAdapted.putTogether.indexEquiv.symm
        ⟨k, first⟩)
  exact horders _

/-- Concrete fundamental-type bridge for a strict aligned Jordan family. -/
noncomputable def sameFundamentalType_of_normalizedWeightCongruence
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (horders : a.SameOrders b)
    (hweight : ∀ k, S.sourceJordan.fundamentalWeightOrder k =
      S.targetJordan.fundamentalWeightOrder k)
    (hcongruent : ∀ k, GoodBONG.UnitsCongruentModulo
      (S.sourceFundamentalGenerator k) (S.targetFundamentalGenerator k)
      (Lattice.powerIdeal (K := K)
        (S.sourceJordan.fundamentalWeightOrder k -
          ordUnit K (S.sourceFundamentalGenerator k)))) :
    Lattice.JordanDecomposition.SameFundamentalType
      S.sourceJordan S.targetJordan :=
  _root_.Bong.Lattice.JordanDecomposition.sameFundamentalTypeOfNormalizedWeightCongruence
    (K := K)
    S.sourceJordan S.targetJordan
    S.sourceFundamentalGenerator S.targetFundamentalGenerator
    S.sourceFundamentalGenerator_spec S.targetFundamentalGenerator_spec
    (fun k ↦ (S.componentRank_eq k).symm)
    (fun k ↦ (congrFun
      S.toStrictJordanEndpointAlignment.scaleOrderFamily_eq k).symm)
    (S.fundamentalGenerator_order_eq horders) hweight hcongruent

/-- Conversely, equality of O'Meara's fundamental type recovers the
normalized-weight congruence between the retained BONG norm generators.
Together with the preceding construction this closes the component part of
Beli (2009), Lemma 3.3 in both directions. -/
theorem componentGenerator_congruent_of_sameFundamentalType
    (S : StrictJordanAdaptedAlignment a.toBONG b.toBONG)
    (horders : a.SameOrders b)
    (F : Lattice.JordanDecomposition.SameFundamentalType
      S.sourceJordan S.targetJordan)
    (k : Fin S.componentCount) :
    GoodBONG.UnitsCongruentModulo
      (S.sourceFundamentalGenerator k) (S.targetFundamentalGenerator k)
      (Lattice.powerIdeal (K := K)
        (S.sourceJordan.fundamentalWeightOrder k -
          ordUnit K (S.sourceFundamentalGenerator k))) := by
  have hgroup := F.normGroup_eq k
  rw [F.indexEquiv_apply_eq_self] at hgroup
  exact Lattice.unitsCongruentModulo_normalizedWeight_of_normGroupSet_eq
    (S.sourceFundamentalGenerator k) (S.targetFundamentalGenerator k)
    (S.sourceFundamentalGenerator_spec k) (S.targetFundamentalGenerator_spec k)
    (S.fundamentalGenerator_order_eq horders k) hgroup

end BONG.StrictJordanAdaptedAlignment

end Bong
