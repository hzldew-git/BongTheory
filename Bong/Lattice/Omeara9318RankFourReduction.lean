/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9318ComplementInvariants
import Bong.Lattice.Omeara9318OddRankFiveSix
import Bong.Lattice.OmearaDisplayedTower
import Bong.Lattice.OmearaScaledHyperbolicTowerSpace

/-!
# Repeated O'Meara 93:18(v) reduction to rank four

Every even-rank modular lattice of rank at least four can be written as a
finite tower of standard scaled hyperbolic planes followed by a rank-four
modular lattice.  At every split the positive-rank complement has the same
norm group as the preceding lattice.  Hence the final rank-four residual has
the norm group of the original lattice.

This is the geometric rank-reduction used in step 2 of the sufficiency proof
of O'Meara 93:28.  The construction below contains the actual displayed
integral isometry; it is not a theorem-shaped interface.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [DyadicDiscriminantClassLaws K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {s : Kˣ}

/-- The canonical full lattice on the zero-dimensional coordinate space. -/
noncomputable def zeroCoordinateLattice : Lattice K (Fin 0 → K) :=
  basisLattice (Pi.basisFun K (Fin 0))

/-- A finite tower of scaled zero-coefficient O'Meara planes displayed to
the left of an arbitrary residual form. -/
noncomputable abbrev rankFourReductionTowerForm
    {X : Type v} [AddCommGroup X] [Module K X]
    (r : QuadraticSpace K X) (s : Kˣ) (k : Nat) :=
  (QuadraticSpace.scaledZeroOmearaTowerForm s k).orthogonalSum r

/-- The product lattice underlying `rankFourReductionTowerForm`. -/
noncomputable abbrev rankFourReductionTowerLattice
    {X : Type v} [AddCommGroup X] [Module K X]
    (M : Lattice K X) (k : Nat) :=
  product
    (hyperbolicExtensionLattice (zeroCoordinateLattice (K := K)) k) M

/-- Concrete output of the repeated 93:18(v) reduction. -/
structure Omeara9318RankFourReductionData
    (q : QuadraticSpace K V) (L : Lattice K V) (s : Kˣ) where
  Carrier : Type v
  [addCommGroup : AddCommGroup Carrier]
  [module : Module K Carrier]
  form : QuadraticSpace K Carrier
  lattice : Lattice K Carrier
  planeCount : Nat
  residual_modular : IsModular form lattice s
  residual_finrank : finrank K Carrier = 4
  residual_normGroupSet_eq : normGroupSet form lattice = normGroupSet q L
  displayedIsometry : Isometry q
    (rankFourReductionTowerForm form s planeCount) L
    (rankFourReductionTowerLattice lattice planeCount)

namespace Omeara9318RankFourReductionData

attribute [instance] addCommGroup module

/-- The number of split planes is determined by the ambient rank. -/
theorem ambient_finrank_eq
    (D : Omeara9318RankFourReductionData q L s) :
    finrank K V = 2 * D.planeCount + 4 := by
  letI : Module.Finite K V := L.moduleFinite
  letI : Module.Finite K D.Carrier := D.lattice.moduleFinite
  letI : Module.Finite K
      (HyperbolicExtension K (Fin 0 → K) D.planeCount) :=
    QuadraticSpace.hyperbolicExtensionZeroModuleFinite D.planeCount
  have h := D.displayedIsometry.toLinearEquiv.finrank_eq
  change finrank K V =
      finrank K
        (HyperbolicExtension K (Fin 0 → K) D.planeCount × D.Carrier) at h
  rw [Module.finrank_prod,
    QuadraticSpace.finrank_hyperbolicExtension_zero,
    D.residual_finrank] at h
  exact h

/-- If the ambient lattice space is a hyperbolic tower with exactly two
more planes than were split off, Witt cancellation identifies the residual
rank-four space with the remaining two-plane tower. -/
noncomputable def residualSpaceIsometryOfFullTowerIsometry
    (D : Omeara9318RankFourReductionData q L s)
    (full : QuadraticSpace.Isometry q
      (QuadraticSpace.scaledZeroOmearaTowerForm s (2 + D.planeCount))) :
    QuadraticSpace.Isometry D.form
      (QuadraticSpace.scaledZeroOmearaTowerForm s 2) := by
  letI : Module.Finite K D.Carrier := D.lattice.moduleFinite
  letI : Module.Finite K
      (HyperbolicExtension K (Fin 0 → K) D.planeCount) :=
    QuadraticSpace.hyperbolicExtensionZeroModuleFinite D.planeCount
  letI : Module.Finite K
      (HyperbolicExtension K (Fin 0 → K) 2) :=
    QuadraticSpace.hyperbolicExtensionZeroModuleFinite 2
  let splitToFull : QuadraticSpace.Isometry
      ((QuadraticSpace.scaledZeroOmearaTowerForm s D.planeCount).orthogonalSum
        D.form)
      ((QuadraticSpace.scaledZeroOmearaTowerForm s D.planeCount).orthogonalSum
        (QuadraticSpace.scaledZeroOmearaTowerForm s 2)) :=
    D.displayedIsometry.symm.toQuadraticSpaceIsometry.trans <|
      full.trans <|
        (QuadraticSpace.scaledZeroOmearaTowerAppendSpaceIsometry
          s D.planeCount 2).symm
  exact QuadraticSpace.orthogonalSumLeftCancel
    (QuadraticSpace.scaledZeroOmearaTowerForm s D.planeCount)
    D.form (QuadraticSpace.scaledZeroOmearaTowerForm s 2) splitToFull

/-- O'Meara 93:18(v), iterated until the remaining modular component has
rank four.  Evenness is preserved because every step removes exactly two
dimensions. -/
noncomputable def reduce
    {X : Type v} [AddCommGroup X] [Module K X]
    (q : QuadraticSpace K X) (L : Lattice K X) (s : Kˣ)
    (hmodular : IsModular q L s)
    (hrank : 4 ≤ finrank K X) (heven : Even (finrank K X)) :
    Omeara9318RankFourReductionData q L s := by
  letI : Module.Finite K X := L.moduleFinite
  by_cases hfour : finrank K X = 4
  · let Z := zeroCoordinateLattice (K := K)
    exact
      { Carrier := X
        form := q
        lattice := L
        planeCount := 0
        residual_modular := hmodular
        residual_finrank := hfour
        residual_normGroupSet_eq := rfl
        displayedIsometry :=
          (zeroLeftOrthogonalProductIsometry (K := K) Z q L).symm }
  · have hsix : 6 ≤ finrank K X := by
      rcases heven with ⟨m, hm⟩
      omega
    let D : Omeara9318vData q L s :=
      omeara9318vDataOfOddRankFiveOrSix
        (omeara9318vOddRankFiveOrSix (K := K)) q L s hmodular (by omega)
    let C := D.decomposition.component 1
    letI : Module.Finite K C.carrier := C.lattice.moduleFinite
    have hCrank : finrank K C.carrier = finrank K X - 2 :=
      D.complement_finrank
    have hCfour : 4 ≤ finrank K C.carrier := by
      rw [hCrank]
      omega
    have hCeven : Even (finrank K C.carrier) := by
      rcases heven with ⟨m, hm⟩
      refine ⟨m - 1, ?_⟩
      rw [hCrank, hm]
      omega
    let R := reduce C.space C.lattice s D.complement_modular hCfour hCeven
    let zeroPlane :=
      (scaledZeroOmearaPlaneLatticeIsometry (K := K) s).symm
    let refineComplement : Isometry
        ((QuadraticSpace.hyperbolicPlane s).orthogonalSum C.space)
        (((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit s).orthogonalSum
          (rankFourReductionTowerForm R.form s R.planeCount))
        (product (hyperbolicPlaneLattice (K := K)) C.lattice)
        (product (hyperbolicPlaneLattice (K := K))
          (rankFourReductionTowerLattice R.lattice R.planeCount)) :=
      zeroPlane.orthogonalProductBasic R.displayedIsometry
    let reassociate : Isometry
        (((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit s).orthogonalSum
          (rankFourReductionTowerForm R.form s R.planeCount))
        (rankFourReductionTowerForm R.form s (R.planeCount + 1))
        (product (hyperbolicPlaneLattice (K := K))
          (rankFourReductionTowerLattice R.lattice R.planeCount))
        (rankFourReductionTowerLattice R.lattice (R.planeCount + 1)) := by
      exact orthogonalProductAssoc.symm
    have hCpos : 0 < finrank K C.carrier := by omega
    exact
      { Carrier := R.Carrier
        form := R.form
        lattice := R.lattice
        planeCount := R.planeCount + 1
        residual_modular := R.residual_modular
        residual_finrank := R.residual_finrank
        residual_normGroupSet_eq :=
          R.residual_normGroupSet_eq.trans
            (D.complement_normGroupSet_eq hCpos)
        displayedIsometry :=
          D.displayedIsometry.trans (refineComplement.trans reassociate) }
termination_by finrank K X
decreasing_by
  rw [hCrank]
  omega

end Omeara9318RankFourReductionData

end Lattice

end Bong
