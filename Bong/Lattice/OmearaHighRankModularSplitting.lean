/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaPrimitiveIsotropicSplitting
import Bong.Lattice.JordanIsometry
import Bong.Lattice.OmearaNormGroupShift
import Bong.Lattice.OmearaStableModularCancellation
import Bong.Lattice.OmearaHyperbolicTransvection
import Bong.Lattice.OmearaTwoPlaneCombination
import Bong.Lattice.OrthogonalProductDecomposition
import Bong.Lattice.OrthogonalProductIsometry
import Bong.QuadraticSpace.DyadicHighRankIsotropy

/-!
# High-rank modular plane splitting

Combining high-rank isotropy with O'Meara 82:16 shows that every modular
lattice of rank at least five splits an explicit scaled binary plane
`a A(alpha,0)`.  The orthogonal complement remains `a`-modular.

This is the geometric part of O'Meara 93:18(v).  It deliberately does not
identify `A(alpha,0)` with `A(0,0)`; that integral normalization is the
remaining norm/weight calculation.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {a : Kˣ}

/-- Concrete output of the high-rank modular splitting step. -/
structure OmearaHighRankModularPlaneData
    (q : QuadraticSpace K V) (L : Lattice K V) (a : Kˣ) where
  isotropicVector : V
  isotropicVector_ne : isotropicVector ≠ 0
  isotropicVector_quadratic : q.quadratic isotropicVector = 0
  lineData : Omeara8216LineData q L a isotropicVector

/-- Exact output of O'Meara 93:18(v): a displayed scaled hyperbolic plane
and its modular orthogonal complement.  Unlike the geometric plane data
above, the first coefficient has already been normalized to zero. -/
structure Omeara9318vData
    (q : QuadraticSpace K V) (L : Lattice K V) (a : Kˣ) where
  decomposition : OrthogonalDecomposition q L 2
  hyperbolic : Isometry
    (decomposition.component 0).space
    (QuadraticSpace.hyperbolicPlane a)
    (decomposition.component 0).lattice
    (hyperbolicPlaneLattice (K := K))
  complement_modular : IsModular
    (decomposition.component 1).space
    (decomposition.component 1).lattice a

namespace Omeara9318vData

variable (D : Omeara9318vData q L a)

/-- The displayed binary splitting, oriented from the original lattice to
the scaled hyperbolic product. -/
noncomputable def displayedIsometry :
    Isometry q
      ((QuadraticSpace.hyperbolicPlane a).orthogonalSum
        (D.decomposition.component 1).space)
      L
      (product (hyperbolicPlaneLattice (K := K))
        (D.decomposition.component 1).lattice) :=
  D.decomposition.pairProductLatticeIsometry.symm |>.trans
    (D.hyperbolic.orthogonalProductBasic
      (Isometry.refl (D.decomposition.component 1).space
        (D.decomposition.component 1).lattice))

/-- Package a displayed scaled hyperbolic summand as the exact output of
O'Meara 93:18(v).  The standard product decomposition is transported back
along the supplied integral isometry. -/
noncomputable def ofDisplayedIsometry
    {W : Type w} [AddCommGroup W] [Module K W]
    (r : QuadraticSpace K W) (M : Lattice K W)
    (hmodular : IsModular q L a)
    (displayed : Isometry q
      ((QuadraticSpace.hyperbolicPlane a).orthogonalSum r)
      L (product (hyperbolicPlaneLattice (K := K)) M)) :
    Omeara9318vData q L a := by
  let T : OrthogonalDecomposition
      ((QuadraticSpace.hyperbolicPlane a).orthogonalSum r)
      (product (hyperbolicPlaneLattice (K := K)) M) 2 :=
    orthogonalProductDecomposition
      (QuadraticSpace.hyperbolicPlane a) r
      (hyperbolicPlaneLattice (K := K)) M
  let pulled := T.mapIsometry displayed.symm
  let standardToLeft : Isometry (QuadraticSpace.hyperbolicPlane a)
      (T.component 0).space (hyperbolicPlaneLattice (K := K))
      (T.component 0).lattice := by
    exact orthogonalProductLeftComponentIsometry
      (QuadraticSpace.hyperbolicPlane a) r
      (hyperbolicPlaneLattice (K := K))
  let leftToPulled := (T.component 0).mapLatticeIsometry displayed.symm
  exact
    { decomposition := pulled
      hyperbolic := (standardToLeft.trans leftToPulled).symm
      complement_modular := pulled.component_modular_of_ambient hmodular 1 }

end Omeara9318vData

/-- Choose the nonzero isotropic line and apply O'Meara 82:16. -/
noncomputable def omearaHighRankModularPlaneData
    [FiniteDimensional K V] (hmodular : IsModular q L a)
    (hrank : 5 ≤ finrank K V) :
    OmearaHighRankModularPlaneData q L a := by
  let hexists :=
    q.exists_ne_zero_quadratic_eq_zero_of_five_le_finrank hrank
  let z := Classical.choose hexists
  have hz : z ≠ 0 := (Classical.choose_spec hexists).1
  have hqz : q.quadratic z = 0 := (Classical.choose_spec hexists).2
  exact
    { isotropicVector := z
      isotropicVector_ne := hz
      isotropicVector_quadratic := hqz
      lineData := omeara8216LineData hmodular hz }

namespace OmearaHighRankModularPlaneData

variable (D : OmearaHighRankModularPlaneData q L a)

/-- The elementary O'Meara 93:10 change of basis, after multiplying both
forms by the same modular scale. -/
noncomputable def scaledHyperbolicToOmearaPlaneLatticeIsometry
    (alpha eta : K) (hcoeff : alpha = 2 * eta)
    (heta : eta ∈ IntegerRing K) :
    Isometry (QuadraticSpace.hyperbolicPlane a)
      ((QuadraticSpace.omearaPlane alpha).rescaleUnit a)
      (hyperbolicPlaneLattice (K := K))
      (hyperbolicPlaneLattice (K := K)) := by
  let f := (hyperbolicToOmearaPlaneLatticeIsometry
    alpha eta hcoeff heta).rescaleUnitBoth a
  exact
    { toLinearEquiv := f.toLinearEquiv
      map_bilin := by
        intro x y
        have h := f.map_bilin x y
        simpa only [QuadraticSpace.rescaleUnit_bilin_apply,
          QuadraticSpace.hyperbolicPlane_bilin_apply,
          Units.val_one, one_mul] using h
      map_mem := f.map_mem }

/-- The orthogonal decomposition supplied by the chosen isotropic line. -/
noncomputable def splitting (hmodular : IsModular q L a) :
    OrthogonalDecomposition q L 2 :=
  D.lineData.splitting hmodular D.isotropicVector_quadratic

@[simp]
theorem splitting_zero (hmodular : IsModular q L a) :
    (D.splitting hmodular).component 0 =
      D.lineData.pairingData.component hmodular
        (D.lineData.vector_isotropic D.isotropicVector_quadratic) :=
  rfl

/-- The coefficient of the scaled plane split from the lattice. -/
noncomputable def planeCoefficient : K :=
  D.lineData.pairingData.planeCoefficient

/-- The first component is integrally isometric to
`a A(planeCoefficient,0)`. -/
noncomputable def planeIsometry (hmodular : IsModular q L a) :
    Isometry
      ((QuadraticSpace.omearaPlane D.planeCoefficient).rescaleUnit a)
      ((D.splitting hmodular).component 0).space
      (hyperbolicPlaneLattice (K := K))
      ((D.splitting hmodular).component 0).lattice := by
  exact D.lineData.planeIsometry hmodular
    D.isotropicVector_quadratic

/-- The complementary component remains modular at the original scale. -/
theorem complement_modular (hmodular : IsModular q L a) :
    IsModular ((D.splitting hmodular).component 1).space
      ((D.splitting hmodular).component 1).lattice a :=
  D.lineData.complement_modular hmodular
    D.isotropicVector_quadratic

/-- The geometric plane has rank two, so its orthogonal complement lowers
the ambient rank by exactly two. -/
theorem complement_finrank (hmodular : IsModular q L a) :
    finrank K ((D.splitting hmodular).component 1).carrier =
      finrank K V - 2 := by
  letI : Module.Finite K V := L.moduleFinite
  let S := D.splitting hmodular
  let P := S.component 0
  let C := S.component 1
  letI : Module.Finite K P.carrier := P.lattice.moduleFinite
  letI : Module.Finite K C.carrier := C.lattice.moduleFinite
  have hplane : finrank K P.carrier = 2 := by
    have h := (D.planeIsometry hmodular).toLinearEquiv.finrank_eq
    simpa only [Module.finrank_fin_fun] using h.symm
  have htotal := S.pairProductLatticeIsometry.toLinearEquiv.finrank_eq
  change finrank K (P.carrier × C.carrier) = finrank K V at htotal
  rw [Module.finrank_prod, hplane] at htotal
  change finrank K C.carrier = finrank K V - 2
  omega

/-- The coefficient of the plane supplied by 82:16 is integral. -/
theorem planeCoefficient_mem_integerRing
    (hmodular : IsModular q L a) :
    D.planeCoefficient ∈ IntegerRing K := by
  let y := D.lineData.pairingData.partner
  have hy : y ∈ L := D.lineData.pairingData.partner_mem
  have hqy : q.quadratic y ∈ principalIdeal (K := K) (a : K) :=
    hmodular.scaleIdeal_le_principal
      (bilin_mem_scaleIdeal_of_mem q L hy hy)
  change (a : K)⁻¹ * q.quadratic y ∈ IntegerRing K
  apply mem_integerRing_of_mul_mem_principalIdeal (Units.ne_zero a)
  have hcancel : (a : K) * ((a : K)⁻¹ * q.quadratic y) =
      q.quadratic y := by
    simp [Units.ne_zero a]
  rw [hcancel]
  exact hqy

/-- The even-coefficient branch of O'Meara 93:18(v).  If the plane split
by the chosen isotropic line has coefficient `2 * eta` with `eta` integral,
the elementary integral transvection already normalizes it to the scaled
hyperbolic plane. -/
noncomputable def toOmeara9318vData_of_even_coefficient
    (hmodular : IsModular q L a)
    (eta : K) (heta : eta ∈ IntegerRing K)
    (hcoefficient : D.planeCoefficient = 2 * eta) :
    Omeara9318vData q L a := by
  let normalize :=
    scaledHyperbolicToOmearaPlaneLatticeIsometry (a := a)
      D.planeCoefficient eta hcoefficient heta
  exact
    { decomposition := D.splitting hmodular
      hyperbolic := (normalize.trans (D.planeIsometry hmodular)).symm
      complement_modular := D.complement_modular hmodular }

/-- If the orthogonal complement of the first displayed plane already
contains a scaled hyperbolic plane, exchange that plane to the front.  This
is the recursive step reducing 93:18(v) by two dimensions. -/
noncomputable def toOmeara9318vData_of_complement
    (hmodular : IsModular q L a)
    (E : Omeara9318vData
      ((D.splitting hmodular).component 1).space
      ((D.splitting hmodular).component 1).lattice a) :
    Omeara9318vData q L a := by
  let S := D.splitting hmodular
  let C := S.component 1
  let P := (QuadraticSpace.omearaPlane D.planeCoefficient).rescaleUnit a
  let planeToFirst := D.planeIsometry hmodular
  let exposePlane : Isometry q (P.orthogonalSum C.space)
      L (product (hyperbolicPlaneLattice (K := K)) C.lattice) :=
    S.pairProductLatticeIsometry.symm |>.trans
      (planeToFirst.symm.orthogonalProductBasic
        (Isometry.refl C.space C.lattice))
  let exposeComplement : Isometry (P.orthogonalSum C.space)
      (P.orthogonalSum
        ((QuadraticSpace.hyperbolicPlane a).orthogonalSum
          (E.decomposition.component 1).space))
      (product (hyperbolicPlaneLattice (K := K)) C.lattice)
      (product (hyperbolicPlaneLattice (K := K))
        (product (hyperbolicPlaneLattice (K := K))
          (E.decomposition.component 1).lattice)) :=
    (Isometry.refl P (hyperbolicPlaneLattice (K := K))).orthogonalProductBasic
      E.displayedIsometry
  let exchange : Isometry
      (P.orthogonalSum
        ((QuadraticSpace.hyperbolicPlane a).orthogonalSum
          (E.decomposition.component 1).space))
      (((QuadraticSpace.hyperbolicPlane a).orthogonalSum P).orthogonalSum
        (E.decomposition.component 1).space)
      (product (hyperbolicPlaneLattice (K := K))
        (product (hyperbolicPlaneLattice (K := K))
          (E.decomposition.component 1).lattice))
      (product
        (product (hyperbolicPlaneLattice (K := K))
          (hyperbolicPlaneLattice (K := K)))
        (E.decomposition.component 1).lattice) :=
    orthogonalProductRotateLeft
  let reassociate : Isometry
      (((QuadraticSpace.hyperbolicPlane a).orthogonalSum P).orthogonalSum
        (E.decomposition.component 1).space)
      ((QuadraticSpace.hyperbolicPlane a).orthogonalSum
        (P.orthogonalSum (E.decomposition.component 1).space))
      (product
        (product (hyperbolicPlaneLattice (K := K))
          (hyperbolicPlaneLattice (K := K)))
        (E.decomposition.component 1).lattice)
      (product (hyperbolicPlaneLattice (K := K))
        (product (hyperbolicPlaneLattice (K := K))
          (E.decomposition.component 1).lattice)) :=
    orthogonalProductAssoc
  let displayed := exposePlane.trans
    (exposeComplement.trans (exchange.trans reassociate))
  exact Omeara9318vData.ofDisplayedIsometry
    (P.orthogonalSum (E.decomposition.component 1).space)
    (product (hyperbolicPlaneLattice (K := K))
      (E.decomposition.component 1).lattice)
    hmodular displayed

/-- Package the explicit four-dimensional coefficient-addition step in an
ambient modular lattice.  This is the final plane-combination calculation in
O'Meara 93:18(v). -/
noncomputable def Omeara9318vData.ofTwoPlaneDisplayedIsometry
    {W : Type w} [AddCommGroup W] [Module K W]
    (hmodular : IsModular q L a)
    (alpha gamma eta : K)
    (halpha : alpha ∈ IntegerRing K)
    (hgamma : gamma ∈ IntegerRing K)
    (hsum : alpha + gamma = 2 * eta)
    (heta : eta ∈ IntegerRing K)
    (r : QuadraticSpace K W) (M : Lattice K W)
    (displayed : Isometry q
      (((QuadraticSpace.omearaPlane alpha).rescaleUnit a).orthogonalSum
        (((QuadraticSpace.omearaPlane gamma).rescaleUnit a).orthogonalSum r))
      L
      (product (hyperbolicPlaneLattice (K := K))
        (product (hyperbolicPlaneLattice (K := K)) M))) :
    Omeara9318vData q L a := by
  let Pminus := (QuadraticSpace.omearaPlane (-gamma)).rescaleUnit a
  let combined := scaledTwoOmearaPlanesHyperbolicDisplayedIsometry
    a alpha gamma eta halpha hgamma hsum heta
  let sourceAssoc : Isometry
      (((QuadraticSpace.hyperbolicPlane a).orthogonalSum Pminus).orthogonalSum r)
      ((QuadraticSpace.hyperbolicPlane a).orthogonalSum
        (Pminus.orthogonalSum r))
      (product
        (product (hyperbolicPlaneLattice (K := K))
          (hyperbolicPlaneLattice (K := K))) M)
      (product (hyperbolicPlaneLattice (K := K))
        (product (hyperbolicPlaneLattice (K := K)) M)) :=
    orthogonalProductAssoc
  let targetAssoc : Isometry
      ((((QuadraticSpace.omearaPlane alpha).rescaleUnit a).orthogonalSum
        ((QuadraticSpace.omearaPlane gamma).rescaleUnit a)).orthogonalSum r)
      (((QuadraticSpace.omearaPlane alpha).rescaleUnit a).orthogonalSum
        (((QuadraticSpace.omearaPlane gamma).rescaleUnit a).orthogonalSum r))
      (product
        (product (hyperbolicPlaneLattice (K := K))
          (hyperbolicPlaneLattice (K := K))) M)
      (product (hyperbolicPlaneLattice (K := K))
        (product (hyperbolicPlaneLattice (K := K)) M)) :=
    orthogonalProductAssoc
  let toOld := sourceAssoc.symm.trans
    ((combined.orthogonalProductBasic (Isometry.refl r M)).trans targetAssoc)
  let hyperbolicDisplayed := displayed.trans toOld.symm
  exact Omeara9318vData.ofDisplayedIsometry
    (Pminus.orthogonalSum r)
    (product (hyperbolicPlaneLattice (K := K)) M)
    hmodular hyperbolicDisplayed

/-- Square-coset version of the four-dimensional extraction.  If
`alpha + gamma*c^2` is even, the first two displayed modular planes contain
a scaled hyperbolic summand. -/
noncomputable def Omeara9318vData.ofTwoPlaneDisplayedIsometryOfSquare
    {W : Type w} [AddCommGroup W] [Module K W]
    (hmodular : IsModular q L a)
    (alpha gamma c eta : K)
    (hgamma : gamma ∈ IntegerRing K)
    (hc : c ∈ IntegerRing K)
    (hsum : alpha + gamma * c ^ 2 = 2 * eta)
    (heta : eta ∈ IntegerRing K)
    (r : QuadraticSpace K W) (M : Lattice K W)
    (displayed : Isometry q
      (((QuadraticSpace.omearaPlane alpha).rescaleUnit a).orthogonalSum
        (((QuadraticSpace.omearaPlane gamma).rescaleUnit a).orthogonalSum r))
      L
      (product (hyperbolicPlaneLattice (K := K))
        (product (hyperbolicPlaneLattice (K := K)) M))) :
    Omeara9318vData q L a := by
  let Pgamma := (QuadraticSpace.omearaPlane gamma).rescaleUnit a
  let combined :=
    scaledTwoOmearaPlanesHyperbolicDisplayedIsometryOfSquare
      a alpha gamma c eta hgamma hc hsum heta
  let sourceAssoc : Isometry
      (((QuadraticSpace.hyperbolicPlane a).orthogonalSum Pgamma).orthogonalSum r)
      ((QuadraticSpace.hyperbolicPlane a).orthogonalSum
        (Pgamma.orthogonalSum r))
      (product
        (product (hyperbolicPlaneLattice (K := K))
          (hyperbolicPlaneLattice (K := K))) M)
      (product (hyperbolicPlaneLattice (K := K))
        (product (hyperbolicPlaneLattice (K := K)) M)) :=
    orthogonalProductAssoc
  let targetAssoc : Isometry
      ((((QuadraticSpace.omearaPlane alpha).rescaleUnit a).orthogonalSum
        ((QuadraticSpace.omearaPlane gamma).rescaleUnit a)).orthogonalSum r)
      (((QuadraticSpace.omearaPlane alpha).rescaleUnit a).orthogonalSum
        (((QuadraticSpace.omearaPlane gamma).rescaleUnit a).orthogonalSum r))
      (product
        (product (hyperbolicPlaneLattice (K := K))
          (hyperbolicPlaneLattice (K := K))) M)
      (product (hyperbolicPlaneLattice (K := K))
        (product (hyperbolicPlaneLattice (K := K)) M)) :=
    orthogonalProductAssoc
  let toOld := sourceAssoc.symm.trans
    ((combined.orthogonalProductBasic (Isometry.refl r M)).trans targetAssoc)
  let hyperbolicDisplayed := displayed.trans toOld.symm
  exact Omeara9318vData.ofDisplayedIsometry
    (Pgamma.orthogonalSum r)
    (product (hyperbolicPlaneLattice (K := K)) M)
    hmodular hyperbolicDisplayed

/-- Normalize the displayed `a A(alpha,0)` to `a A(0,0)` when its
coefficient belongs to the norm group of the complementary scale
truncation.  The normalization moves the plane through the complement, so
the resulting decomposition is obtained by transporting the canonical
product decomposition back to `L`. -/
noncomputable def toOmeara9318vData_of_coefficient_mem
    (hmodular : IsModular q L a)
    (hcoefficient : (a : K) * D.planeCoefficient ∈
      normGroupSet ((D.splitting hmodular).component 1).space
        (omearaScaleTruncation
          ((D.splitting hmodular).component 1).space
          ((D.splitting hmodular).component 1).lattice a)) :
    Omeara9318vData q L a := by
  let S := D.splitting hmodular
  let C := S.component 1
  let planeToFirst := D.planeIsometry hmodular
  let exposePlane : Isometry q
      (((QuadraticSpace.omearaPlane D.planeCoefficient).rescaleUnit a)
        |>.orthogonalSum C.space)
      L (product (hyperbolicPlaneLattice (K := K)) C.lattice) :=
    S.pairProductLatticeIsometry.symm |>.trans
      (planeToFirst.symm.orthogonalProductBasic
        (Isometry.refl C.space C.lattice))
  have hcoefficientFormula :
      0 + ((a⁻¹ : Kˣ) : K) *
        ((a : K) * D.planeCoefficient) = D.planeCoefficient := by
    simp [Units.ne_zero a]
  let normalizeRaw := omeara9313 C.space C.lattice a 0
    ((a : K) * D.planeCoefficient) hcoefficient
  let normalize : Isometry
      (((QuadraticSpace.omearaPlane D.planeCoefficient).rescaleUnit a)
        |>.orthogonalSum C.space)
      (((QuadraticSpace.omearaPlane (K := K) 0).rescaleUnit a)
        |>.orthogonalSum C.space)
      (product (hyperbolicPlaneLattice (K := K)) C.lattice)
      (product (hyperbolicPlaneLattice (K := K)) C.lattice) := by
    simpa only [hcoefficientFormula] using normalizeRaw
  let identify :=
    (scaledZeroOmearaPlaneLatticeIsometry a).orthogonalProductBasic
      (Isometry.refl C.space C.lattice)
  let displayed : Isometry q
      ((QuadraticSpace.hyperbolicPlane a).orthogonalSum C.space)
      L (product (hyperbolicPlaneLattice (K := K)) C.lattice) :=
    exposePlane.trans (normalize.trans identify)
  let T : OrthogonalDecomposition
      ((QuadraticSpace.hyperbolicPlane a).orthogonalSum C.space)
      (product (hyperbolicPlaneLattice (K := K)) C.lattice) 2 :=
    orthogonalProductDecomposition
      (QuadraticSpace.hyperbolicPlane a) C.space
      (hyperbolicPlaneLattice (K := K)) C.lattice
  let pulled := T.mapIsometry displayed.symm
  let standardToLeft : Isometry (QuadraticSpace.hyperbolicPlane a)
      (T.component 0).space (hyperbolicPlaneLattice (K := K))
      (T.component 0).lattice := by
    exact orthogonalProductLeftComponentIsometry
      (QuadraticSpace.hyperbolicPlane a) C.space
      (hyperbolicPlaneLattice (K := K))
  let leftToPulled := (T.component 0).mapLatticeIsometry displayed.symm
  exact
    { decomposition := pulled
      hyperbolic := (standardToLeft.trans leftToPulled).symm
      complement_modular := pulled.component_modular_of_ambient hmodular 1 }

end OmearaHighRankModularPlaneData

/-- Applied form of the geometric half of O'Meara 93:18(v): a modular
lattice of rank at least five has a scaled `A(alpha,0)` component and a
modular orthogonal complement. -/
theorem exists_scaled_omearaPlane_splitting_of_five_le_finrank
    [FiniteDimensional K V] (hmodular : IsModular q L a)
    (hrank : 5 ≤ finrank K V) :
    ∃ (alpha : K) (S : OrthogonalDecomposition q L 2),
      Nonempty
        (Isometry
          ((QuadraticSpace.omearaPlane alpha).rescaleUnit a)
          (S.component 0).space
          (hyperbolicPlaneLattice (K := K))
          (S.component 0).lattice) ∧
      IsModular (S.component 1).space (S.component 1).lattice a := by
  let D := omearaHighRankModularPlaneData hmodular hrank
  exact ⟨D.planeCoefficient, D.splitting hmodular,
    ⟨D.planeIsometry hmodular⟩, D.complement_modular hmodular⟩

end Lattice

end Bong
