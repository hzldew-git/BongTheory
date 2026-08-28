import Bong.Lattice.Omeara933MaximalLattice
import Bong.Lattice.OmearaModularNormClassification
import Bong.Lattice.OmearaScaledHyperbolicTowerSpace

namespace Bong

open Dyadic Module

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

private theorem scalarIdeal_principalIdeal_units_local (a b : Kˣ) :
    scalarIdeal (a : K) (principalIdeal (K := K) (b : K)) =
      principalIdeal (K := K) ((a * b : Kˣ) : K) := by
  rw [scalarIdeal, principalIdeal, Submodule.map_span]
  change Submodule.span (IntegerRing K)
      (coefficientMulLinearMap (K := K) (a : K) '' {(b : K)}) =
    Submodule.span (IntegerRing K) {((a : K) * (b : K))}
  rw [Set.image_singleton]
  rw [coefficientMulLinearMap_apply]

/-- The scale-normalized output of O'Meara 93:3. -/
structure Omeara933ScaledData (q : QuadraticSpace K V)
    (L : Lattice K V) (s : Kˣ) where
  lattice : Lattice K V
  contains : L ≤ lattice
  modular : IsModular q lattice s
  normGroup_eq : normGroupSet q lattice = normGroupSet q L

private theorem isModular_of_isUnimodular_rescaleQuadraticInverse
    (s : Kˣ) (U : Lattice K V)
    (hU : IsUnimodular (q.rescaleUnit s⁻¹) U) :
    IsModular q U s := by
  have hdual : dualLattice (q.rescaleUnit s⁻¹) U = U :=
    (isUnimodular_iff_dualLattice_eq _ _).1 hU
  rw [dualLattice_rescaleQuadraticUnit] at hdual
  rw [IsModular]
  have hscaled := congrArg (rescale s⁻¹) hdual
  simpa [← rescale_mul] using hscaled

/-- O'Meara 93:3 at an arbitrary displayed Jordan scale. -/
noncomputable def omeara933Scaled
    (s : Kˣ) (n : Nat)
    (htower : q.IsIsometric
      (QuadraticSpace.scaledZeroOmearaTowerForm s n))
    (hscale : scaleIdeal q L = principalIdeal (K := K) (s : K)) :
    Omeara933ScaledData q L s := by
  let q' := q.rescaleUnit s⁻¹
  have htower' : q'.IsIsometric
      (hyperbolicExtensionForm
        (zeroCoordinateQuadraticSpace (K := K)) n) := by
    let f := (Classical.choice htower).rescaleUnitBoth s⁻¹
    let g := QuadraticSpace.scaledZeroOmearaTowerRescaleSpaceIsometry
      s s⁻¹ n
    let h := (QuadraticSpace.hyperbolicExtensionToScaledZeroOmearaTowerSpaceIsometry
      (K := K) (1 : Kˣ) n).symm
    refine ⟨f.trans (g.trans ?_)⟩
    convert h using 1 <;> simp
  have hscale' : scaleIdeal q' L = unitIdeal (K := K) := by
    change scaleIdeal (q.rescaleUnit s⁻¹) L = unitIdeal (K := K)
    rw [scaleIdeal_rescaleQuadraticUnit, hscale,
      scalarIdeal_principalIdeal_units_local]
    simp [unitIdeal]
  let D := omeara933 n htower' hscale'
  exact
    { lattice := D.lattice
      contains := D.contains
      modular := isModular_of_isUnimodular_rescaleQuadraticInverse
        s D.lattice D.unimodular
      normGroup_eq :=
        (normGroupSet_rescaleQuadraticUnit_eq_iff
          q s⁻¹ D.lattice L).1 D.normGroup_eq }

end Lattice

end Bong
