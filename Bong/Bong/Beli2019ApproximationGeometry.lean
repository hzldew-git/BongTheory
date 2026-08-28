/- Geometric bridge from Jordan approximation models to BONG-prefix
representations. -/
import Bong.Bong.Beli2019Lemma310Approximation

namespace Bong

open Dyadic Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

namespace BONG.GoodBONG

/-- An abstract quadratic-space approximation, recorded by a nondegenerate
diagonal presentation.  Unlike `SpaceApproximationModel`, this structure does
not assert that the approximation is a subspace of the ambient quadratic
space.  Beli's formal expressions `F L_(k) ⊥ [A]` in Lemma 3.7(ii) are
genuinely of this abstract kind. -/
structure DiagonalApproximationModel
    (a : GoodBONG q L (n + 1)) (i : Fin n) where
  units : Fin (i.val + 1) → Kˣ
  approximation : a.IsSpaceApproximation i units

/-- An approximation together with the actual nondegenerate subspace which
its diagonal coefficients present. -/
structure SpaceApproximationModel
    (a : GoodBONG q L (n + 1)) (i : Fin n) where
  carrier : Submodule K V
  nondegenerate : (q.bilin.restrict carrier).Nondegenerate
  units : Fin (i.val + 1) → Kˣ
  approximation : a.IsSpaceApproximation i units
  presentation : QuadraticSpace.Isometry
    (QuadraticSpace.finiteDiagonal
      (fun j ↦ (units j : K)) (fun j ↦ Units.ne_zero (units j)))
    (q.restrict carrier nondegenerate)

namespace SpaceApproximationModel

/-- Forget an ambient carrier and retain the abstract diagonal
approximation. -/
def toDiagonal
    {a : GoodBONG q L (n + 1)} {i : Fin n}
    (M : SpaceApproximationModel a i) : DiagonalApproximationModel a i :=
  ⟨M.units, M.approximation⟩

/-- Inclusion of nondegenerate carrier subspaces is a quadratic-space
representation between their restricted forms. -/
def carrierRepresentation
    {a : GoodBONG q L (n + 1)} {i : Fin n}
    {b : GoodBONG q M (n + 1)} {j : Fin n}
    (small : SpaceApproximationModel b j)
    (large : SpaceApproximationModel a i)
    (h : small.carrier ≤ large.carrier) :
    QuadraticSpace.Representation
      (q.restrict small.carrier small.nondegenerate)
      (q.restrict large.carrier large.nondegenerate) where
  toLinearMap := Submodule.inclusion h
  injective := Submodule.inclusion_injective h
  map_bilin _ _ := rfl

/-- Carrier inclusion converts directly to a representation between the
diagonal presentations of two approximation models. -/
theorem diagonalRepresents_of_carrier_le
    {a : GoodBONG q L (n + 1)} {i : Fin n}
    {b : GoodBONG q M (n + 1)} {j : Fin n}
    (small : SpaceApproximationModel b j)
    (large : SpaceApproximationModel a i)
    (h : small.carrier ≤ large.carrier) :
    DiagonalRepresents
      (fun k ↦ (small.units k : K))
      (fun k ↦ (large.units k : K)) := by
  let represented :
      (q.restrict large.carrier large.nondegenerate).Represents
        (q.restrict small.carrier small.nondegenerate) :=
    ⟨small.carrierRepresentation large h⟩
  have hfinite :
      (QuadraticSpace.finiteDiagonal
          (fun k ↦ (large.units k : K))
          (fun k ↦ Units.ne_zero (large.units k))).Represents
        (QuadraticSpace.finiteDiagonal
          (fun k ↦ (small.units k : K))
          (fun k ↦ Units.ne_zero (small.units k))) :=
    (QuadraticSpace.represents_iff_of_isometries
      small.presentation large.presentation).mpr represented
  exact (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
    small.units large.units).mp hfinite

end SpaceApproximationModel

namespace DiagonalApproximationModel

/-- Transport an abstract approximation model along equality of its BONG
index. -/
def castIndex
    {a : GoodBONG q L (n + 1)} {i j : Fin n}
    (M : DiagonalApproximationModel a i) (h : i = j) :
    DiagonalApproximationModel a j := by
  subst j
  exact M

/-- A diagonal representation out of an approximation model is preserved
when the model is transported along equality of its BONG index. -/
theorem castIndex_diagonalRepresents
    {m : Nat} {a : GoodBONG q L (n + 1)} {i j : Fin n}
    (M : DiagonalApproximationModel a i) (h : i = j)
    {target : Fin m → K}
    (hrep : DiagonalRepresents (diagonalUnitCoefficients M.units) target) :
    DiagonalRepresents
      (diagonalUnitCoefficients (M.castIndex h).units) target := by
  subst j
  exact hrep

/-- A diagonal representation into an approximation model is likewise
preserved by transport of the model index. -/
theorem castIndex_diagonalRepresentedBy
    {m : Nat} {a : GoodBONG q L (n + 1)} {i j : Fin n}
    (M : DiagonalApproximationModel a i) (h : i = j)
    {source : Fin m → K}
    (hrep : DiagonalRepresents source
      (diagonalUnitCoefficients M.units)) :
    DiagonalRepresents source
      (diagonalUnitCoefficients (M.castIndex h).units) := by
  subst j
  exact hrep

/-- Convert a representation of the finite diagonal source by the carrier
of a concrete target approximation into a representation between the two
coefficient lists. -/
theorem diagonalRepresents_spaceModel_of_represents
    {m : Nat} {a : GoodBONG q L (n + 1)} {i : Fin n}
    (source : DiagonalApproximationModel a i)
    {b : GoodBONG q M (m + 1)} {j : Fin m}
    (target : SpaceApproximationModel b j)
    (hrep : (q.restrict target.carrier target.nondegenerate).Represents
      (QuadraticSpace.finiteDiagonal
        (diagonalUnitCoefficients source.units)
        (QuadraticSpace.diagonalUnitCoefficients_ne_zero source.units))) :
    DiagonalRepresents
      (diagonalUnitCoefficients source.units)
      (diagonalUnitCoefficients target.units) := by
  let sourceSpace := QuadraticSpace.finiteDiagonal
    (diagonalUnitCoefficients source.units)
    (QuadraticSpace.diagonalUnitCoefficients_ne_zero source.units)
  have hfinite :
      (QuadraticSpace.finiteDiagonal
        (diagonalUnitCoefficients target.units)
        (QuadraticSpace.diagonalUnitCoefficients_ne_zero target.units)).Represents
          sourceSpace :=
    (QuadraticSpace.represents_iff_of_isometries
      (QuadraticSpace.Isometry.refl sourceSpace) target.presentation).mpr hrep
  exact (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
    source.units target.units).mp hfinite

end DiagonalApproximationModel

namespace SpaceApproximationModel

/-- The dual conversion: a concrete source carrier represented by an
abstract target diagonal model gives a coefficient-list representation. -/
theorem diagonalRepresents_diagonalModel_of_represents
    {a : GoodBONG q L (n + 1)} {i : Fin n}
    (source : SpaceApproximationModel a i)
    {m : Nat} {b : GoodBONG q M (m + 1)} {j : Fin m}
    (target : DiagonalApproximationModel b j)
    (hrep : (QuadraticSpace.finiteDiagonal
      (diagonalUnitCoefficients target.units)
      (QuadraticSpace.diagonalUnitCoefficients_ne_zero target.units)).Represents
        (q.restrict source.carrier source.nondegenerate)) :
    DiagonalRepresents
      (diagonalUnitCoefficients source.units)
      (diagonalUnitCoefficients target.units) := by
  let targetSpace := QuadraticSpace.finiteDiagonal
    (diagonalUnitCoefficients target.units)
    (QuadraticSpace.diagonalUnitCoefficients_ne_zero target.units)
  have hfinite : targetSpace.Represents
      (QuadraticSpace.finiteDiagonal
        (diagonalUnitCoefficients source.units)
        (QuadraticSpace.diagonalUnitCoefficients_ne_zero source.units)) :=
    (QuadraticSpace.represents_iff_of_isometries
      source.presentation (QuadraticSpace.Isometry.refl targetSpace)).mpr hrep
  exact (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
    source.units target.units).mp hfinite

end SpaceApproximationModel

set_option maxHeartbeats 0 in
/-- Condition (iii) only needs a representation between the two abstract
diagonal approximation spaces.  No realization of either approximation as
an ambient subspace is required.  This is the exact form used in Beli's
Section 5 case analysis. -/
theorem centralRepresentation_of_approximations
    [HilbertSymbolLaws K] [DiagonalRepresentationParityLaws K]
    [alpha : Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.centralAlphaTrigger b i)
    (largeUnits : Fin ((i.val - 1) + 1) → Kˣ)
    (smallUnits : Fin ((i.val - 2) + 1) → Kˣ)
    (largeApproximation : a.IsSpaceApproximation
      (⟨i.val - 1, by have := i.lt_large; have := i.one_lt; omega⟩ : Fin n)
      largeUnits)
    (smallApproximation : b.IsSpaceApproximation
      (⟨i.val - 2, by have := i.lt_large; have := i.one_lt; omega⟩ : Fin n)
      smallUnits)
    (hmodels : DiagonalRepresents
      (fun k ↦ (smallUnits k : K)) (fun k ↦ (largeUnits k : K))) :
    DiagonalRepresents
      (b.prefixValues (i.val - 1) i.previous_le_sameRank)
      (a.prefixValues i.val i.current_le_sameRank) := by
  have hsource : i.val - 1 < n + 1 := by
    have := i.lt_large
    omega
  have htoLarge : DiagonalRepresents
      (b.prefixValues (i.val - 1) i.previous_le_sameRank)
      (fun k ↦ (largeUnits k : K)) :=
    (a.centralSource_iff_of_lemma218
      (targetLaws := alpha) b hdefect i htrigger hsource
      largeUnits smallUnits largeApproximation smallApproximation).mpr
        hmodels
  exact (a.centralTarget_iff_of_lemma218
    (sourceLaws := alpha) b hdefect i htrigger
    largeUnits largeApproximation).mpr htoLarge

set_option maxHeartbeats 0 in
/-- Condition (iv), likewise, only needs an abstract representation between
the approximation spaces of dimensions `i-1` and `i+1`. -/
theorem longRepresentation_of_approximations
    [HilbertSymbolLaws K]
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [DiagonalCodimensionOneCancellationLaws K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (i : LongRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.longRepresentationTrigger b i)
    (largeUnits : Fin (i.val + 1) → Kˣ)
    (smallUnits : Fin ((i.val - 2) + 1) → Kˣ)
    (largeApproximation : a.IsSpaceApproximation
      (⟨i.val, by have := i.succ_lt_large; omega⟩ : Fin n) largeUnits)
    (smallApproximation : b.IsSpaceApproximation
      (⟨i.val - 2, by
        have := i.succ_lt_large
        have := i.one_lt
        omega⟩ : Fin n) smallUnits)
    (hmodels : DiagonalRepresents
      (fun k ↦ (smallUnits k : K)) (fun k ↦ (largeUnits k : K))) :
    DiagonalRepresents
      (b.prefixValues (i.val - 1) i.previous_le_sameRank)
      (a.prefixValues (i.val + 1) i.next_le_sameRank) := by
  have hsource : i.val - 1 < n + 1 := by
    have := i.succ_lt_large
    omega
  have htoLarge : DiagonalRepresents
      (b.prefixValues (i.val - 1) i.previous_le_sameRank)
      (fun k ↦ (largeUnits k : K)) :=
    (a.longSource_iff_of_cancellation
      (targetLaws := alpha) b i htrigger hsource
      largeUnits smallUnits largeApproximation smallApproximation).mpr
        hmodels
  exact (a.longTarget_iff_of_cancellation
    (sourceLaws := alpha) b i htrigger
    largeUnits largeApproximation).mpr htoLarge

namespace DiagonalApproximationModel

set_option maxHeartbeats 0 in
/-- Two abstract approximation models with a diagonal representation between
them discharge condition (iii). -/
theorem centralRepresentation
    [HilbertSymbolLaws K] [DiagonalRepresentationParityLaws K]
    [alpha : Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.centralAlphaTrigger b i)
    (large : DiagonalApproximationModel a
      (⟨i.val - 1, by have := i.lt_large; have := i.one_lt; omega⟩ : Fin n))
    (small : DiagonalApproximationModel b
      (⟨i.val - 2, by have := i.lt_large; have := i.one_lt; omega⟩ : Fin n))
    (hmodels : DiagonalRepresents
      (fun k ↦ (small.units k : K)) (fun k ↦ (large.units k : K))) :
    DiagonalRepresents
      (b.prefixValues (i.val - 1) i.previous_le_sameRank)
      (a.prefixValues i.val i.current_le_sameRank) :=
  centralRepresentation_of_approximations a b hdefect i htrigger
    large.units small.units large.approximation small.approximation hmodels

set_option maxHeartbeats 0 in
/-- The analogous abstract-model discharge of condition (iv). -/
theorem longRepresentation
    [HilbertSymbolLaws K]
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [DiagonalCodimensionOneCancellationLaws K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (i : LongRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.longRepresentationTrigger b i)
    (large : DiagonalApproximationModel a
      (⟨i.val, by have := i.succ_lt_large; omega⟩ : Fin n))
    (small : DiagonalApproximationModel b
      (⟨i.val - 2, by
        have := i.succ_lt_large
        have := i.one_lt
        omega⟩ : Fin n))
    (hmodels : DiagonalRepresents
      (fun k ↦ (small.units k : K)) (fun k ↦ (large.units k : K))) :
    DiagonalRepresents
      (b.prefixValues (i.val - 1) i.previous_le_sameRank)
      (a.prefixValues (i.val + 1) i.next_le_sameRank) :=
  longRepresentation_of_approximations a b i htrigger
    large.units small.units large.approximation small.approximation hmodels

end DiagonalApproximationModel

set_option maxHeartbeats 0 in
/-- Condition (iii) follows once the two Jordan approximation models have
nested carriers.  Lemma 3.10 performs both changes of approximation. -/
theorem centralRepresentation_of_approximationModels
    [HilbertSymbolLaws K] [DiagonalRepresentationParityLaws K]
    [alpha : Beli2006AlphaLaws.{u, v} K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.centralAlphaTrigger b i)
    (large : SpaceApproximationModel a
      (⟨i.val - 1, by have := i.lt_large; have := i.one_lt; omega⟩ : Fin n))
    (small : SpaceApproximationModel b
      (⟨i.val - 2, by have := i.lt_large; have := i.one_lt; omega⟩ : Fin n))
    (hcarrier : small.carrier ≤ large.carrier) :
    DiagonalRepresents
      (b.prefixValues (i.val - 1) i.previous_le_sameRank)
      (a.prefixValues i.val i.current_le_sameRank) := by
  have hmodels : DiagonalRepresents
      (fun k ↦ (small.units k : K))
      (fun k ↦ (large.units k : K)) :=
    small.diagonalRepresents_of_carrier_le large hcarrier
  exact centralRepresentation_of_approximations a b hdefect i htrigger
    large.units small.units large.approximation small.approximation hmodels

set_option maxHeartbeats 0 in
/-- Condition (iv) follows from a nested pair of Jordan approximation models
of dimensions `i-1` and `i+1`. -/
theorem longRepresentation_of_approximationModels
    [HilbertSymbolLaws K]
    [alpha : Beli2006AlphaLaws.{u, v} K]
    [DiagonalCodimensionOneCancellationLaws K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (i : LongRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.longRepresentationTrigger b i)
    (large : SpaceApproximationModel a
      (⟨i.val, by have := i.succ_lt_large; omega⟩ : Fin n))
    (small : SpaceApproximationModel b
      (⟨i.val - 2, by have := i.succ_lt_large; have := i.one_lt; omega⟩ : Fin n))
    (hcarrier : small.carrier ≤ large.carrier) :
    DiagonalRepresents
      (b.prefixValues (i.val - 1) i.previous_le_sameRank)
      (a.prefixValues (i.val + 1) i.next_le_sameRank) := by
  have hmodels : DiagonalRepresents
      (fun k ↦ (small.units k : K))
      (fun k ↦ (large.units k : K)) :=
    small.diagonalRepresents_of_carrier_le large hcarrier
  exact longRepresentation_of_approximations a b i htrigger
    large.units small.units large.approximation small.approximation hmodels

end BONG.GoodBONG

end Bong
