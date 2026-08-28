import Bong.Lattice.Omeara9328RankFourJordanReduction
import Bong.Lattice.Omeara933ScaledMaximalLattice
import Bong.Lattice.OmearaHyperbolicBlockTower
import Bong.Lattice.JordanSuffixScale

/-!
# Norm-preserving modular envelopes of rank-four Jordan suffixes

This is the constructive 93:3 input in O'Meara 93:28, Step 2.
-/

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [DyadicDiscriminantClassLaws K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}
  {J : JordanDecomposition q L (n + 2)}
  {H : JordanDecomposition r M (n + 2)}

namespace Omeara9328RankFourReductionSystem

variable (S : Omeara9328RankFourReductionSystem J H)

/-- The source suffix beginning immediately after a boundary. -/
noncomputable abbrev boundarySuffix (i : Fin (n + 1)) :=
  S.sourceJordan.toOrthogonalDecomposition.suffixQuadraticSublattice
    (i.val + 1)

/-- Number of rank-four components in the source suffix, minus one. -/
def boundarySuffixPred
    (_S : Omeara9328RankFourReductionSystem J H)
    (i : Fin (n + 1)) : Nat := n - i.val

theorem boundarySuffix_cut_eq (i : Fin (n + 1)) :
    i.val + 1 + (S.boundarySuffixPred i + 1) = n + 2 := by
  unfold boundarySuffixPred
  omega

/-- The entire source suffix is a finite tower of hyperbolic planes at the
first suffix scale. -/
noncomputable def boundarySuffixTowerIsometry (i : Fin (n + 1)) :
    (S.boundarySuffix i).space.Isometry
      (QuadraticSpace.scaledZeroOmearaTowerForm
        (J.scaleGenerator (boundaryRightIndex i))
        (2 * (S.boundarySuffixPred i + 1))) := by
  let D := S.sourceJordan.toOrthogonalDecomposition
  let m := S.boundarySuffixPred i
  let hcut : i.val + 1 + (m + 1) = n + 2 :=
    S.boundarySuffix_cut_eq i
  let C := D.suffixBlockCarrier hcut
  let qs := D.suffixBlockSpace hcut
  let Ls := D.suffixBlockLattice hcut
  let present := D.suffixBlockProductIsometry hcut
  have hcomponent : ∀ z : Fin (m + 1),
      (qs z).IsIsometric
        (QuadraticSpace.scaledZeroOmearaTowerForm
          (J.scaleGenerator (boundaryRightIndex i)) 2) := by
    intro z
    let idx : Fin (n + 2) := (D.suffixIndexEquiv hcut z).1
    let original := Classical.choice
      (S.sourceJordan_componentSpace_hyperbolic idx)
    let changeScale :=
      QuadraticSpace.scaledZeroOmearaTowerChangeScaleSpaceIsometry
        (J.scaleGenerator idx)
        (J.scaleGenerator (boundaryRightIndex i)) 2
    exact ⟨original.trans changeScale⟩
  let gather := QuadraticSpace.blockTwoPlaneTowerIsometry
    (J.scaleGenerator (boundaryRightIndex i)) m C qs hcomponent
  exact present.symm.toQuadraticSpaceIsometry.trans gather

/-- O'Meara 93:3 supplies a modular superlattice of the whole suffix with
exactly the same norm group. -/
noncomputable def boundarySuffixEnvelope (i : Fin (n + 1)) :
    Omeara933ScaledData (S.boundarySuffix i).space
      (S.boundarySuffix i).lattice
      (J.scaleGenerator (boundaryRightIndex i)) := by
  let m := S.boundarySuffixPred i
  let hcut : i.val + 1 + (m + 1) = n + 2 :=
    S.boundarySuffix_cut_eq i
  have hscale : scaleIdeal (S.boundarySuffix i).space
      (S.boundarySuffix i).lattice =
        principalIdeal (K := K)
          (J.scaleGenerator (boundaryRightIndex i) : K) := by
    have h := scaleIdeal_suffixQuadraticSublattice S.sourceJordan hcut
    have hindex : (⟨i.val + 1, by omega⟩ : Fin (n + 2)) =
        boundaryRightIndex i := by
      apply Fin.ext
      rfl
    simpa only [S.sourceJordan_scaleGenerator, hindex] using h
  exact omeara933Scaled (J.scaleGenerator (boundaryRightIndex i))
    (2 * (m + 1)) ⟨S.boundarySuffixTowerIsometry i⟩ hscale

end Omeara9328RankFourReductionSystem

end Lattice.JordanDecomposition

end Bong
