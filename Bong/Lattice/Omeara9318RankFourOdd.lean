/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Omeara9318RankFourCongruence
import Bong.Lattice.OmearaModularNormClassification
import Bong.Lattice.ProjectionScaling
import Bong.Bong.DiagonalLocalClassificationProof

/-!
# O'Meara 93:18(iii): the odd quaternary case

The preceding file constructs the two printed models and proves the common
norm-group and determinant assertions.  Here the concrete local field
classification chooses the model whose Hasse symbol agrees with the actual
quadratic space.  O'Meara 93:16 then upgrades the ambient field isometry to
an integral lattice isometry.
-/

namespace Bong

open Dyadic Module BONG.GoodBONG

namespace Lattice

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [laws : DyadicDiscriminantClassLaws K]

private theorem isSquare_mul_of_squareClass_eq (x y : Kˣ)
    (h : squareClass K x = squareClass K y) : IsSquare (x * y) := by
  change QuotientGroup.mk' (Subgroup.square Kˣ) x =
    QuotientGroup.mk' (Subgroup.square Kˣ) y at h
  rw [QuotientGroup.mk'_eq_mk'] at h
  rcases h with ⟨z, hz, hxz⟩
  change IsSquare z at hz
  have hxSquare : IsSquare (x ^ 2) := ⟨x, pow_two x⟩
  have hproduct : IsSquare (x ^ 2 * z) := hxSquare.mul hz
  have heq : x * y = x ^ 2 * z := by
    rw [← hxz]
    simpa only [pow_two] using (mul_assoc x x z).symm
  rw [heq]
  exact hproduct

private theorem intUnit_eq_or_eq_neg (x y : ℤˣ) : x = y ∨ x = -y := by
  rcases Int.units_eq_one_or x with hx | hx <;>
    rcases Int.units_eq_one_or y with hy | hy <;>
      simp [hx, hy]

private theorem rankFourDiagonalRepresents_of_invariants
    {n : Nat} (hn : n = 4) (a : Fin n → Kˣ) (b : Fin 4 → Kˣ)
    (hdet : IsSquare
      (diagonalUnitDeterminant a * diagonalUnitDeterminant b))
    (hhasse : diagonalHasseSymbol K a = diagonalHasseSymbol K b) :
    DiagonalRepresents (diagonalUnitCoefficients a)
      (diagonalUnitCoefficients b) := by
  subst n
  exact DyadicDiagonalClassificationLaws.represents_of_invariants
    a b hdet hhasse

/-- Field classification in rank four, with the target supplied by an
explicit four-entry diagonalization. -/
noncomputable def rankFourFieldIsometryOfExplicitDiagonal
    {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type w} [AddCommGroup W] [Module K W]
    (q : QuadraticSpace K V) [FiniteDimensional K V]
    (r : QuadraticSpace K W)
    (hrank : finrank K V = 4)
    (c : Fin 4 → Kˣ)
    (diagonalize : QuadraticSpace.Isometry r
      (QuadraticSpace.finiteDiagonal
        (diagonalUnitCoefficients c)
        (fun i ↦ Units.ne_zero (c i))))
    (hdet : IsSquare
      (diagonalUnitDeterminant q.diagonalUnits *
        diagonalUnitDeterminant c))
    (hhasse : diagonalHasseSymbol K q.diagonalUnits =
      diagonalHasseSymbol K c) :
    QuadraticSpace.Isometry q r := by
  have hdiag := rankFourDiagonalRepresents_of_invariants
    hrank q.diagonalUnits c hdet hhasse
  have hrepDiagonal :
      (QuadraticSpace.finiteDiagonal
        (diagonalUnitCoefficients c)
        (fun i ↦ Units.ne_zero (c i))).Represents q.diagonalModel :=
    DiagonalRepresents.toQuadraticSpaceRepresents
      (fun i ↦ Units.ne_zero (q.diagonalUnits i))
      (fun i ↦ Units.ne_zero (c i)) hdiag
  let g := Classical.choice hrepDiagonal
  let represented : QuadraticSpace.Representation q
      (QuadraticSpace.finiteDiagonal
        (diagonalUnitCoefficients c)
        (fun i ↦ Units.ne_zero (c i))) :=
    g.trans q.diagonalizationIsometry.toRepresentation
  have hfinrank : finrank K V = finrank K (Fin 4 → K) := by
    simp only [hrank, finrank_pi, Fintype.card_fin]
  let toDiagonal := represented.toIsometryOfFinrankEq hfinrank
  exact toDiagonal.trans diagonalize.symm

/-- Once a field isometry to a unimodular model is known, equality of norm
groups and O'Meara 93:16 give the integral lattice isometry. -/
noncomputable def latticeIsometryToUnimodularModel
    {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type w} [AddCommGroup W] [Module K W]
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W}
    (hL : IsModular q L (1 : Kˣ))
    (hM : IsModular r M (1 : Kˣ))
    (f : QuadraticSpace.Isometry q r)
    (hgroup : normGroupSet q L = normGroupSet r M) :
    Isometry q r L M := by
  let imageIsometry := Isometry.toMap q f L
  have hImage : IsModular r (map f.toLinearEquiv L) (1 : Kˣ) :=
    hL.mapLatticeIsometry imageIsometry
  have hImageGroup : normGroupSet r (map f.toLinearEquiv L) =
      normGroupSet r M := by
    rw [normGroupSet_map_isometry f L]
    exact hgroup
  exact imageIsometry.trans
    (omeara9316_of_modular_normGroupSet_eq
      (1 : Kˣ) hImage hM hImageGroup)

/-- The two odd quaternary models in O'Meara 93:18(iii) cannot be
isometric: their Hasse invariants are opposite. -/
theorem Omeara9318RankFourModelParameters.j_not_isometric_k
    (P : Omeara9318RankFourModelParameters K) :
    ¬ QuadraticSpace.IsIsometric P.jData.space P.kData.space := by
  rintro ⟨f⟩
  let diagonalIsometry :=
    P.jData.diagonalizationIsometry.symm.trans
      (f.trans P.kData.diagonalizationIsometry)
  have hrepSpace :
      (QuadraticSpace.finiteDiagonal
        (diagonalUnitCoefficients P.kData.diagonalUnits)
        (fun i ↦ Units.ne_zero (P.kData.diagonalUnits i))).Represents
      (QuadraticSpace.finiteDiagonal
        (diagonalUnitCoefficients P.jData.diagonalUnits)
        (fun i ↦ Units.ne_zero (P.jData.diagonalUnits i))) :=
    ⟨diagonalIsometry.toRepresentation⟩
  have hrep : DiagonalRepresents
      (diagonalUnitCoefficients P.jData.diagonalUnits)
      (diagonalUnitCoefficients P.kData.diagonalUnits) :=
    (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
      P.jData.diagonalUnits P.kData.diagonalUnits).mp hrepSpace
  have hhasse := DiagonalIsometryInvariantLaws.hasse_eq
    P.jData.diagonalUnits P.kData.diagonalUnits hrep
  have hself : diagonalHasseSymbol K P.jData.diagonalUnits =
      -diagonalHasseSymbol K P.jData.diagonalUnits :=
    hhasse.trans P.k_hasse_eq_neg_j_hasse
  exact (units_ne_neg_self
    (diagonalHasseSymbol K P.jData.diagonalUnits)) hself

/-- The complete odd-quaternary output of O'Meara 93:18(iii). -/
structure Omeara9318RankFourOddData
    {V : Type v} [AddCommGroup V] [Module K V]
    (q : QuadraticSpace K V) (L : Lattice K V) (a : Kˣ) where
  congruence : Omeara9318RankFourCongruenceData q L a
  isometric_j_or_k :
    IsIsometric q congruence.parameters.jData.space L
        congruence.parameters.jData.lattice ∨
      IsIsometric q congruence.parameters.kData.space L
        congruence.parameters.kData.lattice
  not_both : ¬
    (IsIsometric q congruence.parameters.jData.space L
        congruence.parameters.jData.lattice ∧
      IsIsometric q congruence.parameters.kData.space L
        congruence.parameters.kData.lattice)

set_option maxHeartbeats 3000000 in

/-- O'Meara 93:18(iii): every odd quaternary unimodular lattice is
integrally isometric to one of the two displayed models. -/
noncomputable def omeara9318iiiData
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V}
    (hmodular : IsModular q L (1 : Kˣ))
    (hrank : finrank K V = 4)
    (a : Kˣ) (ha : IsNormGeneratorValue q L a)
    (hodd : Odd (ordUnit K a + weightIdealOrder q L)) :
    Omeara9318RankFourOddData q L a := by
  letI : Module.Finite K V := L.moduleFinite
  let C := omeara9318RankFourCongruenceData
    hmodular hrank a ha hodd
  let P := C.parameters
  let actual := q.diagonalUnits
  let j := P.jData.diagonalUnits
  let k := P.kData.diagonalUnits
  let latticeBONG := BONG.ofLattice q L
  have hactualSquareClass :
      squareClass K (diagonalUnitDeterminant actual) =
        squareClass K P.d := by
    have hclasses := congrArg (unitSquareClassToSquareClass K)
      C.determinantClass_eq_d
    calc
      squareClass K (diagonalUnitDeterminant actual) =
          squareClass K q.diagonalizingBONG.valueProduct := by
        apply congrArg (squareClass K)
        apply Units.ext
        simp [actual, diagonalUnitDeterminant,
          QuadraticSpace.diagonalUnits]
      _ = squareClass K latticeBONG.valueProduct :=
        (BONG.valueProduct_squareClass_eq
          latticeBONG q.diagonalizingBONG).symm
      _ = unitSquareClassToSquareClass K (determinantClass q L) :=
        (determinantClass_toSquareClass_eq_valueProduct latticeBONG).symm
      _ = unitSquareClassToSquareClass K (unitSquareClass K P.d) :=
        hclasses
      _ = squareClass K P.d :=
        unitSquareClassToSquareClass_apply K P.d
  have hdetJ : IsSquare
      (diagonalUnitDeterminant actual * diagonalUnitDeterminant j) := by
    have h := isSquare_mul_of_squareClass_eq
      (diagonalUnitDeterminant actual) P.d hactualSquareClass
    simpa only [j, P.jData_diagonalUnits_eq,
      P.jDiagonalUnitDeterminant_eq_d] using h
  have hdetK : IsSquare
      (diagonalUnitDeterminant actual * diagonalUnitDeterminant k) := by
    apply isSquare_mul_trans
      (diagonalUnitDeterminant actual)
      (diagonalUnitDeterminant j)
      (diagonalUnitDeterminant k)
    · exact hdetJ
    · simpa only [j, k, P.jData_diagonalUnits_eq,
        P.kData_diagonalUnits_eq] using
        P.modelDeterminants_product_isSquare
  have hkNeg : diagonalHasseSymbol K k =
      -diagonalHasseSymbol K j :=
    P.k_hasse_eq_neg_j_hasse
  have hgroupJ : normGroupSet q L =
      normGroupSet P.jData.space P.jData.lattice := by
    calc
      normGroupSet q L =
          integralSquareCoset (a : K)
            (principalIdeal (K := K) (P.b : K)) :=
        C.normGroupSet_eq_common
      _ = integralSquareCoset (P.a : K)
            (principalIdeal (K := K) (P.b : K)) := by
        rw [C.parameters_a]
      _ = normGroupSet P.jData.space P.jData.lattice :=
        P.j_normGroupSet_eq.symm
  have hgroupK : normGroupSet q L =
      normGroupSet P.kData.space P.kData.lattice := by
    calc
      normGroupSet q L =
          integralSquareCoset (a : K)
            (principalIdeal (K := K) (P.b : K)) :=
        C.normGroupSet_eq_common
      _ = integralSquareCoset (P.a : K)
            (principalIdeal (K := K) (P.b : K)) := by
        rw [C.parameters_a]
      _ = normGroupSet P.kData.space P.kData.lattice :=
        P.k_normGroupSet_eq.symm
  have hnotBoth : ¬
      (IsIsometric q P.jData.space L P.jData.lattice ∧
        IsIsometric q P.kData.space L P.kData.lattice) := by
    rintro ⟨⟨fJ⟩, ⟨fK⟩⟩
    apply P.j_not_isometric_k
    exact ⟨fJ.toQuadraticSpaceIsometry.symm.trans
      fK.toQuadraticSpaceIsometry⟩
  by_cases hJ : diagonalHasseSymbol K actual =
      diagonalHasseSymbol K j
  · let fJ := rankFourFieldIsometryOfExplicitDiagonal
      q P.jData.space hrank j P.jData.diagonalizationIsometry hdetJ hJ
    let integralJ := latticeIsometryToUnimodularModel
      hmodular P.jData.isModular fJ hgroupJ
    exact
      { congruence := C
        isometric_j_or_k := Or.inl ⟨integralJ⟩
        not_both := hnotBoth }
  · have hnegJ : diagonalHasseSymbol K actual =
        -diagonalHasseSymbol K j :=
      (intUnit_eq_or_eq_neg
        (diagonalHasseSymbol K actual)
        (diagonalHasseSymbol K j)).resolve_left hJ
    have hK : diagonalHasseSymbol K actual =
        diagonalHasseSymbol K k := hnegJ.trans hkNeg.symm
    let fK := rankFourFieldIsometryOfExplicitDiagonal
      q P.kData.space hrank k P.kData.diagonalizationIsometry hdetK hK
    let integralK := latticeIsometryToUnimodularModel
      hmodular P.kData.isModular fK hgroupK
    exact
      { congruence := C
        isometric_j_or_k := Or.inr ⟨integralK⟩
        not_both := hnotBoth }

end Lattice

end Bong
