/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019PrefixThroughApproximation
import Bong.Bong.Beli2009RepresentationBridge
import Bong.Lattice.Omeara9328Necessity
import Bong.Lattice.BinaryDeterminantHyperbolic

/-!
# Jordan-prefix models for Beli (2019), Lemma 3.4

This module supplies the choice-free geometric layer needed to prove that
the spaces built from a prescribed strict Jordan decomposition approximate
the corresponding good-BONG prefixes.  A Jordan prefix is diagonalized with
exactly the good-BONG boundary rank, its determinant is related to the
refined lattice determinant by an explicit square, and O'Meara's boundary
embedding is converted to the matching `DiagonalRepresents` statement.

The trigger-dependent left and right representation clauses of Lemma 3.4
are proved in the subsequent module; no local representation law is assumed
by the definitions or theorems below.
-/

namespace Bong

open Dyadic Module
open BONG.GoodBONG
open scoped BigOperators

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG.JordanOrderProfileWitness

/-- Compare a prescribed strict Jordan decomposition with the strict
decomposition adapted to the same good BONG.  The comparison is constructed
from the identity lattice isometry, so it carries no additional law field. -/
structure PrescribedJordanComparison
    {n t : Nat} (a : BONG.GoodBONG q L (n + 2))
    (J : Lattice.JordanDecomposition q L (t + 1)) where
  adapted : BONG.StrictJordanAdaptedAlignment a.toBONG a.toBONG
  componentCount_eq : adapted.componentCount = t + 1
  sameType : Lattice.JordanDecomposition.SameFundamentalType
    (adapted.sourceJordanSucc componentCount_eq) J

/-- Every prescribed Jordan decomposition admits the concrete comparison
with a Jordan decomposition adapted to the given good BONG. -/
noncomputable def PrescribedJordanComparison.ofProfile
    {n t : Nat} (a : BONG.GoodBONG q L (n + 2))
    (J : Lattice.JordanDecomposition q L (t + 1)) :
    PrescribedJordanComparison a J := by
  let S :=
    (a.nonempty_strictJordanAdaptedAlignment a (fun _ ↦ rfl)).some
  let F := Lattice.JordanDecomposition.sameFundamentalTypeOfIsometry
    S.sourceJordan J (Lattice.Isometry.refl q L)
  have hcount : S.componentCount = t + 1 := by
    simpa only [Fintype.card_fin] using Fintype.card_congr F.indexEquiv
  exact
    { adapted := S
      componentCount_eq := hcount
      sameType := F.castSourceComponentCount hcount }

namespace PrescribedJordanComparison

variable {n t : Nat} {a : BONG.GoodBONG q L (n + 2)}
  {J : Lattice.JordanDecomposition q L (t + 1)}

/-- The order profile carried by the adapted side of the comparison. -/
noncomputable abbrev adaptedProfile (C : PrescribedJordanComparison a J) :=
  C.adapted.sourceProfileSucc C.componentCount_eq

/-- The adapted and prescribed profiles have the same actual BONG boundary
indices. -/
theorem boundaryIndex_eq (C : PrescribedJordanComparison a J)
    (P : JordanOrderProfileWitness a.toBONG J) (z : Fin t) :
    C.adaptedProfile.boundaryIndex z = P.boundaryIndex z := by
  apply Fin.ext
  have hsource :=
    C.adaptedProfile.boundaryIndex_succ_val_eq_componentRankPrefix z
  have htarget := P.boundaryIndex_succ_val_eq_componentRankPrefix z
  have hRank :
      (C.adapted.sourceJordanSucc C.componentCount_eq).toOrthogonalDecomposition.componentRank =
        J.toOrthogonalDecomposition.componentRank := by
    funext k
    have hk := C.sameType.componentRank_eq k
    rw [C.sameType.indexEquiv_apply_eq_self] at hk
    exact hk.symm
  rw [hRank] at hsource
  omega

/-- O'Meara 93:28 for the identity map, oriented from the prescribed
decomposition to the adapted one and with an arbitrary coherent generator
choice on the prescribed side. -/
theorem conditionsFromPrescribed
    [DyadicDiscriminantClassLaws K]
    (C : PrescribedJordanComparison a J)
    (A : Lattice.JordanDecomposition.FundamentalNormGeneratorChoice J) :
    J.Omeara9328ConditionsWith
      (C.adapted.sourceJordanSucc C.componentCount_eq) A := by
  cases t with
  | zero =>
      refine ⟨?_, ?_, ?_⟩ <;> intro i
      all_goals exact Fin.elim0 i
  | succ d =>
      exact
        Lattice.JordanDecomposition.omeara9328ConditionsWith_of_isometry
          J (C.adapted.sourceJordanSucc C.componentCount_eq) A
            (Lattice.Isometry.refl q L)

/-- The same identity comparison in the reverse orientation. -/
theorem conditionsFromAdapted
    [DyadicDiscriminantClassLaws K]
    (C : PrescribedJordanComparison a J)
    (A : Lattice.JordanDecomposition.FundamentalNormGeneratorChoice
      (C.adapted.sourceJordanSucc C.componentCount_eq)) :
    (C.adapted.sourceJordanSucc C.componentCount_eq).Omeara9328ConditionsWith
      J A := by
  cases t with
  | zero =>
      refine ⟨?_, ?_, ?_⟩ <;> intro i
      all_goals exact Fin.elim0 i
  | succ d =>
      exact
        Lattice.JordanDecomposition.omeara9328ConditionsWith_of_isometry
          (C.adapted.sourceJordanSucc C.componentCount_eq) J A
            (Lattice.Isometry.refl q L)

end PrescribedJordanComparison

noncomputable def boundaryPrefixRankEquiv
    {n t : Nat} {a : BONG.GoodBONG q L (n + 2)}
    {J : Lattice.JordanDecomposition q L (t + 1)}
    (P : JordanOrderProfileWitness a.toBONG J) (z : Fin t) :
    Fin ((P.boundaryIndex z).val + 1) ≃
      Fin (finrank K
        (J.toOrthogonalDecomposition.prefixQuadraticSublattice
          (z.val + 1)).carrier) := by
  let ri : Fin (t + 1) :=
    Lattice.JordanDecomposition.boundaryRightIndex z
  have hrank : finrank K
      (J.toOrthogonalDecomposition.prefixQuadraticSublattice
        (z.val + 1)).carrier =
      (P.boundaryIndex z).val + 1 := by
    change finrank K
        (J.toOrthogonalDecomposition.prefixCarrier (z.val + 1)) = _
    have hprefix :=
      J.toOrthogonalDecomposition.finrank_prefixCarrier_index ri
    have hri : ri.val = z.val + 1 := rfl
    rw [hri] at hprefix
    rw [hprefix]
    exact (P.boundaryIndex_succ_val_eq_componentRankPrefix z).symm
  exact finCongr hrank.symm

noncomputable def boundaryPrefixNativeBONG
    {n t : Nat} {a : BONG.GoodBONG q L (n + 2)}
    {J : Lattice.JordanDecomposition q L (t + 1)}
    (_P : JordanOrderProfileWitness a.toBONG J) (z : Fin t) :
    let C := J.toOrthogonalDecomposition.prefixQuadraticSublattice
      (z.val + 1)
    BONG C.carrier C.space C.lattice (finrank K C.carrier) := by
  dsimp only
  exact BONG.ofLattice _ _

noncomputable def boundaryPrefixDiagonalUnits
    {n t : Nat} {a : BONG.GoodBONG q L (n + 2)}
    {J : Lattice.JordanDecomposition q L (t + 1)}
    (P : JordanOrderProfileWitness a.toBONG J) (z : Fin t) :
    Fin ((P.boundaryIndex z).val + 1) → Kˣ :=
  fun i ↦ (P.boundaryPrefixNativeBONG z).valueUnit
    (P.boundaryPrefixRankEquiv z i)

theorem boundaryPrefixDiagonalUnits_product
    {n t : Nat} {a : BONG.GoodBONG q L (n + 2)}
    {J : Lattice.JordanDecomposition q L (t + 1)}
    (P : JordanOrderProfileWitness a.toBONG J) (z : Fin t) :
    diagonalUnitDeterminant (P.boundaryPrefixDiagonalUnits z) =
      (P.boundaryPrefixNativeBONG z).valueProduct := by
  unfold diagonalUnitDeterminant boundaryPrefixDiagonalUnits
  rw [(P.boundaryPrefixRankEquiv z).prod_comp
    (P.boundaryPrefixNativeBONG z).valueUnit]
  simp [BONG.valueProduct, BONG.prefixProduct]

theorem boundaryPrefixDiagonalUnits_eq_refinedDeterminant_mul_square
    {n t : Nat} {a : BONG.GoodBONG q L (n + 2)}
    {J : Lattice.JordanDecomposition q L (t + 1)}
    (P : JordanOrderProfileWitness a.toBONG J) (z : Fin t) :
    ∃ s : Kˣ,
      diagonalUnitDeterminant (P.boundaryPrefixDiagonalUnits z) =
        (J.toOrthogonalDecomposition.prefixQuadraticSublattice
          (z.val + 1)).refinedDeterminantUnit * s ^ 2 := by
  let C := J.toOrthogonalDecomposition.prefixQuadraticSublattice
    (z.val + 1)
  obtain ⟨s, hs⟩ :=
    Lattice.exists_valueProduct_eq_determinantUnit_mul_square
      (P.boundaryPrefixNativeBONG z)
  refine ⟨s, P.boundaryPrefixDiagonalUnits_product z |>.trans ?_⟩
  simpa only [C,
    Lattice.QuadraticSublattice.refinedDeterminantUnit] using hs

set_option maxHeartbeats 0 in
theorem boundaryPrefixDiagonalUnits_isPrefixApproximation
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    {n t : Nat} (a : BONG.GoodBONG q L (n + 2))
    (W : Lattice.WeakJordanDecomposition q L (t + 1))
    (hW : W.HasImproperEvenRank)
    (hstrict : StrictMono (fun i ↦ ordUnit K (W.scaleGenerator i)))
    (P : JordanOrderProfileWitness a.toBONG (W.toJordan hstrict))
    (z : Fin t) :
    a.IsPrefixApproximation ((P.boundaryIndex z).val + 1)
      (diagonalUnitDeterminant (P.boundaryPrefixDiagonalUnits z)) := by
  let J := W.toJordan hstrict
  let p : Fin (t + 1) :=
    Lattice.JordanDecomposition.boundaryLeftIndex z
  let w := BONG.WeakJordanOrderProfileWitness.ofStrict W hstrict P
  let C := w.jordanBlockCoordinates hW p
  have hraw :=
    BONG.WeakJordanOrderProfileWitness.prefixThrough_isPrefixApproximation
      a W hW hstrict P p
  have hstop : C.stop = (P.boundaryIndex z).val + 1 := by
    change w.componentStart p +
        finrank K (W.component p).carrier =
      (P.boundaryIndex z).val + 1
    have hb := P.boundaryIndex_succ_val_eq_componentRankPrefix z
    change (P.boundaryIndex z).val + 1 =
      ∑ k ∈ Finset.Iio
        (Lattice.JordanDecomposition.boundaryRightIndex z),
          finrank K (W.component k).carrier at hb
    have hsum :
        (∑ k ∈ Finset.Iio
          (Lattice.JordanDecomposition.boundaryRightIndex z),
            finrank K (W.component k).carrier) =
        w.componentStart p + finrank K (W.component p).carrier := by
      let ri : Fin (t + 1) :=
        Lattice.JordanDecomposition.boundaryRightIndex z
      have hIio : Finset.Iio ri = insert p (Finset.Iio p) := by
        ext k
        simp only [Finset.mem_Iio, Finset.mem_insert]
        change (k.val < z.val + 1 ↔ k = p ∨ k.val < z.val)
        constructor
        · intro hk
          by_cases heq : k.val = z.val
          · exact Or.inl (Fin.ext heq)
          · exact Or.inr (by omega)
        · rintro (rfl | hk)
          · simp [p, Lattice.JordanDecomposition.boundaryLeftIndex]
          · omega
      rw [hIio, Finset.sum_insert (by simp)]
      change finrank K (W.component p).carrier + w.componentStart p = _
      omega
    omega
  change a.IsPrefixApproximation C.stop
      ((J.toOrthogonalDecomposition.prefixQuadraticSublattice
        (p.val + 1)).refinedDeterminantUnit) at hraw
  have hpval : p.val + 1 = z.val + 1 := by rfl
  rw [hstop, hpval] at hraw
  obtain ⟨s, hs⟩ :=
    P.boundaryPrefixDiagonalUnits_eq_refinedDeterminant_mul_square z
  rw [hs]
  exact (a.isPrefixApproximation_mul_square_iff
    ((P.boundaryIndex z).val + 1)
    ((J.toOrthogonalDecomposition.prefixQuadraticSublattice
      (z.val + 1)).refinedDeterminantUnit) s).2 hraw

noncomputable def boundaryPrefixDiagonalizationIsometry
    {n t : Nat} {a : BONG.GoodBONG q L (n + 2)}
    {J : Lattice.JordanDecomposition q L (t + 1)}
    (P : JordanOrderProfileWitness a.toBONG J) (z : Fin t) :
    QuadraticSpace.Isometry (J.prefixSpace (z.val + 1))
      (QuadraticSpace.finiteDiagonal
        (diagonalUnitCoefficients (P.boundaryPrefixDiagonalUnits z))
        (QuadraticSpace.diagonalUnitCoefficients_ne_zero
          (P.boundaryPrefixDiagonalUnits z))) := by
  let e := P.boundaryPrefixRankEquiv z
  let reindex := QuadraticSpace.finiteDiagonalReindexIsometry
    (P.boundaryPrefixNativeBONG z).value
    (fun i ↦ Units.ne_zero
      ((P.boundaryPrefixNativeBONG z).valueUnit i)) e
  exact (P.boundaryPrefixNativeBONG z).exactDiagonalizationIsometry.trans
    reindex

theorem boundaryIndex_eq_of_sameFundamentalType
    {n t : Nat} {a : BONG.GoodBONG q L (n + 2)}
    {J H : Lattice.JordanDecomposition q L (t + 1)}
    (P : JordanOrderProfileWitness a.toBONG J)
    (Q : JordanOrderProfileWitness a.toBONG H)
    (F : Lattice.JordanDecomposition.SameFundamentalType J H)
    (z : Fin t) :
    P.boundaryIndex z = Q.boundaryIndex z := by
  apply Fin.ext
  have hP := P.boundaryIndex_succ_val_eq_componentRankPrefix z
  have hQ := Q.boundaryIndex_succ_val_eq_componentRankPrefix z
  have hRank :
      J.toOrthogonalDecomposition.componentRank =
        H.toOrthogonalDecomposition.componentRank := by
    funext k
    have hk := F.componentRank_eq k
    rw [F.indexEquiv_apply_eq_self] at hk
    exact hk.symm
  rw [hRank] at hP
  omega

theorem boundaryEmbedding_iff_diagonal
    {X : Type v} [AddCommGroup X] [Module K X]
    {Y : Type v} [AddCommGroup Y] [Module K Y]
    {p : QuadraticSpace K X} {r : QuadraticSpace K Y}
    {C : Lattice.QuadraticSublattice p}
    {D : Lattice.QuadraticSublattice r}
    {m n : Nat} (source : Fin m → Kˣ) (target : Fin n → Kˣ)
    (A : Kˣ)
    (sourceIso : QuadraticSpace.Isometry C.space
      (QuadraticSpace.finiteDiagonal
        (diagonalUnitCoefficients source)
        (QuadraticSpace.diagonalUnitCoefficients_ne_zero source)))
    (targetIso : QuadraticSpace.Isometry D.space
      (QuadraticSpace.finiteDiagonal
        (diagonalUnitCoefficients target)
        (QuadraticSpace.diagonalUnitCoefficients_ne_zero target))) :
    Lattice.QuadraticSublattice.EmbedsIntoOrthogonalSum C D
        (QuadraticSpace.scaledLine A) ↔
      DiagonalRepresents (diagonalUnitCoefficients source)
        (diagonalUnitCoefficients (Fin.snoc target A)) := by
  let targetWithLine := targetIso.orthogonalSum
    (QuadraticSpace.Isometry.refl (QuadraticSpace.scaledLine A))
  unfold Lattice.QuadraticSublattice.EmbedsIntoOrthogonalSum
    QuadraticSpace.EmbedsInto
  rw [QuadraticSpace.represents_iff_of_isometries sourceIso targetWithLine]
  exact QuadraticSpace.finiteDiagonal_orthogonalSum_scaledLine_represents_iff
    source target A

end BONG.JordanOrderProfileWitness

end Bong
