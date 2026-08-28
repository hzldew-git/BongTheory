/- Construction of the orthogonal-complement model in Beli 2019, Lemma 3.4(iii). -/
import Bong.Bong.Beli2019Lemma34OneBefore
import Bong.QuadraticSpace.LineOrthogonalSplit

namespace Bong

open Dyadic Module
open BONG.GoodBONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG.JordanOrderProfileWitness.BoundaryOneBeforeModel

variable {n t : Nat} {a : BONG.GoodBONG q L (n + 2)}
  {J : Lattice.JordanDecomposition q L (t + 1)}
  {P : BONG.JordanOrderProfileWitness a.toBONG J} {z : Fin t} {A : Kˣ}

/-- A represented nonzero value canonically supplies the complement model
used in Beli's notation `F L_(k) ⊥ [A_k]`. -/
noncomputable def ofRepresentedVector
    (x : (J.toOrthogonalDecomposition.prefixQuadraticSublattice
      (z.val + 1)).carrier)
    (hA : (J.prefixSpace (z.val + 1)).quadratic x = (A : K)) :
    BoundaryOneBeforeModel P z A := by
  letI : Module.Finite K V := L.moduleFinite
  let Qp := J.prefixSpace (z.val + 1)
  have hx : Qp.IsAnisotropic x := by
    unfold QuadraticSpace.IsAnisotropic
    rw [hA]
    exact Units.ne_zero A
  let Qc := Qp.orthogonalSpace x hx
  have hprefix : (P.boundaryIndex z).val + 1 =
      finrank K (J.toOrthogonalDecomposition.prefixQuadraticSublattice
        (z.val + 1)).carrier := by
    simpa only [Fintype.card_fin] using
      Fintype.card_congr (P.boundaryPrefixRankEquiv z)
  have horth := Qp.finrank_vectorOrthogonal hx
  have hcomplement : finrank K (Qp.vectorOrthogonal x) =
      (P.boundaryIndex z).val := by
    omega
  let e : Fin (P.boundaryIndex z).val ≃
      Fin (finrank K (Qp.vectorOrthogonal x)) :=
    finCongr hcomplement.symm
  let units : Fin (P.boundaryIndex z).val → Kˣ :=
    Qc.diagonalUnits ∘ e
  let reindex := QuadraticSpace.finiteDiagonalReindexIsometry
    (diagonalUnitCoefficients Qc.diagonalUnits)
    (QuadraticSpace.diagonalUnitCoefficients_ne_zero Qc.diagonalUnits) e
  let complementIso : QuadraticSpace.Isometry
      (QuadraticSpace.finiteDiagonal
        (diagonalUnitCoefficients units)
        (QuadraticSpace.diagonalUnitCoefficients_ne_zero units)) Qc := by
    have hraw := reindex.symm.trans Qc.diagonalizationIsometry.symm
    change QuadraticSpace.Isometry
      (QuadraticSpace.finiteDiagonal
        (fun i ↦ (Qc.diagonalUnits (e i) : K))
        (fun i ↦ Units.ne_zero (Qc.diagonalUnits (e i)))) Qc
    simpa only [reindex, Qc, QuadraticSpace.diagonalModel,
      diagonalUnitCoefficients] using hraw
  refine
    { units := units
      splitIsometry := ?_ }
  exact
    (complementIso.orthogonalSum
        (QuadraticSpace.Isometry.refl (QuadraticSpace.scaledLine A)))
      |>.trans (QuadraticSpace.orthogonalSumSwap Qc
        (QuadraticSpace.scaledLine A))
      |>.trans (QuadraticSpace.scaledLineOrthogonalIsometry Qp x A hx hA)

/-- A field-space representation of `[A]` by the Jordan prefix supplies the
represented vector and hence the complement model. -/
noncomputable def ofLineRepresentation
    (hrep : (J.prefixSpace (z.val + 1)).Represents
      (QuadraticSpace.scaledLine A)) :
    BoundaryOneBeforeModel P z A := by
  let f := Classical.choice hrep
  let x := f.toLinearMap 1
  apply ofRepresentedVector (P := P) (z := z) (A := A) x
  have hq := f.map_quadratic 1
  simpa only [x, QuadraticSpace.scaledLine_quadratic_apply, one_pow,
    mul_one] using hq

/-- In particular, an integral represented value in the actual Jordan prefix
constructs the complement model used in Lemma 3.4(iii). -/
noncomputable def ofQuadraticValue
    (hvalue : (A : K) ∈ Lattice.quadraticValueSet
      (J.prefixSpace (z.val + 1))
      (J.prefixIntegralLattice (z.val + 1))) :
    BoundaryOneBeforeModel P z A := by
  have hexists := (Lattice.mem_quadraticValueSet_iff
    (J.prefixSpace (z.val + 1))
    (J.prefixIntegralLattice (z.val + 1)) (A : K)).1 hvalue
  let x := Classical.choose hexists
  have hquadratic := (Classical.choose_spec hexists).2
  exact ofRepresentedVector (P := P) (z := z) (A := A) x hquadratic

end BONG.JordanOrderProfileWitness.BoundaryOneBeforeModel

end Bong
