import Bong.Lattice.BinaryDeterminantHyperbolic
import Bong.Bong.DiagonalQuaternaryComplementProof
import Bong.Lattice.Omeara9318DeterminantOneHyperbolicModel

/-!
# A rank-four hyperbolicity criterion

A quaternary space of determinant square class one is split once it
represents a hyperbolic plane.  The proof constructs the orthogonal binary
complement of that represented plane and computes its determinant square
class.  Thus the criterion is independent of any local-classification law
interface.
-/

namespace Bong

open Dyadic Module BONG.GoodBONG

namespace QuadraticSpace

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

/-- A rank-four space whose ordinary diagonal determinant is a square and
which represents a hyperbolic plane is the orthogonal sum of two hyperbolic
planes.  This is the space-level form of the exceptional case used by
He--Hu, Theorem 1.1. -/
theorem rankFour_isIsometric_hyperbolicPair_of_diagonalDeterminant_isSquare
    [FiniteDimensional K V]
    (q : QuadraticSpace K V)
    (hrank : finrank K V = 4)
    (hdet : IsSquare
      (BONG.GoodBONG.diagonalUnitDeterminant q.diagonalUnits))
    (hrep : q.Represents (hyperbolicPlane (1 : Kˣ))) :
    q.IsIsometric
      ((hyperbolicPlane (1 : Kˣ)).orthogonalSum
        (hyperbolicPlane (1 : Kˣ))) := by
  classical
  let b : Fin 2 → Kˣ := ![(1 : Kˣ), (-1 : Kˣ)]
  have hbSquare : IsSquare (-(b 0 / b 1)) := by
    refine ⟨1, ?_⟩
    simp [b]
  rcases finiteDiagonal_fin_two_isIsometric_hyperbolicPlane_one
      (b 0) (b 1) hbSquare with ⟨bToHyperbolicRaw⟩
  have hbCoefficients : diagonalUnitCoefficients b =
      ![(b 0 : K), (b 1 : K)] := by
    funext i
    fin_cases i <;> rfl
  let bToHyperbolic : Isometry
      (finiteDiagonal (diagonalUnitCoefficients b)
        (fun i ↦ Units.ne_zero (b i)))
      (hyperbolicPlane (1 : Kˣ)) := by
    simpa only [hbCoefficients] using bToHyperbolicRaw
  let e : Fin 4 ≃ Fin (finrank K V) := finCongr hrank.symm
  let d : Fin 4 → Kˣ := fun i ↦ q.diagonalUnits (e i)
  let qToD : Isometry q
      (finiteDiagonal (diagonalUnitCoefficients d)
        (fun i ↦ Units.ne_zero (d i))) :=
    q.diagonalizationIsometry.trans
      (finiteDiagonalReindexIsometry
        (diagonalUnitCoefficients q.diagonalUnits)
        (fun i ↦ Units.ne_zero (q.diagonalUnits i)) e)
  rcases hrep with ⟨hyperbolicInQ⟩
  have hbinarySpace :
      (finiteDiagonal (diagonalUnitCoefficients d)
        (fun i ↦ Units.ne_zero (d i))).Represents
          (finiteDiagonal (diagonalUnitCoefficients b)
            (fun i ↦ Units.ne_zero (b i))) :=
    ⟨qToD.toRepresentation.trans
      (hyperbolicInQ.trans bToHyperbolic.toRepresentation)⟩
  have hbinary : DiagonalRepresents
      (diagonalUnitCoefficients b)
      (diagonalUnitCoefficients d) :=
    (finiteDiagonal_represents_iff_diagonalRepresents b d).mp hbinarySpace
  rcases DiagonalRepresents.binary_complete_to_quaternary b d hbinary with
    ⟨c, hfull⟩
  have hfullSpace :
      (finiteDiagonal (diagonalUnitCoefficients d)
        (fun i ↦ Units.ne_zero (d i))).Represents
          (finiteDiagonal
            (diagonalUnitCoefficients (Fin.append b c))
            (fun i ↦ Units.ne_zero (Fin.append b c i))) :=
    (finiteDiagonal_represents_iff_diagonalRepresents
      (Fin.append b c) d).mpr hfull
  rcases hfullSpace with ⟨fullRepresentation⟩
  let fullToD : Isometry
      (finiteDiagonal
        (diagonalUnitCoefficients (Fin.append b c))
        (fun i ↦ Units.ne_zero (Fin.append b c i)))
      (finiteDiagonal (diagonalUnitCoefficients d)
        (fun i ↦ Units.ne_zero (d i))) :=
    fullRepresentation.toIsometryOfFinrankEq (by simp)
  have hdProduct : diagonalUnitDeterminant d =
      diagonalUnitDeterminant q.diagonalUnits := by
    unfold diagonalUnitDeterminant d
    exact e.prod_comp q.diagonalUnits
  have hdSquare : IsSquare (diagonalUnitDeterminant d) := by
    rw [hdProduct]
    exact hdet
  rcases DiagonalRepresents.exists_prod_eq_mul_square_of_sameRank hfull with
    ⟨p, hp⟩
  have hfullDet : diagonalUnitDeterminant (Fin.append b c) =
      diagonalUnitDeterminant d * p ^ 2 := by
    apply Units.ext
    change (∏ i, ((Fin.append b c i : Kˣ) : K)) =
      (∏ i, ((d i : Kˣ) : K)) * (p : K) ^ 2
    exact hp
  have hfullSquare :
      IsSquare (diagonalUnitDeterminant (Fin.append b c)) := by
    rcases hdSquare with ⟨s, hs⟩
    refine ⟨s * p, ?_⟩
    rw [hfullDet, hs]
    simp only [pow_two]
    ac_rfl
  have hbcDet : diagonalUnitDeterminant (Fin.append b c) =
      (-1 : Kˣ) * (c 0 * c 1) := by
    unfold diagonalUnitDeterminant
    rw [Fin.prod_univ_add]
    simp only [Fin.append_left, Fin.append_right, Fin.prod_univ_two]
    simp [b]
  have hcProductSquare : IsSquare ((c 0 * c 1) * (-1 : Kˣ)) := by
    rw [hbcDet] at hfullSquare
    simpa only [mul_comm] using hfullSquare
  rcases hcProductSquare with ⟨t, ht⟩
  have hcSignedRatio : IsSquare (-(c 0 / c 1)) := by
    refine ⟨t / c 1, ?_⟩
    calc
      -(c 0 / c 1) =
          ((c 0 * c 1) * (-1 : Kˣ)) / (c 1 * c 1) := by
        apply Units.ext
        simp only [div_eq_mul_inv, Units.val_neg, Units.val_mul,
          Units.val_inv_eq_inv_val, Units.val_one]
        field_simp [Units.ne_zero]
      _ = (t * t) / (c 1 * c 1) := by rw [ht]
      _ = (t / c 1) * (t / c 1) := by
        apply Units.ext
        simp only [div_eq_mul_inv, Units.val_mul, Units.val_inv_eq_inv_val]
        field_simp [Units.ne_zero]
  rcases finiteDiagonal_fin_two_isIsometric_hyperbolicPlane_one
      (c 0) (c 1) hcSignedRatio with ⟨cToHyperbolicRaw⟩
  have hcCoefficients : diagonalUnitCoefficients c =
      ![(c 0 : K), (c 1 : K)] := by
    funext i
    fin_cases i <;> rfl
  let cToHyperbolic : Isometry
      (finiteDiagonal (diagonalUnitCoefficients c)
        (fun i ↦ Units.ne_zero (c i)))
      (hyperbolicPlane (1 : Kˣ)) := by
    simpa only [hcCoefficients] using cToHyperbolicRaw
  let splitAppend := (finiteDiagonalOrthogonalSumIsometry b c).symm
  exact ⟨qToD.trans <| fullToD.symm.trans <|
    splitAppend.trans (bToHyperbolic.orthogonalSum cToHyperbolic)⟩

/-- A rank-four space of refined determinant class one that represents a
hyperbolic plane is split.  This lattice-level wrapper retains the original
O'Meara-facing statement while delegating the geometric argument to the
ordinary determinant criterion above. -/
theorem rankFour_isIsometric_hyperbolicPair_of_determinantClass_eq_one
    [FiniteDimensional K V]
    (q : QuadraticSpace K V) (L : Lattice K V)
    (hrank : finrank K V = 4)
    (hdet : Lattice.determinantClass q L = 1)
    (hrep : q.Represents (hyperbolicPlane (1 : Kˣ))) :
    q.IsIsometric
      ((hyperbolicPlane (1 : Kˣ)).orthogonalSum
        (hyperbolicPlane (1 : Kˣ))) := by
  apply rankFour_isIsometric_hyperbolicPair_of_diagonalDeterminant_isSquare
    q hrank
  · have hdClass :
        squareClass K (diagonalUnitDeterminant q.diagonalUnits) =
          squareClass K (1 : Kˣ) := by
      calc
        squareClass K (diagonalUnitDeterminant q.diagonalUnits) =
            unitSquareClassToSquareClass K
              (Lattice.determinantClass q L) :=
          Lattice.squareClass_diagonalUnitDeterminant_eq_determinantClass_toSquareClass
            q L
        _ = unitSquareClassToSquareClass K 1 := by rw [hdet]
        _ = squareClass K (1 : Kˣ) := by rfl
    simpa using
      (isSquare_mul_of_squareClass_eq
        (diagonalUnitDeterminant q.diagonalUnits) (1 : Kˣ) hdClass)
  · exact hrep

end QuadraticSpace

end Bong
