/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009QuadraticRepresentation
import Bong.Bong.DiagonalRepresentationParityProof
import Bong.QuadraticSpace.OrthogonalSumDiagonal

/-!
# Proof of Beli (2009), Lemma 3.5

The former representation-law boundary is discharged by diagonalizing both
spaces with the proved BONG existence theorem.  Both sides of each assertion
are codimension-one representation questions, so the concrete Hasse-sign
criterion applies.  The remaining identities use Hilbert-symbol
multiplicativity.  Crucially, the displayed determinants are required to be
actual representatives of the determinant square classes of the two spaces.
-/

namespace Bong

open Dyadic BONG.GoodBONG

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- Products of two chosen determinant representatives have the same square
class as the products of the corresponding diagonal determinants. -/
theorem determinantRepresentatives_product_square {m n : Nat}
    (q : Fin m → Kˣ) (r : Fin n → Kˣ) (detQ detR : Kˣ)
    (hq : IsSquare (detQ * diagonalUnitDeterminant q))
    (hr : IsSquare (detR * diagonalUnitDeterminant r)) :
    IsSquare ((detQ * detR) *
      (diagonalUnitDeterminant q * diagonalUnitDeterminant r)) := by
  rcases hq with ⟨uq, huq⟩
  rcases hr with ⟨ur, hur⟩
  refine ⟨uq * ur, ?_⟩
  calc
    (detQ * detR) *
          (diagonalUnitDeterminant q * diagonalUnitDeterminant r) =
        (detQ * diagonalUnitDeterminant q) *
          (detR * diagonalUnitDeterminant r) := by ac_rfl
    _ = (uq * uq) * (ur * ur) := by rw [huq, hur]
    _ = (uq * ur) * (uq * ur) := by ac_rfl

/-- The line coefficients built from chosen and diagonal determinants have
the same square class. -/
theorem determinantRepresentatives_twistedLine_square {m n : Nat}
    (q : Fin m → Kˣ) (r : Fin n → Kˣ) (detQ detR a : Kˣ)
    (hq : IsSquare (detQ * diagonalUnitDeterminant q))
    (hr : IsSquare (detR * diagonalUnitDeterminant r)) :
    IsSquare
      ((a * detQ * detR) *
        (a * diagonalUnitDeterminant q * diagonalUnitDeterminant r)) := by
  rcases hq with ⟨uq, huq⟩
  rcases hr with ⟨ur, hur⟩
  refine ⟨a * uq * ur, ?_⟩
  calc
    (a * detQ * detR) *
          (a * diagonalUnitDeterminant q * diagonalUnitDeterminant r) =
        (a * a) * (detQ * diagonalUnitDeterminant q) *
          (detR * diagonalUnitDeterminant r) := by ac_rfl
    _ = (a * a) * (uq * uq) * (ur * ur) := by rw [huq, hur]
    _ = (a * uq * ur) * (a * uq * ur) := by ac_rfl

/-- Replacing an appended line coefficient by the same square class does not
change a diagonal representation question. -/
theorem diagonalRepresents_snoc_iff_of_isSquare_mul {n m : Nat}
    (source : Fin m → Kˣ) (head : Fin n → Kˣ) (c d : Kˣ)
    (hcd : IsSquare (c * d)) :
    DiagonalRepresents (diagonalUnitCoefficients source)
        (diagonalUnitCoefficients (Fin.snoc head c)) ↔
      DiagonalRepresents (diagonalUnitCoefficients source)
        (diagonalUnitCoefficients (Fin.snoc head d)) := by
  rcases hcd with ⟨s, hs⟩
  have hs' : c * d = s * s := by simpa only [pow_two] using hs
  let uc := s * d⁻¹
  let ud := s * c⁻¹
  have hc : c = d * uc ^ 2 := by
    rw [pow_two]
    calc
      c = d⁻¹ * (c * d) := by
        simp [mul_assoc, mul_comm]
      _ = d⁻¹ * (s * s) := by rw [hs']
      _ = d * (s * d⁻¹) * (s * d⁻¹) := by
        simp [mul_assoc, mul_comm]
      _ = d * (uc * uc) := by simp only [uc, mul_assoc]
  have hd : d = c * ud ^ 2 := by
    rw [pow_two]
    calc
      d = c⁻¹ * (c * d) := by group
      _ = c⁻¹ * (s * s) := by rw [hs']
      _ = c * (s * c⁻¹) * (s * c⁻¹) := by
        simp [mul_assoc, mul_comm]
      _ = c * (ud * ud) := by simp only [ud, mul_assoc]
  have hcdRep := diagonalRepresents_snoc_mul_square head d uc
  have hdcRep := diagonalRepresents_snoc_mul_square head c ud
  rw [← hc] at hcdRep
  rw [← hd] at hdcRep
  exact ⟨fun h ↦ h.trans hcdRep, fun h ↦ h.trans hdcRep⟩

/-- The two Hasse-sign expressions in Lemma 3.5(ii), using the exact
diagonal determinants, are identical. -/
theorem beli2009Lemma35ii_sign_identity {n : Nat}
    (q r : Fin n → Kˣ) (a : Kˣ) :
    (diagonalHasseSymbol K (Fin.snoc q a) *
          diagonalHasseSymbol K r *
          hilbertSymbol K (diagonalUnitDeterminant r)
            (diagonalUnitDeterminant (Fin.snoc q a)) *
          hilbertSymbol K (diagonalUnitDeterminant (Fin.snoc q a)) (-1)) =
      (diagonalHasseSymbol K
            (Fin.snoc r (a * diagonalUnitDeterminant q *
              diagonalUnitDeterminant r)) *
          diagonalHasseSymbol K q *
          hilbertSymbol K (diagonalUnitDeterminant q)
            (diagonalUnitDeterminant
              (Fin.snoc r (a * diagonalUnitDeterminant q *
                diagonalUnitDeterminant r))) *
          hilbertSymbol K
            (diagonalUnitDeterminant
              (Fin.snoc r (a * diagonalUnitDeterminant q *
                diagonalUnitDeterminant r))) (-1)) := by
  simp only [diagonalHasseSymbol_snoc, diagonalUnitDeterminant_snoc,
    hilbertSymbol_mul_left, hilbertSymbol_mul_right,
    hilbertSymbol_self_eq_neg_one]
  rcases Int.units_eq_one_or
      (hilbertSymbol K (diagonalUnitDeterminant q) (-1)) with hq | hq <;>
    rcases Int.units_eq_one_or
      (hilbertSymbol K (diagonalUnitDeterminant q)
        (diagonalUnitDeterminant r)) with hqr | hqr <;>
    rcases Int.units_eq_one_or
      (hilbertSymbol K (diagonalUnitDeterminant r) (-1)) with hr | hr <;>
    simp [hq, hqr, hr, mul_assoc, mul_comm, mul_left_comm]

/-- Exact-diagonal form of Lemma 3.5(ii). -/
theorem beli2009Lemma35ii_diagonal {n : Nat}
    (q r : Fin n → Kˣ) (a : Kˣ) :
    DiagonalRepresents (diagonalUnitCoefficients r)
        (diagonalUnitCoefficients (Fin.snoc q a)) ↔
      DiagonalRepresents (diagonalUnitCoefficients q)
        (diagonalUnitCoefficients
          (Fin.snoc r (a * diagonalUnitDeterminant q *
            diagonalUnitDeterminant r))) := by
  rw [diagonalCodimensionOneRepresents_iff_sign_eq_one,
    diagonalCodimensionOneRepresents_iff_sign_eq_one]
  rw [beli2009Lemma35ii_sign_identity]

/-- Heterogeneous-rank form of Lemma 3.5(ii), with the numerical rank
equality kept explicit so that it can be applied to unrelated carrier types. -/
theorem beli2009Lemma35ii_diagonal_of_rank_eq {m n : Nat}
    (q : Fin m → Kˣ) (r : Fin n → Kˣ) (a : Kˣ) (h : m = n) :
    DiagonalRepresents (diagonalUnitCoefficients r)
        (diagonalUnitCoefficients (Fin.snoc q a)) ↔
      DiagonalRepresents (diagonalUnitCoefficients q)
        (diagonalUnitCoefficients
          (Fin.snoc r (a * diagonalUnitDeterminant q *
            diagonalUnitDeterminant r))) := by
  subst n
  exact beli2009Lemma35ii_diagonal q r a

/-- Under Beli's Hilbert condition, the two Hasse signs in Lemma 3.5(iii)
are identical. -/
theorem beli2009Lemma35iii_sign_identity {n : Nat}
    (q r : Fin n → Kˣ) (a b : Kˣ)
    (h : hilbertSymbol K (a * b)
      (diagonalUnitDeterminant q * diagonalUnitDeterminant r) = 1) :
    (diagonalHasseSymbol K (Fin.snoc q a) *
          diagonalHasseSymbol K r *
          hilbertSymbol K (diagonalUnitDeterminant r)
            (diagonalUnitDeterminant (Fin.snoc q a)) *
          hilbertSymbol K (diagonalUnitDeterminant (Fin.snoc q a)) (-1)) =
      (diagonalHasseSymbol K (Fin.snoc q b) *
          diagonalHasseSymbol K r *
          hilbertSymbol K (diagonalUnitDeterminant r)
            (diagonalUnitDeterminant (Fin.snoc q b)) *
          hilbertSymbol K (diagonalUnitDeterminant (Fin.snoc q b)) (-1)) := by
  rw [hilbertSymbol_mul_left, hilbertSymbol_mul_right,
    hilbertSymbol_mul_right] at h
  simp only [diagonalHasseSymbol_snoc, diagonalUnitDeterminant_snoc,
    hilbertSymbol_mul_left, hilbertSymbol_mul_right,
    hilbertSymbol_self_eq_neg_one]
  rw [hilbertSymbol_comm K (diagonalUnitDeterminant q) a,
    hilbertSymbol_comm K (diagonalUnitDeterminant q) b,
    hilbertSymbol_comm K (diagonalUnitDeterminant r) a,
    hilbertSymbol_comm K (diagonalUnitDeterminant r) b]
  rcases Int.units_eq_one_or
      (hilbertSymbol K a (diagonalUnitDeterminant q)) with haq | haq <;>
    rcases Int.units_eq_one_or
      (hilbertSymbol K b (diagonalUnitDeterminant q)) with hbq | hbq <;>
    rcases Int.units_eq_one_or
      (hilbertSymbol K a (diagonalUnitDeterminant r)) with har | har <;>
    rcases Int.units_eq_one_or
      (hilbertSymbol K b (diagonalUnitDeterminant r)) with hbr | hbr <;>
    rcases Int.units_eq_one_or (hilbertSymbol K a (-1)) with ham | ham <;>
    rcases Int.units_eq_one_or (hilbertSymbol K b (-1)) with hbm | hbm <;>
    simp [haq, hbq, har, hbr, ham, hbm,
      mul_assoc, mul_comm, mul_left_comm] at h ⊢

/-- Exact-diagonal form of Lemma 3.5(iii). -/
theorem beli2009Lemma35iii_diagonal {n : Nat}
    (q r : Fin n → Kˣ) (a b : Kˣ)
    (h : hilbertSymbol K (a * b)
      (diagonalUnitDeterminant q * diagonalUnitDeterminant r) = 1) :
    DiagonalRepresents (diagonalUnitCoefficients r)
        (diagonalUnitCoefficients (Fin.snoc q a)) ↔
      DiagonalRepresents (diagonalUnitCoefficients r)
        (diagonalUnitCoefficients (Fin.snoc q b)) := by
  rw [diagonalCodimensionOneRepresents_iff_sign_eq_one,
    diagonalCodimensionOneRepresents_iff_sign_eq_one]
  rw [beli2009Lemma35iii_sign_identity q r a b h]

/-- Heterogeneous-rank form of Lemma 3.5(iii). -/
theorem beli2009Lemma35iii_diagonal_of_rank_eq {m n : Nat}
    (q : Fin m → Kˣ) (r : Fin n → Kˣ) (a b : Kˣ) (hrank : m = n)
    (h : hilbertSymbol K (a * b)
      (diagonalUnitDeterminant q * diagonalUnitDeterminant r) = 1) :
    DiagonalRepresents (diagonalUnitCoefficients r)
        (diagonalUnitCoefficients (Fin.snoc q a)) ↔
      DiagonalRepresents (diagonalUnitCoefficients r)
        (diagonalUnitCoefficients (Fin.snoc q b)) := by
  subst n
  exact beli2009Lemma35iii_diagonal q r a b h

/-- The two codimension-one signs in Lemma 3.5(i) agree after adjoining the
diagonal hyperbolic pair `t,-t`. -/
theorem beli2009Lemma35i_sign_identity {n : Nat}
    (v : Fin (n + 1) → Kˣ) (w : Fin n → Kˣ) (t : Kˣ) :
    (diagonalHasseSymbol K v * diagonalHasseSymbol K w *
          hilbertSymbol K (diagonalUnitDeterminant w)
            (diagonalUnitDeterminant v) *
          hilbertSymbol K (diagonalUnitDeterminant v) (-1)) =
      (diagonalHasseSymbol K (Fin.snoc (Fin.snoc w t) (-t)) *
          diagonalHasseSymbol K v *
          hilbertSymbol K (diagonalUnitDeterminant v)
            (diagonalUnitDeterminant (Fin.snoc (Fin.snoc w t) (-t))) *
          hilbertSymbol K
            (diagonalUnitDeterminant (Fin.snoc (Fin.snoc w t) (-t)))
            (-1)) := by
  simp only [diagonalHasseSymbol_snoc, diagonalUnitDeterminant_snoc,
    hilbertSymbol_mul_left, hilbertSymbol_mul_right,
    hilbertSymbol_self_eq_neg_one]
  have htneg : (-t : Kˣ) = (-1) * t := by
    apply Units.ext
    simp
  rw [htneg]
  simp only [hilbertSymbol_mul_left, hilbertSymbol_mul_right]
  rw [hilbertSymbol_self_eq_neg_one (K := K) t,
    hilbertSymbol_comm K (diagonalUnitDeterminant v)
      (diagonalUnitDeterminant w)]
  rcases Int.units_eq_one_or
      (hilbertSymbol K (diagonalUnitDeterminant w) t) with hwt | hwt <;>
    rcases Int.units_eq_one_or (hilbertSymbol K t (-1)) with htm | htm <;>
    rcases Int.units_eq_one_or
      (hilbertSymbol K (diagonalUnitDeterminant w) (-1)) with hwm | hwm <;>
    rcases Int.units_eq_one_or (hilbertSymbol K (-1) (-1)) with hmm | hmm <;>
    rcases Int.units_eq_one_or
      (hilbertSymbol K (diagonalUnitDeterminant v) t) with hvt | hvt <;>
    simp [hwt, htm, hwm, hmm, hvt,
      mul_assoc, mul_comm, mul_left_comm]

/-- Exact-diagonal form of Lemma 3.5(i). -/
theorem beli2009Lemma35i_diagonal {n : Nat}
    (v : Fin (n + 1) → Kˣ) (w : Fin n → Kˣ) (t : Kˣ) :
    DiagonalRepresents (diagonalUnitCoefficients w)
        (diagonalUnitCoefficients v) ↔
      DiagonalRepresents (diagonalUnitCoefficients v)
        (diagonalUnitCoefficients (Fin.snoc (Fin.snoc w t) (-t))) := by
  rw [diagonalCodimensionOneRepresents_iff_sign_eq_one,
    diagonalCodimensionOneRepresents_iff_sign_eq_one]
  rw [beli2009Lemma35i_sign_identity]

/-- Heterogeneous-rank form of Lemma 3.5(i). -/
theorem beli2009Lemma35i_diagonal_of_rank_eq {m n : Nat}
    (v : Fin m → Kˣ) (w : Fin n → Kˣ) (t : Kˣ) (h : n + 1 = m) :
    DiagonalRepresents (diagonalUnitCoefficients w)
        (diagonalUnitCoefficients v) ↔
      DiagonalRepresents (diagonalUnitCoefficients v)
        (diagonalUnitCoefficients (Fin.snoc (Fin.snoc w t) (-t))) := by
  subst m
  exact beli2009Lemma35i_diagonal v w t

namespace QuadraticSpace

variable {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  [FiniteDimensional K V] [FiniteDimensional K W]

/-- Beli (2009), Lemma 3.5(i), proved from diagonal local classification. -/
theorem beli2009Lemma35_i_proved
    (q : QuadraticSpace K V) (r : QuadraticSpace K W)
    (hdim : Module.finrank K W + 1 = Module.finrank K V) :
    EmbedsInto r q ↔
      EmbedsInto q (orthogonalSum r (hyperbolicPlane (1 : Kˣ))) := by
  change q.Represents r ↔
    (orthogonalSum r (hyperbolicPlane (1 : Kˣ))).Represents q
  rw [r.represents_iff_diagonalRepresents q,
    orthogonalSum_hyperbolic_represents_iff_diagonalRepresents]
  exact beli2009Lemma35i_diagonal_of_rank_eq
    q.diagonalUnits r.diagonalUnits (fieldTwoUnit (K := K)) hdim

/-- Beli (2009), Lemma 3.5(ii), proved with the displayed determinant
representatives tied to the actual determinant square classes. -/
theorem beli2009Lemma35_ii_proved
    (q : QuadraticSpace K V) (r : QuadraticSpace K W)
    (detQ detR a : Kˣ)
    (detQ_spec : q.IsDeterminantRepresentative detQ)
    (detR_spec : r.IsDeterminantRepresentative detR)
    (hdim : Module.finrank K V = Module.finrank K W) :
    EmbedsInto r (orthogonalSum q (scaledLine a)) ↔
      EmbedsInto q
        (orthogonalSum r (scaledLine (a * detQ * detR))) := by
  change (orthogonalSum q (scaledLine a)).Represents r ↔
    (orthogonalSum r (scaledLine (a * detQ * detR))).Represents q
  rw [orthogonalSum_scaledLine_represents_iff_diagonalRepresents,
    orthogonalSum_scaledLine_represents_iff_diagonalRepresents]
  have hq : IsSquare
      (detQ * diagonalUnitDeterminant q.diagonalUnits) := by
    simpa [IsDeterminantRepresentative, diagonalUnitDeterminant] using detQ_spec
  have hr : IsSquare
      (detR * diagonalUnitDeterminant r.diagonalUnits) := by
    simpa [IsDeterminantRepresentative, diagonalUnitDeterminant] using detR_spec
  calc
    DiagonalRepresents (diagonalUnitCoefficients r.diagonalUnits)
          (diagonalUnitCoefficients (Fin.snoc q.diagonalUnits a)) ↔
        DiagonalRepresents (diagonalUnitCoefficients q.diagonalUnits)
          (diagonalUnitCoefficients
            (Fin.snoc r.diagonalUnits
              (a * diagonalUnitDeterminant q.diagonalUnits *
                diagonalUnitDeterminant r.diagonalUnits))) :=
      beli2009Lemma35ii_diagonal_of_rank_eq
        q.diagonalUnits r.diagonalUnits a hdim
    _ ↔ DiagonalRepresents (diagonalUnitCoefficients q.diagonalUnits)
          (diagonalUnitCoefficients
            (Fin.snoc r.diagonalUnits (a * detQ * detR))) :=
      diagonalRepresents_snoc_iff_of_isSquare_mul q.diagonalUnits
        r.diagonalUnits
        (a * diagonalUnitDeterminant q.diagonalUnits *
          diagonalUnitDeterminant r.diagonalUnits)
        (a * detQ * detR)
        (by
          simpa only [mul_comm] using
            determinantRepresentatives_twistedLine_square
              q.diagonalUnits r.diagonalUnits detQ detR a hq hr)

/-- Beli (2009), Lemma 3.5(iii), proved with the determinant hypotheses made
explicit. -/
theorem beli2009Lemma35_iii_proved
    (q : QuadraticSpace K V) (r : QuadraticSpace K W)
    (detQ detR a b : Kˣ)
    (detQ_spec : q.IsDeterminantRepresentative detQ)
    (detR_spec : r.IsDeterminantRepresentative detR)
    (hdim : Module.finrank K V = Module.finrank K W)
    (hhilbert : hilbertSymbol K (a * b) (detQ * detR) = 1) :
    EmbedsInto r (orthogonalSum q (scaledLine a)) ↔
      EmbedsInto r (orthogonalSum q (scaledLine b)) := by
  change (orthogonalSum q (scaledLine a)).Represents r ↔
    (orthogonalSum q (scaledLine b)).Represents r
  rw [orthogonalSum_scaledLine_represents_iff_diagonalRepresents,
    orthogonalSum_scaledLine_represents_iff_diagonalRepresents]
  have hq : IsSquare
      (detQ * diagonalUnitDeterminant q.diagonalUnits) := by
    simpa [IsDeterminantRepresentative, diagonalUnitDeterminant] using detQ_spec
  have hr : IsSquare
      (detR * diagonalUnitDeterminant r.diagonalUnits) := by
    simpa [IsDeterminantRepresentative, diagonalUnitDeterminant] using detR_spec
  have hproduct := determinantRepresentatives_product_square
    q.diagonalUnits r.diagonalUnits detQ detR hq hr
  have heq := hilbertSymbol_eq_of_isSquare_mul_right
    (K := K) (z := a * b) hproduct
  have hactual : hilbertSymbol K (a * b)
      (diagonalUnitDeterminant q.diagonalUnits *
        diagonalUnitDeterminant r.diagonalUnits) = 1 := by
    rw [← heq]
    exact hhilbert
  exact beli2009Lemma35iii_diagonal_of_rank_eq
    q.diagonalUnits r.diagonalUnits a b hdim hactual

end QuadraticSpace

/-- The unconditional proved instance of Beli (2009), Lemma 3.5. -/
noncomputable instance beli2009QuadraticRepresentationLawsProved :
    Beli2009QuadraticRepresentationLaws.{u, v, w} K where
  lemma35_i := QuadraticSpace.beli2009Lemma35_i_proved
  lemma35_ii := QuadraticSpace.beli2009Lemma35_ii_proved
  lemma35_iii := QuadraticSpace.beli2009Lemma35_iii_proved

end Bong
