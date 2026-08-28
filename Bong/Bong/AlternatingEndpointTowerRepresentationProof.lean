/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.AlternatingEndpointTowerRepresentation
import Bong.Bong.AlternatingEndpointProduct
import Bong.Bong.DiagonalBinaryRepresentation
import Bong.Bong.DiagonalHyperbolicBlocks
import Bong.Bong.DiagonalLocalClassificationProof
import Bong.Bong.DiagonalRepresentationParityProof
import Bong.Bong.DiagonalTailCancellation
import Bong.Bong.DiagonalTernaryRepresentationObstructionProof
import Bong.Bong.Beli2019RepresentationTransitivity
import Bong.Dyadic.UnramifiedNormDirectProof

/-!
# Concrete representation laws for alternating endpoint towers

This file proves the Witt-reduction interface used in Beli (2019), Lemmas
7.16 and 7.9.  At one fixed scale, every binary endpoint is either a
hyperbolic plane or a scalar multiple of the unramified norm plane.  The
Hasse invariant of the complete tower therefore depends only on its signed
determinant square class and the common scale.

The common-scale hypothesis is essential.  Matching only corresponding
orders permits two unramified norm planes at scales of opposite parity and
does not determine the Witt class.
-/

namespace Bong

open Dyadic BONG.GoodBONG

universe u

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [discriminant : DyadicDiscriminantClassLaws K]

namespace AlternatingEndpointTower

/-- The standard equivalence which interchanges two consecutive finite
coordinate blocks. -/
private def finAddCommEquiv (m n : Nat) : Fin (m + n) ≃ Fin (n + m) :=
  finSumFinEquiv.symm |>.trans (Equiv.sumComm (Fin m) (Fin n)) |>.trans
    finSumFinEquiv

/-- Orthogonal sums of diagonal forms commute. -/
theorem diagonalRepresents_append_comm {m n : Nat}
    (a : Fin m → K) (b : Fin n → K) :
    DiagonalRepresents (Fin.append a b) (Fin.append b a) := by
  let e := finAddCommEquiv m n
  let E := LinearEquiv.piCongrLeft K (fun _ : Fin (n + m) => K) e
  refine ⟨E.toLinearMap, E.injective, ?_⟩
  intro x
  have hE (i : Fin (m + n)) : E x (e i) = x i := by
    change (Equiv.piCongrLeft (fun _ : Fin (n + m) => K) e) x (e i) = x i
    exact Equiv.piCongrLeft_apply_apply (fun _ : Fin (n + m) => K) e x i
  have hcoeff (i : Fin (m + n)) :
      Fin.append b a (e i) = Fin.append a b i := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [e, finAddCommEquiv]
    · simp [e, finAddCommEquiv]
  unfold diagonalQuadratic
  calc
    (∑ i, Fin.append b a i * (E x i) ^ 2) =
        ∑ i, Fin.append b a (e i) * (E x (e i)) ^ 2 := by
      exact (Equiv.sum_comp e
        (fun j => Fin.append b a j * (E x j) ^ 2)).symm
    _ = ∑ i, Fin.append a b i * x i ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hcoeff, hE]

/-- A codimension-two diagonal representation has a nondegenerate binary
orthogonal complement. -/
theorem exists_diagonalBinaryComplement
    {m : Nat} (source : Fin m → Kˣ) (target : Fin (m + 2) → Kˣ)
    (hrep : DiagonalRepresents (diagonalUnitCoefficients source)
      (diagonalUnitCoefficients target)) :
    ∃ complement : Fin 2 → Kˣ,
      DiagonalRepresents
        (diagonalUnitCoefficients (Fin.append source complement))
        (diagonalUnitCoefficients target) := by
  induction m with
  | zero =>
      refine ⟨target, ?_⟩
      have happend : Fin.append source target = target := by
        funext i
        refine Fin.addCases (fun j => Fin.elim0 j) (fun j => ?_) i
        rw [Fin.append_right]
        congr 1
        exact Fin.ext (by simp)
      rw [happend]
      exact diagonalRepresents_refl _
  | succ m ih =>
      let A : Kˣ := source 0
      let sourceTail : Fin m → Kˣ := Fin.tail source
      have hsource : source = Fin.cons A sourceTail :=
        (Fin.cons_self_tail source).symm
      rcases hrep with ⟨f, hf, hquadratic⟩
      let e₀ : Fin (m + 1) → K := Pi.basisFun K (Fin (m + 1)) 0
      let y : Fin ((m + 1) + 2) → K := f e₀
      have hy : diagonalQuadratic (diagonalUnitCoefficients target) y =
          (A : K) := by
        calc
          diagonalQuadratic (diagonalUnitCoefficients target) y =
              diagonalQuadratic (diagonalUnitCoefficients source) e₀ :=
            hquadratic e₀
          _ = diagonalUnitCoefficients source 0 :=
            DiagonalRepresents.diagonalQuadratic_basisFun
              (diagonalUnitCoefficients source) 0
          _ = (A : K) := rfl
      rcases exists_diagonal_split_first (K := K) (m + 2) target A y hy with
        ⟨targetTail, hsplit, _⟩
      have hfull : DiagonalRepresents
          (diagonalUnitCoefficients source)
          (diagonalUnitCoefficients (Fin.cons A targetTail)) :=
        DiagonalRepresents.trans
          (⟨f, hf, hquadratic⟩ : DiagonalRepresents
            (diagonalUnitCoefficients source)
            (diagonalUnitCoefficients target))
          hsplit.symm_of_sameRank
      have hcons : DiagonalRepresents
          (diagonalUnitCoefficients (Fin.cons A sourceTail))
          (diagonalUnitCoefficients (Fin.cons A targetTail)) := by
        rw [← hsource]
        exact hfull
      have htail : DiagonalRepresents
          (diagonalUnitCoefficients sourceTail)
          (diagonalUnitCoefficients targetTail) := by
        apply DiagonalRepresents.cancel_common_head (A : K)
          (diagonalUnitCoefficients sourceTail)
          (diagonalUnitCoefficients targetTail)
        · exact Units.ne_zero A
        · intro i
          exact Units.ne_zero (sourceTail i)
        · intro i
          exact Units.ne_zero (targetTail i)
        · simpa only [diagonalUnitCoefficients_cons] using hcons
      rcases ih sourceTail targetTail htail with ⟨complement, hcomplement⟩
      have hprepend : DiagonalRepresents
          (diagonalUnitCoefficients
            (Fin.cons A (Fin.append sourceTail complement)))
          (diagonalUnitCoefficients (Fin.cons A targetTail)) := by
        simpa only [diagonalUnitCoefficients_cons] using
          diagonalRepresents_cons hcomplement (A : K)
      have happend : Fin.append source complement =
          Fin.cons A (Fin.append sourceTail complement) := by
        rw [hsource]
        simpa using Fin.append_cons A sourceTail complement
      refine ⟨complement, ?_⟩
      rw [happend]
      exact DiagonalRepresents.trans hprepend hsplit

/-- Signed determinant of an even diagonal tower, grouped into binary
endpoint blocks. -/
noncomputable def signedDeterminant {pairs : Nat}
    (a : Fin (2 * pairs) → Kˣ) : Kˣ :=
  (-1) ^ pairs * diagonalUnitDeterminant a

/-- Determinants multiply under concatenation. -/
theorem diagonalUnitDeterminant_append {m n : Nat}
    (a : Fin m → Kˣ) (b : Fin n → Kˣ) :
    diagonalUnitDeterminant (Fin.append a b) =
      diagonalUnitDeterminant a * diagonalUnitDeterminant b := by
  unfold diagonalUnitDeterminant
  rw [Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right]

/-- Unit-valued diagonal coefficients commute with concatenation. -/
theorem diagonalUnitCoefficients_append {m n : Nat}
    (a : Fin m → Kˣ) (b : Fin n → Kˣ) :
    diagonalUnitCoefficients (Fin.append a b) =
      Fin.append (diagonalUnitCoefficients a) (diagonalUnitCoefficients b) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [diagonalUnitCoefficients]
  · simp [diagonalUnitCoefficients]

/-- Beli's Hasse symbol under an orthogonal concatenation. -/
theorem diagonalHasseSymbol_append
    [HilbertSymbolLaws K] {m n : Nat}
    (a : Fin m → Kˣ) (b : Fin n → Kˣ) :
    diagonalHasseSymbol K (Fin.append a b) =
      diagonalHasseSymbol K a *
        hilbertSymbol K (diagonalUnitDeterminant a)
          (diagonalUnitDeterminant b) *
        diagonalHasseSymbol K b := by
  induction n with
  | zero =>
      have hab : Fin.append a b = a := by
        funext i
        exact Fin.addCases (fun j => by
          convert Fin.append_left a b j
          apply Fin.ext
          rfl) (fun j => Fin.elim0 j) i
      rw [hab]
      simp [diagonalUnitDeterminant]
  | succ n ih =>
      let b' : Fin n → Kˣ := Fin.init b
      let d : Kˣ := b (Fin.last n)
      have hb : b = Fin.snoc b' d := by
        exact (Fin.snoc_init_self b).symm
      rw [hb, Fin.append_snoc, diagonalHasseSymbol_snoc,
        diagonalHasseSymbol_snoc, ih]
      rw [diagonalUnitDeterminant_append,
        diagonalUnitDeterminant_snoc,
        hilbertSymbol_mul_left, hilbertSymbol_mul_right]
      ac_rfl

/-- The unramified discriminant pairs trivially with every element of even
valuation. -/
theorem hilbertSymbol_discriminant_eq_one_of_even_order
    [DyadicUnramifiedNormLaws K] (x : Kˣ)
    (hx : Even (ordUnit K x)) :
    hilbertSymbol K discriminant.discriminantUnit x = 1 :=
  (hilbertSymbol_discriminant_eq_one_iff_even_order x).2 hx

/-- A square-or-discriminant endpoint class pairs trivially with every
even-order element. -/
theorem hilbertSymbol_endpointClass_eq_one_of_even_order
    [HilbertSymbolLaws K] [DyadicUnramifiedNormLaws K]
    {d x : Kˣ}
    (hd : IsSquare d ∨ IsSquare (d * discriminant.discriminantUnit))
    (hx : Even (ordUnit K x)) :
    hilbertSymbol K d x = 1 := by
  rcases hd with hd | hd
  · exact hilbertSymbol_eq_one_of_isSquare_left K hd
  · rw [hilbertSymbol_eq_discriminant_of_isSquare_mul_discriminant hd]
    exact hilbertSymbol_discriminant_eq_one_of_even_order x hx

/-- The Beli Hasse symbol of one endpoint pair.  Its variable part is the
Hilbert pairing between the signed determinant and the common scale. -/
theorem diagonalHasseSymbol_endpointPair
    [HilbertSymbolLaws K] [DyadicUnramifiedNormLaws K]
    (x y scale : Kˣ)
    (hclass : IsSquare (-(x * y)) ∨
      IsSquare (-(x * y) * discriminant.discriminantUnit))
    (horder : ordUnit K x = ordUnit K scale) :
    diagonalHasseSymbol K ![x, y] =
      hilbertSymbol K (-1) (-1) *
        hilbertSymbol K (-(x * y)) scale := by
  let d : Kˣ := -(x * y)
  have hdClass : IsSquare d ∨
      IsSquare (d * discriminant.discriminantUnit) := by
    simpa only [d] using hclass
  have hminusOneEven : Even (ordUnit K (-1 : Kˣ)) := by
    have hone : ordUnit K (1 : Kˣ) = 0 := by
      have h := ordUnit_mul K (1 : Kˣ) 1
      simp only [mul_one] at h
      omega
    have hnegOne : ordUnit K (-1 : Kˣ) = 0 := by
      have h := ordUnit_mul K (-1 : Kˣ) (-1)
      have hmul : (-1 : Kˣ) * (-1) = 1 := by norm_num
      rw [hmul, hone] at h
      omega
    rw [hnegOne]
    exact ⟨0, by omega⟩
  have hdMinusOne : hilbertSymbol K d (-1) = 1 :=
    hilbertSymbol_endpointClass_eq_one_of_even_order hdClass hminusOneEven
  have hquotientOrder : ordUnit K (x * scale⁻¹) = 0 := by
    rw [ordUnit_mul, ordUnit_inv, horder]
    omega
  have hquotientEven : Even (ordUnit K (x * scale⁻¹)) := by
    rw [hquotientOrder]
    exact ⟨0, by omega⟩
  have hdQuotient : hilbertSymbol K d (x * scale⁻¹) = 1 :=
    hilbertSymbol_endpointClass_eq_one_of_even_order hdClass hquotientEven
  have hdx : hilbertSymbol K d x = hilbertSymbol K d scale := by
    have hmul := hilbertSymbol_mul_right (K := K) d x scale⁻¹
    rw [hdQuotient] at hmul
    have hscaleInv : hilbertSymbol K d scale⁻¹ =
        hilbertSymbol K d scale := by
      rw [show scale⁻¹ = scale * (scale⁻¹) ^ 2 by group,
        hilbertSymbol_mul_square_right]
    rw [hscaleInv] at hmul
    rcases Int.units_eq_one_or (hilbertSymbol K d x) with hx | hx <;>
      rcases Int.units_eq_one_or (hilbertSymbol K d scale) with hs | hs <;>
        simp [hx, hs] at hmul ⊢
  rw [diagonalHasseSymbol_fin_two_eq_det_cross]
  have hdet : diagonalUnitDeterminant ![x, y] = -d := by
    simp only [diagonalUnitDeterminant, Fin.prod_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, d]
    group
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hdet, show -d = (-1 : Kˣ) * d by simp,
    hilbertSymbol_mul_left, hdMinusOne, mul_one]
  have hxy : hilbertSymbol K x y = hilbertSymbol K x d := by
    have hy : y = d * x⁻¹ * (-1) := by
      dsimp only [d]
      apply Units.ext
      simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_neg]
      field_simp [Units.ne_zero x] <;> norm_num
    rw [hy, hilbertSymbol_mul_right, hilbertSymbol_mul_right]
    have hinv : hilbertSymbol K x x⁻¹ = hilbertSymbol K x x := by
      rw [show x⁻¹ = x * (x⁻¹) ^ 2 by group,
        hilbertSymbol_mul_square_right]
    rw [hinv, hilbertSymbol_self_eq_neg_one]
    have hself := Int.units_mul_self (hilbertSymbol K x (-1))
    calc
      hilbertSymbol K x d * hilbertSymbol K x (-1) *
          hilbertSymbol K x (-1) =
        hilbertSymbol K x d *
          (hilbertSymbol K x (-1) * hilbertSymbol K x (-1)) := by
            rw [mul_assoc]
      _ = hilbertSymbol K x d := by rw [hself, mul_one]
  rw [hxy, hilbertSymbol_comm K x d, hdx]

/-- The initial binary blocks of a nonempty endpoint tower. -/
def init {pairs : Nat} (a : Fin (2 * (pairs + 1)) → Kˣ) :
    Fin (2 * pairs) → Kˣ :=
  fun i => a ⟨i.val, by omega⟩

/-- The final binary block of a nonempty endpoint tower. -/
def lastPair {pairs : Nat} (a : Fin (2 * (pairs + 1)) → Kˣ) :
    Fin 2 → Kˣ :=
  fun i => a ⟨2 * pairs + i.val, by omega⟩

/-- Splitting an endpoint tower before its final binary block recovers the
original coefficient family. -/
theorem append_init_lastPair {pairs : Nat}
    (a : Fin (2 * (pairs + 1)) → Kˣ) :
    Fin.append (init a) (lastPair a) = a := by
  funext i
  refine Fin.addCases (m := 2 * pairs) (n := 2)
    (fun j => ?_) (fun j => ?_) i
  · simp only [Fin.append_left, init]
    congr 2
  · simp only [Fin.append_right, lastPair]
    congr 2

/-- The signed determinant recurrence obtained by adding the final endpoint
pair. -/
theorem signedDeterminant_succ {pairs : Nat}
    (a : Fin (2 * (pairs + 1)) → Kˣ) :
    signedDeterminant a = signedDeterminant (init a) *
      (-(lastPair a 0 * lastPair a 1)) := by
  have hdet : diagonalUnitDeterminant a =
      diagonalUnitDeterminant (init a) *
        diagonalUnitDeterminant (lastPair a) := by
    calc
      diagonalUnitDeterminant a =
          diagonalUnitDeterminant (Fin.append (init a) (lastPair a)) :=
        congrArg diagonalUnitDeterminant (append_init_lastPair a).symm
      _ = diagonalUnitDeterminant (init a) *
          diagonalUnitDeterminant (lastPair a) :=
        diagonalUnitDeterminant_append _ _
  unfold signedDeterminant
  rw [hdet, pow_succ]
  simp only [diagonalUnitDeterminant, Fin.prod_univ_two]
  apply Units.ext
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg]
  norm_num
  ring

/-- Endpoint classes are inherited by the initial subtower. -/
theorem pairClasses_init {pairs : Nat}
    (a : Fin (2 * (pairs + 1)) → Kˣ)
    (ha : AlternatingEndpointPairClasses a) :
    AlternatingEndpointPairClasses (init a) := by
  intro t
  simpa only [init] using ha ⟨t.val, by omega⟩

/-- The final block of an endpoint tower satisfies the endpoint dichotomy. -/
theorem pairClasses_lastPair {pairs : Nat}
    (a : Fin (2 * (pairs + 1)) → Kˣ)
    (ha : AlternatingEndpointPairClasses a) :
    IsSquare (-(lastPair a 0 * lastPair a 1)) ∨
      IsSquare (-(lastPair a 0 * lastPair a 1) *
        discriminant.discriminantUnit) := by
  simpa [lastPair] using ha ⟨pairs, by omega⟩

/-- The signed determinant of an endpoint tower is either square or in the
distinguished unramified discriminant class. -/
theorem signedDeterminant_cases
    {pairs : Nat} (a : Fin (2 * pairs) → Kˣ)
    (ha : AlternatingEndpointPairClasses a) :
    IsSquare (signedDeterminant a) ∨
      IsSquare (signedDeterminant a *
        discriminant.discriminantUnit) := by
  induction pairs with
  | zero =>
      left
      refine ⟨1, ?_⟩
      simp [signedDeterminant, diagonalUnitDeterminant]
  | succ pairs ih =>
      let aInit := init a
      let aLast := lastPair a
      have hinit : AlternatingEndpointPairClasses aInit := by
        simpa only [aInit] using pairClasses_init a ha
      have hlast : IsSquare (-(aLast 0 * aLast 1)) ∨
          IsSquare (-(aLast 0 * aLast 1) *
            discriminant.discriminantUnit) := by
        simpa only [aLast] using pairClasses_lastPair a ha
      have hproduct := BONG.endpointSquareCases_product
        (laws := discriminant) (1 : Kˣ)
        (signedDeterminant aInit) (-(aLast 0 * aLast 1))
        (by simpa using ih aInit hinit) (by simpa using hlast)
      rw [signedDeterminant_succ a]
      simpa only [one_mul] using hproduct

/-- The valuation of `-1` is zero. -/
theorem ordUnit_neg_one_eq_zero : ordUnit K (-1 : Kˣ) = 0 := by
  have hone : ordUnit K (1 : Kˣ) = 0 := by
    have h := ordUnit_mul K (1 : Kˣ) 1
    simp only [mul_one] at h
    omega
  have h := ordUnit_mul K (-1 : Kˣ) (-1)
  have hmul : (-1 : Kˣ) * (-1) = 1 := by norm_num
  rw [hmul, hone] at h
  omega

/-- Two square-or-discriminant classes have trivial Hilbert pairing. -/
theorem hilbertSymbol_endpointClasses_eq_one
    [HilbertSymbolLaws K] [DyadicUnramifiedNormLaws K]
    {d e : Kˣ}
    (hd : IsSquare d ∨ IsSquare (d * discriminant.discriminantUnit))
    (he : IsSquare e ∨ IsSquare (e * discriminant.discriminantUnit)) :
    hilbertSymbol K d e = 1 := by
  rcases hd with hd | hd
  · exact hilbertSymbol_eq_one_of_isSquare_left K hd
  · rw [hilbertSymbol_eq_discriminant_of_isSquare_mul_discriminant hd]
    rcases he with he | he
    · exact hilbertSymbol_eq_one_of_isSquare_right K he
    · rw [hilbertSymbol_eq_of_isSquare_mul_right he,
        hilbertSymbol_self_eq_neg_one]
      apply hilbertSymbol_discriminant_eq_one_of_even_order
      rw [ordUnit_neg_one_eq_zero]
      exact ⟨0, by omega⟩

/-- The determinant of a subtower in terms of its signed determinant. -/
theorem determinant_eq_sign_mul_signedDeterminant {pairs : Nat}
    (a : Fin (2 * pairs) → Kˣ) :
    diagonalUnitDeterminant a = (-1) ^ pairs * signedDeterminant a := by
  unfold signedDeterminant
  symm
  calc
    (-1 : Kˣ) ^ pairs *
          ((-1 : Kˣ) ^ pairs * diagonalUnitDeterminant a) =
        (((-1 : Kˣ) ^ pairs) ^ 2) *
          diagonalUnitDeterminant a := by
      rw [pow_two, mul_assoc]
    _ = (((-1 : Kˣ) ^ 2) ^ pairs) *
          diagonalUnitDeterminant a := by
      rw [← pow_mul, Nat.mul_comm pairs 2, pow_mul]
    _ = diagonalUnitDeterminant a := by norm_num

/-- The fixed field-dependent factor in the Hasse symbol of an endpoint
tower.  Its precise closed exponent is immaterial; the recursion makes
comparisons between towers transparent. -/
noncomputable def hasseConstant (K : Type u) [Field K] : Nat → ℤˣ
  | 0 => 1
  | pairs + 1 =>
      hasseConstant K pairs *
        hilbertSymbol K ((-1 : Kˣ) ^ pairs) (-1) *
        hilbertSymbol K (-1) (-1)

/-- Initial blocks retain the common-scale order condition. -/
theorem leadingOrdersAt_init {pairs : Nat}
    (a : Fin (2 * (pairs + 1)) → Kˣ) (scale : Kˣ)
    (ha : AlternatingEndpointLeadingOrdersAt a scale) :
    AlternatingEndpointLeadingOrdersAt (init a) scale := by
  intro t
  simpa only [init] using ha ⟨t.val, by omega⟩

/-- The leading coefficient of the last pair has the common scale. -/
theorem leadingOrder_lastPair {pairs : Nat}
    (a : Fin (2 * (pairs + 1)) → Kˣ) (scale : Kˣ)
    (ha : AlternatingEndpointLeadingOrdersAt a scale) :
    ordUnit K (lastPair a 0) = ordUnit K scale := by
  simpa [lastPair] using ha ⟨pairs, by omega⟩

/-- Closed Hasse formula for a fixed-scale alternating endpoint tower. -/
theorem diagonalHasseSymbol_eq_constant_mul_signedDeterminant
    [HilbertSymbolLaws K] [DyadicUnramifiedNormLaws K]
    {pairs : Nat} (a : Fin (2 * pairs) → Kˣ) (scale : Kˣ)
    (ha : AlternatingEndpointPairClasses a)
    (horders : AlternatingEndpointLeadingOrdersAt a scale) :
    diagonalHasseSymbol K a =
      hasseConstant K pairs *
        hilbertSymbol K (signedDeterminant a) scale := by
  induction pairs with
  | zero =>
      simp [hasseConstant, signedDeterminant, diagonalUnitDeterminant]
  | succ pairs ih =>
      let aInit := init a
      let aLast := lastPair a
      let d : Kˣ := -(aLast 0 * aLast 1)
      have hinitClasses : AlternatingEndpointPairClasses aInit := by
        simpa only [aInit] using pairClasses_init a ha
      have hlastClass : IsSquare d ∨
          IsSquare (d * discriminant.discriminantUnit) := by
        simpa only [d, aLast] using pairClasses_lastPair a ha
      have hinitOrders : AlternatingEndpointLeadingOrdersAt aInit scale := by
        simpa only [aInit] using leadingOrdersAt_init a scale horders
      have hlastOrder : ordUnit K (aLast 0) = ordUnit K scale := by
        simpa only [aLast] using leadingOrder_lastPair a scale horders
      have hinitFormula := ih aInit hinitClasses hinitOrders
      have hlastFormula : diagonalHasseSymbol K aLast =
          hilbertSymbol K (-1) (-1) * hilbertSymbol K d scale := by
        have hpair := diagonalHasseSymbol_endpointPair
          (aLast 0) (aLast 1) scale hlastClass hlastOrder
        have haLast : aLast = ![aLast 0, aLast 1] := by
          funext i
          fin_cases i <;> rfl
        rw [haLast]
        simpa only [d] using hpair
      have hinitEndpoint := signedDeterminant_cases aInit hinitClasses
      have hcrossEndpoint :
          hilbertSymbol K (signedDeterminant aInit) d = 1 :=
        hilbertSymbol_endpointClasses_eq_one hinitEndpoint hlastClass
      have hminusOneEven : Even (ordUnit K (-1 : Kˣ)) := by
        rw [ordUnit_neg_one_eq_zero]
        exact ⟨0, by omega⟩
      have hinitMinusOne :
          hilbertSymbol K (signedDeterminant aInit) (-1) = 1 :=
        hilbertSymbol_endpointClass_eq_one_of_even_order
          hinitEndpoint hminusOneEven
      have hsignOrder : ordUnit K ((-1 : Kˣ) ^ pairs) = 0 := by
        rw [ordUnit_pow, ordUnit_neg_one_eq_zero]
        omega
      have hsignEven : Even (ordUnit K ((-1 : Kˣ) ^ pairs)) := by
        rw [hsignOrder]
        exact ⟨0, by omega⟩
      have hsignD : hilbertSymbol K ((-1 : Kˣ) ^ pairs) d = 1 := by
        rw [hilbertSymbol_comm K ((-1 : Kˣ) ^ pairs) d]
        exact hilbertSymbol_endpointClass_eq_one_of_even_order
          hlastClass hsignEven
      have hcross :
          hilbertSymbol K (diagonalUnitDeterminant aInit)
              (diagonalUnitDeterminant aLast) =
            hilbertSymbol K ((-1 : Kˣ) ^ pairs) (-1) := by
        rw [determinant_eq_sign_mul_signedDeterminant aInit]
        have hlastDet : diagonalUnitDeterminant aLast = -d := by
          simp only [diagonalUnitDeterminant, Fin.prod_univ_two, d]
          group
        rw [hlastDet, show -d = (-1 : Kˣ) * d by simp,
          hilbertSymbol_mul_left, hilbertSymbol_mul_right,
          hilbertSymbol_mul_right, hsignD, hinitMinusOne,
          hcrossEndpoint]
        simp
      have hsplit : diagonalHasseSymbol K a =
          diagonalHasseSymbol K aInit *
            hilbertSymbol K (diagonalUnitDeterminant aInit)
              (diagonalUnitDeterminant aLast) *
            diagonalHasseSymbol K aLast := by
        calc
          diagonalHasseSymbol K a =
              diagonalHasseSymbol K (Fin.append aInit aLast) :=
            congrArg (diagonalHasseSymbol K)
              (by simpa only [aInit, aLast] using
                (append_init_lastPair a).symm)
          _ = _ := diagonalHasseSymbol_append aInit aLast
      rw [hsplit, hinitFormula, hcross, hlastFormula,
        signedDeterminant_succ a]
      simp only [hasseConstant, d, aLast, hilbertSymbol_mul_left]
      ac_rfl

/-- Equal-dimensional fixed-scale endpoint towers in the same determinant
square class are isometric. -/
theorem equalDeterminantRepresentation_proved
    {pairs : Nat} (a b : Fin (2 * pairs) → Kˣ) (scale : Kˣ)
    (ha : AlternatingEndpointPairClasses a)
    (hb : AlternatingEndpointPairClasses b)
    (haOrders : AlternatingEndpointLeadingOrdersAt a scale)
    (hbOrders : AlternatingEndpointLeadingOrdersAt b scale)
    (hdet : IsSquare
      (diagonalUnitDeterminant a * diagonalUnitDeterminant b)) :
    DiagonalRepresents
      (diagonalUnitCoefficients b)
      (diagonalUnitCoefficients a) := by
  have hsignSquare : IsSquare (((-1 : Kˣ) ^ pairs) ^ 2) :=
    ⟨(-1 : Kˣ) ^ pairs, by simp [pow_two]⟩
  have hsigned : IsSquare (signedDeterminant a * signedDeterminant b) := by
    have hraw := hsignSquare.mul hdet
    have heq : (((-1 : Kˣ) ^ pairs) ^ 2) *
          (diagonalUnitDeterminant a * diagonalUnitDeterminant b) =
        signedDeterminant a * signedDeterminant b := by
      unfold signedDeterminant
      rw [pow_two]
      ac_rfl
    rw [heq] at hraw
    exact hraw
  have hhilbert : hilbertSymbol K (signedDeterminant b) scale =
      hilbertSymbol K (signedDeterminant a) scale := by
    symm
    exact hilbertSymbol_eq_of_isSquare_mul_left hsigned
  have haHasse :=
    diagonalHasseSymbol_eq_constant_mul_signedDeterminant a scale ha haOrders
  have hbHasse :=
    diagonalHasseSymbol_eq_constant_mul_signedDeterminant b scale hb hbOrders
  have hhasse : diagonalHasseSymbol K b = diagonalHasseSymbol K a := by
    rw [hbHasse, haHasse, hhilbert]
  apply DyadicDiagonalClassificationLaws.represents_of_invariants b a
  · simpa only [mul_comm] using hdet
  · exact hhasse

/-- Multiplication by the discriminant switches the two endpoint classes. -/
theorem endpointClass_mul_discriminant {d : Kˣ}
    (hd : IsSquare d ∨
      IsSquare (d * discriminant.discriminantUnit)) :
    IsSquare (d * discriminant.discriminantUnit) ∨
      IsSquare ((d * discriminant.discriminantUnit) *
        discriminant.discriminantUnit) := by
  rcases hd with hd | hd
  · right
    have hdeltaSquare : IsSquare
        (discriminant.discriminantUnit ^ 2) :=
      ⟨discriminant.discriminantUnit, by simp [pow_two]⟩
    have hproduct := hd.mul hdeltaSquare
    simpa only [pow_two, mul_assoc] using hproduct
  · exact Or.inl hd

/-- The prefix obtained by deleting the last line of one fixed-scale tower
embeds into every other tower of the same length and scale. -/
theorem commonCodimensionOne_proved
    {pairs : Nat} (a b : Fin (2 * pairs) → Kˣ) (scale : Kˣ)
    (ha : AlternatingEndpointPairClasses a)
    (hb : AlternatingEndpointPairClasses b)
    (haOrders : AlternatingEndpointLeadingOrdersAt a scale)
    (hbOrders : AlternatingEndpointLeadingOrdersAt b scale) :
    DiagonalRepresents
      (diagonalUnitCoefficients
        (diagonalUnitTake b (2 * pairs - 1) (by omega)))
      (diagonalUnitCoefficients a) := by
  cases pairs with
  | zero =>
      exact DiagonalRepresents.of_source_length_eq_zero
        (diagonalUnitCoefficients
          (diagonalUnitTake b (2 * 0 - 1) (by omega)))
        (diagonalUnitCoefficients a) rfl
  | succ pairs =>
      have haSigned := signedDeterminant_cases a ha
      have hbSigned := signedDeterminant_cases b hb
      have hdetCases :
          IsSquare (diagonalUnitDeterminant a *
              diagonalUnitDeterminant b) ∨
            IsSquare (diagonalUnitDeterminant a *
              diagonalUnitDeterminant b *
                discriminant.discriminantUnit) := by
        have h := BONG.endpointSquareCases_product
          (laws := discriminant) ((-1 : Kˣ) ^ Nat.succ pairs)
          (diagonalUnitDeterminant a) (diagonalUnitDeterminant b)
          (by simpa only [signedDeterminant] using haSigned)
          (by simpa only [signedDeterminant] using hbSigned)
        exact h
      rcases hdetCases with hdet | hdet
      · have hfull := equalDeterminantRepresentation_proved
          a b scale ha hb haOrders hbOrders hdet
        have hprefix : DiagonalRepresents
            (diagonalUnitCoefficients
              (diagonalUnitTake b (2 * Nat.succ pairs - 1) (by omega)))
            (diagonalUnitCoefficients b) := by
          convert DiagonalRepresents.prefixOfLE
            (k := 2 * Nat.succ pairs - 1)
            (diagonalUnitCoefficients b) (by omega) using 1
          funext i
          simp only [diagonalUnitTake, diagonalUnitCoefficients]
          congr 2
        exact hprefix.trans hfull
      · let lastIndex : Fin (2 * Nat.succ pairs) :=
          ⟨2 * Nat.succ pairs - 1, by omega⟩
        let switched : Fin (2 * Nat.succ pairs) → Kˣ :=
          Function.update b lastIndex
            (b lastIndex * discriminant.discriminantUnit)
        have hswitched_of_lt (i : Fin (2 * Nat.succ pairs))
            (hi : i.val < 2 * Nat.succ pairs - 1) :
            switched i = b i := by
          rw [show switched = Function.update b lastIndex
              (b lastIndex * discriminant.discriminantUnit) by rfl]
          rw [Function.update_of_ne]
          intro hilast
          have hval := congrArg Fin.val hilast
          dsimp only [lastIndex] at hval
          omega
        have hswitched_nat (i : Nat)
            (hi : i < 2 * Nat.succ pairs - 1)
            (hiBound : i < 2 * Nat.succ pairs) :
            switched ⟨i, hiBound⟩ = b ⟨i, hiBound⟩ := by
          apply hswitched_of_lt
          exact hi
        have hswitched_last :
            switched lastIndex =
              b lastIndex * discriminant.discriminantUnit := by
          simp only [switched, Function.update_self]
        have hswitchedClasses : AlternatingEndpointPairClasses switched := by
          intro t
          by_cases ht : t.val < pairs
          · have hlead : switched ⟨2 * t.val, by omega⟩ =
                b ⟨2 * t.val, by omega⟩ :=
              hswitched_nat (2 * t.val) (by omega) (by omega)
            have htrail : switched ⟨2 * t.val + 1, by omega⟩ =
                b ⟨2 * t.val + 1, by omega⟩ :=
              hswitched_nat (2 * t.val + 1) (by omega) (by omega)
            rw [hlead, htrail]
            exact hb t
          · have htval : t.val = pairs := by omega
            have htrailIndex :
                (⟨2 * t.val + 1, by omega⟩ :
                    Fin (2 * Nat.succ pairs)) = lastIndex := by
              apply Fin.ext
              dsimp only [lastIndex]
              omega
            have hlead : switched ⟨2 * t.val, by omega⟩ =
                b ⟨2 * t.val, by omega⟩ :=
              hswitched_nat (2 * t.val) (by omega) (by omega)
            have hlastValue : b lastIndex =
                b ⟨2 * t.val + 1, by omega⟩ := by
              congr 1
              exact htrailIndex.symm
            rw [hlead, htrailIndex, hswitched_last, hlastValue]
            let d : Kˣ :=
              -(b ⟨2 * t.val, by omega⟩ *
                b ⟨2 * t.val + 1, by omega⟩)
            have hd := hb t
            have htoggle := endpointClass_mul_discriminant
              (d := d) (by simpa only [d] using hd)
            have heq :
                -(b ⟨2 * t.val, by omega⟩ *
                    (b ⟨2 * t.val + 1, by omega⟩ *
                      discriminant.discriminantUnit)) =
                  d * discriminant.discriminantUnit := by
              dsimp only [d]
              apply Units.ext
              simp only [Units.val_neg, Units.val_mul]
              ring
            rw [heq]
            exact htoggle
        have hswitchedOrders :
            AlternatingEndpointLeadingOrdersAt switched scale := by
          intro t
          rw [hswitched_nat (2 * t.val) (by omega) (by omega)]
          exact hbOrders t
        have hswitchedDet : diagonalUnitDeterminant switched =
            diagonalUnitDeterminant b *
              discriminant.discriminantUnit := by
          have hbProd :=
            Finset.prod_eq_mul_prod_sdiff_singleton_of_mem
              (Finset.mem_univ lastIndex) b
          unfold diagonalUnitDeterminant
          rw [show switched = Function.update b lastIndex
              (b lastIndex * discriminant.discriminantUnit) by rfl]
          rw [Finset.prod_update_of_mem (Finset.mem_univ lastIndex)]
          rw [hbProd]
          ac_rfl
        have hdetSwitched : IsSquare
            (diagonalUnitDeterminant a *
              diagonalUnitDeterminant switched) := by
          rw [hswitchedDet]
          simpa only [mul_assoc] using hdet
        have hfull := equalDeterminantRepresentation_proved
          a switched scale ha hswitchedClasses haOrders hswitchedOrders
            hdetSwitched
        have hprefix : DiagonalRepresents
            (diagonalUnitCoefficients
              (diagonalUnitTake b (2 * Nat.succ pairs - 1) (by omega)))
            (diagonalUnitCoefficients switched) := by
          convert DiagonalRepresents.prefixOfLE
            (k := 2 * Nat.succ pairs - 1)
            (diagonalUnitCoefficients switched) (by omega) using 1
          funext i
          simp only [diagonalUnitCoefficients, diagonalUnitTake]
          rw [hswitched_of_lt]
          · congr 2
          · simp only [Fin.castLE, Fin.val_mk]
            omega
        exact hprefix.trans hfull

/-- Append one hyperbolic endpoint pair to an alternating tower. -/
def appendHyperbolicPair {pairs : Nat}
    (a : Fin (2 * pairs) → Kˣ) (extra : Kˣ) :
    Fin (2 * (pairs + 1)) → Kˣ := fun i =>
  if h : i.val < 2 * pairs then a ⟨i.val, h⟩
  else if i.val = 2 * pairs then extra else -extra

/-- Appending a hyperbolic pair preserves the endpoint-class condition. -/
theorem appendHyperbolicPair_pairClasses {pairs : Nat}
    (a : Fin (2 * pairs) → Kˣ) (extra : Kˣ)
    (ha : AlternatingEndpointPairClasses a) :
    AlternatingEndpointPairClasses (appendHyperbolicPair a extra) := by
  intro t
  by_cases ht : t.val < pairs
  · have heven : 2 * t.val < 2 * pairs := by omega
    have hodd : 2 * t.val + 1 < 2 * pairs := by omega
    simpa only [appendHyperbolicPair, dif_pos heven, dif_pos hodd] using
      ha ⟨t.val, ht⟩
  · have htval : t.val = pairs := by omega
    left
    refine ⟨extra, ?_⟩
    apply Units.ext
    simp [appendHyperbolicPair, htval, pow_two]

/-- The appended hyperbolic pair has the same leading scale as the old
tower. -/
theorem appendHyperbolicPair_leadingOrders {pairs : Nat}
    (a : Fin (2 * pairs) → Kˣ) (extra : Kˣ)
    (ha : AlternatingEndpointLeadingOrdersAt a extra) :
    AlternatingEndpointLeadingOrdersAt (appendHyperbolicPair a extra)
      extra := by
  intro t
  by_cases ht : t.val < pairs
  · have heven : 2 * t.val < 2 * pairs := by omega
    simpa only [appendHyperbolicPair, dif_pos heven] using
      ha ⟨t.val, ht⟩
  · have htval : t.val = pairs := by omega
    simp [appendHyperbolicPair, htval]

/-- Deleting the final line of the appended hyperbolic pair leaves the old
tower followed by its new leading line. -/
theorem diagonalUnitTake_appendHyperbolicPair {pairs : Nat}
    (a : Fin (2 * pairs) → Kˣ) (extra : Kˣ) :
    diagonalUnitTake (appendHyperbolicPair a extra)
        (2 * (pairs + 1) - 1) (by omega) =
      Fin.snoc a extra := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [diagonalUnitTake, appendHyperbolicPair]
  · simp [diagonalUnitTake, appendHyperbolicPair, j.isLt]

/-- Arithmetically normalized form of
`diagonalUnitTake_appendHyperbolicPair`. -/
theorem diagonalUnitTake_appendHyperbolicPair_normalized {pairs : Nat}
    (a : Fin (2 * pairs) → Kˣ) (extra : Kˣ) :
    diagonalUnitTake (appendHyperbolicPair a extra)
        (2 * pairs + 1) (by omega) = Fin.snoc a extra := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [diagonalUnitTake, appendHyperbolicPair]
  · simp [diagonalUnitTake, appendHyperbolicPair]

/-- The coordinate definition of `appendHyperbolicPair` agrees with two
successive `Fin.snoc` operations. -/
theorem appendHyperbolicPair_eq_snoc_snoc {pairs : Nat}
    (a : Fin (2 * pairs) → Kˣ) (extra : Kˣ) :
    appendHyperbolicPair a extra =
      Fin.snoc (Fin.snoc a extra) (-extra) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [appendHyperbolicPair]
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · simp [appendHyperbolicPair]
    · simp [appendHyperbolicPair, k.isLt]

/-- The one-pair extension law follows by completing the requested odd
tower with a hyperbolic mate and applying common codimension one. -/
theorem onePairExtensionRepresentation_proved
    {pairs : Nat} (large : Fin (2 * (pairs + 1)) → Kˣ)
    (small : Fin (2 * pairs) → Kˣ) (extra : Kˣ)
    (hlarge : AlternatingEndpointPairClasses large)
    (hsmall : AlternatingEndpointPairClasses small)
    (hlargeOrders : ∀ t : Fin (pairs + 1),
      ordUnit K (large ⟨2 * t.val, by omega⟩) = ordUnit K extra)
    (hsmallOrders : ∀ t : Fin pairs,
      ordUnit K (small ⟨2 * t.val, by omega⟩) = ordUnit K extra) :
    DiagonalRepresents
      (diagonalUnitCoefficients (Fin.snoc small extra))
      (diagonalUnitCoefficients large) := by
  let completed := appendHyperbolicPair small extra
  have hcompletedClasses : AlternatingEndpointPairClasses completed :=
    appendHyperbolicPair_pairClasses small extra hsmall
  have hcompletedOrders :
      AlternatingEndpointLeadingOrdersAt completed extra :=
    appendHyperbolicPair_leadingOrders small extra hsmallOrders
  have hrep := commonCodimensionOne_proved large completed extra hlarge
    hcompletedClasses hlargeOrders hcompletedOrders
  convert hrep using 1
  · omega
  · simp only [completed, diagonalUnitTake_appendHyperbolicPair]
    rfl

/-- Representation in a unary extension is obtained by adding a common
hyperbolic mate, applying the one-pair theorem, and cancelling that mate. -/
theorem representationInUnaryExtension_proved
    {pairs : Nat} (target comparison : Fin (2 * pairs) → Kˣ)
    (extra : Kˣ)
    (htarget : AlternatingEndpointPairClasses target)
    (hcomparison : AlternatingEndpointPairClasses comparison)
    (htargetOrders : ∀ t : Fin pairs,
      ordUnit K (target ⟨2 * t.val, by omega⟩) = ordUnit K extra)
    (hcomparisonOrders : ∀ t : Fin pairs,
      ordUnit K (comparison ⟨2 * t.val, by omega⟩) = ordUnit K extra) :
    DiagonalRepresents
      (diagonalUnitCoefficients comparison)
      (diagonalUnitCoefficients (Fin.snoc target extra)) := by
  let large := appendHyperbolicPair target extra
  have hlargeClasses : AlternatingEndpointPairClasses large :=
    appendHyperbolicPair_pairClasses target extra htarget
  have hlargeOrdersExtra :
      AlternatingEndpointLeadingOrdersAt large extra :=
    appendHyperbolicPair_leadingOrders target extra htargetOrders
  have hlargeOrdersNeg : ∀ t : Fin (pairs + 1),
      ordUnit K (large ⟨2 * t.val, by omega⟩) =
        ordUnit K (-extra) := by
    intro t
    rw [ordUnit_neg]
    exact hlargeOrdersExtra t
  have hcomparisonOrdersNeg : ∀ t : Fin pairs,
      ordUnit K (comparison ⟨2 * t.val, by omega⟩) =
        ordUnit K (-extra) := by
    intro t
    rw [ordUnit_neg]
    exact hcomparisonOrders t
  have hrep := onePairExtensionRepresentation_proved large comparison
    (-extra) hlargeClasses hcomparison hlargeOrdersNeg
      hcomparisonOrdersNeg
  have hrepSnoc : DiagonalRepresents
      (Fin.snoc (diagonalUnitCoefficients comparison) ((-extra : Kˣ) : K))
      (Fin.snoc (diagonalUnitCoefficients (Fin.snoc target extra))
        ((-extra : Kˣ) : K)) := by
    simpa only [large, appendHyperbolicPair_eq_snoc_snoc,
      diagonalUnitCoefficients_snoc] using hrep
  apply DiagonalRepresents.cancel_common_last ((-extra : Kˣ) : K)
    (diagonalUnitCoefficients comparison)
    (diagonalUnitCoefficients (Fin.snoc target extra))
  · exact Units.ne_zero (-extra)
  · intro i
    exact Units.ne_zero (comparison i)
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [diagonalUnitCoefficients] using Units.ne_zero extra
    · simpa [diagonalUnitCoefficients] using Units.ne_zero (target j)
  · exact hrepSnoc

/-- An unramified binary endpoint does not represent a line whose relative
valuation is odd, even after cancelling equal-scale endpoint towers. -/
theorem unaryExtensionExclusion_proved
    {pairs : Nat} (initial : Fin 2 → Kˣ)
    (source comparison : Fin (2 * pairs) → Kˣ) (extra : Kˣ)
    (hinitial : IsSquare
      (-(initial 0 * initial 1) *
        (discriminant.discriminantUnit : Kˣ)))
    (hsource : AlternatingEndpointPairClasses source)
    (hcomparison : AlternatingEndpointPairClasses comparison)
    (hsourceOrders : ∀ t : Fin pairs,
      ordUnit K (source ⟨2 * t.val, by omega⟩) = ordUnit K extra)
    (hcomparisonOrders : ∀ t : Fin pairs,
      ordUnit K (comparison ⟨2 * t.val, by omega⟩) = ordUnit K extra)
    (hodd : Odd (ordUnit K (extra * (initial 0)⁻¹))) :
    ¬ DiagonalRepresents
      (diagonalUnitCoefficients (Fin.snoc comparison extra))
      (diagonalUnitCoefficients (Fin.append initial source)) := by
  intro hrepresented
  let large := appendHyperbolicPair source extra
  let candidate : Fin (2 * pairs + 1) → Kˣ :=
    Fin.snoc comparison extra
  let ambient : Fin (2 + 2 * pairs) → Kˣ :=
    Fin.append initial source
  have hlargeClasses : AlternatingEndpointPairClasses large :=
    appendHyperbolicPair_pairClasses source extra hsource
  have hlargeOrders : AlternatingEndpointLeadingOrdersAt large extra :=
    appendHyperbolicPair_leadingOrders source extra hsourceOrders
  have hcandidateLarge : DiagonalRepresents
      (diagonalUnitCoefficients candidate)
      (diagonalUnitCoefficients large) := by
    exact onePairExtensionRepresentation_proved large comparison extra
      hlargeClasses hcomparison hlargeOrders hcomparisonOrders
  have hcandidateAmbient : DiagonalRepresents
      (diagonalUnitCoefficients candidate)
      (diagonalUnitCoefficients ambient) := by
    simpa only [candidate, ambient] using hrepresented
  have hcycle := DiagonalRepresentationParityLaws.caseI
    ambient large candidate (by omega) (by omega)

  let DI := diagonalUnitDeterminant initial
  let DS := diagonalUnitDeterminant source
  let DC := diagonalUnitDeterminant comparison
  have hambientDet : diagonalUnitDeterminant ambient = DI * DS := by
    exact diagonalUnitDeterminant_append initial source
  have hlargeDet : diagonalUnitDeterminant large =
      DS * extra * (-extra) := by
    rw [show large = appendHyperbolicPair source extra by rfl,
      appendHyperbolicPair_eq_snoc_snoc,
      diagonalUnitDeterminant_snoc, diagonalUnitDeterminant_snoc]
  have hprefixDet : diagonalUnitDeterminant
      (diagonalUnitTake large (2 * pairs + 1) (by omega)) =
        DS * extra := by
    rw [show large = appendHyperbolicPair source extra by rfl,
      diagonalUnitTake_appendHyperbolicPair_normalized,
      diagonalUnitDeterminant_snoc]
  have hcandidateDet : diagonalUnitDeterminant candidate = DC * extra := by
    rw [show candidate = Fin.snoc comparison extra by rfl,
      diagonalUnitDeterminant_snoc]
  have hinitialDet : DI = initial 0 * initial 1 := by
    simp only [DI, diagonalUnitDeterminant, Fin.prod_univ_two]
  have hinitialClass : IsSquare
      ((-DI) * discriminant.discriminantUnit) := by
    simpa only [hinitialDet] using hinitial
  have hxClass : IsSquare
      ((diagonalUnitDeterminant ambient *
          diagonalUnitDeterminant large) * (-DI)) := by
    refine ⟨(-DI) * DS * extra, ?_⟩
    rw [hambientDet, hlargeDet]
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, Units.val_mul, Units.val_neg]
    ring
  have hxDiscriminant : IsSquare
      ((diagonalUnitDeterminant ambient *
          diagonalUnitDeterminant large) *
        discriminant.discriminantUnit) :=
    isSquare_mul_trans _ (-DI) _ hxClass hinitialClass
  have htowerCases : IsSquare (DS * DC) ∨
      IsSquare (DS * DC * discriminant.discriminantUnit) := by
    have hsigned := signedDeterminant_cases source hsource
    have hcomparisonSigned :=
      signedDeterminant_cases comparison hcomparison
    exact BONG.endpointSquareCases_product
      (laws := discriminant) ((-1 : Kˣ) ^ pairs) DS DC
      (by simpa only [signedDeterminant, DS] using hsigned)
      (by simpa only [signedDeterminant, DC] using hcomparisonSigned)
  have hyCases : IsSquare
        (diagonalUnitDeterminant
            (diagonalUnitTake large (2 * pairs + 1) (by omega)) *
          diagonalUnitDeterminant candidate) ∨
      IsSquare
        (diagonalUnitDeterminant
            (diagonalUnitTake large (2 * pairs + 1) (by omega)) *
          diagonalUnitDeterminant candidate *
            discriminant.discriminantUnit) := by
    have he2 : IsSquare (extra ^ 2) :=
      ⟨extra, by simp only [pow_two]⟩
    rcases htowerCases with htower | htower
    · left
      rw [hprefixDet, hcandidateDet]
      simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using
        htower.mul he2
    · right
      rw [hprefixDet, hcandidateDet]
      simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using
        htower.mul he2
  have hhilbert : hilbertSymbol K
      (diagonalUnitDeterminant ambient * diagonalUnitDeterminant large)
      (diagonalUnitDeterminant
          (diagonalUnitTake large (2 * pairs + 1) (by omega)) *
        diagonalUnitDeterminant candidate) = 1 := by
    rcases hyCases with hySquare | hyDiscriminant
    · exact hilbertSymbol_eq_one_of_isSquare_right K hySquare
    · rw [hilbertSymbol_eq_of_isSquare_mul_left hxDiscriminant,
        hilbertSymbol_eq_of_isSquare_mul_right hyDiscriminant,
        hilbertSymbol_self_eq_neg_one]
      exact hilbertSymbol_discriminant_eq_one_of_even_order (-1)
        (by rw [ordUnit_neg_one_eq_zero]; exact ⟨0, by omega⟩)
  have hprefixLarge :=
    hcycle.all_triple_consequences.2.2.2 hcandidateLarge
      hcandidateAmbient hhilbert
  have hsourceExtra : DiagonalRepresents
      (diagonalUnitCoefficients (Fin.snoc source extra))
      (diagonalUnitCoefficients ambient) := by
    simpa only [large, diagonalUnitTake_appendHyperbolicPair_normalized]
      using hprefixLarge

  let line : Fin 1 → K := fun _ => (extra : K)
  let common := diagonalUnitCoefficients source
  have hsnocCoefficients : diagonalUnitCoefficients (Fin.snoc source extra) =
      Fin.append common line := by
    have hlineFunction :
        Fin.cons (extra : K) (Fin.elim0 : Fin 0 → K) = line := by
      funext i
      fin_cases i
      rfl
    rw [diagonalUnitCoefficients_snoc, Fin.snoc_eq_append,
      hlineFunction]
  have hambientCoefficients : diagonalUnitCoefficients ambient =
      Fin.append (diagonalUnitCoefficients initial) common := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [ambient, common, diagonalUnitCoefficients]
    · simp [ambient, common, diagonalUnitCoefficients]
  have hswap : DiagonalRepresents (Fin.append line common)
      (Fin.append common line) :=
    diagonalRepresents_append_comm line common
  have hsourceExtra' : DiagonalRepresents (Fin.append common line)
      (Fin.append (diagonalUnitCoefficients initial) common) := by
    rw [← hsnocCoefficients, ← hambientCoefficients]
    exact hsourceExtra
  have happended : DiagonalRepresents (Fin.append line common)
      (Fin.append (diagonalUnitCoefficients initial) common) := by
    exact hswap.trans hsourceExtra'
  have hline : DiagonalRepresents line
      (diagonalUnitCoefficients initial) := by
    apply DiagonalRepresents.cancel_common_append line
      (diagonalUnitCoefficients initial) common
    · intro i
      exact Units.ne_zero extra
    · intro i
      exact Units.ne_zero (initial i)
    · intro i
      exact Units.ne_zero (source i)
    · exact happended
  have hbinary : DiagonalRepresents (fun _ : Fin 1 => (extra : K))
      (Fin.cons (initial 0 : K)
        (fun _ : Fin 1 => (initial 1 : K))) := by
    have hinitialCoefficients : diagonalUnitCoefficients initial =
        Fin.cons (initial 0 : K)
          (fun _ : Fin 1 => (initial 1 : K)) := by
      funext i
      fin_cases i <;> rfl
    rw [← hinitialCoefficients]
    simpa only [line] using hline
  have hnormHilbert : hilbertSymbol K
      (-(initial 0 * initial 1))
      (extra * (initial 0)⁻¹) = 1 := by
    rw [hilbertSymbol_comm]
    exact (DiagonalRepresents.unary_binary_iff_hilbertSymbol_one
      (initial 0) (initial 1) extra).mp hbinary
  exact (hilbertSymbol_ne_one_of_isSquare_mul_discriminant_of_odd_order
    hinitial hodd) hnormHilbert

/-- Concrete codimension-two determinant cancellation for equal-scale
alternating endpoint towers.  A hypothetical discriminant-twisted endpoint
class makes the binary orthogonal complement hyperbolic; its represented
scale would then violate `unaryExtensionExclusion_proved`. -/
theorem codimensionTwoDeterminantSquare_proved
    {pairs : Nat} (initial : Fin 2 → Kˣ)
    (source comparison : Fin (2 * pairs) → Kˣ) (scale : Kˣ)
    (hinitial : IsSquare
      (-(initial 0 * initial 1) *
        (discriminant.discriminantUnit : Kˣ)))
    (hsource : AlternatingEndpointPairClasses source)
    (hcomparison : AlternatingEndpointPairClasses comparison)
    (hsourceOrders : ∀ t : Fin pairs,
      ordUnit K (source ⟨2 * t.val, by omega⟩) = ordUnit K scale)
    (hcomparisonOrders : ∀ t : Fin pairs,
      ordUnit K (comparison ⟨2 * t.val, by omega⟩) = ordUnit K scale)
    (hodd : Odd (ordUnit K scale - ordUnit K (initial 0)))
    (hrep : DiagonalRepresents
      (diagonalUnitCoefficients comparison)
      (diagonalUnitCoefficients (Fin.append initial source))) :
    IsSquare
      (diagonalUnitDeterminant source *
        diagonalUnitDeterminant comparison) := by
  let DI := diagonalUnitDeterminant initial
  let DS := diagonalUnitDeterminant source
  let DC := diagonalUnitDeterminant comparison
  have hinitialDet : DI = initial 0 * initial 1 := by
    simp only [DI, diagonalUnitDeterminant, Fin.prod_univ_two]
  have hinitialClass : IsSquare
      ((-DI) * discriminant.discriminantUnit) := by
    simpa only [hinitialDet] using hinitial
  have htowerCases : IsSquare (DS * DC) ∨
      IsSquare (DS * DC * discriminant.discriminantUnit) := by
    have hsigned := signedDeterminant_cases source hsource
    have hcomparisonSigned := signedDeterminant_cases comparison hcomparison
    exact BONG.endpointSquareCases_product
      (laws := discriminant) ((-1 : Kˣ) ^ pairs) DS DC
      (by simpa only [signedDeterminant, DS] using hsigned)
      (by simpa only [signedDeterminant, DC] using hcomparisonSigned)
  rcases htowerCases with hdesired | htwisted
  · exact hdesired
  · exfalso
    have hswapForward : DiagonalRepresents
        (diagonalUnitCoefficients (Fin.append initial source))
        (diagonalUnitCoefficients (Fin.append source initial)) := by
      rw [diagonalUnitCoefficients_append, diagonalUnitCoefficients_append]
      exact diagonalRepresents_append_comm
        (diagonalUnitCoefficients initial) (diagonalUnitCoefficients source)
    have hrepNormalized : DiagonalRepresents
        (diagonalUnitCoefficients comparison)
        (diagonalUnitCoefficients (Fin.append source initial)) :=
      DiagonalRepresents.trans hrep hswapForward
    obtain ⟨complement, hcomplement⟩ :=
      exists_diagonalBinaryComplement comparison
        (Fin.append source initial) hrepNormalized
    let DE := diagonalUnitDeterminant complement
    have hfullRaw := DiagonalIsometryInvariantLaws.determinant_square
      (Fin.append comparison complement) (Fin.append source initial) hcomplement
    have hfull : IsSquare ((DI * DS * DC) * DE) := by
      rw [diagonalUnitDeterminant_append,
        diagonalUnitDeterminant_append] at hfullRaw
      simpa only [DI, DS, DC, DE, mul_assoc, mul_comm, mul_left_comm]
        using hfullRaw
    have hnegativeCore : IsSquare ((-1 : Kˣ) * (DI * DS * DC)) := by
      have hinitialClass' : IsSquare
          (discriminant.discriminantUnit * (-DI)) := by
        simpa only [mul_comm] using hinitialClass
      have htrans := isSquare_mul_trans (DS * DC)
        discriminant.discriminantUnit (-DI) htwisted hinitialClass'
      rw [show ((-1 : Kˣ) * (DI * DS * DC)) =
          (DS * DC) * (-DI) by
        apply Units.ext
        simp only [Units.val_mul, Units.val_neg, Units.val_one]
        ring]
      exact htrans
    have hcomplementSigned : IsSquare (-DE) := by
      have htrans := isSquare_mul_trans (-1 : Kˣ) (DI * DS * DC) DE
        hnegativeCore hfull
      rw [show -DE = (-1 : Kˣ) * DE by
        apply Units.ext
        simp only [Units.val_mul, Units.val_neg, Units.val_one]
        ring]
      exact htrans
    have hcomplementIsotropic :
        DiagonalIsotropic (diagonalUnitCoefficients complement) :=
      diagonalUnitBinary_isotropic_of_signedDeterminantSquare complement
        (by simpa only [DE] using hcomplementSigned)
    obtain ⟨x, hx⟩ := diagonal_exists_value_of_isotropic
      (diagonalUnitCoefficients complement)
      (fun i => Units.ne_zero (complement i)) hcomplementIsotropic scale
    obtain ⟨tail, hsplit, _⟩ :=
      exists_diagonal_split_first (K := K) 1 complement scale x hx
    let line : Fin 1 → K := fun _ => (scale : K)
    have hlinePrefix : DiagonalRepresents line
        (diagonalUnitCoefficients (Fin.cons scale tail)) := by
      have hp := DiagonalRepresents.prefixOfLE
        (k := 1) (diagonalUnitCoefficients (Fin.cons scale tail)) (by omega)
      simpa [line, diagonalUnitCoefficients] using hp
    have hlineComplement : DiagonalRepresents line
        (diagonalUnitCoefficients complement) :=
      DiagonalRepresents.trans hlinePrefix hsplit
    have hcomparisonIdentity : DiagonalRepresents
        (diagonalUnitCoefficients comparison)
        (diagonalUnitCoefficients comparison) :=
      diagonalRepresents_refl _
    have happended : DiagonalRepresents
        (Fin.append (diagonalUnitCoefficients comparison) line)
        (Fin.append (diagonalUnitCoefficients comparison)
          (diagonalUnitCoefficients complement)) :=
      DiagonalRepresents.appendBoth hcomparisonIdentity hlineComplement
    have hsourceCoefficients :
        diagonalUnitCoefficients (Fin.snoc comparison scale) =
          Fin.append (diagonalUnitCoefficients comparison) line := by
      rw [diagonalUnitCoefficients_snoc, Fin.snoc_eq_append]
      congr 1
      funext i
      fin_cases i
      rfl
    have hcomparisonComplement : DiagonalRepresents
        (diagonalUnitCoefficients (Fin.snoc comparison scale))
        (diagonalUnitCoefficients (Fin.append comparison complement)) := by
      rw [hsourceCoefficients, diagonalUnitCoefficients_append]
      exact happended
    have htoNormalized : DiagonalRepresents
        (diagonalUnitCoefficients (Fin.snoc comparison scale))
        (diagonalUnitCoefficients (Fin.append source initial)) :=
      DiagonalRepresents.trans hcomparisonComplement hcomplement
    have hswapBack : DiagonalRepresents
        (diagonalUnitCoefficients (Fin.append source initial))
        (diagonalUnitCoefficients (Fin.append initial source)) := by
      rw [diagonalUnitCoefficients_append, diagonalUnitCoefficients_append]
      exact diagonalRepresents_append_comm
        (diagonalUnitCoefficients source) (diagonalUnitCoefficients initial)
    have hforbidden : DiagonalRepresents
        (diagonalUnitCoefficients (Fin.snoc comparison scale))
        (diagonalUnitCoefficients (Fin.append initial source)) :=
      DiagonalRepresents.trans htoNormalized hswapBack
    have hodd' : Odd (ordUnit K (scale * (initial 0)⁻¹)) := by
      simpa only [ordUnit_mul, ordUnit_inv, sub_eq_add_neg] using hodd
    exact (unaryExtensionExclusion_proved initial source comparison scale
      hinitial hsource hcomparison hsourceOrders hcomparisonOrders hodd')
      hforbidden

/-- Concrete type-II residual-ternary cancellation.  Lemma 1.5(ii)'s parity
cycle forces the forbidden unary extension after the two endpoint towers are
cancelled; hence the represented ambient configuration can occur only if the
displayed residual ternary form is isotropic. -/
theorem residualTernaryIsotropic_proved
    {pairs : Nat} (initial : Fin 2 → Kˣ)
    (source : Fin (2 * pairs) → Kˣ)
    (comparison : Fin (2 * (pairs + 1)) → Kˣ) (extra : Kˣ)
    (hinitial : IsSquare
      (-(initial 0 * initial 1) *
        (discriminant.discriminantUnit : Kˣ)))
    (hodd : Odd (ordUnit K (extra * (initial 0)⁻¹)))
    (hsource : AlternatingEndpointPairClasses source)
    (hcomparison : AlternatingEndpointPairClasses comparison)
    (hsourceOrders : ∀ t : Fin pairs,
      ordUnit K (source ⟨2 * t.val, by omega⟩) = ordUnit K extra)
    (hcomparisonOrders : ∀ t : Fin (pairs + 1),
      ordUnit K (comparison ⟨2 * t.val, by omega⟩) = ordUnit K extra)
    (hrep : DiagonalRepresents
      (diagonalUnitCoefficients comparison)
      (diagonalUnitCoefficients
        (Fin.snoc (Fin.append initial source) extra))) :
    DiagonalIsotropic
      (diagonalUnitCoefficients ![initial 0, initial 1, extra]) := by
  exfalso
  let ambient : Fin (2 * pairs + 2 + 1) → Kˣ :=
    Fin.snoc (Fin.append source initial) extra
  let candidate : Fin (2 * pairs + 1) → Kˣ := Fin.snoc source (-extra)
  have hsourceOrdersNeg : ∀ t : Fin pairs,
      ordUnit K (source ⟨2 * t.val, by omega⟩) = ordUnit K (-extra) := by
    intro t
    rw [ordUnit_neg]
    exact hsourceOrders t
  have hcomparisonOrdersNeg : ∀ t : Fin (pairs + 1),
      ordUnit K (comparison ⟨2 * t.val, by omega⟩) =
        ordUnit K (-extra) := by
    intro t
    rw [ordUnit_neg]
    exact hcomparisonOrders t
  have hcandidateComparison : DiagonalRepresents
      (diagonalUnitCoefficients candidate)
      (diagonalUnitCoefficients comparison) := by
    simpa only [candidate] using
      onePairExtensionRepresentation_proved comparison source (-extra)
        hcomparison hsource hcomparisonOrdersNeg hsourceOrdersNeg
  have hcomparisonAmbient : DiagonalRepresents
      (diagonalUnitCoefficients comparison)
      (diagonalUnitCoefficients ambient) := by
    have hswapBase : DiagonalRepresents
        (diagonalUnitCoefficients (Fin.append initial source))
        (diagonalUnitCoefficients (Fin.append source initial)) := by
      rw [diagonalUnitCoefficients_append, diagonalUnitCoefficients_append]
      exact diagonalRepresents_append_comm
        (diagonalUnitCoefficients initial) (diagonalUnitCoefficients source)
    have hswapAmbient : DiagonalRepresents
        (diagonalUnitCoefficients
          (Fin.snoc (Fin.append initial source) extra))
        (diagonalUnitCoefficients
          (Fin.snoc (Fin.append source initial) extra)) := by
      simpa only [diagonalUnitCoefficients_snoc] using
        diagonalRepresents_snoc hswapBase (extra : K)
    exact DiagonalRepresents.trans hrep (by
      simpa only [ambient] using hswapAmbient)
  have htake : 2 * (pairs + 1) ≤ 2 * pairs + 2 + 1 := by omega
  have hcycle := DiagonalRepresentationParityLaws.caseII
    ambient comparison candidate (by omega) (by omega)

  let DI := diagonalUnitDeterminant initial
  let DS := diagonalUnitDeterminant source
  let DC := diagonalUnitDeterminant comparison
  have hinitialDet : DI = initial 0 * initial 1 := by
    simp only [DI, diagonalUnitDeterminant, Fin.prod_univ_two]
  have hinitialClass : IsSquare
      ((-DI) * discriminant.discriminantUnit) := by
    simpa only [hinitialDet] using hinitial
  have hinitialClass' : IsSquare
      (discriminant.discriminantUnit * (-DI)) := by
    simpa only [mul_comm] using hinitialClass
  have hpairCases : IsSquare (-(DS * DC)) ∨
      IsSquare (-(DS * DC) * discriminant.discriminantUnit) := by
    have hsigned := signedDeterminant_cases source hsource
    have hcomparisonSigned := signedDeterminant_cases comparison hcomparison
    have hraw := BONG.endpointSquareCases_product
      (laws := discriminant) (1 : Kˣ)
      (signedDeterminant source) (signedDeterminant comparison)
      (by simpa only [one_mul] using hsigned)
      (by simpa only [one_mul] using hcomparisonSigned)
    have hsignedProduct : signedDeterminant source *
        signedDeterminant comparison = -(DS * DC) := by
      apply Units.ext
      have hexponent : pairs + (pairs + 1) = 2 * pairs + 1 := by omega
      have hsign : ((-1 : K) ^ pairs) * ((-1 : K) ^ (pairs + 1)) = -1 := by
        rw [← pow_add, hexponent, pow_succ, pow_mul]
        norm_num
      simp only [signedDeterminant, DS, DC, Units.val_mul,
        Units.val_pow_eq_pow_val, Units.val_neg]
      calc
        (-1 : K) ^ pairs * (diagonalUnitDeterminant source : K) *
              ((-1 : K) ^ (pairs + 1) *
                (diagonalUnitDeterminant comparison : K)) =
            (((-1 : K) ^ pairs) * ((-1 : K) ^ (pairs + 1))) *
              ((diagonalUnitDeterminant source : K) *
                (diagonalUnitDeterminant comparison : K)) := by ring
        _ = -((diagonalUnitDeterminant source : K) *
              (diagonalUnitDeterminant comparison : K)) := by rw [hsign]; ring
    simpa only [hsignedProduct] using hraw
  have hprefixAmbient : diagonalUnitTake ambient (2 * (pairs + 1))
      htake = Fin.append source initial := by
    funext i
    change Fin.snoc (α := fun _ => Kˣ) (Fin.append source initial) extra
        (Fin.castLE htake i) = Fin.append source initial i
    rw [show Fin.castLE htake i = i.castSucc by
      apply Fin.ext
      rfl]
    exact @Fin.snoc_castSucc (2 * pairs + 2) (fun _ => Kˣ)
      extra (Fin.append source initial) i
  have hprefixDet : diagonalUnitDeterminant
      (diagonalUnitTake ambient (2 * (pairs + 1)) htake) =
        DI * DS := by
    rw [hprefixAmbient, diagonalUnitDeterminant_append]
    simpa only [DI, DS, mul_comm]
  have hambientDet : diagonalUnitDeterminant ambient =
      DI * DS * extra := by
    rw [show ambient = Fin.snoc (Fin.append source initial) extra by rfl,
      diagonalUnitDeterminant_snoc, diagonalUnitDeterminant_append]
    simpa only [DI, DS, mul_comm]
  have hcandidateDet : diagonalUnitDeterminant candidate =
      DS * (-extra) := by
    rw [show candidate = Fin.snoc source (-extra) by rfl,
      diagonalUnitDeterminant_snoc]
  let X := diagonalUnitDeterminant
      (diagonalUnitTake ambient (2 * (pairs + 1)) htake) *
        diagonalUnitDeterminant comparison
  let Y := -diagonalUnitDeterminant ambient *
      diagonalUnitDeterminant candidate
  have hX : X = (DI * DS) * DC := by
    dsimp only [X, DC]
    rw [hprefixDet]
  have hYDI : IsSquare (Y * DI) := by
    refine ⟨DI * DS * extra, ?_⟩
    rw [show Y = -(diagonalUnitDeterminant ambient) *
        diagonalUnitDeterminant candidate by rfl,
      hambientDet, hcandidateDet]
    apply Units.ext
    simp only [Units.val_mul, Units.val_neg, Units.val_pow_eq_pow_val]
    ring
  have hDInegDiscriminant : IsSquare
      (DI * (-discriminant.discriminantUnit)) := by
    rw [show DI * (-discriminant.discriminantUnit) =
        (-DI) * discriminant.discriminantUnit by
      apply Units.ext
      simp only [Units.val_mul, Units.val_neg]
      ring]
    exact hinitialClass
  have hYnegDiscriminant : IsSquare
      (Y * (-discriminant.discriminantUnit)) :=
    isSquare_mul_trans (K := K) Y DI (-discriminant.discriminantUnit)
      hYDI hDInegDiscriminant
  have hhilbertCore : hilbertSymbol K ((DI * DS) * DC) Y = 1 := by
    rcases hpairCases with hpairSquare | hpairDiscriminant
    · have hxDiscriminant : IsSquare
          (((DI * DS) * DC) * discriminant.discriminantUnit) := by
        have hproduct := hpairSquare.mul hinitialClass
        rw [show ((DI * DS) * DC) * discriminant.discriminantUnit =
            (-(DS * DC)) * ((-DI) * discriminant.discriminantUnit) by
          apply Units.ext
          simp only [Units.val_mul, Units.val_neg]
          ring]
        exact hproduct
      rw [hilbertSymbol_eq_of_isSquare_mul_left hxDiscriminant,
        hilbertSymbol_eq_of_isSquare_mul_right hYnegDiscriminant]
      exact hilbertSymbol_self_neg_eq_one discriminant.discriminantUnit
    · have hxSquare : IsSquare ((DI * DS) * DC) := by
        have htrans := isSquare_mul_trans (-(DS * DC))
          discriminant.discriminantUnit (-DI)
          hpairDiscriminant hinitialClass'
        rw [show (DI * DS) * DC = (-(DS * DC)) * (-DI) by
          apply Units.ext
          simp only [Units.val_mul, Units.val_neg]
          ring]
        exact htrans
      exact hilbertSymbol_eq_one_of_isSquare_left K hxSquare
  have hhilbert : hilbertSymbol K X Y = 1 := by
    rw [hX]
    exact hhilbertCore
  have hprefixCandidate := hcycle.all_triple_consequences.2.1
    hcomparisonAmbient hcandidateComparison hhilbert
  have hforbidden : DiagonalRepresents
      (diagonalUnitCoefficients (Fin.snoc source (-extra)))
      (diagonalUnitCoefficients (Fin.append initial source)) := by
    have htoNormalized : DiagonalRepresents
        (diagonalUnitCoefficients (Fin.snoc source (-extra)))
        (diagonalUnitCoefficients (Fin.append source initial)) := by
      rw [← hprefixAmbient]
      simpa only [candidate] using hprefixCandidate
    have hswapBack : DiagonalRepresents
        (diagonalUnitCoefficients (Fin.append source initial))
        (diagonalUnitCoefficients (Fin.append initial source)) := by
      rw [diagonalUnitCoefficients_append, diagonalUnitCoefficients_append]
      exact diagonalRepresents_append_comm
        (diagonalUnitCoefficients source) (diagonalUnitCoefficients initial)
    exact DiagonalRepresents.trans htoNormalized hswapBack
  have hoddNeg : Odd (ordUnit K ((-extra) * (initial 0)⁻¹)) := by
    simpa only [ordUnit_mul, ordUnit_neg, ordUnit_inv] using hodd
  exact (unaryExtensionExclusion_proved initial source source (-extra)
    hinitial hsource hsource hsourceOrdersNeg hsourceOrdersNeg hoddNeg)
    hforbidden

/-- The unconditional alternating-endpoint representation package used in
Beli (2019), Lemmas 7.9 and 7.16. -/
noncomputable instance dyadicAlternatingEndpointTowerRepresentationLawsProved :
    DyadicAlternatingEndpointTowerRepresentationLaws K where
  commonCodimensionOne := commonCodimensionOne_proved
  equalDeterminantRepresentation := equalDeterminantRepresentation_proved
  onePairExtensionRepresentation := onePairExtensionRepresentation_proved
  representationInUnaryExtension := representationInUnaryExtension_proved
  unaryExtensionExclusion := unaryExtensionExclusion_proved
  codimensionTwoDeterminantSquare := codimensionTwoDeterminantSquare_proved
  residualTernaryIsotropic := residualTernaryIsotropic_proved

example : DyadicAlternatingEndpointTowerRepresentationLaws K := inferInstance

end AlternatingEndpointTower

end Bong
