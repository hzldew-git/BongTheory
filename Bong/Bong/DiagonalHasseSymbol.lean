/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.DiagonalTernaryCore
import Bong.Bong.DiagonalCodimensionOneCancellation
import Bong.Bong.DiagonalHeadCancellation

/-!
# Hasse symbols of diagonal quadratic forms

This file records the Hasse-symbol convention used by Beli.  In that
convention the one-dimensional form `[a]` has symbol `(a, a)`.  Thus the
symbol differs from the pair-only convention by the diagonal self-pairings.

The definition and its Hilbert-symbol identities are concrete.  Invariance
under an equal-dimensional quadratic isometry is isolated in
`DiagonalIsometryInvariantLaws`; this is a standard theorem about Hasse and
determinant invariants, not a paper-specific representation hypothesis.
-/

namespace Bong

open Dyadic
open BONG.GoodBONG

universe u

variable {K : Type u}

/-- Reindexing diagonal coefficients by a permutation gives an isometric
diagonal form. -/
theorem diagonalRepresents_reindex [Field K] {n : Nat}
    (a : Fin n → K) (e : Equiv.Perm (Fin n)) :
    DiagonalRepresents (a ∘ e) a := by
  let E := LinearEquiv.piCongrLeft K (fun _ : Fin n => K) e
  refine ⟨E.toLinearMap, E.injective, ?_⟩
  intro x
  have hE (i : Fin n) : E x (e i) = x i := by
    change (Equiv.piCongrLeft (fun _ : Fin n => K) e) x (e i) = x i
    exact Equiv.piCongrLeft_apply_apply (fun _ : Fin n => K) e x i
  unfold diagonalQuadratic
  calc
    (∑ i, a i * (E x i) ^ 2) =
        ∑ i, a (e i) * (E x (e i)) ^ 2 := by
      exact (Equiv.sum_comp e (fun j => a j * (E x j) ^ 2)).symm
    _ = ∑ i, (a ∘ e) i * x i ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [hE]
      rfl

/-- Swapping the last two diagonal coefficients is an isometry. -/
theorem diagonalRepresents_swap_last_two [Field K] {n : Nat}
    (a : Fin n → K) (x y : K) :
    DiagonalRepresents (Fin.snoc (Fin.snoc a x) y)
      (Fin.snoc (Fin.snoc a y) x) := by
  let penultimate : Fin (n + 2) := (Fin.last n).castSucc
  let last : Fin (n + 2) := Fin.last (n + 1)
  let e : Equiv.Perm (Fin (n + 2)) := Equiv.swap penultimate last
  have h := diagonalRepresents_reindex (Fin.snoc (Fin.snoc a y) x) e
  have hcoefficients :
      (Fin.snoc (Fin.snoc a y) x) ∘ e =
        Fin.snoc (Fin.snoc a x) y := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [e, last, penultimate]
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · simp [e, last, penultimate]
      · have hpenultimate :
            k.castSucc.castSucc ≠ (Fin.last n).castSucc := by
          intro heq
          have hval := congrArg Fin.val heq
          simp at hval
          omega
        have hlast :
            k.castSucc.castSucc ≠ Fin.last (n + 1) := by
          intro heq
          have hval := congrArg Fin.val heq
          simp at hval
          omega
        simp only [Function.comp_apply]
        dsimp only [e, penultimate, last]
        rw [Equiv.swap_apply_of_ne_of_ne hpenultimate hlast]
        simp
  rw [hcoefficients] at h
  exact h

/-- An anisotropic diagonal form has no zero coefficient. -/
theorem diagonalAnisotropic_coefficient_ne_zero [Field K] {n : Nat}
    (a : Fin n → K) (hanisotropic : DiagonalAnisotropic a) (i : Fin n) :
    a i ≠ 0 := by
  classical
  intro hzero
  let x : Fin n → K := fun j => if j = i then 1 else 0
  have hquadratic : diagonalQuadratic a x = 0 := by
    unfold diagonalQuadratic
    apply Finset.sum_eq_zero
    intro j _hj
    by_cases hji : j = i
    · subst j
      simp [x, hzero]
    · simp [x, hji]
  have hxzero := hanisotropic x hquadratic
  have hi := congrFun hxzero i
  simp [x] at hi

/-- Bundle the coefficients of a nondegenerate diagonal form as units. -/
def diagonalUnitization [Field K] {n : Nat} (a : Fin n → K)
    (hne : ∀ i, a i ≠ 0) : Fin n → Kˣ :=
  fun i => Units.mk0 (a i) (hne i)

@[simp]
theorem diagonalUnitCoefficients_unitization [Field K] {n : Nat}
    (a : Fin n → K) (hne : ∀ i, a i ≠ 0) :
    diagonalUnitCoefficients (diagonalUnitization a hne) = a := by
  rfl

@[simp]
theorem diagonalUnitCoefficients_snoc [Field K] {n : Nat}
    (a : Fin n → Kˣ) (d : Kˣ) :
    diagonalUnitCoefficients (Fin.snoc a d) =
      Fin.snoc (diagonalUnitCoefficients a) (d : K) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [diagonalUnitCoefficients]
  · simp [diagonalUnitCoefficients]

@[simp]
theorem diagonalUnitCoefficients_cons [Field K] {n : Nat}
    (d : Kˣ) (a : Fin n → Kˣ) :
    diagonalUnitCoefficients (Fin.cons d a) =
      Fin.cons (d : K) (diagonalUnitCoefficients a) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rfl

/-- Determinant of a diagonal unit list after adding its first entry. -/
@[simp]
theorem diagonalUnitDeterminant_cons [Field K] {n : Nat}
    (d : Kˣ) (a : Fin n → Kˣ) :
    diagonalUnitDeterminant (Fin.cons d a) =
      d * diagonalUnitDeterminant a := by
  unfold diagonalUnitDeterminant
  rw [Fin.prod_univ_succ]
  rfl

/-- Complete any represented codimension-one diagonal form by the
determinant line. -/
theorem determinantCompletion_represents_base_general
    [Field K] [CharZero K] [DiagonalCodimensionOneCancellationLaws K]
    {n : Nat} (base : Fin (n + 1) → Kˣ) (head : Fin n → Kˣ)
    (hrep : DiagonalRepresents
      (diagonalUnitCoefficients head)
      (diagonalUnitCoefficients base)) :
    let d := diagonalUnitDeterminant base * diagonalUnitDeterminant head
    DiagonalRepresents
      (diagonalUnitCoefficients (Fin.snoc head d))
      (diagonalUnitCoefficients base) := by
  let d := diagonalUnitDeterminant base * diagonalUnitDeterminant head
  let candidate : Fin (n + 1) → Kˣ := Fin.snoc head d
  let extended : Fin (n + 2) → Kˣ := Fin.snoc base d
  have happended : DiagonalRepresents
      (diagonalUnitCoefficients candidate)
      (diagonalUnitCoefficients extended) := by
    have h := diagonalRepresents_snoc hrep (d : K)
    simpa [candidate, extended] using h
  apply DiagonalCodimensionOneCancellationLaws.cancel
    base candidate extended
  · exact diagonalUnitPrefix_snoc base d
  · exact happended
  · rw [show diagonalUnitDeterminant candidate =
        diagonalUnitDeterminant head * d by
      exact diagonalUnitDeterminant_snoc head d]
    refine ⟨diagonalUnitDeterminant base *
      diagonalUnitDeterminant head, ?_⟩
    simp only [d]
    ac_rfl

/-- Beli's Hasse symbol of a nondegenerate diagonal form.  Appending `d`
multiplies the old symbol by `(det, d) (d, d)`. -/
noncomputable def diagonalHasseSymbol (K : Type u) [Field K] :
    {n : Nat} → (Fin n → Kˣ) → ℤˣ
  | 0, _ => 1
  | n + 1, a =>
      diagonalHasseSymbol K (Fin.init a) *
        hilbertSymbol K (diagonalUnitDeterminant (Fin.init a))
          (a (Fin.last n)) *
        hilbertSymbol K (a (Fin.last n)) (a (Fin.last n))

@[simp]
theorem diagonalHasseSymbol_zero [Field K] (a : Fin 0 → Kˣ) :
    diagonalHasseSymbol K a = 1 :=
  rfl

/-- The defining orthogonal-sum formula for an appended diagonal line. -/
@[simp]
theorem diagonalHasseSymbol_snoc [Field K] {n : Nat}
    (a : Fin n → Kˣ) (d : Kˣ) :
    diagonalHasseSymbol K (Fin.snoc a d) =
      diagonalHasseSymbol K a *
        hilbertSymbol K (diagonalUnitDeterminant a) d *
        hilbertSymbol K d d := by
  rw [diagonalHasseSymbol]
  simp only [Fin.init_snoc, Fin.snoc_last]

/-- The standard equal-rank isometry invariants for nondegenerate diagonal
quadratic forms.  The determinant assertion is equality of square classes;
the Hasse assertion uses `diagonalHasseSymbol` above. -/
class DiagonalIsometryInvariantLaws
    (K : Type u) [Field K] [CharZero K] : Prop where
  determinant_square {n : Nat} (a b : Fin n → Kˣ)
      (hrep : DiagonalRepresents
        (diagonalUnitCoefficients a) (diagonalUnitCoefficients b)) :
      IsSquare (diagonalUnitDeterminant a * diagonalUnitDeterminant b)
  hasse_eq {n : Nat} (a b : Fin n → Kˣ)
      (hrep : DiagonalRepresents
        (diagonalUnitCoefficients a) (diagonalUnitCoefficients b)) :
      diagonalHasseSymbol K a = diagonalHasseSymbol K b

/-- Moving the first coefficient of a four-dimensional diagonal form to
the end gives the orthogonal-sum expansion used for a ternary complement.
The proof is a concrete coordinate permutation. -/
theorem diagonalHasseSymbol_cons_fin_three
    [Field K] [CharZero K] [DiagonalIsometryInvariantLaws K]
    (b : Kˣ) (c : Fin 3 → Kˣ) :
    diagonalHasseSymbol K (Fin.cons b c) =
      diagonalHasseSymbol K c *
        hilbertSymbol K (diagonalUnitDeterminant c) b *
        hilbertSymbol K b b := by
  let rotated : Fin 4 → Kˣ := Fin.snoc c b
  let e : Equiv.Perm (Fin 4) :=
    { toFun := fun i ↦ ![(3 : Fin 4), (0 : Fin 4),
        (1 : Fin 4), (2 : Fin 4)] i
      invFun := fun i ↦ ![(1 : Fin 4), (2 : Fin 4),
        (3 : Fin 4), (0 : Fin 4)] i
      left_inv := by
        intro i
        fin_cases i <;> rfl
      right_inv := by
        intro i
        fin_cases i <;> rfl }
  have hcoefficients :
      diagonalUnitCoefficients rotated ∘ e =
        diagonalUnitCoefficients (Fin.cons b c) := by
    funext i
    fin_cases i <;> rfl
  have hrep : DiagonalRepresents
      (diagonalUnitCoefficients (Fin.cons b c))
      (diagonalUnitCoefficients rotated) := by
    rw [← hcoefficients]
    exact diagonalRepresents_reindex
      (diagonalUnitCoefficients rotated) e
  have hhasse := DiagonalIsometryInvariantLaws.hasse_eq
    (Fin.cons b c) rotated hrep
  simpa only [rotated, diagonalHasseSymbol_snoc] using hhasse

variable [Field K] [CharZero K]

/-- The Hilbert symbol takes only the two values `1` and `-1`, so every
value is its own inverse. -/
@[simp]
theorem hilbertSymbol_mul_self (a b : Kˣ) :
    hilbertSymbol K a b * hilbertSymbol K a b = 1 := by
  rcases Int.units_eq_one_or (hilbertSymbol K a b) with h | h <;>
    simp [h]

variable [ValuativeRel K] [TopologicalSpace K] [DyadicContext K]
  [HilbertSymbolLaws K]

/-- If `(x, yz) = 1`, then `(x, y) = (x, z)`. -/
theorem hilbertSymbol_eq_of_mul_right_eq_one (x y z : Kˣ)
    (h : hilbertSymbol K x (y * z) = 1) :
    hilbertSymbol K x y = hilbertSymbol K x z := by
  rw [hilbertSymbol_mul_right] at h
  rcases Int.units_eq_one_or (hilbertSymbol K x y) with hy | hy <;>
    rcases Int.units_eq_one_or (hilbertSymbol K x z) with hz | hz <;>
      simp [hy, hz] at h ⊢

/-- Left-handed version of `hilbertSymbol_eq_of_mul_right_eq_one`. -/
theorem hilbertSymbol_eq_of_mul_left_eq_one (x y z : Kˣ)
    (h : hilbertSymbol K (x * y) z = 1) :
    hilbertSymbol K x z = hilbertSymbol K y z := by
  rw [hilbertSymbol_mul_left] at h
  rcases Int.units_eq_one_or (hilbertSymbol K x z) with hx | hx <;>
    rcases Int.units_eq_one_or (hilbertSymbol K y z) with hy | hy <;>
      simp [hx, hy] at h ⊢

/-- Equality of square classes in the first variable preserves the Hilbert
symbol.  The product formulation avoids choosing square roots of quotients. -/
theorem hilbertSymbol_eq_of_isSquare_mul_left {x y z : Kˣ}
    (hxy : IsSquare (x * y)) :
    hilbertSymbol K x z = hilbertSymbol K y z := by
  apply hilbertSymbol_eq_of_mul_left_eq_one x y z
  exact hilbertSymbol_eq_one_of_isSquare_left K hxy

/-- Equality of square classes in the second variable preserves the Hilbert
symbol. -/
theorem hilbertSymbol_eq_of_isSquare_mul_right {x y z : Kˣ}
    (hxy : IsSquare (x * y)) :
    hilbertSymbol K z x = hilbertSymbol K z y := by
  rw [hilbertSymbol_comm K z x, hilbertSymbol_comm K z y]
  exact hilbertSymbol_eq_of_isSquare_mul_left hxy

/-- The norm identity `(a, -a) = 1`. -/
theorem hilbertSymbol_self_neg_eq_one (a : Kˣ) :
    hilbertSymbol K a (-a) = 1 := by
  apply (hilbertSymbol_eq_one_iff K a (-a)).2
  refine ⟨0, 1, ?_⟩
  simp

/-- Multiplying the norm value `-a` by a square keeps Hilbert symbol one. -/
theorem hilbertSymbol_neg_self_mul_square_eq_one (a s : Kˣ) :
    hilbertSymbol K a ((-a) * s ^ 2) = 1 := by
  rw [hilbertSymbol_mul_square_right]
  exact hilbertSymbol_self_neg_eq_one a

/-- The diagonal self-pairing identity `(a, a) = (a, -1)`. -/
theorem hilbertSymbol_self_eq_neg_one (a : Kˣ) :
    hilbertSymbol K a a = hilbertSymbol K a (-1) := by
  apply hilbertSymbol_eq_of_mul_right_eq_one a a (-1)
  simpa using hilbertSymbol_self_neg_eq_one (K := K) a

/-- Hasse-symbol relation between a ternary head and the ternary
complement of a line in its one-dimensional extension.  This is the
paper-independent identity behind the last Hasse comparison in Beli's
Lemma 8.14(c). -/
theorem diagonalTernaryComplement_hasse_eq_factor_mul
    [DiagonalIsometryInvariantLaws K]
    (head : Fin 3 → Kˣ) (d b : Kˣ) (c : Fin 3 → Kˣ)
    (hcomplement : DiagonalRepresents
      (diagonalUnitCoefficients (Fin.cons b c))
      (diagonalUnitCoefficients (Fin.snoc head d))) :
    diagonalHasseSymbol K c =
      hilbertSymbol K
          (-(diagonalUnitDeterminant head * b))
          (diagonalUnitDeterminant (Fin.snoc head d)) *
        diagonalHasseSymbol K head := by
  let H := diagonalUnitDeterminant head
  let A := diagonalUnitDeterminant (Fin.snoc head d)
  let C := diagonalUnitDeterminant c
  have hhasse := DiagonalIsometryInvariantLaws.hasse_eq
    (Fin.cons b c) (Fin.snoc head d) hcomplement
  rw [diagonalHasseSymbol_cons_fin_three,
    diagonalHasseSymbol_snoc] at hhasse
  have hsquareRaw := DiagonalIsometryInvariantLaws.determinant_square
    (Fin.cons b c) (Fin.snoc head d) hcomplement
  have hsquare : IsSquare (C * (b * A)) := by
    dsimp only [C, A]
    rw [show diagonalUnitDeterminant c *
        (b * diagonalUnitDeterminant (Fin.snoc head d)) =
      diagonalUnitDeterminant (Fin.cons b c) *
        diagonalUnitDeterminant (Fin.snoc head d) by
          rw [diagonalUnitDeterminant_cons]
          ac_rfl]
    exact hsquareRaw
  have hdetHilbert : hilbertSymbol K C b =
      hilbertSymbol K (b * A) b :=
    hilbertSymbol_eq_of_isSquare_mul_left hsquare
  have hA : A = H * d := by
    exact diagonalUnitDeterminant_snoc head d
  have hfactor :
      hilbertSymbol K (-(H * b)) A =
        hilbertSymbol K H d * hilbertSymbol K d d *
          hilbertSymbol K A b := by
    calc
      hilbertSymbol K (-(H * b)) A =
          hilbertSymbol K ((-1) * H * b) A := by simp
      _ = (hilbertSymbol K (-1) A * hilbertSymbol K H A) *
            hilbertSymbol K b A := by
        rw [hilbertSymbol_mul_left, hilbertSymbol_mul_left]
      _ = ((hilbertSymbol K (-1) H * hilbertSymbol K (-1) d) *
            (hilbertSymbol K H H * hilbertSymbol K H d)) *
            hilbertSymbol K b A := by
        rw [hA, hilbertSymbol_mul_right, hilbertSymbol_mul_right]
      _ = ((hilbertSymbol K H (-1) * hilbertSymbol K (-1) d) *
            (hilbertSymbol K H (-1) * hilbertSymbol K H d)) *
            hilbertSymbol K b A := by
        rw [hilbertSymbol_comm K (-1) H,
          hilbertSymbol_self_eq_neg_one]
      _ = hilbertSymbol K (-1) d * hilbertSymbol K H d *
            hilbertSymbol K b A := by
        have hself := hilbertSymbol_mul_self (K := K) H (-1)
        calc
          ((hilbertSymbol K H (-1) * hilbertSymbol K (-1) d) *
                (hilbertSymbol K H (-1) * hilbertSymbol K H d)) *
              hilbertSymbol K b A =
              (hilbertSymbol K H (-1) * hilbertSymbol K H (-1)) *
                (hilbertSymbol K (-1) d * hilbertSymbol K H d *
                  hilbertSymbol K b A) := by ac_rfl
          _ = hilbertSymbol K (-1) d * hilbertSymbol K H d *
                hilbertSymbol K b A := by rw [hself, one_mul]
      _ = hilbertSymbol K H d * hilbertSymbol K d d *
            hilbertSymbol K A b := by
        rw [hilbertSymbol_comm K (-1) d,
          ← hilbertSymbol_self_eq_neg_one,
          hilbertSymbol_comm K b A]
        ac_rfl
  have hmain : diagonalHasseSymbol K c * hilbertSymbol K A b =
      diagonalHasseSymbol K head * hilbertSymbol K H d *
        hilbertSymbol K d d := by
    rw [hdetHilbert, hilbertSymbol_mul_left] at hhasse
    have hself := hilbertSymbol_mul_self (K := K) b b
    calc
      diagonalHasseSymbol K c * hilbertSymbol K A b =
          (diagonalHasseSymbol K c *
              (hilbertSymbol K b b * hilbertSymbol K b b)) *
            hilbertSymbol K A b := by rw [hself, mul_one]
      _ = diagonalHasseSymbol K c *
            (hilbertSymbol K b b * hilbertSymbol K A b) *
              hilbertSymbol K b b := by ac_rfl
      _ = diagonalHasseSymbol K head * hilbertSymbol K H d *
            hilbertSymbol K d d := hhasse
  have hsolved : diagonalHasseSymbol K c =
      diagonalHasseSymbol K head * hilbertSymbol K H d *
        hilbertSymbol K d d * hilbertSymbol K A b := by
    have hcongr := congrArg (fun z : ℤˣ ↦ z * hilbertSymbol K A b) hmain
    have hself := hilbertSymbol_mul_self (K := K) A b
    calc
      diagonalHasseSymbol K c =
          (diagonalHasseSymbol K c * hilbertSymbol K A b) *
            hilbertSymbol K A b := by rw [mul_assoc, hself, mul_one]
      _ = (diagonalHasseSymbol K head * hilbertSymbol K H d *
            hilbertSymbol K d d) * hilbertSymbol K A b := hcongr
      _ = diagonalHasseSymbol K head * hilbertSymbol K H d *
            hilbertSymbol K d d * hilbertSymbol K A b := by rfl
  dsimp only [H, A] at hfactor hsolved ⊢
  rw [hfactor]
  rw [hsolved]
  ac_rfl

/-- The Hilbert-factor calculation in Beli's quaternary-complement
comparison.  It is stated independently of BONGs: `A` and `A'` are the two
quaternary determinants, `H` is the common ternary-head determinant, and
`d'` is the final coefficient of the second quaternary form. -/
theorem diagonalHasse_extensionFactor_eq
    (b A A' H d' cdet cdet' : Kˣ)
    (hA' : A' = H * d')
    (hsquare : IsSquare (cdet * (b * A)))
    (hsquare' : IsSquare (cdet' * (b * A')))
    (hresidual : hilbertSymbol K (A * A') (-(H * b)) = 1) :
    hilbertSymbol K cdet d' * hilbertSymbol K d' d' =
      hilbertSymbol K cdet' (A * H) *
        hilbertSymbol K (A * H) (A * H) := by
  let d := A * H
  let common := b * A * d'
  let residual := -(H * b)
  have hleftDet :
      hilbertSymbol K cdet d' = hilbertSymbol K (b * A) d' := by
    exact hilbertSymbol_eq_of_isSquare_mul_left hsquare
  have hrightDet :
      hilbertSymbol K cdet' d = hilbertSymbol K (b * A') d := by
    exact hilbertSymbol_eq_of_isSquare_mul_left hsquare'
  rw [hleftDet, hrightDet]
  rw [hilbertSymbol_comm K (b * A) d',
    hilbertSymbol_comm K (b * A') d]
  rw [← hilbertSymbol_mul_right, ← hilbertSymbol_mul_right]
  have hrightArgument : (b * A') * d = common * H ^ 2 := by
    dsimp only [d, common]
    rw [hA']
    simp only [pow_two]
    ac_rfl
  rw [hrightArgument, hilbertSymbol_mul_square_right]
  have hfirstProduct : d' * d = A * A' := by
    dsimp only [d]
    rw [hA']
    ac_rfl
  have hcommonResidualProduct :
      common * residual = (-(A * A')) * b ^ 2 := by
    dsimp only [common, residual]
    rw [hA']
    apply Units.ext
    simp only [pow_two, Units.val_mul, Units.val_neg]
    ring
  have hcommonResidual :
      hilbertSymbol K (A * A') (common * residual) = 1 := by
    rw [hcommonResidualProduct]
    exact hilbertSymbol_neg_self_mul_square_eq_one (A * A') b
  have hcommonEqResidual :
      hilbertSymbol K (A * A') common =
        hilbertSymbol K (A * A') residual :=
    hilbertSymbol_eq_of_mul_right_eq_one
      (A * A') common residual hcommonResidual
  have hcommon : hilbertSymbol K (A * A') common = 1 := by
    exact hcommonEqResidual.trans hresidual
  have hfirst : hilbertSymbol K d' common = hilbertSymbol K d common := by
    apply hilbertSymbol_eq_of_mul_left_eq_one
    rw [hfirstProduct]
    exact hcommon
  exact hfirst

/-- Absence of a nonzero isotropic vector is equivalent to diagonal
anisotropy. -/
theorem not_diagonalIsotropic_iff_diagonalAnisotropic {n : Nat}
    (a : Fin n → K) :
    ¬DiagonalIsotropic a ↔ DiagonalAnisotropic a := by
  constructor
  · intro h x hzero
    by_contra hx
    exact h ⟨x, hx, hzero⟩
  · intro h
    rintro ⟨x, hx, hzero⟩
    exact hx (h x hzero)

set_option maxHeartbeats 600000 in
-- The proof composes three dependent diagonal representations and then
-- normalizes the Hasse extension factors.
/-- Generic Hasse-symbol comparison for the ternary complements occurring
in Beli's Lemma 8.14(c). -/
theorem diagonalTernaryComplement_hasse_eq_of_hilbert
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    (base : Fin 4 → Kˣ) (head : Fin 3 → Kˣ)
    (b d' : Kˣ) (c c' : Fin 3 → Kˣ)
    (hheadRep : DiagonalRepresents
      (diagonalUnitCoefficients head)
      (diagonalUnitCoefficients base))
    (hcomplement : DiagonalRepresents
      (diagonalUnitCoefficients (Fin.cons b c))
      (diagonalUnitCoefficients base))
    (hcomplement' : DiagonalRepresents
      (diagonalUnitCoefficients (Fin.cons b c'))
      (diagonalUnitCoefficients (Fin.snoc head d')))
    (hresidual : hilbertSymbol K
      (diagonalUnitDeterminant base *
        diagonalUnitDeterminant (Fin.snoc head d'))
      (-(diagonalUnitDeterminant head * b)) = 1) :
    diagonalHasseSymbol K c = diagonalHasseSymbol K c' := by
  let A := diagonalUnitDeterminant base
  let H := diagonalUnitDeterminant head
  let A' := diagonalUnitDeterminant (Fin.snoc head d')
  let d := A * H
  let candidate : Fin 4 → Kˣ := Fin.snoc head d
  let other : Fin 4 → Kˣ := Fin.snoc head d'
  have hcandidateRep : DiagonalRepresents
      (diagonalUnitCoefficients candidate)
      (diagonalUnitCoefficients base) := by
    simpa [candidate, d, A, H] using
      determinantCompletion_represents_base_general base head hheadRep
  have hleftBase : DiagonalRepresents
      (diagonalUnitCoefficients (Fin.cons b c))
      (diagonalUnitCoefficients candidate) :=
    hcomplement.trans hcandidateRep.symm_of_sameRank
  have hleft : DiagonalRepresents
      (diagonalUnitCoefficients (Fin.snoc (Fin.cons b c) d'))
      (diagonalUnitCoefficients (Fin.snoc candidate d')) := by
    simpa using diagonalRepresents_snoc hleftBase (d' : K)
  have hswap : DiagonalRepresents
      (diagonalUnitCoefficients (Fin.snoc candidate d'))
      (diagonalUnitCoefficients (Fin.snoc other d)) := by
    simpa [candidate, other] using
      diagonalRepresents_swap_last_two
        (diagonalUnitCoefficients head) (d : K) (d' : K)
  have hrightForward : DiagonalRepresents
      (diagonalUnitCoefficients (Fin.snoc (Fin.cons b c') d))
      (diagonalUnitCoefficients (Fin.snoc other d)) := by
    simpa [other] using diagonalRepresents_snoc hcomplement' (d : K)
  have hfull : DiagonalRepresents
      (diagonalUnitCoefficients
        (Fin.cons b (Fin.snoc c d')))
      (diagonalUnitCoefficients
        (Fin.cons b (Fin.snoc c' d))) := by
    have hcomposed :=
      (hleft.trans hswap).trans hrightForward.symm_of_sameRank
    simpa only [Fin.cons_snoc_eq_snoc_cons] using hcomposed
  have htail : DiagonalRepresents
      (diagonalUnitCoefficients (Fin.snoc c d'))
      (diagonalUnitCoefficients (Fin.snoc c' d)) := by
    apply DiagonalRepresents.cancel_common_head
      (b : K)
      (diagonalUnitCoefficients (Fin.snoc c d'))
      (diagonalUnitCoefficients (Fin.snoc c' d))
    · exact Units.ne_zero b
    · intro i
      exact Units.ne_zero ((Fin.snoc c d' : Fin 4 → Kˣ) i)
    · intro i
      exact Units.ne_zero ((Fin.snoc c' d : Fin 4 → Kˣ) i)
    · simpa using hfull
  have hhasseExtension :
      diagonalHasseSymbol K (Fin.snoc c d') =
        diagonalHasseSymbol K (Fin.snoc c' d) :=
    DiagonalIsometryInvariantLaws.hasse_eq
      (Fin.snoc c d') (Fin.snoc c' d) htail
  have hsquareRaw := DiagonalIsometryInvariantLaws.determinant_square
    (Fin.cons b c) base hcomplement
  have hsquare : IsSquare
      (diagonalUnitDeterminant c * (b * A)) := by
    dsimp only [A]
    rw [show diagonalUnitDeterminant c *
        (b * diagonalUnitDeterminant base) =
      b * diagonalUnitDeterminant c *
        diagonalUnitDeterminant base by ac_rfl]
    simpa only [diagonalUnitDeterminant_cons] using hsquareRaw
  have hsquareRaw' := DiagonalIsometryInvariantLaws.determinant_square
    (Fin.cons b c') other (by simpa [other] using hcomplement')
  have hsquare' : IsSquare
      (diagonalUnitDeterminant c' * (b * A')) := by
    dsimp only [A', other]
    rw [show diagonalUnitDeterminant c' *
        (b * diagonalUnitDeterminant (Fin.snoc head d')) =
      b * diagonalUnitDeterminant c' *
        diagonalUnitDeterminant (Fin.snoc head d') by ac_rfl]
    simpa only [diagonalUnitDeterminant_cons] using hsquareRaw'
  have hA' : A' = H * d' := by
    exact diagonalUnitDeterminant_snoc head d'
  have hfactor :
      hilbertSymbol K (diagonalUnitDeterminant c) d' *
          hilbertSymbol K d' d' =
        hilbertSymbol K (diagonalUnitDeterminant c') d *
          hilbertSymbol K d d := by
    apply diagonalHasse_extensionFactor_eq b A A' H d'
      (diagonalUnitDeterminant c) (diagonalUnitDeterminant c')
      hA' hsquare hsquare'
    simpa only [A, A', H] using hresidual
  have hhasse : diagonalHasseSymbol K c = diagonalHasseSymbol K c' := by
    rw [diagonalHasseSymbol_snoc, diagonalHasseSymbol_snoc] at hhasseExtension
    have hhasseExtension' :
        diagonalHasseSymbol K c *
            (hilbertSymbol K (diagonalUnitDeterminant c) d' *
              hilbertSymbol K d' d') =
          diagonalHasseSymbol K c' *
            (hilbertSymbol K (diagonalUnitDeterminant c') d *
              hilbertSymbol K d d) := by
      simpa only [mul_assoc] using hhasseExtension
    rw [hfactor] at hhasseExtension'
    exact mul_right_cancel hhasseExtension'
  exact hhasse

omit [ValuativeRel K] [TopologicalSpace K] [DyadicContext K]
    [HilbertSymbolLaws K] in
/-- A diagonal ternary form is isotropic exactly when the Hilbert symbol of
its adjacent negative products is one. -/
theorem diagonalUnitTernary_isotropic_iff_adjacentHilbertOne
    (c : Fin 3 → Kˣ) :
    DiagonalIsotropic (diagonalUnitCoefficients c) ↔
      hilbertSymbol K (-(c 0 * c 1)) (-(c 1 * c 2)) = 1 := by
  constructor
  · rintro ⟨z, hz, hquadratic⟩
    have hcoefficients :
        diagonalUnitCoefficients c =
          (fun i => ![(c 0 : K), (c 1 : K), (c 2 : K)] i) := by
      funext i
      fin_cases i <;> rfl
    apply hilbertSymbol_eq_one_of_diagonalTernary_isotropic
      (c 0) (c 1) (c 2) z hz
    rw [← hcoefficients]
    exact hquadratic
  · intro h
    rcases diagonalTernary_isotropic_of_adjacent_hilbert_one
        (c 0) (c 1) (c 2) h with ⟨z, hz, hquadratic⟩
    have hcoefficients :
        diagonalUnitCoefficients c =
          (fun i => ![(c 0 : K), (c 1 : K), (c 2 : K)] i) := by
      funext i
      fin_cases i <;> rfl
    refine ⟨z, hz, ?_⟩
    rw [hcoefficients]
    exact hquadratic

/-- Concrete expansion of Beli's Hasse symbol in dimension three. -/
theorem diagonalHasseSymbol_fin_three (c : Fin 3 → Kˣ) :
    diagonalHasseSymbol K c =
      hilbertSymbol K (c 0) (c 0) *
        hilbertSymbol K (c 0) (c 1) *
        hilbertSymbol K (c 1) (c 1) *
        hilbertSymbol K (c 0 * c 1) (c 2) *
        hilbertSymbol K (c 2) (c 2) := by
  simp [diagonalHasseSymbol, diagonalUnitDeterminant,
    Fin.prod_univ_two, Fin.init]

/-- In dimension three, Beli's Hasse symbol equals the adjacent-product
Hilbert symbol times the fixed field constant `(-1, -1)`. -/
theorem diagonalHasseSymbol_fin_three_eq_adjacent (c : Fin 3 → Kˣ) :
    diagonalHasseSymbol K c =
      hilbertSymbol K (-1) (-1) *
        hilbertSymbol K (-(c 0 * c 1)) (-(c 1 * c 2)) := by
  rw [diagonalHasseSymbol_fin_three]
  have hselfZero := hilbertSymbol_self_eq_neg_one (K := K) (c 0)
  have hselfOne := hilbertSymbol_self_eq_neg_one (K := K) (c 1)
  have hselfTwo := hilbertSymbol_self_eq_neg_one (K := K) (c 2)
  rw [hselfZero, hselfOne, hselfTwo]
  rw [show -(c 0 * c 1) = (-1) * c 0 * c 1 by simp,
    show -(c 1 * c 2) = (-1) * c 1 * c 2 by simp]
  simp only [hilbertSymbol_mul_left, hilbertSymbol_mul_right]
  rw [hilbertSymbol_comm K (c 0) (-1),
    hilbertSymbol_comm K (c 1) (-1),
    hilbertSymbol_comm K (c 2) (-1)]
  rw [hselfOne, hilbertSymbol_comm K (c 1) (-1)]
  rcases Int.units_eq_one_or (hilbertSymbol K (-1) (-1)) with hnn | hnn <;>
    rcases Int.units_eq_one_or (hilbertSymbol K (-1) (c 0)) with hn0 | hn0 <;>
    rcases Int.units_eq_one_or (hilbertSymbol K (-1) (c 1)) with hn1 | hn1 <;>
    rcases Int.units_eq_one_or (hilbertSymbol K (-1) (c 2)) with hn2 | hn2 <;>
    rcases Int.units_eq_one_or (hilbertSymbol K (c 0) (c 1)) with h01 | h01 <;>
    rcases Int.units_eq_one_or (hilbertSymbol K (c 0) (c 2)) with h02 | h02 <;>
    rcases Int.units_eq_one_or (hilbertSymbol K (c 1) (c 2)) with h12 | h12 <;>
      simp [hnn, hn0, hn1, hn2, h01, h02, h12]

/-- Ternary isotropy in Beli's convention is equality with the field
constant `(-1, -1)`. -/
theorem diagonalUnitTernary_isotropic_iff_hasseConstant
    (c : Fin 3 → Kˣ) :
    DiagonalIsotropic (diagonalUnitCoefficients c) ↔
      diagonalHasseSymbol K c = hilbertSymbol K (-1) (-1) := by
  rw [diagonalUnitTernary_isotropic_iff_adjacentHilbertOne,
    diagonalHasseSymbol_fin_three_eq_adjacent]
  constructor
  · intro h
    rw [h, mul_one]
  · intro h
    rcases Int.units_eq_one_or
        (hilbertSymbol K (-(c 0 * c 1)) (-(c 1 * c 2))) with hadj | hadj
    · exact hadj
    · rw [hadj] at h
      rcases Int.units_eq_one_or (hilbertSymbol K (-1) (-1)) with hnn | hnn <;>
        simp [hnn] at h

/-- Equal Beli Hasse symbols of ternary forms give identical isotropy
behaviour. -/
theorem diagonalUnitTernary_isotropic_iff_of_hasse_eq
    (a b : Fin 3 → Kˣ)
    (hhasse : diagonalHasseSymbol K a = diagonalHasseSymbol K b) :
    DiagonalIsotropic (diagonalUnitCoefficients a) ↔
      DiagonalIsotropic (diagonalUnitCoefficients b) := by
  rw [diagonalUnitTernary_isotropic_iff_hasseConstant,
    diagonalUnitTernary_isotropic_iff_hasseConstant, hhasse]

/-- Conversely, in dimension three the isotropy dichotomy determines the
Hasse symbol.  Both symbols differ from the fixed field constant
`(-1, -1)` by an element of `{1, -1}`, so equality of the two isotropy
predicates forces equality of the symbols. -/
theorem diagonalHasseSymbol_fin_three_eq_of_isotropic_iff
    (a b : Fin 3 → Kˣ)
    (hisotropic :
      DiagonalIsotropic (diagonalUnitCoefficients a) ↔
        DiagonalIsotropic (diagonalUnitCoefficients b)) :
    diagonalHasseSymbol K a = diagonalHasseSymbol K b := by
  rw [diagonalHasseSymbol_fin_three_eq_adjacent,
    diagonalHasseSymbol_fin_three_eq_adjacent]
  congr 1
  let ha := hilbertSymbol K (-(a 0 * a 1)) (-(a 1 * a 2))
  let hb := hilbertSymbol K (-(b 0 * b 1)) (-(b 1 * b 2))
  have hone : ha = 1 ↔ hb = 1 := by
    rw [show ha = 1 ↔
          DiagonalIsotropic (diagonalUnitCoefficients a) by
        exact (diagonalUnitTernary_isotropic_iff_adjacentHilbertOne a).symm,
      show hb = 1 ↔
          DiagonalIsotropic (diagonalUnitCoefficients b) by
        exact (diagonalUnitTernary_isotropic_iff_adjacentHilbertOne b).symm]
    exact hisotropic
  rcases Int.units_eq_one_or ha with haOne | haNeg <;>
    rcases Int.units_eq_one_or hb with hbOne | hbNeg
  · exact haOne.trans hbOne.symm
  · exact False.elim (by
      have : hb = 1 := hone.mp haOne
      rw [hbNeg] at this
      norm_num at this)
  · exact False.elim (by
      have : ha = 1 := hone.mpr hbOne
      rw [haNeg] at this
      norm_num at this)
  · exact haNeg.trans hbNeg.symm

/-- If the complement factor is one, anisotropy of the ternary head passes
to the ternary complement. -/
theorem diagonalTernaryComplement_anisotropic_of_factor_one
    [DiagonalIsometryInvariantLaws K]
    (head : Fin 3 → Kˣ) (d b : Kˣ) (c : Fin 3 → Kˣ)
    (hcomplement : DiagonalRepresents
      (diagonalUnitCoefficients (Fin.cons b c))
      (diagonalUnitCoefficients (Fin.snoc head d)))
    (hfactor : hilbertSymbol K
      (-(diagonalUnitDeterminant head * b))
      (diagonalUnitDeterminant (Fin.snoc head d)) = 1)
    (hhead : DiagonalAnisotropic (diagonalUnitCoefficients head)) :
    DiagonalAnisotropic (diagonalUnitCoefficients c) := by
  have hhasse := diagonalTernaryComplement_hasse_eq_factor_mul
    head d b c hcomplement
  rw [hfactor, one_mul] at hhasse
  have hisotropy :=
    diagonalUnitTernary_isotropic_iff_of_hasse_eq c head hhasse
  apply (not_diagonalIsotropic_iff_diagonalAnisotropic _).mp
  intro hc
  have hh := hisotropy.mp hc
  exact ((not_diagonalIsotropic_iff_diagonalAnisotropic _).mpr hhead) hh

/-- If the complement factor is minus one, an isotropic ternary head has
an anisotropic ternary complement. -/
theorem diagonalTernaryComplement_anisotropic_of_factor_neg_one
    [DiagonalIsometryInvariantLaws K]
    (head : Fin 3 → Kˣ) (d b : Kˣ) (c : Fin 3 → Kˣ)
    (hcomplement : DiagonalRepresents
      (diagonalUnitCoefficients (Fin.cons b c))
      (diagonalUnitCoefficients (Fin.snoc head d)))
    (hfactor : hilbertSymbol K
      (-(diagonalUnitDeterminant head * b))
      (diagonalUnitDeterminant (Fin.snoc head d)) = -1)
    (hhead : DiagonalIsotropic (diagonalUnitCoefficients head)) :
    DiagonalAnisotropic (diagonalUnitCoefficients c) := by
  have hhasse := diagonalTernaryComplement_hasse_eq_factor_mul
    head d b c hcomplement
  rw [hfactor] at hhasse
  have hheadHasse :=
    (diagonalUnitTernary_isotropic_iff_hasseConstant head).mp hhead
  apply (not_diagonalIsotropic_iff_diagonalAnisotropic _).mp
  intro hc
  have hcHasse :=
    (diagonalUnitTernary_isotropic_iff_hasseConstant c).mp hc
  rw [hheadHasse, hcHasse] at hhasse
  rcases Int.units_eq_one_or (hilbertSymbol K (-1) (-1)) with h | h <;>
    simp [h] at hhasse

/-- The generic Hasse comparison gives identical anisotropy behaviour for
the two ternary complements. -/
theorem diagonalTernaryComplementAnisotropic_iff_of_hilbert
    [DiagonalCodimensionOneCancellationLaws K]
    [DiagonalIsometryInvariantLaws K]
    (base : Fin 4 → Kˣ) (head : Fin 3 → Kˣ)
    (b d' : Kˣ) (c c' : Fin 3 → Kˣ)
    (hheadRep : DiagonalRepresents
      (diagonalUnitCoefficients head)
      (diagonalUnitCoefficients base))
    (hcomplement : DiagonalRepresents
      (diagonalUnitCoefficients (Fin.cons b c))
      (diagonalUnitCoefficients base))
    (hcomplement' : DiagonalRepresents
      (diagonalUnitCoefficients (Fin.cons b c'))
      (diagonalUnitCoefficients (Fin.snoc head d')))
    (hresidual : hilbertSymbol K
      (diagonalUnitDeterminant base *
        diagonalUnitDeterminant (Fin.snoc head d'))
      (-(diagonalUnitDeterminant head * b)) = 1) :
    DiagonalAnisotropic (diagonalUnitCoefficients c) ↔
      DiagonalAnisotropic (diagonalUnitCoefficients c') := by
  have hhasse := diagonalTernaryComplement_hasse_eq_of_hilbert
    base head b d' c c' hheadRep hcomplement hcomplement' hresidual
  have hisotropy :=
    diagonalUnitTernary_isotropic_iff_of_hasse_eq c c' hhasse
  rw [← not_diagonalIsotropic_iff_diagonalAnisotropic,
    ← not_diagonalIsotropic_iff_diagonalAnisotropic]
  exact not_congr hisotropy

end Bong
