/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019JordanApproximation

/-!
# Beli (2019), Corollary 3.3: dual prefix approximations

This file proves the exact product identity behind the passage from a prefix
of a reverse-dual BONG to the complementary prefix of the original BONG.
Together with alpha reversal, it transports scalar approximations across
lattice duality.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {N : Nat}

/-- Prefix products of reciprocal reversed BONG values.  This is the exact
unit-valued identity used in Corollary 3.3. -/
theorem prefixProduct_mul_valueProduct_of_reverseValues
    (b : BONG V q L N) (c : BONG V q M N)
    (hvalues : ∀ i, c.valueUnit i = (b.valueUnit (Fin.rev i))⁻¹)
    (i : Nat) (hi : i ≤ N) :
    c.prefixProduct i * b.valueProduct = b.prefixProduct (N - i) := by
  induction i with
  | zero =>
      simp [valueProduct]
  | succ i ih =>
      have hiN : i < N := by
        omega
      have hsub : N - i = (N - (i + 1)) + 1 := by
        omega
      have hrev : Fin.rev (⟨i, hiN⟩ : Fin N) =
          (⟨N - (i + 1), by omega⟩ : Fin N) := by
        apply Fin.ext
        simp
      rw [c.prefixProduct_succ i hiN]
      calc
        (c.prefixProduct i * c.valueUnit ⟨i, hiN⟩) * b.valueProduct =
            (c.prefixProduct i * b.valueProduct) *
              c.valueUnit ⟨i, hiN⟩ := by
          ac_rfl
        _ = b.prefixProduct (N - i) *
              c.valueUnit ⟨i, hiN⟩ := by
          rw [ih (by omega)]
        _ = b.prefixProduct ((N - (i + 1)) + 1) *
              (b.valueUnit (Fin.rev ⟨i, hiN⟩))⁻¹ := by
          rw [hsub, hvalues]
        _ = b.prefixProduct (N - (i + 1)) := by
          rw [b.prefixProduct_succ (N - (i + 1)) (by omega), hrev]
          simp [mul_assoc]

end BONG

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

/-- Alpha caps at complementary boundaries agree for reverse-dual good
BONGs. -/
theorem prefixAlphaCap_eq_reverseDual
    (b : GoodBONG q L (n + 1))
    (c : GoodBONG q M (n + 1))
    (halpha : ∀ i, c.alphaValue i = b.alphaValue (Fin.rev i))
    (i : Nat) (hi : i ≤ n + 1) :
    c.prefixAlphaCap i = b.prefixAlphaCap (n + 1 - i) := by
  by_cases hzero : i = 0
  · subst i
    simp
  by_cases hlast : i = n + 1
  · subst i
    simp
  have hi0 : 0 < i := Nat.pos_of_ne_zero hzero
  have hiN : i < n + 1 := by
    omega
  have href0 : 0 < n + 1 - i := by
    omega
  have hrefN : n + 1 - i < n + 1 := by
    omega
  rw [c.prefixAlphaCap_of_internal hi0 hiN,
    b.prefixAlphaCap_of_internal href0 hrefN]
  rw [halpha]
  congr 2
  apply Fin.ext
  simp
  omega

/-- Corollary 3.3's dual transport formula for an explicitly supplied
reverse-dual good BONG. -/
theorem isPrefixApproximation_reverseDual
    (b : GoodBONG q L (n + 1))
    (c : GoodBONG q M (n + 1))
    (hvalues : ∀ i,
      c.value i = ((b.toBONG.valueUnit (Fin.rev i))⁻¹ : K))
    (halpha : ∀ i, c.alphaValue i = b.alphaValue (Fin.rev i))
    (i : Nat) (hi : i ≤ n + 1) (X : Kˣ)
    (hX : b.IsPrefixApproximation (n + 1 - i) X) :
    c.IsPrefixApproximation i (X * b.prefixProduct (n + 1)) := by
  have hunits : ∀ j,
      c.toBONG.valueUnit j = (b.toBONG.valueUnit (Fin.rev j))⁻¹ := by
    intro j
    apply Units.ext
    change c.value j = ((b.toBONG.valueUnit (Fin.rev j))⁻¹ : K)
    exact hvalues j
  have hproduct :=
    b.toBONG.prefixProduct_mul_valueProduct_of_reverseValues c.toBONG
      hunits i hi
  unfold IsPrefixApproximation at hX ⊢
  rw [b.prefixAlphaCap_eq_reverseDual c halpha i hi]
  calc
    b.prefixAlphaCap (n + 1 - i) ≤
        defectOrder (K := K) (X * b.prefixProduct (n + 1 - i)) := hX
    _ = defectOrder (K := K)
        ((X * b.prefixProduct (n + 1)) * c.prefixProduct i) := by
      apply congrArg (defectOrder (K := K))
      change X * b.toBONG.prefixProduct (n + 1 - i) =
        (X * b.toBONG.valueProduct) * c.toBONG.prefixProduct i
      rw [← hproduct]
      ac_rfl

/-- The inverse form of Corollary 3.3.  Approximation at a prefix of a
reciprocal reversed BONG gives approximation at the complementary prefix of
the original BONG.  Keeping the second lattice arbitrary makes this usable
for transported and cast reverse-dual BONGs without introducing a new law
interface. -/
theorem isPrefixApproximation_of_reverseDual
    (b : GoodBONG q L (n + 1)) (c : GoodBONG q M (n + 1))
    (hvalues : ∀ i,
      c.value i = ((b.toBONG.valueUnit (Fin.rev i))⁻¹ : K))
    (halpha : ∀ i, c.alphaValue i = b.alphaValue (Fin.rev i))
    (i : Nat) (hi : i ≤ n + 1) (Y : Kˣ)
    (hY : c.IsPrefixApproximation i Y) :
    b.IsPrefixApproximation (n + 1 - i)
      (Y * c.prefixProduct (n + 1)) := by
  have hvaluesBack : ∀ j,
      b.value j = ((c.toBONG.valueUnit (Fin.rev j))⁻¹ : K) := by
    intro j
    change b.toBONG.value j =
      ((c.toBONG.valueUnit (Fin.rev j))⁻¹ : K)
    have h := hvalues (Fin.rev j)
    change c.toBONG.value (Fin.rev j) =
      ((b.toBONG.valueUnit (Fin.rev (Fin.rev j)))⁻¹ : K) at h
    simpa using (congrArg Inv.inv h).symm
  have halphaBack : ∀ j,
      b.alphaValue j = c.alphaValue (Fin.rev j) := by
    intro j
    have h := halpha (Fin.rev j)
    simpa using h.symm
  have hY' : c.IsPrefixApproximation
      (n + 1 - (n + 1 - i)) Y := by
    simpa [Nat.sub_sub_self hi] using hY
  exact c.isPrefixApproximation_reverseDual b hvaluesBack halphaBack
    (n + 1 - i) (Nat.sub_le _ _) Y hY'

/-- Existence form of Corollary 3.3, using the reverse-dual good BONG supplied
by the structural and alpha-duality laws. -/
theorem exists_reverseDual_prefixApproximation
    [Beli2006AlphaLaws.{u, v} K] [BONGStructuralLaws.{u, v} K]
    (b : GoodBONG q L (n + 1)) (i : Nat) (hi : i ≤ n + 1)
    (X : Kˣ) (hX : b.IsPrefixApproximation (n + 1 - i) X) :
    ∃ c : GoodBONG q (Lattice.dualLattice q L) (n + 1),
      b.IsReverseDualGoodBONG c ∧
      c.IsPrefixApproximation i (X * b.prefixProduct (n + 1)) := by
  rcases b.exists_reverseDual_with_alpha with
    ⟨c, hvectors, hvalues, _, halpha⟩
  exact ⟨c, hvectors,
    b.isPrefixApproximation_reverseDual c hvalues halpha i hi X hX⟩

end BONG.GoodBONG

end Bong
