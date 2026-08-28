/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma74
import Bong.Bong.Beli2019Lemma79EvenAssembly

/-!
# Beli (2019), Lemma 7.9(ii), case 3: the source plateau

Lemma 7.4(iii) identifies the capped alternating self-prefix defect on an
even constant-order plateau with its final alpha value.  Consequently the
paper's remaining arithmetic estimate `B_i <= beta_i` is exactly the input
needed for the source half of case 3.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V} {n : Nat}

/-- On an even source-order plateau, the capped alternating prefix is the
alpha value at its right endpoint. -/
theorem even_selfCapped_eq_alpha_of_plateau
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q M (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiTwo : 2 <= i.val) (hiNext : i.val + 1 < n + 2)
    (hiEven : Even i.val)
    (hplateau : b.orderSequence.entryOrZero 0 =
      b.orderSequence.entryOrZero i.val) :
    b.truncatedPrefixDefect b ((-1) ^ (i.val / 2)) 0 i.val =
      (b.alphaValue ⟨i.val - 1, by omega⟩ : WithTop ℚ) := by
  let first : Fin (n + 1) := ⟨0, by omega⟩
  let last : Fin (n + 1) := ⟨i.val, by omega⟩
  have horder : b.order first.castSucc = b.order last.castSucc := by
    rw [← b.orderSequence_entryOrZero_eq_order first.castSucc,
      ← b.orderSequence_entryOrZero_eq_order last.castSucc]
    change b.orderSequence.entryOrZero 0 =
      b.orderSequence.entryOrZero i.val
    exact hplateau
  have h74 := b.beli2019Lemma74_iii first last
    (by change first.val < last.val; simp only [first, last]; omega)
    (by simpa only [first, last, Nat.sub_zero] using hiEven)
    horder
  dsimp only at h74
  have hdefect := h74.1.1
  have hcritical := h74.1.2
  simp only [first, last, Nat.sub_zero] at hdefect hcritical
  rw [hdefect]
  exact congrArg (fun x : ℚ => (x : WithTop ℚ)) hcritical

/-- The source self-prefix estimate follows from the paper's scalar
inequality `B_i <= beta_i` on a constant-order plateau. -/
theorem lemma79_even_sourceCapped_of_plateau
    [Beli2006AlphaLaws.{u, v} K]
    (b : GoodBONG q M (n + 2)) (c : GoodBONG q N (n + 2))
    (i : RepresentationIndex (n + 2) (n + 2))
    (hiTwo : 2 <= i.val) (hiNext : i.val + 1 < n + 2)
    (hiEven : Even i.val)
    (hplateau : b.orderSequence.entryOrZero 0 =
      b.orderSequence.entryOrZero i.val)
    (hbeta : b.representationAlphaValue c i <=
      b.alphaValue ⟨i.val - 1, by omega⟩) :
    (b.representationAlphaValue c i : WithTop ℚ) <=
      b.truncatedPrefixDefect b ((-1) ^ (i.val / 2)) 0 i.val := by
  rw [b.even_selfCapped_eq_alpha_of_plateau i hiTwo hiNext hiEven hplateau]
  exact_mod_cast hbeta

end BONG.GoodBONG

end Bong
