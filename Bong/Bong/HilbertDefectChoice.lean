/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Dyadic.HilbertSymbol

/-!
# Hilbert partners of prescribed dyadic defect

This file contains only the low-level interface used by Beli (2019), Lemma
8.2.  It is separated from that lemma so the concrete local-field proof does
not depend on the later Beli 2003 binary-group development.
-/

namespace Bong

open Dyadic

universe u

namespace BONG

class DyadicHilbertDefectChoiceLaws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  exists_negative_same_defect_of_sum_le
      (a reference : Kˣ)
      (h : quadraticDefect K a + quadraticDefect K reference ≤
        ((2 * ramificationIndex K : Nat) : ℕ∞)) :
      ∃ b : Kˣ,
        quadraticDefect K b = quadraticDefect K reference ∧
          hilbertSymbol K a b = -1
  exists_higher_defect_negative_of_sum_lt
      (a reference : Kˣ)
      (h : quadraticDefect K a + quadraticDefect K reference <
        ((2 * ramificationIndex K : Nat) : ℕ∞)) :
      ∃ c : Kˣ,
        quadraticDefect K reference < quadraticDefect K c ∧
          hilbertSymbol K a c = -1
  hilbert_eq_neg_one_of_zero_twoE
      (a b : Kˣ)
      (h :
        (quadraticDefect K a = 0 ∧
            quadraticDefect K b =
              ((2 * ramificationIndex K : Nat) : ℕ∞)) ∨
          (quadraticDefect K a =
              ((2 * ramificationIndex K : Nat) : ℕ∞) ∧
            quadraticDefect K b = 0)) :
      hilbertSymbol K a b = -1

end BONG

end Bong
