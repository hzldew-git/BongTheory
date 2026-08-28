/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.ResidueFieldSize
import Bong.Dyadic.QuadraticDefect

/-!
# Equal-defect product interface

This is the exact field-level statement consumed by Beli (2019), Lemma 8.1.
Its concrete dyadic proof is kept in `ResidueDefectProductProof`.
-/

namespace Bong

open Dyadic

universe u

namespace BONG

/-- The Hensel/residue calculation underlying Beli (2019), Lemma 8.1. -/
class DyadicResidueDefectProductLaws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  exists_same_defect_product_of_large_residue
      (hres : HasResidueFieldMoreThanTwoElements (K := K))
      (a : Kˣ)
      (hfinite : quadraticDefect K a ≠ ⊤)
      (hzero : quadraticDefect K a ≠ 0)
      (htwoE : quadraticDefect K a ≠
        ((2 * ramificationIndex K : Nat) : ℕ∞)) :
      ∃ b : Kˣ,
        quadraticDefect K b = quadraticDefect K a ∧
          quadraticDefect K (a * b) = quadraticDefect K a
  product_defect_strict_of_residue_two
      (hres : ¬HasResidueFieldMoreThanTwoElements (K := K))
      (a b : Kˣ)
      (heq : quadraticDefect K a = quadraticDefect K b)
      (hfinite : quadraticDefect K a ≠ ⊤) :
      quadraticDefect K a < quadraticDefect K (a * b)

end BONG

end Bong
