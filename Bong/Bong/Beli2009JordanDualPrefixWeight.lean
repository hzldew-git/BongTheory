/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009JordanFundamentalLayerFormula

/-!
# Weight orders of rescaled dual good BONGs

These are the two endpoint evaluations used in Beli (2009), Lemma 2.16.
They make the unary and non-unary prefix cases of the fundamental-layer
splitting formula available without any auxiliary law interface.
-/

namespace Bong

open Dyadic Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG.GoodBONG

/-- The weight order of a rescaled dual unary lattice. -/
theorem weightIdealOrder_rescale_dual_unary
    (b : GoodBONG q L 1) (c : Kˣ) :
    Lattice.weightIdealOrder q
        (Lattice.rescale c (Lattice.dualLattice q L)) =
      2 * ordUnit K c - b.order 0 + ramificationIndex K := by
  have hrescale := Lattice.weightIdealOrder_rescaleLattice
    q (Lattice.dualLattice q L) c
      (by simpa only [b.toBONG.length_eq_finrank] using Nat.zero_lt_one)
  rw [BONG.StrictJordanAdaptedAlignment.weightIdealOrder_dual_goodBONG_unary b]
    at hrescale
  omega

/-- The weight order of a rescaled dual non-unary lattice. -/
theorem weightIdealOrder_rescale_dual
    {p : Nat} (b : GoodBONG q L (p + 2)) (c : Kˣ) :
    (Lattice.weightIdealOrder q
        (Lattice.rescale c (Lattice.dualLattice q L)) : ℚ) =
      min
        (((2 * ordUnit K c - b.order ⟨p + 1, by omega⟩ : Int) : ℚ) +
          b.alphaValue ⟨p, by omega⟩)
        (((2 * ordUnit K c - b.order ⟨p + 1, by omega⟩ : Int) : ℚ) +
          (ramificationIndex K : ℚ)) := by
  have hrescale := Lattice.weightIdealOrder_rescaleLattice
    q (Lattice.dualLattice q L) c
      (by
        rw [← b.toBONG.length_eq_finrank]
        omega)
  have hdual :=
    BONG.StrictJordanAdaptedAlignment.weightIdealOrder_dual_goodBONG b
  have hrescaleQ :
      (Lattice.weightIdealOrder q
          (Lattice.rescale c (Lattice.dualLattice q L)) : ℚ) =
        (2 * ordUnit K c : Int) +
          (Lattice.weightIdealOrder q (Lattice.dualLattice q L) : ℚ) := by
    exact_mod_cast hrescale
  rw [hdual] at hrescaleQ
  calc
    (Lattice.weightIdealOrder q
        (Lattice.rescale c (Lattice.dualLattice q L)) : ℚ) =
        ((2 * ordUnit K c : Int) : ℚ) +
          min
            (-(b.order ⟨p + 1, by omega⟩ : ℚ) +
              b.alphaValue ⟨p, by omega⟩)
            (-(b.order ⟨p + 1, by omega⟩ : ℚ) +
              (ramificationIndex K : ℚ)) := hrescaleQ
    _ = min
          (((2 * ordUnit K c : Int) : ℚ) +
            (-(b.order ⟨p + 1, by omega⟩ : ℚ) +
              b.alphaValue ⟨p, by omega⟩))
          (((2 * ordUnit K c : Int) : ℚ) +
            (-(b.order ⟨p + 1, by omega⟩ : ℚ) +
              (ramificationIndex K : ℚ))) := by
        exact (min_add_add_left _ _ _).symm
    _ = _ := by
      apply congrArg₂ min
      · push_cast
        ring
      · push_cast
        ring

end BONG.GoodBONG

end Bong
