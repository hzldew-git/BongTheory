/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BinarySpinorMonotonicity

/-!
# M69 Beli Lemma 3.8 smoke tests
-/

namespace BongTest.M69

open Bong Bong.Dyadic

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

variable [BinarySpinorLocalLaws.{u, v} K]

example (b : BONG V q L 2) (s : Kˣ)
    (hs : (s : K) ∈ IntegerRing K) :
    beliSpinorGroup K
        (unitSquareClass K (b.binaryParameter * s ^ 2)) ≤
      beliSpinorGroup K b.binaryUnitSquareClass :=
  b.beliSpinorGroup_mul_integral_square_le s hs

variable [BinarySpinorLocalLaws.{u, u} K]

example (ε : Kˣ) (hε : IsValuationUnit K (ε : K))
    {R R' : Int}
    (ha : BONG.IsBinaryParameterAdmissible
      (uniformizerPowerUnit K R * ε))
    (hle : R ≤ R') (hmod : R' ≡ R [ZMOD 2]) :
    BONG.IsBinaryParameterAdmissible
        (uniformizerPowerUnit K R' * ε) ∧
      ordUnit K (uniformizerPowerUnit K R * ε) = R ∧
      ordUnit K (uniformizerPowerUnit K R' * ε) = R' ∧
      beliSpinorGroup K
          (unitSquareClass K (uniformizerPowerUnit K R' * ε)) ≤
        beliSpinorGroup K
          (unitSquareClass K (uniformizerPowerUnit K R * ε)) :=
  BONG.beliSpinorGroup_uniformizer_order_mono ε hε ha hle hmod

#print axioms Bong.BONG.beliSpinorGroup_mul_integral_square_le
#print axioms Bong.BONG.beliSpinorGroup_uniformizer_order_mono

end

end BongTest.M69
