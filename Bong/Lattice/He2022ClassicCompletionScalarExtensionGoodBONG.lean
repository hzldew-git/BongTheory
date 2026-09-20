/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Lattice.He2022ClassicCompletionBONGIsometry
import Bong.Bong.GoodMap

/-!
# A good BONG on the literal finite-completion scalar extension

The mapped-value realization can be transported through the proved integral
isometry to the tensor scalar-extension lattice itself. This constructs a
good BONG there without asserting literal equality with a separately
realized diagonal lattice in a common ambient space.
-/

open scoped NumberField TensorProduct

namespace Bong.HeClassic2024NumberFieldScalarExtension

open Dyadic

universe u v w

variable {K : Type u} {E : Type v}
  [Field K] [Field E] [NumberField K] [NumberField E]
  [Algebra K E] [FiniteDimensional K E]

/-- In the corrected even classic-universal case, the literal scalar
extension carries a good BONG with the mapped exact coefficient values.
The construction chooses an integral isometry to a standard diagonal
realization; it does not assert literal equality with that realization. -/
theorem completionScalarExtension_hasGoodBONG_of_evenUniversal
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 E))
    [P.asIdeal.LiesOver p.asIdeal]
    (hp : NumberFieldCompletion.IsDyadic p) :
    letI := NumberFieldCompletion.dyadicContext p hp
    let hpP := HeClassic2024NumberFieldBONGBridge.isDyadic_of_liesOver p P hp
    letI := NumberFieldCompletion.dyadicContext P hpP
    letI := HeClassic2024NumberFieldLocalExtension.CompletionLiesOver.instAlgebra
      (p := p) (P := P)
    ∀ {V : Type w} [AddCommGroup V] [Module (p.adicCompletion K) V]
      [FiniteDimensional (p.adicCompletion K) V]
      {q : QuadraticSpace (p.adicCompletion K) V}
      {L : Lattice (p.adicCompletion K) V} {n : Nat}
      (lower : BONG.GoodBONG q L (n + 3))
      (_ : 2 ≤ n) (_ : Even n)
      (_ : Lattice.IsClassicIntegral q L)
      (_ : Lattice.IsClassicNUniversal.{u, w, u} q L n),
      ∃ upper : BONG.GoodBONG
          (q.scalarExtension (E := P.adicCompletion E))
          (Lattice.scalarExtension (E := P.adicCompletion E) L) (n + 3),
        ∀ i, upper.valueUnit i = Units.map
          (HeClassic2024NumberFieldLocalExtension.completionMap p P)
            (lower.valueUnit i) := by
  letI := NumberFieldCompletion.dyadicContext p hp
  let hpP := HeClassic2024NumberFieldBONGBridge.isDyadic_of_liesOver p P hp
  letI := NumberFieldCompletion.dyadicContext P hpP
  letI := HeClassic2024NumberFieldLocalExtension.CompletionLiesOver.instAlgebra
    (p := p) (P := P)
  dsimp only
  intro V _ _ _ q L n lower hn hnEven hClassic hUniversal
  obtain ⟨R, hGood, hValues⟩ :=
    HeClassic2024NumberFieldBONGBridge.goodBONG_mappedValues_haveRealization
      p P hp lower
  obtain ⟨f⟩ := completionScalarExtension_isIsometric_diagonalRealization_of_evenUniversal
    p P hp lower R hn hnEven hClassic hUniversal
  let realized : BONG.GoodBONG
      (BONG.coefficientDiagonalSpace
        (fun i ↦ Units.map
          (HeClassic2024NumberFieldLocalExtension.completionMap p P)
            (lower.valueUnit i))) R.lattice (n + 3) :=
    ⟨R.bong, hGood⟩
  let upper := realized.mapLatticeIsometry f.symm
  refine ⟨upper, ?_⟩
  intro i
  change (realized.mapLatticeIsometry f.symm).valueUnit i = _
  rw [BONG.GoodBONG.valueUnit_mapLatticeIsometry]
  change R.bong.valueUnit i = _
  exact hValues i

end Bong.HeClassic2024NumberFieldScalarExtension
