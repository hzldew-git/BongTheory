/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Lattice.He2022ClassicCompletionLatticeScalarExtension
import Bong.Lattice.He2022ClassicScalarExtensionBONGIsometry

/-!
# Mapped BONG isometry at actual finite completions

This specializes the generic mapped-value BONG isometry to the continuous
field embedding of finite number-field completions. The lower and upper
basis-lattice identifications remain explicit premises.
-/

open scoped NumberField TensorProduct

namespace Bong.HeClassic2024NumberFieldScalarExtension

open Dyadic

universe u v w

variable {K : Type u} {E : Type v}
  [Field K] [Field E] [NumberField K] [NumberField E]
  [Algebra K E] [FiniteDimensional K E]

/-- At actual finite completions, the mapped diagonal realization is
isometric to the literal scalar extension whenever the two displayed
BONGs are integral bases. This does not establish either basis hypothesis. -/
theorem completionScalarExtension_isIsometric_diagonalRealization
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
      {L : Lattice (p.adicCompletion K) V} {m : Nat}
      (b : BONG V q L (m + 1))
      (R : BONG.DiagonalBONGRealization (K := P.adicCompletion E)
        (fun i ↦ Units.map
          (HeClassic2024NumberFieldLocalExtension.completionMap p P)
            (b.valueUnit i))),
      L = Lattice.basisLattice b.basis →
      Monotone (fun i : Fin (m + 1) ↦ R.bong.order i) →
      Lattice.IsIsometric (q.scalarExtension (E := P.adicCompletion E))
        (BONG.coefficientDiagonalSpace
          (fun i ↦ Units.map
            (HeClassic2024NumberFieldLocalExtension.completionMap p P)
              (b.valueUnit i)))
        (Lattice.scalarExtension (E := P.adicCompletion E) L) R.lattice := by
  letI := NumberFieldCompletion.dyadicContext p hp
  let hpP := HeClassic2024NumberFieldBONGBridge.isDyadic_of_liesOver p P hp
  letI := NumberFieldCompletion.dyadicContext P hpP
  letI := HeClassic2024NumberFieldLocalExtension.CompletionLiesOver.instAlgebra
    (p := p) (P := P)
  dsimp only
  intro V _ _ _ q L m b R hLower hMono
  have hIntegral : ∀ a : IntegerRing (p.adicCompletion K),
      Dyadic.IsIntegral (P.adicCompletion E)
        (algebraMap (p.adicCompletion K) (P.adicCompletion E)
          (a : p.adicCompletion K)) := by
    intro a
    simpa only [RingHom.algebraMap_toAlgebra] using
      (completionMap_preserves_integerRing p P hp a)
  exact Bong.Lattice.scalarExtension_isIsometric_diagonalRealization
    b R hIntegral hLower (fun i j hij ↦ hMono hij)

/-- In the corrected even classic-universal range, the lower good BONG and
its mapped diagonal realization are isometric after actual finite completion.
The separately specified upper lattice is not identified here. -/
theorem completionScalarExtension_isIsometric_diagonalRealization_of_evenUniversal
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
      (R : BONG.DiagonalBONGRealization (K := P.adicCompletion E)
        (fun i ↦ Units.map
          (HeClassic2024NumberFieldLocalExtension.completionMap p P)
            (lower.valueUnit i)))
      (_ : 2 ≤ n) (_ : Even n)
      (_ : Lattice.IsClassicIntegral q L)
      (_ : Lattice.IsClassicNUniversal.{u, w, u} q L n),
      Lattice.IsIsometric (q.scalarExtension (E := P.adicCompletion E))
        (BONG.coefficientDiagonalSpace
          (fun i ↦ Units.map
            (HeClassic2024NumberFieldLocalExtension.completionMap p P)
              (lower.valueUnit i)))
        (Lattice.scalarExtension (E := P.adicCompletion E) L) R.lattice := by
  letI := NumberFieldCompletion.dyadicContext p hp
  let hpP := HeClassic2024NumberFieldBONGBridge.isDyadic_of_liesOver p P hp
  letI := NumberFieldCompletion.dyadicContext P hpP
  letI := HeClassic2024NumberFieldLocalExtension.CompletionLiesOver.instAlgebra
    (p := p) (P := P)
  dsimp only
  intro V _ _ _ q L n lower R hn hnEven hClassic hUniversal
  letI : QuadraticDefectLaws (p.adicCompletion K) :=
    quadraticDefectLawsOfHensel (p.adicCompletion K)
  letI : HilbertSymbolLaws (p.adicCompletion K) :=
    Dyadic.hilbertSymbolLawsProved
  letI : DyadicDiscriminantClassLaws (p.adicCompletion K) :=
    Dyadic.dyadicDiscriminantClassLawsProved
  have hLower := lower.he2022ClassicCorollary63_even
    hn hnEven hClassic hUniversal
  have hLowerMono := lower.he2022ClassicCorollary63_even_order_monotone
    hn hnEven hClassic hUniversal
  have hUpperMono :=
    HeClassic2024NumberFieldBONGBridge.mappedValues_order_monotone_of_lower
      p P hp lower R hLowerMono
  exact completionScalarExtension_isIsometric_diagonalRealization
    p P hp lower.toBONG R hLower hUpperMono

end Bong.HeClassic2024NumberFieldScalarExtension
