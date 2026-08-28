/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma715Alpha

/-!
# Beli (2019), Lemma 7.15

This module assembles the three assertions of Lemma 7.15:

* equality of the order sequences from coefficient index `s` onward;
* equality of the rational alpha invariants from alpha index `s` onward;
* isometry of all corresponding diagonal prefixes, with the additional
  type-I prefix at length `s`.

The index shift is exactly the paper's one-based statement `i ≥ s + 1`.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- The complete paper-facing conclusion of Beli (2019), Lemma 7.15. -/
inductive Beli2019Lemma715Conclusion
    [DyadicDiscriminantClassLaws K]
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData b R s)
    (hnorm : Lattice.normIdeal q L = Lattice.powerIdeal (K := K) R)
    (hscale : Lattice.scaleIdeal q L ≤
      Lattice.powerIdeal (K := K)
        (R - ramificationIndex K + 1))
    (ε η : Kˣ) : Prop where
  | typeI
      (hI : Lemma714IsTypeI b R s)
      (result : GoodBONG q
        (Lattice.nonNormGeneratorLattice R hnorm hscale) (n + 3))
      (values : ∀ i, result.valueUnit i =
        lemma714TypeITargetValues b s D.two_le D.le_rank i)
      (order_eq : ∀ i, s ≤ i.val → b.order i = result.order i)
      (alpha_eq : ∀ i, s ≤ i.val →
        b.alphaValue i = result.alphaValue i)
      (prefix_isometric : ∀ (k : Nat), s ≤ k → (hk : k ≤ n + 3) →
        (b.prefixDiagonalSpace k hk).IsIsometric
          (result.prefixDiagonalSpace k hk)) :
      Beli2019Lemma715Conclusion b R s D hnorm hscale ε η
  | typeII
      (hII : Lemma714IsTypeII b R s)
      (result : GoodBONG q
        (Lattice.nonNormGeneratorLattice R hnorm hscale) (n + 3))
      (values : ∀ i, result.valueUnit i =
        lemma714TypeIITargetValues b s D.two_le
          (Classical.choose hII) ε η i)
      (order_eq : ∀ i, s ≤ i.val → b.order i = result.order i)
      (alpha_eq : ∀ i, s ≤ i.val →
        b.alphaValue i = result.alphaValue i)
      (prefix_isometric : ∀ (k : Nat), s + 1 ≤ k →
        (hk : k ≤ n + 3) →
        (b.prefixDiagonalSpace k hk).IsIsometric
          (result.prefixDiagonalSpace k hk)) :
      Beli2019Lemma715Conclusion b R s D hnorm hscale ε η

variable [DyadicDiscriminantClassLaws K]
variable [Beli2006AlphaLaws.{u, v} K]
variable [Beli2009AlphaParityLaws.{u, v} K]

/-- Enrich the order and prefix conclusions with the complete alpha assertion
of Lemma 7.15. -/
theorem Beli2019Lemma715PrefixConclusion.toLemma715Conclusion
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData b R s)
    (hnorm : Lattice.normIdeal q L = Lattice.powerIdeal (K := K) R)
    (hscale : Lattice.scaleIdeal q L ≤
      Lattice.powerIdeal (K := K)
        (R - ramificationIndex K + 1))
    (ε η : Kˣ)
    (C : Beli2019Lemma715PrefixConclusion
      b R s D hnorm hscale ε η)
    (hsecond : b.order ⟨1, by omega⟩ =
      R - 2 * (ramificationIndex K : Int))
    (hthird : R + 1 ≤ b.order ⟨2, by omega⟩)
    (hεUnit : IsValuationUnit K (ε : K))
    (hηUnit : IsValuationUnit K (η : K))
    (hηDefect : defectOrder (K := K) η =
      (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ)) :
    Beli2019Lemma715Conclusion b R s D hnorm hscale ε η := by
  cases C with
  | typeI hI result hvalues horders hprefix =>
      exact Beli2019Lemma715Conclusion.typeI hI result hvalues horders
        (fun i hi ↦ b.lemma715_typeI_alphaValue_eq R s D hsecond hthird
          hI result hvalues i hi)
        hprefix
  | typeII hII result hvalues horders hprefix =>
      exact Beli2019Lemma715Conclusion.typeII hII result hvalues horders
        (fun i hi ↦ b.lemma715_typeII_alphaValue_eq R s D hsecond hthird
          hII ε η hεUnit hηUnit hηDefect result hvalues i hi)
        hprefix

/-- A realization supplied by Lemma 7.14 satisfies all assertions of Lemma
7.15. -/
theorem Beli2019Lemma714Realization.toLemma715Conclusion
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData b R s)
    (hnorm : Lattice.normIdeal q L = Lattice.powerIdeal (K := K) R)
    (hscale : Lattice.scaleIdeal q L ≤
      Lattice.powerIdeal (K := K)
        (R - ramificationIndex K + 1))
    (ε η : Kˣ)
    (H : Beli2019Lemma714Realization b R s D hnorm hscale ε η)
    (hsecond : b.order ⟨1, by omega⟩ =
      R - 2 * (ramificationIndex K : Int))
    (hthird : R + 1 ≤ b.order ⟨2, by omega⟩)
    (hεUnit : IsValuationUnit K (ε : K))
    (hηUnit : IsValuationUnit K (η : K))
    (hηDefect : defectOrder (K := K) η =
      (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ)) :
    Beli2019Lemma715Conclusion b R s D hnorm hscale ε η := by
  have horders := H.toLemma715OrderConclusion b R s D hnorm hscale ε η
    hεUnit hηUnit
  have hprefix := horders.toPrefixConclusion b R s D hnorm hscale ε η
  exact hprefix.toLemma715Conclusion b R s D hnorm hscale ε η
    hsecond hthird hεUnit hηUnit hηDefect

/-- Paper-facing pipeline: the complete conclusion of Lemma 7.14 immediately
yields the complete conclusion of Lemma 7.15. -/
theorem Beli2019Lemma714Conclusion.toLemma715Conclusion
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData b R s)
    (hnorm : Lattice.normIdeal q L = Lattice.powerIdeal (K := K) R)
    (hscale : Lattice.scaleIdeal q L ≤
      Lattice.powerIdeal (K := K)
        (R - ramificationIndex K + 1))
    (ε η : Kˣ)
    (C : Beli2019Lemma714Conclusion b R s D hnorm hscale ε η)
    (hsecond : b.order ⟨1, by omega⟩ =
      R - 2 * (ramificationIndex K : Int))
    (hthird : R + 1 ≤ b.order ⟨2, by omega⟩)
    (hεUnit : IsValuationUnit K (ε : K))
    (hηUnit : IsValuationUnit K (η : K))
    (hηDefect : defectOrder (K := K) η =
      (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ)) :
    Beli2019Lemma715Conclusion b R s D hnorm hscale ε η :=
  C.realization.toLemma715Conclusion b R s D hnorm hscale ε η
    hsecond hthird hεUnit hηUnit hηDefect

end BONG.GoodBONG

end Bong
