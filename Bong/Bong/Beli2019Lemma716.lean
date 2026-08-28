/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma715
import Bong.Bong.Beli2019Lemma716LongComplete

/-!
# Beli (2019), Lemma 7.16

This module assembles the four representation conditions proved in the
preceding files.  The conclusion retains the type-I/type-II realization from
Lemmas 7.14 and 7.15, together with the complete revised condition package
for the constructed BONG and the comparison lattice.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L N : Lattice K V} {n : Nat}

/-- The complete paper-facing conclusion of Beli (2019), Lemma 7.16. -/
inductive Beli2019Lemma716Conclusion
    [DyadicDiscriminantClassLaws K]
    (a : GoodBONG q L (n + 3)) (c : GoodBONG q N (n + 3))
    (R : Int) (s : Nat) (D : Lemma714StoppingData a R s)
    (hnorm : Lattice.normIdeal q L = Lattice.powerIdeal (K := K) R)
    (hscale : Lattice.scaleIdeal q L ≤
      Lattice.powerIdeal (K := K)
        (R - ramificationIndex K + 1))
    (ε η : Kˣ) : Prop where
  | typeI
      (hI : Lemma714IsTypeI a R s)
      (result : GoodBONG q
        (Lattice.nonNormGeneratorLattice R hnorm hscale) (n + 3))
      (values : ∀ i, result.valueUnit i =
        lemma714TypeITargetValues a s D.two_le D.le_rank i)
      (conditions : RepresentationConditionsPrime result c le_rfl) :
      Beli2019Lemma716Conclusion a c R s D hnorm hscale ε η
  | typeII
      (hII : Lemma714IsTypeII a R s)
      (result : GoodBONG q
        (Lattice.nonNormGeneratorLattice R hnorm hscale) (n + 3))
      (values : ∀ i, result.valueUnit i =
        lemma714TypeIITargetValues a s D.two_le
          (Classical.choose hII) ε η i)
      (conditions : RepresentationConditionsPrime result c le_rfl) :
      Beli2019Lemma716Conclusion a c R s D hnorm hscale ε η

variable [laws : DyadicDiscriminantClassLaws K]
variable [Beli2006AlphaLaws.{u, v} K]
variable [Beli2009AlphaParityLaws.{u, v} K]
variable [DyadicUnramifiedNormLaws K]
variable [HilbertSymbolLaws K]
variable [PerfectResidueFieldLaws K]
variable [DyadicAlternatingEndpointTowerRepresentationLaws K]

/-- Branch-independent assembly of the four revised conditions in the
type-I case.  The target lattice of `result` is intentionally arbitrary:
the proof of Lemma 7.16 uses only its displayed coefficient sequence and
the conclusions of Lemma 7.15. -/
theorem lemma716_typeI_representationConditionsPrime
    {M : Lattice K V}
    (a : GoodBONG q L (n + 3)) (result : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData a R s)
    (hfirst : a.order 0 = R)
    (hsecond : a.order 1 =
      R - 2 * (ramificationIndex K : Int))
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (hdiscriminant : a.toBONG.adjacentUnitSquareClass
      (0 : Fin (n + 3)) (by simp) = unitSquareClass K
        (lemma712DiscriminantParameter (K := K)))
    (hnormStrict : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (hac : RepresentationConditionsPrime a c le_rfl)
    (hI : Lemma714IsTypeI a R s)
    (hvalues : ∀ i, result.valueUnit i =
      lemma714TypeITargetValues a s D.two_le D.le_rank i)
    (horders : ∀ i, s ≤ i.val → a.order i = result.order i)
    (halphas : ∀ i, s ≤ i.val →
      a.alphaValue i = result.alphaValue i)
    (hprefix : ∀ (k : Nat), s ≤ k → (hk : k ≤ n + 3) →
      (a.prefixDiagonalSpace k hk).IsIsometric
        (result.prefixDiagonalSpace k hk)) :
    RepresentationConditionsPrime result c le_rfl := by
  have horder := a.lemma716_typeI_orderCondition result c R s D
    hfirst hsecond hthird hdiscriminant hnormStrict hac hI hvalues horders
  have hdefect := a.lemma716_typeI_defectCondition result c R s D
    hfirst hsecond hthird hnormStrict hac hI hdiscriminant hvalues horder
      horders halphas hprefix
  have hcentral :=
    a.lemma716_typeI_centralRepresentationConditionsPrime result c R s D
      hfirst hsecond hthird hnormStrict hac hI hdiscriminant hvalues horder
        hdefect horders halphas hprefix
  have hlong := a.lemma716_typeI_longRepresentationConditions result c R s D
    hfirst hsecond hthird hnormStrict hac hvalues horders hprefix
  exact ⟨horder, hdefect, hcentral, hlong⟩

/-- Branch-independent assembly of the four revised conditions in the
type-II case. -/
theorem lemma716_typeII_representationConditionsPrime
    {M : Lattice K V}
    (a : GoodBONG q L (n + 3)) (result : GoodBONG q M (n + 3))
    (c : GoodBONG q N (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData a R s)
    (hfirst : a.order 0 = R)
    (hsecond : a.order 1 =
      R - 2 * (ramificationIndex K : Int))
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (hdiscriminant : a.toBONG.adjacentUnitSquareClass
      (0 : Fin (n + 3)) (by simp) = unitSquareClass K
        (lemma712DiscriminantParameter (K := K)))
    (hnormStrict : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (hac : RepresentationConditionsPrime a c le_rfl)
    (hII : Lemma714IsTypeII a R s) (ε η : Kˣ)
    (hεUnit : IsValuationUnit K (ε : K))
    (hηUnit : IsValuationUnit K (η : K))
    (hηDefect : defectOrder (K := K) η =
      (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ))
    (hvalues : ∀ i, result.valueUnit i =
      lemma714TypeIITargetValues a s D.two_le
        (Classical.choose hII) ε η i)
    (horders : ∀ i, s ≤ i.val → a.order i = result.order i)
    (halphas : ∀ i, s ≤ i.val →
      a.alphaValue i = result.alphaValue i)
    (hprefix : ∀ (k : Nat), s + 1 ≤ k → (hk : k ≤ n + 3) →
      (a.prefixDiagonalSpace k hk).IsIsometric
        (result.prefixDiagonalSpace k hk)) :
    RepresentationConditionsPrime result c le_rfl := by
  have horder := a.lemma716_typeII_orderCondition result c R s D
    hfirst hsecond hthird hdiscriminant hnormStrict hac hII ε η hεUnit
      hηUnit hvalues horders
  have hdefect := a.lemma716_typeII_defectCondition result c R s D
    hfirst hsecond hthird hnormStrict hac hII ε η hεUnit hηUnit hηDefect
      hvalues horder horders halphas hprefix
  have hcentral :=
    a.lemma716_typeII_centralRepresentationConditionsPrime result c R s D
      hfirst hthird hnormStrict hac hII ε η hεUnit hηUnit hvalues horder
        hdefect horders halphas hprefix
  have hlong := a.lemma716_typeII_longRepresentationConditions result c
    R s D hthird hac hII ε η hεUnit hηUnit hvalues horders hprefix
  exact ⟨horder, hdefect, hcentral, hlong⟩

/-- The complete conclusion of Lemma 7.15 satisfies all four revised
representation conditions of Lemma 7.16. -/
theorem Beli2019Lemma715Conclusion.toLemma716Conclusion
    (a : GoodBONG q L (n + 3)) (c : GoodBONG q N (n + 3))
    (R : Int) (s : Nat) (D : Lemma714StoppingData a R s)
    (hnorm : Lattice.normIdeal q L = Lattice.powerIdeal (K := K) R)
    (hscale : Lattice.scaleIdeal q L ≤
      Lattice.powerIdeal (K := K)
        (R - ramificationIndex K + 1))
    (ε η : Kˣ)
    (H : Beli2019Lemma715Conclusion a R s D hnorm hscale ε η)
    (hfirst : a.order 0 = R)
    (hsecond : a.order 1 =
      R - 2 * (ramificationIndex K : Int))
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (hdiscriminant : a.toBONG.adjacentUnitSquareClass
      (0 : Fin (n + 3)) (by simp) = unitSquareClass K
        (lemma712DiscriminantParameter (K := K)))
    (hnormStrict : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (hac : RepresentationConditionsPrime a c le_rfl)
    (hεUnit : IsValuationUnit K (ε : K))
    (hηUnit : IsValuationUnit K (η : K))
    (hηDefect : defectOrder (K := K) η =
      (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ)) :
    Beli2019Lemma716Conclusion a c R s D hnorm hscale ε η := by
  cases H with
  | typeI hI result hvalues horders halphas hprefix =>
      exact Beli2019Lemma716Conclusion.typeI hI result hvalues
        (a.lemma716_typeI_representationConditionsPrime result c R s D
          hfirst hsecond hthird hdiscriminant hnormStrict hac hI hvalues
            horders halphas hprefix)
  | typeII hII result hvalues horders halphas hprefix =>
      exact Beli2019Lemma716Conclusion.typeII hII result hvalues
        (a.lemma716_typeII_representationConditionsPrime result c R s D
          hfirst hsecond hthird hdiscriminant hnormStrict hac hII ε η
            hεUnit hηUnit hηDefect hvalues horders halphas hprefix)

/-- Paper-facing bridge from the output of Lemma 7.14 to Lemma 7.16. -/
theorem Beli2019Lemma714Conclusion.toLemma716Conclusion
    (a : GoodBONG q L (n + 3)) (c : GoodBONG q N (n + 3))
    (R : Int) (s : Nat) (D : Lemma714StoppingData a R s)
    (hnorm : Lattice.normIdeal q L = Lattice.powerIdeal (K := K) R)
    (hscale : Lattice.scaleIdeal q L ≤
      Lattice.powerIdeal (K := K)
        (R - ramificationIndex K + 1))
    (ε η : Kˣ)
    (C : Beli2019Lemma714Conclusion a R s D hnorm hscale ε η)
    (hfirst : a.order 0 = R)
    (hsecond : a.order 1 =
      R - 2 * (ramificationIndex K : Int))
    (hthird : R + 1 ≤ a.order ⟨2, by omega⟩)
    (hdiscriminant : a.toBONG.adjacentUnitSquareClass
      (0 : Fin (n + 3)) (by simp) = unitSquareClass K
        (lemma712DiscriminantParameter (K := K)))
    (hnormStrict : Lattice.normIdeal q N < Lattice.normIdeal q L)
    (hac : RepresentationConditionsPrime a c le_rfl)
    (hεUnit : IsValuationUnit K (ε : K))
    (hηUnit : IsValuationUnit K (η : K))
    (hηDefect : defectOrder (K := K) η =
      (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ)) :
    Beli2019Lemma716Conclusion a c R s D hnorm hscale ε η := by
  have H := C.toLemma715Conclusion a R s D hnorm hscale ε η hsecond hthird
    hεUnit hηUnit hηDefect
  exact H.toLemma716Conclusion a c R s D hnorm hscale ε η hfirst hsecond
    hthird hdiscriminant hnormStrict hac hεUnit hηUnit hηDefect

end BONG.GoodBONG

end Bong
