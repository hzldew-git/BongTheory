/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma715AlphaPropagation

/-!
# Beli (2019), Lemma 7.15: all alpha invariants

The type-I and type-II boundary calculations are combined here with the
propagation theorem coming from Beli (2009/2010), Lemma 2.4.  Thus the alpha
invariants agree at every paper index `i ≥ s + 1`, represented below by
zero-based indices satisfying `s ≤ i.val`.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {n : Nat}

variable [DyadicDiscriminantClassLaws K]
variable [Beli2006AlphaLaws.{u, v} K]
variable [Beli2009AlphaParityLaws.{u, v} K]

/-- In the type-I branch, all alpha invariants at and after the stopping
boundary agree as `WithTop` values. -/
theorem lemma715_typeI_alpha_eq
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData b R s)
    (hsecond : b.order ⟨1, by omega⟩ =
      R - 2 * (ramificationIndex K : Int))
    (hthird : R + 1 ≤ b.order ⟨2, by omega⟩)
    (hI : Lemma714IsTypeI b R s)
    (result : GoodBONG q M (n + 3))
    (hvalues : ∀ i, result.valueUnit i =
      lemma714TypeITargetValues b s D.two_le D.le_rank i)
    (i : Fin (n + 2)) (hsi : s ≤ i.val) :
    b.alpha i = result.alpha i := by
  have hsAlpha : s < n + 2 := by omega
  have hsBoundary : s + 2 ≤ n + 3 := by omega
  have hboundary : b.alpha ⟨s, hsAlpha⟩ =
      result.alpha ⟨s, hsAlpha⟩ :=
    b.lemma715_typeI_boundary_alpha_eq R s D hsecond hthird hI
      result hvalues hsBoundary
  have htail : ∀ j : Fin (n + 3), s < j.val →
      b.valueUnit j = result.valueUnit j := by
    intro j hj
    calc
      b.valueUnit j = lemma714TypeITargetValues
          b s D.two_le D.le_rank j :=
        (lemma714TypeITargetValues_suffix b s D.two_le D.le_rank j hj.le).symm
      _ = result.valueUnit j := (hvalues j).symm
  by_cases his : i.val = s
  · have hi : i = (⟨s, hsAlpha⟩ : Fin (n + 2)) := Fin.ext his
    simpa only [hi] using hboundary
  · have hstrict : s < i.val := by omega
    exact b.alpha_eq_of_lemma715_boundary_alpha_eq_of_strict_tail
      result s hsAlpha i hstrict hboundary htail

/-- Rational form of `lemma715_typeI_alpha_eq`, matching the paper's alpha
invariants. -/
theorem lemma715_typeI_alphaValue_eq
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData b R s)
    (hsecond : b.order ⟨1, by omega⟩ =
      R - 2 * (ramificationIndex K : Int))
    (hthird : R + 1 ≤ b.order ⟨2, by omega⟩)
    (hI : Lemma714IsTypeI b R s)
    (result : GoodBONG q M (n + 3))
    (hvalues : ∀ i, result.valueUnit i =
      lemma714TypeITargetValues b s D.two_le D.le_rank i)
    (i : Fin (n + 2)) (hsi : s ≤ i.val) :
    b.alphaValue i = result.alphaValue i := by
  apply WithTop.coe_injective
  rw [b.coe_alphaValue, result.coe_alphaValue]
  exact b.lemma715_typeI_alpha_eq R s D hsecond hthird hI result
    hvalues i hsi

/-- In the type-II branch, all alpha invariants at and after the stopping
boundary agree as `WithTop` values. -/
theorem lemma715_typeII_alpha_eq
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData b R s)
    (hsecond : b.order ⟨1, by omega⟩ =
      R - 2 * (ramificationIndex K : Int))
    (hthird : R + 1 ≤ b.order ⟨2, by omega⟩)
    (hII : Lemma714IsTypeII b R s)
    (ε η : Kˣ)
    (hεUnit : IsValuationUnit K (ε : K))
    (hηUnit : IsValuationUnit K (η : K))
    (hηDefect : defectOrder (K := K) η =
      (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ))
    (result : GoodBONG q M (n + 3))
    (hvalues : ∀ i, result.valueUnit i =
      lemma714TypeIITargetValues b s D.two_le
        (Classical.choose hII) ε η i)
    (i : Fin (n + 2)) (hsi : s ≤ i.val) :
    b.alpha i = result.alpha i := by
  have hsAlpha : s < n + 2 := by omega
  have hsBoundary : s + 2 ≤ n + 3 := by omega
  have hboundary : b.alpha ⟨s, hsAlpha⟩ =
      result.alpha ⟨s, hsAlpha⟩ :=
    b.lemma715_typeII_boundary_alpha_eq R s D hsecond hthird hII
      ε η hεUnit hηUnit hηDefect result hvalues hsBoundary
  have htail : ∀ j : Fin (n + 3), s < j.val →
      b.valueUnit j = result.valueUnit j := by
    intro j hj
    calc
      b.valueUnit j = lemma714TypeIITargetValues b s D.two_le
          (Classical.choose hII) ε η j :=
        (lemma714TypeIITargetValues_suffix b s D.two_le
          (Classical.choose hII) ε η j hj).symm
      _ = result.valueUnit j := (hvalues j).symm
  by_cases his : i.val = s
  · have hi : i = (⟨s, hsAlpha⟩ : Fin (n + 2)) := Fin.ext his
    simpa only [hi] using hboundary
  · have hstrict : s < i.val := by omega
    exact b.alpha_eq_of_lemma715_boundary_alpha_eq_of_strict_tail
      result s hsAlpha i hstrict hboundary htail

/-- Rational form of `lemma715_typeII_alpha_eq`, matching the paper's alpha
invariants. -/
theorem lemma715_typeII_alphaValue_eq
    (b : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (D : Lemma714StoppingData b R s)
    (hsecond : b.order ⟨1, by omega⟩ =
      R - 2 * (ramificationIndex K : Int))
    (hthird : R + 1 ≤ b.order ⟨2, by omega⟩)
    (hII : Lemma714IsTypeII b R s)
    (ε η : Kˣ)
    (hεUnit : IsValuationUnit K (ε : K))
    (hηUnit : IsValuationUnit K (η : K))
    (hηDefect : defectOrder (K := K) η =
      (((2 * (ramificationIndex K : ℚ) - 1 : ℚ)) : WithTop ℚ))
    (result : GoodBONG q M (n + 3))
    (hvalues : ∀ i, result.valueUnit i =
      lemma714TypeIITargetValues b s D.two_le
        (Classical.choose hII) ε η i)
    (i : Fin (n + 2)) (hsi : s ≤ i.val) :
    b.alphaValue i = result.alphaValue i := by
  apply WithTop.coe_injective
  rw [b.coe_alphaValue, result.coe_alphaValue]
  exact b.lemma715_typeII_alpha_eq R s D hsecond hthird hII ε η
    hεUnit hηUnit hηDefect result hvalues i hsi

end BONG.GoodBONG

end Bong
