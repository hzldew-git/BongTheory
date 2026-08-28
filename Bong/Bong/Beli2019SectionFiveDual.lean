/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFiveDefectEqual
import Bong.Bong.Beli2019DefectConditionDual
import Bong.Lattice.DeterminantBasis

/-!
# Beli (2019), Section 5: the swapped reverse-dual index-p inclusion

The reductions in Section 5.2 repeatedly replace an inclusion `N <= M` by
the swapped inclusion `M# <= N#`.  This file records that this is again an
index-uniformizer inclusion.  Keeping the statement at the bundled-lattice
level prevents the right-hand calculations in conditions (ii)--(iv) from
silently assuming that duality preserves, rather than reverses, inclusion.
-/

namespace Bong

open Dyadic

universe u v

namespace Beli2019IndexPInclusion

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V}

/-- An index-`p` inclusion remains an index-`p` inclusion after reversing
the lattice order by integral duality. -/
theorem reverseDual (h : Beli2019IndexPInclusion q M N) :
    Beli2019IndexPInclusion q (Lattice.dualLattice q N)
      (Lattice.dualLattice q M) where
  lattice_le := Lattice.dualLattice_antitone q h.lattice_le
  volumeOrder_eq := by
    rw [Lattice.volumeOrder_dualLattice,
      Lattice.volumeOrder_dualLattice, h.volumeOrder_eq]
    omega

end Beli2019IndexPInclusion

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V} {n : Nat}

/-- All identities attached to the swapped reverse-dual pair used in
Section 5.2.  The names `sourceDual` and `targetDual` refer to the direction
of the swapped inclusion: the former is a BONG of `N#`, and the latter a
BONG of `M#`. -/
structure Beli2019SectionFiveReverseDualData
    (a : GoodBONG q M (n + 1)) (b : GoodBONG q N (n + 1))
    (inclusion : Beli2019IndexPInclusion q M N) where
  sourceDual : GoodBONG q (Lattice.dualLattice q N) (n + 1)
  targetDual : GoodBONG q (Lattice.dualLattice q M) (n + 1)
  sourceValues (j : Fin (n + 1)) :
    sourceDual.valueUnit j = (b.valueUnit (Fin.rev j))⁻¹
  targetValues (j : Fin (n + 1)) :
    targetDual.valueUnit j = (a.valueUnit (Fin.rev j))⁻¹
  sourceOrder (j : Fin (n + 1)) :
    sourceDual.order j = -b.order (Fin.rev j)
  targetOrder (j : Fin (n + 1)) :
    targetDual.order j = -a.order (Fin.rev j)
  sourceAlpha (j : Fin n) :
    sourceDual.alphaValue j = b.alphaValue (Fin.rev j)
  targetAlpha (j : Fin n) :
    targetDual.alphaValue j = a.alphaValue (Fin.rev j)
  truncatedPrefixDefect
      (p r : Nat) (hp : p ≤ n + 1) (hr : r ≤ n + 1)
      (epsilon : Kˣ) :
    sourceDual.truncatedPrefixDefect targetDual epsilon p r =
      a.truncatedPrefixDefect b epsilon (n + 1 - r) (n + 1 - p)
  lemma51 : Lattice.Beli2019Lemma51Data q
    (Lattice.dualLattice q N) (Lattice.dualLattice q M)

/-- Reverse-dual good BONG existence together with the concrete dual
index-`p` inclusion supplies the complete data above. -/
theorem exists_sectionFiveReverseDualData
    [Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    (a : GoodBONG q M (n + 1)) (b : GoodBONG q N (n + 1))
    (inclusion : Beli2019IndexPInclusion q M N) :
    Nonempty (Beli2019SectionFiveReverseDualData a b inclusion) := by
  rcases a.exists_reverseDual_with_alpha with
    ⟨aDual, _haVectors, haValues, haOrders, haAlpha⟩
  rcases b.exists_reverseDual_with_alpha with
    ⟨bDual, _hbVectors, hbValues, hbOrders, hbAlpha⟩
  have haUnits : ∀ j,
      aDual.valueUnit j = (a.valueUnit (Fin.rev j))⁻¹ := by
    intro j
    apply Units.ext
    exact haValues j
  have hbUnits : ∀ j,
      bDual.valueUnit j = (b.valueUnit (Fin.rev j))⁻¹ := by
    intro j
    apply Units.ext
    exact hbValues j
  exact ⟨{
    sourceDual := bDual
    targetDual := aDual
    sourceValues := hbUnits
    targetValues := haUnits
    sourceOrder := hbOrders
    targetOrder := haOrders
    sourceAlpha := hbAlpha
    targetAlpha := haAlpha
    truncatedPrefixDefect := by
      intro p r hp hr epsilon
      exact truncatedPrefixDefect_reverseDual_swap_general
        a b aDual bDual haUnits hbUnits haAlpha hbAlpha
          p r hp hr epsilon
    lemma51 := Lattice.beli2019Lemma51Data q
      (Lattice.dualLattice q N) (Lattice.dualLattice q M)
        inclusion.reverseDual
  }⟩

namespace Beli2019SectionFiveReverseDualData

/-- A pointwise defect certificate for the swapped reverse-dual inclusion
at the complementary boundary gives a direct certificate for the original
inclusion.  This is the certificate-level form of the reverse-dual step in
the proof of condition 2.1(ii). -/
theorem originalCertificate_of_reverse
    [Beli2006AlphaLaws.{u, v} K]
    {a : GoodBONG q M (n + 1)} {b : GoodBONG q N (n + 1)}
    {inclusion : Beli2019IndexPInclusion q M N}
    (D : Beli2019SectionFiveReverseDualData a b inclusion)
    (i : RepresentationIndex (n + 1) (n + 1))
    (C : Beli2019SectionFiveDefectCertificate
      D.sourceDual D.targetDual i.reverse) :
    Beli2019SectionFiveDefectCertificate a b i := by
  apply Beli2019SectionFiveDefectCertificate.direct
  have hDual := C.discharge
  have hAlpha := a.representationAlphaValue_reverseDual_swap b
    D.targetDual D.sourceDual D.targetOrder D.sourceOrder
      D.truncatedPrefixDefect i
  have hComparison := D.truncatedPrefixDefect
    i.reverse.val i.reverse.val
      (Nat.le_of_lt i.reverse.lt_large)
      (Nat.le_of_lt i.reverse.lt_large) 1
  have hBoundary : n + 1 - i.reverse.val = i.val := by
    simp only [RepresentationIndex.reverse_val]
    have hpos := i.pos
    have hlt := i.lt_large
    omega
  rw [hBoundary] at hComparison
  calc
    (a.representationAlphaValue b i : WithTop ℚ) =
        (D.sourceDual.representationAlphaValue D.targetDual i.reverse :
          WithTop ℚ) := congrArg (fun x : ℚ => (x : WithTop ℚ)) hAlpha.symm
    _ ≤ D.sourceDual.truncatedPrefixDefect D.targetDual
        1 i.reverse.val i.reverse.val := hDual
    _ = a.truncatedPrefixDefect b 1 i.val i.val := hComparison

end Beli2019SectionFiveReverseDualData

end BONG.GoodBONG

end Bong
