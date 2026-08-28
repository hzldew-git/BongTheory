/- Carrier inclusions for prefixes of orthogonal decompositions. -/
import Bong.Lattice.OrthogonalDecompositionPrefix

namespace Bong

open Dyadic Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M : Lattice K V} {t : Nat}

namespace Lattice.OrthogonalDecomposition

/-- Every component before a numerical cut is contained in the carrier of
that prefix. -/
theorem component_carrier_le_prefixCarrier
    (D : OrthogonalDecomposition q L t) (i : Fin t) {k : Nat}
    (hi : i.val < k) :
    (D.component i).carrier ≤ D.prefixCarrier k := by
  unfold prefixCarrier
  exact le_iSup (fun j : D.PrefixIndex k ↦ (D.component j.1).carrier)
    ⟨i, hi⟩

/-- Prefix carriers are monotone in the numerical cut. -/
theorem prefixCarrier_mono
    (D : OrthogonalDecomposition q L t) {k l : Nat} (hkl : k ≤ l) :
    D.prefixCarrier k ≤ D.prefixCarrier l := by
  unfold prefixCarrier
  apply iSup_le
  intro i
  exact D.component_carrier_le_prefixCarrier i.1 (i.2.trans_le hkl)

/-- A componentwise containment criterion for prefix carriers of two
decompositions of the same ambient quadratic space. -/
theorem prefixCarrier_le_of_component_le
    (D : OrthogonalDecomposition q L t)
    (E : OrthogonalDecomposition q M t) (k l : Nat)
    (h : ∀ i : Fin t, i.val < k →
      (D.component i).carrier ≤ E.prefixCarrier l) :
    D.prefixCarrier k ≤ E.prefixCarrier l := by
  unfold prefixCarrier
  apply iSup_le
  intro i
  exact h i.1 i.2

/-- A componentwise containment criterion allowing the two orthogonal
decompositions to have different numbers of components. -/
theorem prefixCarrier_le_of_component_le_general
    {s : Nat}
    (D : OrthogonalDecomposition q L t)
    (E : OrthogonalDecomposition q M s) (k l : Nat)
    (h : ∀ i : Fin t, i.val < k →
      (D.component i).carrier ≤ E.prefixCarrier l) :
    D.prefixCarrier k ≤ E.prefixCarrier l := by
  unfold prefixCarrier
  apply iSup_le
  intro i
  exact h i.1 i.2

/-- Prefix carriers are equal when all component carriers before the cut
are equal. -/
theorem prefixCarrier_eq_of_component_carrier_eq
    (D : OrthogonalDecomposition q L t)
    (E : OrthogonalDecomposition q M t) (k : Nat)
    (h : ∀ i : Fin t, i.val < k →
      (D.component i).carrier = (E.component i).carrier) :
    D.prefixCarrier k = E.prefixCarrier k := by
  apply le_antisymm
  · apply D.prefixCarrier_le_of_component_le E k k
    intro i hi
    rw [h i hi]
    exact E.component_carrier_le_prefixCarrier i hi
  · apply E.prefixCarrier_le_of_component_le D k k
    intro i hi
    rw [← h i hi]
    exact D.component_carrier_le_prefixCarrier i hi

end Lattice.OrthogonalDecomposition

end Bong
