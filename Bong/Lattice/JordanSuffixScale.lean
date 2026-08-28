import Bong.Lattice.OrthogonalDecompositionSuffixProduct
import Bong.Lattice.OrthogonalDecompositionIdeals
import Bong.Lattice.BlockProductOrthogonalDecomposition

/-!
# The scale of an exact Jordan suffix
-/

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {t n k : Nat}

/-- The first Jordan scale generates the scale ideal of every nonempty exact
suffix. -/
theorem scaleIdeal_suffixQuadraticSublattice
    (J : JordanDecomposition q L t) (hkn : k + (n + 1) = t) :
    scaleIdeal
        (J.toOrthogonalDecomposition.suffixQuadraticSublattice k).space
        (J.toOrthogonalDecomposition.suffixQuadraticSublattice k).lattice =
      principalIdeal (K := K)
        (J.scaleGenerator ⟨k, by omega⟩ : K) := by
  let D := J.toOrthogonalDecomposition
  let C := D.suffixBlockCarrier hkn
  let qs := D.suffixBlockSpace hkn
  let Ls := D.suffixBlockLattice hkn
  let P := BONG.blockProductOrthogonalDecomposition C qs Ls
  let f := D.suffixBlockProductIsometry hkn
  have hcomponent : ∀ z : Fin (n + 1),
      scaleIdeal (P.component z).space (P.component z).lattice =
        principalIdeal (K := K)
          (J.scaleGenerator (D.suffixIndexEquiv hkn z).1 : K) := by
    intro z
    let g := BONG.blockProductComponentIsometry C qs Ls z
    calc
      scaleIdeal (P.component z).space (P.component z).lattice =
          scaleIdeal (qs z) (Ls z) := by
        rw [← g.map_eq]
        exact scaleIdeal_map_isometry g.toQuadraticSpaceIsometry (Ls z)
      _ = principalIdeal (K := K)
          (J.scaleGenerator (D.suffixIndexEquiv hkn z).1 : K) :=
        J.scaleIdeal_eq (D.suffixIndexEquiv hkn z).1
  calc
    scaleIdeal
        (D.suffixQuadraticSublattice k).space
        (D.suffixQuadraticSublattice k).lattice =
        scaleIdeal (BONG.blockOrthogonalForm n C qs)
          (BONG.blockProductLattice n C Ls) := by
      rw [← f.map_eq]
      exact scaleIdeal_map_isometry f.toQuadraticSpaceIsometry
        (BONG.blockProductLattice n C Ls)
    _ = ⨆ z, scaleIdeal (P.component z).space
        (P.component z).lattice := P.scaleIdeal_eq_iSup_component
    _ = principalIdeal (K := K)
        (J.scaleGenerator ⟨k, by omega⟩ : K) := by
      apply le_antisymm
      · apply iSup_le
        intro z
        rw [hcomponent z]
        apply (principalIdeal_le_iff_ord_ge
          (Units.ne_zero (J.scaleGenerator (D.suffixIndexEquiv hkn z).1))
          (Units.ne_zero (J.scaleGenerator ⟨k, by omega⟩))).2
        by_cases hz : z = 0
        · subst z
          rfl
        · have hindex : (⟨k, by omega⟩ : Fin t) <
              (D.suffixIndexEquiv hkn z).1 := by
            change k < k + z.val
            have hzpos : 0 < z.val := Nat.pos_of_ne_zero (by
              intro hzero
              apply hz
              apply Fin.ext
              exact hzero)
            omega
          simpa only [coe_ordUnit] using
            WithTop.coe_le_coe.mpr (J.scaleOrder_strict hindex).le
      · have hle := le_iSup
            (fun z : Fin (n + 1) ↦
              scaleIdeal (P.component z).space (P.component z).lattice) 0
        rw [hcomponent 0] at hle
        have hzeroIndex : (D.suffixIndexEquiv hkn 0).1 =
            (⟨k, by omega⟩ : Fin t) := by
          apply Fin.ext
          simp
        rwa [hzeroIndex] at hle

end Lattice.JordanDecomposition

end Bong
