import Bong.Bong.JordanProfileOrder
import Bong.Lattice.OmearaFundamentalIdeals

namespace Bong

open Dyadic Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace Lattice.JordanDecomposition

set_option maxHeartbeats 0 in
/-- Beli (2019), Lemma 3.5(ii): if the intrinsic norm order at a component
is strictly separated from the neighboring intrinsic norm orders in both
the direct and dual orientations, then that component itself attains the
intrinsic norm.  Endpoint alternatives omit the nonexistent inequality. -/
theorem beli2019Lemma35_ii {t : Nat}
    (J : Lattice.JordanDecomposition q L t) (p : Fin t)
    (hleft : ∀ hp : 0 < p.val,
      ordUnit K (J.fundamentalNormGenerator p) -
          2 * J.fundamentalScaleOrder p <
        ordUnit K (J.fundamentalNormGenerator
          ⟨p.val - 1, by omega⟩) -
          2 * J.fundamentalScaleOrder ⟨p.val - 1, by omega⟩)
    (hright : ∀ hp : p.val + 1 < t,
      ordUnit K (J.fundamentalNormGenerator p) <
        ordUnit K (J.fundamentalNormGenerator
          ⟨p.val + 1, by omega⟩)) :
    ordUnit K (J.normGenerator p) =
      ordUnit K (J.fundamentalNormGenerator p) := by
  let scale : Fin t → Int := fun j ↦ ordUnit K (J.scaleGenerator j)
  let norm : Fin t → Int := fun j ↦ ordUnit K (J.normGenerator j)
  have hfund_le_norm (j : Fin t) :
      ordUnit K (J.fundamentalNormGenerator j) ≤ norm j := by
    rw [J.fundamentalNormGenerator_order_eq_effective j]
    unfold BONG.jordanEffectiveNormOrder BONG.jordanEffectiveNormOrderAt
    change JordanProfileOrder.effectiveAt scale norm j (scale j) ≤ norm j
    calc
      JordanProfileOrder.effectiveAt scale norm j (scale j) ≤
          JordanProfileOrder.adjustedAt scale norm (scale j) j :=
        JordanProfileOrder.effectiveAt_le scale norm j j (scale j)
      _ = norm j := by simp [JordanProfileOrder.adjustedAt]
  apply le_antisymm
  · obtain ⟨j, _hj, hjmin⟩ := Finset.exists_mem_eq_inf'
      (s := (Finset.univ : Finset (Fin t)))
      ⟨p, Finset.mem_univ p⟩
      (JordanProfileOrder.adjustedAt scale norm (scale p))
    have hmin : JordanProfileOrder.adjustedAt scale norm (scale p) j =
        ordUnit K (J.fundamentalNormGenerator p) := by
      rw [J.fundamentalNormGenerator_order_eq_effective p]
      unfold BONG.jordanEffectiveNormOrder BONG.jordanEffectiveNormOrderAt
      change JordanProfileOrder.adjustedAt scale norm (scale p) j =
        JordanProfileOrder.effectiveAt scale norm p (scale p)
      exact hjmin.symm
    rcases lt_trichotomy j p with hjp | rfl | hpj
    · have hppos : 0 < p.val := by
        have := Nat.zero_le j.val
        change j.val < p.val at hjp
        omega
      have hleft := hleft hppos
      let previous : Fin t := ⟨p.val - 1, by omega⟩
      have hjprevious : j ≤ previous := by
        change j.val ≤ p.val - 1
        omega
      have hanti :=
        J.fundamentalNormGenerator_order_sub_two_scale_anti hjprevious
      have hjscale : scale j < scale p := by
        exact J.scaleOrder_strict hjp
      unfold JordanProfileOrder.adjustedAt at hmin
      rw [if_pos hjscale] at hmin
      change ordUnit K (J.fundamentalNormGenerator p) - 2 * scale p <
        ordUnit K (J.fundamentalNormGenerator previous) -
          2 * scale previous at hleft
      change ordUnit K (J.fundamentalNormGenerator previous) -
          2 * scale previous ≤
        ordUnit K (J.fundamentalNormGenerator j) - 2 * scale j at hanti
      have hjnorm := hfund_le_norm j
      omega
    · simpa [JordanProfileOrder.adjustedAt] using hmin.le
    · have hpnext : p.val + 1 < t := by
        have hjlt := j.isLt
        change p.val < j.val at hpj
        omega
      have hright := hright hpnext
      let next : Fin t := ⟨p.val + 1, hpnext⟩
      have hnextj : next ≤ j := by
        change p.val + 1 ≤ j.val
        omega
      have hmono := J.fundamentalNormGenerator_order_mono hnextj
      have hjscale : ¬scale j < scale p := by
        exact not_lt_of_ge (J.scaleOrder_strict hpj).le
      unfold JordanProfileOrder.adjustedAt at hmin
      rw [if_neg hjscale] at hmin
      have hjnorm := hfund_le_norm j
      change ordUnit K (J.fundamentalNormGenerator p) <
        ordUnit K (J.fundamentalNormGenerator next) at hright
      omega
  · exact hfund_le_norm p

end Lattice.JordanDecomposition

end Bong
