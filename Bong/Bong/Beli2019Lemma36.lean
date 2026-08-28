import Bong.Bong.Beli2019BinaryNormGeneratorComplement
import Bong.Bong.Beli2019JordanApproximationProfile

namespace Bong

open Dyadic Module

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG.JordanOrderProfileWitness

noncomputable def profileComponentFirstIndex
    {n t : Nat} {a : BONG.GoodBONG q L n}
    {J : Lattice.JordanDecomposition q L t}
    (P : JordanOrderProfileWitness a.toBONG J) (p : Fin t) : Fin n :=
  P.indexEquiv.symm ⟨p, ⟨0, J.component_finrank_pos p⟩⟩

noncomputable def profileComponentSecondIndex
    {n t : Nat} {a : BONG.GoodBONG q L n}
    {J : Lattice.JordanDecomposition q L t}
    (P : JordanOrderProfileWitness a.toBONG J) (p : Fin t)
    (hrank : 1 < J.componentRank p) : Fin n :=
  P.indexEquiv.symm ⟨p, ⟨1, hrank⟩⟩

noncomputable def profileComponentLastIndex
    {n t : Nat} {a : BONG.GoodBONG q L n}
    {J : Lattice.JordanDecomposition q L t}
    (P : JordanOrderProfileWitness a.toBONG J) (p : Fin t) : Fin n :=
  P.indexEquiv.symm ⟨p, ⟨J.componentRank p - 1, by
    exact Nat.sub_lt (J.component_finrank_pos p) Nat.zero_lt_one⟩⟩

@[simp] theorem profileComponentFirstIndex_val
    {n t : Nat} {a : BONG.GoodBONG q L n}
    {J : Lattice.JordanDecomposition q L t}
    (P : JordanOrderProfileWitness a.toBONG J) (p : Fin t) :
    (P.profileComponentFirstIndex p).val =
      ∑ h ∈ Finset.Iio p, J.componentRank h := by
  unfold profileComponentFirstIndex
  rw [P.inverse_index_val]
  rfl

@[simp] theorem profileComponentSecondIndex_val
    {n t : Nat} {a : BONG.GoodBONG q L n}
    {J : Lattice.JordanDecomposition q L t}
    (P : JordanOrderProfileWitness a.toBONG J) (p : Fin t)
    (hrank : 1 < J.componentRank p) :
    (P.profileComponentSecondIndex p hrank).val =
      (∑ h ∈ Finset.Iio p, J.componentRank h) + 1 := by
  unfold profileComponentSecondIndex
  rw [P.inverse_index_val]
  rfl

@[simp] theorem profileComponentLastIndex_val
    {n t : Nat} {a : BONG.GoodBONG q L n}
    {J : Lattice.JordanDecomposition q L t}
    (P : JordanOrderProfileWitness a.toBONG J) (p : Fin t) :
    (P.profileComponentLastIndex p).val =
      (∑ h ∈ Finset.Iio p, J.componentRank h) +
        (J.componentRank p - 1) := by
  unfold profileComponentLastIndex
  rw [P.inverse_index_val]
  rfl

theorem order_profileComponentFirstIndex
    {n t : Nat} {a : BONG.GoodBONG q L n}
    {J : Lattice.JordanDecomposition q L t}
    (P : JordanOrderProfileWitness a.toBONG J) (p : Fin t) :
    a.order (P.profileComponentFirstIndex p) =
      BONG.jordanEffectiveNormOrder J p := by
  unfold profileComponentFirstIndex
  change a.toBONG.order
      (P.indexEquiv.symm ⟨p, ⟨0, J.component_finrank_pos p⟩⟩) = _
  rw [P.order_inverse_indexEquiv]
  unfold BONG.jordanExpectedOrder
  by_cases hproper : ordUnit K (J.scaleGenerator p) =
      BONG.jordanEffectiveNormOrder J p
  · simp [hproper]
  · simp [hproper]

theorem order_profileComponentSecondIndex
    {n t : Nat} {a : BONG.GoodBONG q L n}
    {J : Lattice.JordanDecomposition q L t}
    (P : JordanOrderProfileWitness a.toBONG J) (p : Fin t)
    (hrank : 1 < J.componentRank p) :
    a.order (P.profileComponentSecondIndex p hrank) =
      2 * ordUnit K (J.scaleGenerator p) -
        BONG.jordanEffectiveNormOrder J p := by
  unfold profileComponentSecondIndex
  change a.toBONG.order (P.indexEquiv.symm ⟨p, ⟨1, hrank⟩⟩) = _
  rw [P.order_inverse_indexEquiv]
  unfold BONG.jordanExpectedOrder
  by_cases hproper : ordUnit K (J.scaleGenerator p) =
      BONG.jordanEffectiveNormOrder J p
  · simp [hproper]
    omega
  · simp [hproper]

theorem order_profileComponentLastIndex
    {n t : Nat} {a : BONG.GoodBONG q L n}
    (W : Lattice.WeakJordanDecomposition q L t)
    (hW : W.HasImproperEvenRank)
    (hstrict : StrictMono (fun i ↦ ordUnit K (W.scaleGenerator i)))
    (P : JordanOrderProfileWitness a.toBONG (W.toJordan hstrict))
    (p : Fin t) :
    a.order (P.profileComponentLastIndex p) =
      2 * ordUnit K (W.scaleGenerator p) -
        BONG.jordanEffectiveNormOrder (W.toJordan hstrict) p := by
  unfold profileComponentLastIndex
  change a.toBONG.order (P.indexEquiv.symm ⟨p,
      ⟨(W.toJordan hstrict).componentRank p - 1, _⟩⟩) = _
  rw [P.order_inverse_indexEquiv]
  rw [W.jordanExpectedOrder_toJordan]
  exact hW.localOrder_last W p

set_option maxHeartbeats 0 in
/-- Beli (2019), Lemma 3.6.  For a binary component, the two strict
outer-order inequalities (with endpoint omissions) imply that the component
norm equals the intrinsic norm of the scale truncation. -/
theorem beli2019Lemma36
    {n t : Nat} {a : BONG.GoodBONG q L n}
    (W : Lattice.WeakJordanDecomposition q L t)
    (hW : W.HasImproperEvenRank)
    (hstrict : StrictMono (fun i ↦ ordUnit K (W.scaleGenerator i)))
    (P : JordanOrderProfileWitness a.toBONG (W.toJordan hstrict))
    (p : Fin t) (hrank : (W.toJordan hstrict).componentRank p = 2)
    (hleft : ∀ hp : 0 < p.val,
      a.order (P.profileComponentLastIndex
        ⟨p.val - 1, by omega⟩) <
      a.order (P.profileComponentSecondIndex p (by omega)))
    (hright : ∀ hp : p.val + 1 < t,
      a.order (P.profileComponentFirstIndex p) <
      a.order (P.profileComponentFirstIndex
        ⟨p.val + 1, by omega⟩)) :
    BONG.jordanEffectiveNormOrder (W.toJordan hstrict) p =
      ordUnit K ((W.toJordan hstrict).normGenerator p) := by
  let J := W.toJordan hstrict
  have hnorm := J.beli2019Lemma35_ii p
    (fun hp ↦ by
      let previous : Fin t := ⟨p.val - 1, by omega⟩
      have horders := hleft hp
      rw [order_profileComponentLastIndex W hW hstrict P previous,
        order_profileComponentSecondIndex P p (by omega)] at horders
      simp only [Lattice.WeakJordanDecomposition.toJordan_scaleGenerator]
        at horders
      change ordUnit K (J.fundamentalNormGenerator p) -
          2 * ordUnit K (W.scaleGenerator p) <
        ordUnit K (J.fundamentalNormGenerator previous) -
          2 * ordUnit K (W.scaleGenerator previous)
      rw [J.fundamentalNormGenerator_order_eq_effective p,
        J.fundamentalNormGenerator_order_eq_effective previous]
      dsimp only [J]
      omega)
    (fun hp ↦ by
      let next : Fin t := ⟨p.val + 1, hp⟩
      have horders := hright hp
      rw [order_profileComponentFirstIndex P p,
        order_profileComponentFirstIndex P next] at horders
      simpa only [J.fundamentalNormGenerator_order_eq_effective] using horders)
  exact (J.fundamentalNormGenerator_order_eq_effective p).symm.trans
    hnorm.symm

end BONG.JordanOrderProfileWitness

end Bong
