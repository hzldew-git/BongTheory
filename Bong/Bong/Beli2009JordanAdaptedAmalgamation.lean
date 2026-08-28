import Bong.Bong.Beli2009JordanAlignment
import Bong.Bong.Beli2019Lemma710BONGProduct

open Bong
open Bong.Dyadic

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG

noncomputable def componentFamilyAmbientVector {t : Nat}
    {D : Lattice.OrthogonalDecomposition q L t}
    (c : D.ComponentBONGFamily)
    (z : Σ i : Fin t, Fin (D.componentRank i)) : V :=
  ((c z.1).ambientVector z.2 : D.component z.1 |>.carrier)

def weakComponentHeadIndex {t : Nat}
    (W : Lattice.WeakJordanDecomposition q L t) (i : Fin t) :
    Fin (W.toOrthogonalDecomposition.componentRank i) :=
  ⟨0, W.component_finrank_pos i⟩

noncomputable def mergeComponentBONG {t : Nat}
    (W : Lattice.WeakJordanDecomposition q L (t + 1))
    (c : W.toOrthogonalDecomposition.ComponentBONGFamily)
    (hlocal : ∀ i j, (c i).order j ≤
      (c i).order (weakComponentHeadIndex W i))
    (hhead : ∀ i, (c i).order (weakComponentHeadIndex W i) =
      ordUnit K (W.normGeneratorUnit i))
    (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ))
    (hnorm : ordUnit K (W.normGeneratorUnit k.castSucc) =
      ordUnit K (W.normGeneratorUnit k.succ)) :
    BONG ((W.mergeAdjacentAt k heq).component k).carrier
      ((W.mergeAdjacentAt k heq).component k).space
      ((W.mergeAdjacentAt k heq).component k).lattice
      (Module.finrank K ((W.mergeAdjacentAt k heq).component k).carrier) := by
  let left := c k.castSucc
  let rightRaw := c k.succ
  have hrightPos : 0 < W.toOrthogonalDecomposition.componentRank k.succ :=
    W.component_finrank_pos k.succ
  let right : BONG (W.component k.succ).carrier
      (W.component k.succ).space (W.component k.succ).lattice
      ((W.toOrthogonalDecomposition.componentRank k.succ - 1) + 1) :=
    rightRaw.castLength (by omega)
  let rightHead : Fin ((W.toOrthogonalDecomposition.componentRank k.succ - 1) + 1) :=
    ⟨0, by omega⟩
  have hrightOrderZero : right.order rightHead =
      rightRaw.order (weakComponentHeadIndex W k.succ) := by
    change (rightRaw.castLength _).order rightHead = _
    rw [BONG.order_castLength]
    congr 1
  have horder : ∀ i, left.order i ≤ right.order rightHead := by
    intro i
    rw [hrightOrderZero]
    calc
      left.order i ≤
          (c k.castSucc).order (weakComponentHeadIndex W k.castSucc) :=
        hlocal k.castSucc i
      _ = ordUnit K (W.normGeneratorUnit k.castSucc) := hhead k.castSucc
      _ = ordUnit K (W.normGeneratorUnit k.succ) := hnorm
      _ = rightRaw.order (weakComponentHeadIndex W k.succ) :=
        (hhead k.succ).symm
  let raw := left.orthogonalProductRight right horder
  let mapped := raw.mapLatticeIsometry
    (W.toOrthogonalDecomposition.orthogonalSupLatticeIsometry
      k.castSucc_lt_succ.ne)
  have hcomponent :
      W.toOrthogonalDecomposition.orthogonalSup k.castSucc_lt_succ.ne =
        (W.mergeAdjacentAt k heq).component k := by
    exact (W.mergeAdjacentAt_component_self k heq).symm
  let transported := mapped.castQuadraticSublattice hcomponent
  exact transported.castLength (by
    change
      (W.toOrthogonalDecomposition.componentRank k.succ - 1 + 1) +
          W.toOrthogonalDecomposition.componentRank k.castSucc =
        Module.finrank K
          ((W.mergeAdjacentAt k heq).component k).carrier
    rw [W.mergeAdjacentAt_componentRank_self k heq]
    simp only [Lattice.OrthogonalDecomposition.componentRank] at hrightPos ⊢
    omega)

noncomputable def mergeComponentBONGFamily {t : Nat}
    (W : Lattice.WeakJordanDecomposition q L (t + 1))
    (c : W.toOrthogonalDecomposition.ComponentBONGFamily)
    (hlocal : ∀ i j, (c i).order j ≤
      (c i).order (weakComponentHeadIndex W i))
    (hhead : ∀ i, (c i).order (weakComponentHeadIndex W i) =
      ordUnit K (W.normGeneratorUnit i))
    (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ))
    (hnorm : ordUnit K (W.normGeneratorUnit k.castSucc) =
      ordUnit K (W.normGeneratorUnit k.succ)) :
    (W.mergeAdjacentAt k heq).toOrthogonalDecomposition.ComponentBONGFamily := by
  classical
  intro j
  by_cases hj : j = k
  · subst j
    exact mergeComponentBONG W c hlocal hhead k heq hnorm
  · let old := c (k.succ.succAbove j)
    have hcomponent : W.component (k.succ.succAbove j) =
        (W.mergeAdjacentAt k heq).component j :=
      (W.mergeAdjacentAt_component_of_ne k heq j hj).symm
    let transported := old.castQuadraticSublattice hcomponent
    exact transported.castLength (by
      change W.toOrthogonalDecomposition.componentRank
          (k.succ.succAbove j) =
        (W.mergeAdjacentAt k heq).toOrthogonalDecomposition.componentRank j
      simp only [Lattice.OrthogonalDecomposition.componentRank]
      rw [W.mergeAdjacentAt_component_of_ne k heq j hj])

@[simp] theorem mergeComponentBONGFamily_self {t : Nat}
    (W : Lattice.WeakJordanDecomposition q L (t + 1))
    (c : W.toOrthogonalDecomposition.ComponentBONGFamily)
    (hlocal : ∀ i j, (c i).order j ≤
      (c i).order (weakComponentHeadIndex W i))
    (hhead : ∀ i, (c i).order (weakComponentHeadIndex W i) =
      ordUnit K (W.normGeneratorUnit i))
    (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ))
    (hnorm : ordUnit K (W.normGeneratorUnit k.castSucc) =
      ordUnit K (W.normGeneratorUnit k.succ)) :
    mergeComponentBONGFamily W c hlocal hhead k heq hnorm k =
      mergeComponentBONG W c hlocal hhead k heq hnorm := by
  simp only [mergeComponentBONGFamily]
  rw [dif_pos trivial]

theorem mergeComponentBONGFamily_of_ne {t : Nat}
    (W : Lattice.WeakJordanDecomposition q L (t + 1))
    (c : W.toOrthogonalDecomposition.ComponentBONGFamily)
    (hlocal : ∀ i j, (c i).order j ≤
      (c i).order (weakComponentHeadIndex W i))
    (hhead : ∀ i, (c i).order (weakComponentHeadIndex W i) =
      ordUnit K (W.normGeneratorUnit i))
    (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ))
    (hnorm : ordUnit K (W.normGeneratorUnit k.castSucc) =
      ordUnit K (W.normGeneratorUnit k.succ))
    (j : Fin t) (hj : j ≠ k) :
    mergeComponentBONGFamily W c hlocal hhead k heq hnorm j =
      (((c (k.succ.succAbove j)).castQuadraticSublattice
        (W.mergeAdjacentAt_component_of_ne k heq j hj).symm).castLength (by
          simp only [Lattice.OrthogonalDecomposition.componentRank]
          rw [W.mergeAdjacentAt_component_of_ne k heq j hj])) := by
  simp only [mergeComponentBONGFamily, dif_neg hj]

noncomputable def mergeComponentLeftIndex {t : Nat}
    (W : Lattice.WeakJordanDecomposition q L (t + 1))
    (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ))
    (i : Fin (W.toOrthogonalDecomposition.componentRank k.castSucc)) :
    Fin ((W.mergeAdjacentAt k heq).toOrthogonalDecomposition.componentRank k) :=
  ⟨i.val, by
    simp only [Lattice.OrthogonalDecomposition.componentRank]
    rw [W.mergeAdjacentAt_componentRank_self k heq]
    exact Nat.lt_add_right _ i.isLt⟩

noncomputable def mergeComponentRightIndex {t : Nat}
    (W : Lattice.WeakJordanDecomposition q L (t + 1))
    (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ))
    (j : Fin (W.toOrthogonalDecomposition.componentRank k.succ)) :
    Fin ((W.mergeAdjacentAt k heq).toOrthogonalDecomposition.componentRank k) :=
  ⟨W.toOrthogonalDecomposition.componentRank k.castSucc + j.val, by
    simp only [Lattice.OrthogonalDecomposition.componentRank]
    rw [W.mergeAdjacentAt_componentRank_self k heq]
    omega⟩

@[simp] theorem mergeComponentBONG_order_left {t : Nat}
    (W : Lattice.WeakJordanDecomposition q L (t + 1))
    (c : W.toOrthogonalDecomposition.ComponentBONGFamily)
    (hlocal : ∀ i j, (c i).order j ≤
      (c i).order (weakComponentHeadIndex W i))
    (hhead : ∀ i, (c i).order (weakComponentHeadIndex W i) =
      ordUnit K (W.normGeneratorUnit i))
    (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ))
    (hnorm : ordUnit K (W.normGeneratorUnit k.castSucc) =
      ordUnit K (W.normGeneratorUnit k.succ))
    (i : Fin (W.toOrthogonalDecomposition.componentRank k.castSucc)) :
    (mergeComponentBONG W c hlocal hhead k heq hnorm).order
        (mergeComponentLeftIndex W k heq i) =
      (c k.castSucc).order i := by
  let left := c k.castSucc
  let rightRaw := c k.succ
  have hrightPos : 0 < W.toOrthogonalDecomposition.componentRank k.succ :=
    W.component_finrank_pos k.succ
  let right : BONG (W.component k.succ).carrier
      (W.component k.succ).space (W.component k.succ).lattice
      ((W.toOrthogonalDecomposition.componentRank k.succ - 1) + 1) :=
    rightRaw.castLength (by omega)
  let rightHead : Fin
      ((W.toOrthogonalDecomposition.componentRank k.succ - 1) + 1) :=
    ⟨0, by omega⟩
  have hrightOrderZero : right.order rightHead =
      rightRaw.order (weakComponentHeadIndex W k.succ) := by
    change (rightRaw.castLength _).order rightHead = _
    rw [BONG.order_castLength]
    congr 1
  have horder : ∀ z, left.order z ≤ right.order rightHead := by
    intro z
    rw [hrightOrderZero]
    calc
      left.order z ≤
          (c k.castSucc).order (weakComponentHeadIndex W k.castSucc) :=
        hlocal k.castSucc z
      _ = ordUnit K (W.normGeneratorUnit k.castSucc) := hhead k.castSucc
      _ = ordUnit K (W.normGeneratorUnit k.succ) := hnorm
      _ = rightRaw.order (weakComponentHeadIndex W k.succ) :=
        (hhead k.succ).symm
  let raw := left.orthogonalProductRight right horder
  let mapped := raw.mapLatticeIsometry
    (W.toOrthogonalDecomposition.orthogonalSupLatticeIsometry
      k.castSucc_lt_succ.ne)
  have hcomponent :
      W.toOrthogonalDecomposition.orthogonalSup k.castSucc_lt_succ.ne =
        (W.mergeAdjacentAt k heq).component k :=
    (W.mergeAdjacentAt_component_self k heq).symm
  let transported := mapped.castQuadraticSublattice hcomponent
  have hindex :
      ⟨(mergeComponentLeftIndex W k heq i).val, by
        change (mergeComponentLeftIndex W k heq i).val <
          (W.toOrthogonalDecomposition.componentRank k.succ - 1 + 1) +
            W.toOrthogonalDecomposition.componentRank k.castSucc
        dsimp only [mergeComponentLeftIndex]
        omega⟩ =
      orthogonalProductLeftIndex
        (W.toOrthogonalDecomposition.componentRank k.succ - 1 + 1) i := by
    apply Fin.ext
    rfl
  change (transported.castLength _).order
      (mergeComponentLeftIndex W k heq i) = left.order i
  rw [BONG.order_castLength]
  change transported.order ⟨_, _⟩ = _
  rw [BONG.order_castQuadraticSublattice]
  change mapped.order ⟨_, _⟩ = _
  rw [BONG.order_mapLatticeIsometry]
  change raw.order ⟨_, _⟩ = _
  rw [hindex, BONG.order_orthogonalProductRight_left]

@[simp] theorem mergeComponentBONG_order_right {t : Nat}
    (W : Lattice.WeakJordanDecomposition q L (t + 1))
    (c : W.toOrthogonalDecomposition.ComponentBONGFamily)
    (hlocal : ∀ i j, (c i).order j ≤
      (c i).order (weakComponentHeadIndex W i))
    (hhead : ∀ i, (c i).order (weakComponentHeadIndex W i) =
      ordUnit K (W.normGeneratorUnit i))
    (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ))
    (hnorm : ordUnit K (W.normGeneratorUnit k.castSucc) =
      ordUnit K (W.normGeneratorUnit k.succ))
    (j : Fin (W.toOrthogonalDecomposition.componentRank k.succ)) :
    (mergeComponentBONG W c hlocal hhead k heq hnorm).order
        (mergeComponentRightIndex W k heq j) =
      (c k.succ).order j := by
  let left := c k.castSucc
  let rightRaw := c k.succ
  have hrightPos : 0 < W.toOrthogonalDecomposition.componentRank k.succ :=
    W.component_finrank_pos k.succ
  let right : BONG (W.component k.succ).carrier
      (W.component k.succ).space (W.component k.succ).lattice
      ((W.toOrthogonalDecomposition.componentRank k.succ - 1) + 1) :=
    rightRaw.castLength (by omega)
  let rightHead : Fin
      ((W.toOrthogonalDecomposition.componentRank k.succ - 1) + 1) :=
    ⟨0, by omega⟩
  have hrightOrderZero : right.order rightHead =
      rightRaw.order (weakComponentHeadIndex W k.succ) := by
    change (rightRaw.castLength _).order rightHead = _
    rw [BONG.order_castLength]
    congr 1
  have horder : ∀ z, left.order z ≤ right.order rightHead := by
    intro z
    rw [hrightOrderZero]
    calc
      left.order z ≤
          (c k.castSucc).order (weakComponentHeadIndex W k.castSucc) :=
        hlocal k.castSucc z
      _ = ordUnit K (W.normGeneratorUnit k.castSucc) := hhead k.castSucc
      _ = ordUnit K (W.normGeneratorUnit k.succ) := hnorm
      _ = rightRaw.order (weakComponentHeadIndex W k.succ) :=
        (hhead k.succ).symm
  let raw := left.orthogonalProductRight right horder
  let mapped := raw.mapLatticeIsometry
    (W.toOrthogonalDecomposition.orthogonalSupLatticeIsometry
      k.castSucc_lt_succ.ne)
  have hcomponent :
      W.toOrthogonalDecomposition.orthogonalSup k.castSucc_lt_succ.ne =
        (W.mergeAdjacentAt k heq).component k :=
    (W.mergeAdjacentAt_component_self k heq).symm
  let transported := mapped.castQuadraticSublattice hcomponent
  let jr : Fin
      ((W.toOrthogonalDecomposition.componentRank k.succ - 1) + 1) :=
    ⟨j.val, by omega⟩
  have hindex :
      ⟨(mergeComponentRightIndex W k heq j).val, by
        change (mergeComponentRightIndex W k heq j).val <
          (W.toOrthogonalDecomposition.componentRank k.succ - 1 + 1) +
            W.toOrthogonalDecomposition.componentRank k.castSucc
        dsimp only [mergeComponentRightIndex]
        omega⟩ = orthogonalProductRightIndex
          (W.toOrthogonalDecomposition.componentRank k.castSucc) jr := by
    apply Fin.ext
    dsimp only [mergeComponentRightIndex,
      orthogonalProductRightIndex, jr]
  change (transported.castLength _).order
      (mergeComponentRightIndex W k heq j) = rightRaw.order j
  rw [BONG.order_castLength]
  change transported.order ⟨_, _⟩ = _
  rw [BONG.order_castQuadraticSublattice]
  change mapped.order ⟨_, _⟩ = _
  rw [BONG.order_mapLatticeIsometry]
  change raw.order ⟨_, _⟩ = _
  rw [hindex, BONG.order_orthogonalProductRight_right]
  change (rightRaw.castLength _).order jr = rightRaw.order j
  rw [BONG.order_castLength]

@[simp] theorem mergeComponentBONG_ambientVector_left {t : Nat}
    (W : Lattice.WeakJordanDecomposition q L (t + 1))
    (c : W.toOrthogonalDecomposition.ComponentBONGFamily)
    (hlocal : ∀ i j, (c i).order j ≤
      (c i).order (weakComponentHeadIndex W i))
    (hhead : ∀ i, (c i).order (weakComponentHeadIndex W i) =
      ordUnit K (W.normGeneratorUnit i))
    (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ))
    (hnorm : ordUnit K (W.normGeneratorUnit k.castSucc) =
      ordUnit K (W.normGeneratorUnit k.succ))
    (i : Fin (W.toOrthogonalDecomposition.componentRank k.castSucc)) :
    ((((mergeComponentBONG W c hlocal hhead k heq hnorm).ambientVector
        (mergeComponentLeftIndex W k heq i) :
          (W.mergeAdjacentAt k heq).component k |>.carrier) : V)) =
      (((c k.castSucc).ambientVector i : W.component k.castSucc |>.carrier) : V) := by
  let left := c k.castSucc
  let rightRaw := c k.succ
  have hrightPos : 0 < W.toOrthogonalDecomposition.componentRank k.succ :=
    W.component_finrank_pos k.succ
  let right : BONG (W.component k.succ).carrier
      (W.component k.succ).space (W.component k.succ).lattice
      ((W.toOrthogonalDecomposition.componentRank k.succ - 1) + 1) :=
    rightRaw.castLength (by omega)
  let rightHead : Fin
      ((W.toOrthogonalDecomposition.componentRank k.succ - 1) + 1) :=
    ⟨0, by omega⟩
  have hrightOrderZero : right.order rightHead =
      rightRaw.order (weakComponentHeadIndex W k.succ) := by
    change (rightRaw.castLength _).order rightHead = _
    rw [BONG.order_castLength]
    congr 1
  have horder : ∀ z, left.order z ≤ right.order rightHead := by
    intro z
    rw [hrightOrderZero]
    calc
      left.order z ≤
          (c k.castSucc).order (weakComponentHeadIndex W k.castSucc) :=
        hlocal k.castSucc z
      _ = ordUnit K (W.normGeneratorUnit k.castSucc) := hhead k.castSucc
      _ = ordUnit K (W.normGeneratorUnit k.succ) := hnorm
      _ = rightRaw.order (weakComponentHeadIndex W k.succ) :=
        (hhead k.succ).symm
  let raw := left.orthogonalProductRight right horder
  let iso := W.toOrthogonalDecomposition.orthogonalSupLatticeIsometry
    k.castSucc_lt_succ.ne
  let mapped := raw.mapLatticeIsometry iso
  have hcomponent :
      W.toOrthogonalDecomposition.orthogonalSup k.castSucc_lt_succ.ne =
        (W.mergeAdjacentAt k heq).component k :=
    (W.mergeAdjacentAt_component_self k heq).symm
  let transported := mapped.castQuadraticSublattice hcomponent
  have hindex :
      ⟨(mergeComponentLeftIndex W k heq i).val, by
        change (mergeComponentLeftIndex W k heq i).val <
          (W.toOrthogonalDecomposition.componentRank k.succ - 1 + 1) +
            W.toOrthogonalDecomposition.componentRank k.castSucc
        dsimp only [mergeComponentLeftIndex]
        omega⟩ =
      orthogonalProductLeftIndex
        (W.toOrthogonalDecomposition.componentRank k.succ - 1 + 1) i := by
    apply Fin.ext
    rfl
  change ((((transported.castLength _).ambientVector
      (mergeComponentLeftIndex W k heq i) :
        (W.mergeAdjacentAt k heq).component k |>.carrier) : V)) = _
  rw [BONG.ambientVector_castLength]
  change (((transported.ambientVector ⟨_, _⟩ :
      (W.mergeAdjacentAt k heq).component k |>.carrier) : V)) = _
  rw [BONG.ambientVector_castQuadraticSublattice]
  change (((mapped.ambientVector ⟨_, _⟩ :
      (W.toOrthogonalDecomposition.orthogonalSup
        k.castSucc_lt_succ.ne).carrier) : V)) = _
  rw [BONG.ambientVector_mapLatticeIsometry]
  change ((W.toOrthogonalDecomposition.orthogonalSupEquiv
      k.castSucc_lt_succ.ne (raw.ambientVector ⟨_, _⟩) : V)) = _
  rw [hindex, BONG.ambientVector_orthogonalProductRight_left,
    W.toOrthogonalDecomposition.coe_orthogonalSupEquiv]
  simp
  rfl

@[simp] theorem mergeComponentBONG_ambientVector_right {t : Nat}
    (W : Lattice.WeakJordanDecomposition q L (t + 1))
    (c : W.toOrthogonalDecomposition.ComponentBONGFamily)
    (hlocal : ∀ i j, (c i).order j ≤
      (c i).order (weakComponentHeadIndex W i))
    (hhead : ∀ i, (c i).order (weakComponentHeadIndex W i) =
      ordUnit K (W.normGeneratorUnit i))
    (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ))
    (hnorm : ordUnit K (W.normGeneratorUnit k.castSucc) =
      ordUnit K (W.normGeneratorUnit k.succ))
    (j : Fin (W.toOrthogonalDecomposition.componentRank k.succ)) :
    ((((mergeComponentBONG W c hlocal hhead k heq hnorm).ambientVector
        (mergeComponentRightIndex W k heq j) :
          (W.mergeAdjacentAt k heq).component k |>.carrier) : V)) =
      (((c k.succ).ambientVector j : W.component k.succ |>.carrier) : V) := by
  let left := c k.castSucc
  let rightRaw := c k.succ
  have hrightPos : 0 < W.toOrthogonalDecomposition.componentRank k.succ :=
    W.component_finrank_pos k.succ
  let right : BONG (W.component k.succ).carrier
      (W.component k.succ).space (W.component k.succ).lattice
      ((W.toOrthogonalDecomposition.componentRank k.succ - 1) + 1) :=
    rightRaw.castLength (by omega)
  let rightHead : Fin
      ((W.toOrthogonalDecomposition.componentRank k.succ - 1) + 1) :=
    ⟨0, by omega⟩
  have hrightOrderZero : right.order rightHead =
      rightRaw.order (weakComponentHeadIndex W k.succ) := by
    change (rightRaw.castLength _).order rightHead = _
    rw [BONG.order_castLength]
    congr 1
  have horder : ∀ z, left.order z ≤ right.order rightHead := by
    intro z
    rw [hrightOrderZero]
    calc
      left.order z ≤
          (c k.castSucc).order (weakComponentHeadIndex W k.castSucc) :=
        hlocal k.castSucc z
      _ = ordUnit K (W.normGeneratorUnit k.castSucc) := hhead k.castSucc
      _ = ordUnit K (W.normGeneratorUnit k.succ) := hnorm
      _ = rightRaw.order (weakComponentHeadIndex W k.succ) :=
        (hhead k.succ).symm
  let raw := left.orthogonalProductRight right horder
  let iso := W.toOrthogonalDecomposition.orthogonalSupLatticeIsometry
    k.castSucc_lt_succ.ne
  let mapped := raw.mapLatticeIsometry iso
  have hcomponent :
      W.toOrthogonalDecomposition.orthogonalSup k.castSucc_lt_succ.ne =
        (W.mergeAdjacentAt k heq).component k :=
    (W.mergeAdjacentAt_component_self k heq).symm
  let transported := mapped.castQuadraticSublattice hcomponent
  let jr : Fin
      ((W.toOrthogonalDecomposition.componentRank k.succ - 1) + 1) :=
    ⟨j.val, by omega⟩
  have hindex :
      ⟨(mergeComponentRightIndex W k heq j).val, by
        change (mergeComponentRightIndex W k heq j).val <
          (W.toOrthogonalDecomposition.componentRank k.succ - 1 + 1) +
            W.toOrthogonalDecomposition.componentRank k.castSucc
        dsimp only [mergeComponentRightIndex]
        omega⟩ = orthogonalProductRightIndex
          (W.toOrthogonalDecomposition.componentRank k.castSucc) jr := by
    apply Fin.ext
    dsimp only [mergeComponentRightIndex,
      orthogonalProductRightIndex, jr]
  change ((((transported.castLength _).ambientVector
      (mergeComponentRightIndex W k heq j) :
        (W.mergeAdjacentAt k heq).component k |>.carrier) : V)) = _
  rw [BONG.ambientVector_castLength]
  change (((transported.ambientVector ⟨_, _⟩ :
      (W.mergeAdjacentAt k heq).component k |>.carrier) : V)) = _
  rw [BONG.ambientVector_castQuadraticSublattice]
  change (((mapped.ambientVector ⟨_, _⟩ :
      (W.toOrthogonalDecomposition.orthogonalSup
        k.castSucc_lt_succ.ne).carrier) : V)) = _
  rw [BONG.ambientVector_mapLatticeIsometry]
  change ((W.toOrthogonalDecomposition.orthogonalSupEquiv
      k.castSucc_lt_succ.ne (raw.ambientVector ⟨_, _⟩) : V)) = _
  rw [hindex, BONG.ambientVector_orthogonalProductRight_right,
    W.toOrthogonalDecomposition.coe_orthogonalSupEquiv]
  simp
  dsimp only [right]
  rw [BONG.ambientVector_castLength]

theorem mergeComponentBONGFamily_ambientVector {t : Nat}
    (W : Lattice.WeakJordanDecomposition q L (t + 1))
    (c : W.toOrthogonalDecomposition.ComponentBONGFamily)
    (hlocal : ∀ i j, (c i).order j ≤
      (c i).order (weakComponentHeadIndex W i))
    (hhead : ∀ i, (c i).order (weakComponentHeadIndex W i) =
      ordUnit K (W.normGeneratorUnit i))
    (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ))
    (hnorm : ordUnit K (W.normGeneratorUnit k.castSucc) =
      ordUnit K (W.normGeneratorUnit k.succ))
    (z : Σ j : Fin t, Fin
      ((W.mergeAdjacentAt k heq).toOrthogonalDecomposition.componentRank j)) :
    componentFamilyAmbientVector
        (mergeComponentBONGFamily W c hlocal hhead k heq hnorm) z =
      componentFamilyAmbientVector c (W.mergeIndexEquiv k heq z) := by
  classical
  rcases z with ⟨j, ell⟩
  unfold componentFamilyAmbientVector
  by_cases hj : j = k
  · subst j
    by_cases hleft : ell.val <
        W.toOrthogonalDecomposition.componentRank k.castSucc
    · let i : Fin (W.toOrthogonalDecomposition.componentRank k.castSucc) :=
        ⟨ell.val, hleft⟩
      have hell : ell = mergeComponentLeftIndex W k heq i := by
        apply Fin.ext
        rfl
      rw [hell]
      change ((((mergeComponentBONGFamily W c hlocal hhead k heq hnorm k).ambientVector
        (mergeComponentLeftIndex W k heq i) :
          (W.mergeAdjacentAt k heq).component k |>.carrier) : V)) = _
      rw [mergeComponentBONGFamily_self]
      calc
        _ = (((c k.castSucc).ambientVector i :
              W.component k.castSucc |>.carrier) : V) := by
          simpa only [Lattice.OrthogonalDecomposition.componentRank] using
            mergeComponentBONG_ambientVector_left
              W c hlocal hhead k heq hnorm i
        _ = _ := by
          have hmap := W.mergeIndexEquiv_left k heq i
          have hvmap := congrArg (componentFamilyAmbientVector c) hmap
          exact hvmap.symm
    · have hrightBound :
          ell.val - W.toOrthogonalDecomposition.componentRank k.castSucc <
            W.toOrthogonalDecomposition.componentRank k.succ := by
        have hrank :
            (W.mergeAdjacentAt k heq).toOrthogonalDecomposition.componentRank k =
              W.toOrthogonalDecomposition.componentRank k.castSucc +
                W.toOrthogonalDecomposition.componentRank k.succ := by
          exact W.mergeAdjacentAt_componentRank_self k heq
        have hellBound := ell.isLt
        omega
      let i : Fin (W.toOrthogonalDecomposition.componentRank k.succ) :=
        ⟨ell.val - W.toOrthogonalDecomposition.componentRank k.castSucc,
          hrightBound⟩
      have hell : ell = mergeComponentRightIndex W k heq i := by
        apply Fin.ext
        dsimp only [mergeComponentRightIndex, i]
        omega
      rw [hell]
      change ((((mergeComponentBONGFamily W c hlocal hhead k heq hnorm k).ambientVector
        (mergeComponentRightIndex W k heq i) :
          (W.mergeAdjacentAt k heq).component k |>.carrier) : V)) = _
      rw [mergeComponentBONGFamily_self]
      calc
        _ = (((c k.succ).ambientVector i :
              W.component k.succ |>.carrier) : V) := by
          simpa only [Lattice.OrthogonalDecomposition.componentRank] using
            mergeComponentBONG_ambientVector_right
              W c hlocal hhead k heq hnorm i
        _ = _ := by
          have hmap := W.mergeIndexEquiv_right k heq i
          have hvmap := congrArg (componentFamilyAmbientVector c) hmap
          exact hvmap.symm
  · rw [mergeComponentBONGFamily_of_ne W c hlocal hhead k heq hnorm j hj]
    rcases lt_or_gt_of_ne hj with hjk | hkj
    · have hmap := W.mergeIndexEquiv_of_lt k heq j hjk ell
      simp only [BONG.ambientVector_castLength,
        BONG.ambientVector_castQuadraticSublattice]
      have hskip : k.succ.succAbove j = j.castSucc := by
        rw [Fin.succAbove_of_castSucc_lt]
        exact Fin.castSucc_lt_succ_iff.mpr hjk.le
      change componentFamilyAmbientVector c
          ⟨k.succ.succAbove j, ⟨ell.val, _⟩⟩ =
        componentFamilyAmbientVector c (W.mergeIndexEquiv k heq ⟨j, ell⟩)
      apply congrArg (componentFamilyAmbientVector c)
      calc
        ⟨k.succ.succAbove j, ⟨ell.val, _⟩⟩ =
            ⟨j.castSucc, ⟨ell.val, _⟩⟩ := by
          apply Sigma.ext
          · exact hskip
          · exact (Fin.heq_ext_iff (congrArg
              W.toOrthogonalDecomposition.componentRank hskip)).2 rfl
        _ = W.mergeIndexEquiv k heq ⟨j, ell⟩ := hmap.symm
    · have hmap := W.mergeIndexEquiv_of_gt k heq j hkj ell
      simp only [BONG.ambientVector_castLength,
        BONG.ambientVector_castQuadraticSublattice]
      have hskip : k.succ.succAbove j = j.succ := by
        rw [Fin.succAbove_of_le_castSucc]
        exact Fin.succ_le_castSucc_iff.mpr hkj
      change componentFamilyAmbientVector c
          ⟨k.succ.succAbove j, ⟨ell.val, _⟩⟩ =
        componentFamilyAmbientVector c (W.mergeIndexEquiv k heq ⟨j, ell⟩)
      apply congrArg (componentFamilyAmbientVector c)
      calc
        ⟨k.succ.succAbove j, ⟨ell.val, _⟩⟩ =
            ⟨j.succ, ⟨ell.val, _⟩⟩ := by
          apply Sigma.ext
          · exact hskip
          · exact (Fin.heq_ext_iff (congrArg
              W.toOrthogonalDecomposition.componentRank hskip)).2 rfl
        _ = W.mergeIndexEquiv k heq ⟨j, ell⟩ := hmap.symm

namespace PutTogetherWitness

noncomputable def mergeAdjacentAtAdapted {n t : Nat}
    {b : BONG V q L n}
    (W : Lattice.WeakJordanDecomposition q L (t + 1))
    (c : W.toOrthogonalDecomposition.ComponentBONGFamily)
    (hlocal : ∀ i j, (c i).order j ≤
      (c i).order (weakComponentHeadIndex W i))
    (hhead : ∀ i, (c i).order (weakComponentHeadIndex W i) =
      ordUnit K (W.normGeneratorUnit i))
    (w : PutTogetherWitness b W.toOrthogonalDecomposition c)
    (k : Fin t)
    (heq : ordUnit K (W.scaleGenerator k.castSucc) =
      ordUnit K (W.scaleGenerator k.succ))
    (hnorm : ordUnit K (W.normGeneratorUnit k.castSucc) =
      ordUnit K (W.normGeneratorUnit k.succ)) :
    PutTogetherWitness b (W.mergeAdjacentAt k heq).toOrthogonalDecomposition
      (mergeComponentBONGFamily W c hlocal hhead k heq hnorm) where
  indexEquiv := w.indexEquiv.trans (W.mergeIndexEquiv k heq).symm
  order_iff := by
    intro i j
    let x := (W.mergeIndexEquiv k heq).symm (w.indexEquiv i)
    let y := (W.mergeIndexEquiv k heq).symm (w.indexEquiv j)
    have hx : W.mergeIndexOrderIso k heq (toLex x) =
        toLex (w.indexEquiv i) := by
      rw [← W.toLex_mergeIndexEquiv]
      simp only [x, (W.mergeIndexEquiv k heq).apply_symm_apply]
      rfl
    have hy : W.mergeIndexOrderIso k heq (toLex y) =
        toLex (w.indexEquiv j) := by
      rw [← W.toLex_mergeIndexEquiv]
      simp only [y, (W.mergeIndexEquiv k heq).apply_symm_apply]
      rfl
    change i < j ↔ BONG.ComponentIndexBefore
      (W.mergeAdjacentAt k heq).toOrthogonalDecomposition x y
    rw [JordanOrderProfileWitness.componentIndexBefore_iff_lex_lt]
    constructor
    · intro hij
      have holdComponent := (w.order_iff i j).1 hij
      have hold : toLex (w.indexEquiv i) < toLex (w.indexEquiv j) :=
        (JordanOrderProfileWitness.componentIndexBefore_iff_lex_lt
          W.toOrthogonalDecomposition (w.indexEquiv i) (w.indexEquiv j)).1
          holdComponent
      have hmapped : W.mergeIndexOrderIso k heq (toLex x) <
          W.mergeIndexOrderIso k heq (toLex y) := by
        rwa [hx, hy]
      exact (W.mergeIndexOrderIso k heq).lt_iff_lt.mp hmapped
    · intro hnew
      apply (w.order_iff i j).2
      apply (JordanOrderProfileWitness.componentIndexBefore_iff_lex_lt
        W.toOrthogonalDecomposition (w.indexEquiv i) (w.indexEquiv j)).2
      have hmapped : W.mergeIndexOrderIso k heq (toLex x) <
          W.mergeIndexOrderIso k heq (toLex y) :=
        (W.mergeIndexOrderIso k heq).lt_iff_lt.mpr hnew
      rwa [hx, hy] at hmapped
  ambientVector_eq := by
    intro i
    let z := (W.mergeIndexEquiv k heq).symm (w.indexEquiv i)
    have hz : W.mergeIndexEquiv k heq z = w.indexEquiv i :=
      (W.mergeIndexEquiv k heq).apply_symm_apply (w.indexEquiv i)
    change b.ambientVector i = componentFamilyAmbientVector
      (mergeComponentBONGFamily W c hlocal hhead k heq hnorm) z
    calc
      b.ambientVector i = componentFamilyAmbientVector c (w.indexEquiv i) := by
        exact w.ambientVector_eq i
      _ = componentFamilyAmbientVector c (W.mergeIndexEquiv k heq z) := by
        rw [hz]
      _ = componentFamilyAmbientVector
          (mergeComponentBONGFamily W c hlocal hhead k heq hnorm) z :=
        (mergeComponentBONGFamily_ambientVector
          W c hlocal hhead k heq hnorm z).symm

end PutTogetherWitness

end BONG
end Bong
