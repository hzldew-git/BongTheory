/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.Jordan
import Bong.Lattice.ModularSplitting
import Bong.Lattice.NormGeneratorValues

/-!
# Ideals of a finite orthogonal decomposition

For an integral orthogonal decomposition, the scale and norm ideals of the
whole lattice are the suprema of the corresponding component ideals.  The
norm calculation uses `2 B(x,y) \in nL` inside a component; pairings between
distinct components vanish.
-/

namespace Bong

open Dyadic

namespace Lattice
namespace OrthogonalDecomposition

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {t : Nat}

/-- The scale ideal of an orthogonal decomposition is the supremum of the
component scale ideals. -/
theorem scaleIdeal_eq_iSup_component
    (D : OrthogonalDecomposition q L t) :
    scaleIdeal q L =
      ⨆ i, scaleIdeal (D.component i).space (D.component i).lattice := by
  let S : Submodule (IntegerRing K) V :=
    ⨆ i, (D.component i).ambientSubmodule
  let I : CoefficientIdeal (K := K) :=
    ⨆ i, scaleIdeal (D.component i).space (D.component i).lattice
  have hpair : ∀ {x y : V}, x ∈ S → y ∈ S → q.bilin x y ∈ I := by
    intro x y hx hy
    change x ∈ ⨆ i, (D.component i).ambientSubmodule at hx
    change y ∈ ⨆ i, (D.component i).ambientSubmodule at hy
    refine Submodule.iSup_induction
      (p := fun i ↦ (D.component i).ambientSubmodule)
      (motive := fun z ↦ q.bilin z y ∈ I) hx ?_ ?_ ?_
    · intro i x hxi
      refine Submodule.iSup_induction
        (p := fun j ↦ (D.component j).ambientSubmodule)
        (motive := fun z ↦ q.bilin x z ∈ I) hy ?_ ?_ ?_
      · intro j y hyj
        rcases hxi with ⟨xi, hxiL, rfl⟩
        rcases hyj with ⟨yj, hyjL, rfl⟩
        by_cases hij : i = j
        · subst j
          apply le_iSup
              (fun k ↦ scaleIdeal (D.component k).space
                (D.component k).lattice) i
          exact bilin_mem_scaleIdeal (D.component i).space
            (D.component i).lattice ⟨xi, hxiL⟩ ⟨yj, hyjL⟩
        · change q.bilin (xi : V) (yj : V) ∈ I
          rw [D.orthogonal i j hij xi yj]
          exact Submodule.zero_mem I
      · simp [I]
      · intro y z hyI hzI
        rw [LinearMap.BilinForm.add_right]
        exact I.add_mem hyI hzI
    · simp [I]
    · intro x z hxI hzI
      rw [LinearMap.BilinForm.add_left]
      exact I.add_mem hxI hzI
  apply le_antisymm
  · rw [scaleIdeal, Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    apply hpair
    · change (p.1 : V) ∈ ⨆ i, (D.component i).ambientSubmodule
      rw [D.sum_eq]
      exact p.1.property
    · change (p.2 : V) ∈ ⨆ i, (D.component i).ambientSubmodule
      rw [D.sum_eq]
      exact p.2.property
  · apply iSup_le
    intro i
    rw [scaleIdeal, Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    change q.bilin (p.1 : V) (p.2 : V) ∈ scaleIdeal q L
    exact bilin_mem_scaleIdeal_of_mem q L
      (D.component_ambientSubmodule_le i ⟨p.1, p.1.property, rfl⟩)
      (D.component_ambientSubmodule_le i ⟨p.2, p.2.property, rfl⟩)

/-- The norm ideal of an orthogonal decomposition is the supremum of the
component norm ideals. -/
theorem normIdeal_eq_iSup_component
    (D : OrthogonalDecomposition q L t) :
    normIdeal q L =
      ⨆ i, normIdeal (D.component i).space (D.component i).lattice := by
  let S : Submodule (IntegerRing K) V :=
    ⨆ i, (D.component i).ambientSubmodule
  let I : CoefficientIdeal (K := K) :=
    ⨆ i, normIdeal (D.component i).space (D.component i).lattice
  have hpair : ∀ {x y : V}, x ∈ S → y ∈ S →
      (2 : IntegerRing K) • q.bilin x y ∈ I := by
    intro x y hx hy
    change x ∈ ⨆ i, (D.component i).ambientSubmodule at hx
    change y ∈ ⨆ i, (D.component i).ambientSubmodule at hy
    refine Submodule.iSup_induction
      (p := fun i ↦ (D.component i).ambientSubmodule)
      (motive := fun z ↦ (2 : IntegerRing K) • q.bilin z y ∈ I)
      hx ?_ ?_ ?_
    · intro i x hxi
      refine Submodule.iSup_induction
        (p := fun j ↦ (D.component j).ambientSubmodule)
        (motive := fun z ↦
          (2 : IntegerRing K) • q.bilin x z ∈ I) hy ?_ ?_ ?_
      · intro j y hyj
        rcases hxi with ⟨xi, hxiL, rfl⟩
        rcases hyj with ⟨yj, hyjL, rfl⟩
        by_cases hij : i = j
        · subst j
          apply le_iSup
              (fun k ↦ normIdeal (D.component k).space
                (D.component k).lattice) i
          exact two_smul_mem_normIdeal (D.component i).space
            (D.component i).lattice
            (bilin_mem_scaleIdeal (D.component i).space
              (D.component i).lattice ⟨xi, hxiL⟩ ⟨yj, hyjL⟩)
        · change (2 : IntegerRing K) • q.bilin (xi : V) (yj : V) ∈ I
          rw [D.orthogonal i j hij xi yj]
          exact Submodule.smul_mem I 2 (Submodule.zero_mem I)
      · simp [I]
      · intro y z hyI hzI
        rw [LinearMap.BilinForm.add_right, smul_add]
        exact I.add_mem hyI hzI
    · simp [I]
    · intro x z hxI hzI
      rw [LinearMap.BilinForm.add_left, smul_add]
      exact I.add_mem hxI hzI
  have hquadratic : ∀ {x : V}, x ∈ S → q.quadratic x ∈ I := by
    intro x hx
    change x ∈ ⨆ i, (D.component i).ambientSubmodule at hx
    induction hx using Submodule.iSup_induction' with
    | mem i x hxi =>
        rcases hxi with ⟨xi, hxiL, rfl⟩
        apply le_iSup
            (fun k ↦ normIdeal (D.component k).space
              (D.component k).lattice) i
        exact quadratic_mem_normIdeal_of_mem (D.component i).space
          (D.component i).lattice hxiL
    | zero => simp [I]
    | add x y hx hy hxI hyI =>
        have hxy := hpair hx hy
        rw [q.quadratic_add]
        have hsum := I.add_mem (I.add_mem hxI hyI) hxy
        simpa only [Algebra.smul_def, map_ofNat] using hsum
  apply le_antisymm
  · apply normIdeal_le_of_quadratic_mem q L
    intro x hx
    apply hquadratic
    change x ∈ ⨆ i, (D.component i).ambientSubmodule
    rw [D.sum_eq]
    exact hx
  · apply iSup_le
    intro i
    rw [normIdeal, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    change q.quadratic (x : V) ∈ normIdeal q L
    exact quadratic_mem_normIdeal_of_mem q L
      (D.component_ambientSubmodule_le i ⟨x, x.property, rfl⟩)

/-- A vector in the sum of any injectively selected family of orthogonal
components has quadratic value in the supremum of their norm ideals. -/
theorem quadratic_mem_iSup_component_normIdeal
    (D : OrthogonalDecomposition q L t)
    {ι : Type*} (e : ι → Fin t) (he : Function.Injective e)
    {x : V}
    (hx : x ∈ ⨆ i, (D.component (e i)).ambientSubmodule) :
    q.quadratic x ∈
      ⨆ i, normIdeal (D.component (e i)).space
        (D.component (e i)).lattice := by
  let S : Submodule (IntegerRing K) V :=
    ⨆ i, (D.component (e i)).ambientSubmodule
  let I : CoefficientIdeal (K := K) :=
    ⨆ i, normIdeal (D.component (e i)).space
      (D.component (e i)).lattice
  have hpair : ∀ {y z : V}, y ∈ S → z ∈ S →
      (2 : IntegerRing K) • q.bilin y z ∈ I := by
    intro y z hy hz
    change y ∈ ⨆ i, (D.component (e i)).ambientSubmodule at hy
    change z ∈ ⨆ i, (D.component (e i)).ambientSubmodule at hz
    refine Submodule.iSup_induction
      (p := fun i ↦ (D.component (e i)).ambientSubmodule)
      (motive := fun w ↦ (2 : IntegerRing K) • q.bilin w z ∈ I)
      hy ?_ ?_ ?_
    · intro i y hyi
      refine Submodule.iSup_induction
        (p := fun j ↦ (D.component (e j)).ambientSubmodule)
        (motive := fun w ↦ (2 : IntegerRing K) • q.bilin y w ∈ I)
        hz ?_ ?_ ?_
      · intro j z hzj
        rcases hyi with ⟨yi, hyiL, rfl⟩
        rcases hzj with ⟨zj, hzjL, rfl⟩
        by_cases hij : i = j
        · subst j
          apply le_iSup
              (fun k ↦ normIdeal (D.component (e k)).space
                (D.component (e k)).lattice) i
          exact two_smul_mem_normIdeal (D.component (e i)).space
            (D.component (e i)).lattice
            (bilin_mem_scaleIdeal (D.component (e i)).space
              (D.component (e i)).lattice ⟨yi, hyiL⟩ ⟨zj, hzjL⟩)
        · change (2 : IntegerRing K) •
              q.bilin (yi : V) (zj : V) ∈ I
          rw [D.orthogonal (e i) (e j) (fun h ↦ hij (he h)) yi zj]
          exact Submodule.smul_mem I 2 (Submodule.zero_mem I)
      · simp [I]
      · intro y z hyI hzI
        rw [LinearMap.BilinForm.add_right, smul_add]
        exact I.add_mem hyI hzI
    · simp [I]
    · intro y z hyI hzI
      rw [LinearMap.BilinForm.add_left, smul_add]
      exact I.add_mem hyI hzI
  change x ∈ S at hx
  induction hx using Submodule.iSup_induction' with
  | mem i x hxi =>
      rcases hxi with ⟨xi, hxiL, rfl⟩
      apply le_iSup
          (fun k ↦ normIdeal (D.component (e k)).space
            (D.component (e k)).lattice) i
      exact quadratic_mem_normIdeal_of_mem (D.component (e i)).space
        (D.component (e i)).lattice hxiL
  | zero => simp [I]
  | add x y hx hy hxI hyI =>
      have hxy := hpair hx hy
      rw [q.quadratic_add]
      have hsum := I.add_mem (I.add_mem hxI hyI) hxy
      simpa only [Algebra.smul_def, map_ofNat] using hsum

/-- Splitting one index out of a finite supremum of component lattices. -/
theorem iSup_component_eq_sup_iSup_ne
    (D : OrthogonalDecomposition q L t) (i : Fin t) :
    (⨆ j, (D.component j).ambientSubmodule) =
      (D.component i).ambientSubmodule ⊔
        ⨆ j : {j : Fin t // j ≠ i},
          (D.component j.1).ambientSubmodule := by
  apply le_antisymm
  · apply iSup_le
    intro j
    by_cases hji : j = i
    · subst j
      exact (_root_.le_sup_left :
        (D.component i).ambientSubmodule ≤
          (D.component i).ambientSubmodule ⊔
            ⨆ j : {j : Fin t // j ≠ i},
              (D.component j.1).ambientSubmodule)
    · exact le_trans
        (le_iSup
          (fun k : {k : Fin t // k ≠ i} ↦
            (D.component k.1).ambientSubmodule) ⟨j, hji⟩)
        (_root_.le_sup_right :
          (⨆ j : {j : Fin t // j ≠ i},
              (D.component j.1).ambientSubmodule) ≤
            (D.component i).ambientSubmodule ⊔
              ⨆ j : {j : Fin t // j ≠ i},
                (D.component j.1).ambientSubmodule)
  · apply _root_.sup_le
    · exact le_iSup (fun j ↦ (D.component j).ambientSubmodule) i
    · apply iSup_le
      intro j
      exact le_iSup (fun k ↦ (D.component k).ambientSubmodule) j.1

/-- The integral sum of all components other than `i` is orthogonal to the
carrier of component `i`. -/
theorem bilin_eq_zero_of_mem_iSup_ne
    (D : OrthogonalDecomposition q L t) (i : Fin t) {z : V}
    (hz : z ∈ ⨆ j : {j : Fin t // j ≠ i},
      (D.component j.1).ambientSubmodule)
    (y : (D.component i).carrier) : q.bilin z (y : V) = 0 := by
  refine Submodule.iSup_induction
    (p := fun j : {j : Fin t // j ≠ i} ↦
      (D.component j.1).ambientSubmodule)
    (motive := fun w ↦ q.bilin w (y : V) = 0) hz ?_ ?_ ?_
  · intro j w hw
    rcases hw with ⟨wj, hwjL, rfl⟩
    change q.bilin (wj : V) (y : V) = 0
    exact D.orthogonal j.1 i j.2 wj y
  · simp
  · intro w z hw hz
    rw [LinearMap.BilinForm.add_left, hw, hz, add_zero]

/-- An integral vector orthogonal to one component belongs to the integral
sum of all the other components. -/
theorem mem_iSup_ne_of_mem_orthogonalCarrier
    (D : OrthogonalDecomposition q L t) (i : Fin t)
    (x : (D.component i).orthogonalCarrier) (hx : (x : V) ∈ L) :
    (x : V) ∈
      ⨆ j : {j : Fin t // j ≠ i},
        (D.component j.1).ambientSubmodule := by
  have hxAll : (x : V) ∈ ⨆ j, (D.component j).ambientSubmodule := by
    rw [D.sum_eq]
    exact hx
  rw [D.iSup_component_eq_sup_iSup_ne i] at hxAll
  rcases Submodule.mem_sup.mp hxAll with ⟨a, ha, b, hb, hab⟩
  rcases ha with ⟨ai, haiL, haiEq⟩
  have haiEq' : (ai : V) = a := by
    simpa using haiEq
  have haOrth : ∀ y : (D.component i).carrier,
      q.bilin a (y : V) = 0 := by
    intro y
    have hsum := congrArg (fun z : V ↦ q.bilin z (y : V)) hab
    have hxOrth : q.bilin (x : V) (y : V) = 0 := by
      rw [q.isSymm.eq (x : V) (y : V)]
      exact x.property (y : V) y.property
    have hbOrth : q.bilin b (y : V) = 0 :=
      D.bilin_eq_zero_of_mem_iSup_ne i hb y
    simpa only [LinearMap.BilinForm.add_left, hbOrth, add_zero,
      hxOrth] using hsum
  have haiOrth : ∀ y : (D.component i).carrier,
      (D.component i).space.bilin ai y = 0 := by
    intro y
    change q.bilin (ai : V) (y : V) = 0
    rw [haiEq']
    exact haOrth y
  have haiZero : ai = 0 := (D.component i).nondegenerate.1 ai haiOrth
  have haZero : a = 0 := by
    rw [← haiEq', haiZero]
    rfl
  have hbx : b = (x : V) := by
    simpa only [haZero, zero_add] using hab
  rw [← hbx]
  exact hb

end OrthogonalDecomposition

namespace JordanDecomposition

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {t : Nat}

/-- Every component recorded by a Jordan decomposition has positive rank.
Indeed, its scale ideal is generated by a nonzero element, whereas a
zero-dimensional component has zero scale ideal. -/
theorem component_finrank_pos (J : JordanDecomposition q L t) (i : Fin t) :
    0 < Module.finrank K (J.component i).carrier := by
  letI : Module.Finite K (J.component i).carrier :=
    (J.component i).lattice.moduleFinite
  by_contra hpos
  have hzero : Module.finrank K (J.component i).carrier = 0 :=
    Nat.eq_zero_of_not_pos hpos
  letI : Subsingleton (J.component i).carrier :=
    Module.finrank_zero_iff.mp hzero
  have hle : scaleIdeal (J.component i).space
        (J.component i).lattice ≤ ⊥ := by
    rw [scaleIdeal, Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    have hx : (p.1 : (J.component i).carrier) = 0 :=
      Subsingleton.elim _ _
    have hy : (p.2 : (J.component i).carrier) = 0 :=
      Subsingleton.elim _ _
    simp [hx, hy]
  have hgenerator : (J.scaleGenerator i : K) ∈
      scaleIdeal (J.component i).space (J.component i).lattice := by
    rw [J.scaleIdeal_eq i]
    exact generator_mem_principalIdeal _
  have : (J.scaleGenerator i : K) = 0 := by
    simpa only [Submodule.mem_bot] using hle hgenerator
  exact (Units.ne_zero (J.scaleGenerator i)) this

/-- In a nonempty Jordan decomposition, the first modular scale generates
the scale ideal of the whole lattice. -/
theorem scaleIdeal_eq_first (J : JordanDecomposition q L t) (ht : 0 < t) :
    scaleIdeal q L =
      principalIdeal (K := K) (J.scaleGenerator ⟨0, ht⟩ : K) := by
  rw [J.toOrthogonalDecomposition.scaleIdeal_eq_iSup_component]
  apply le_antisymm
  · apply iSup_le
    intro i
    rw [J.scaleIdeal_eq i]
    by_cases hi : i = ⟨0, ht⟩
    · subst i
      exact le_rfl
    · apply (principalIdeal_le_iff_ord_ge
          (Units.ne_zero (J.scaleGenerator i))
          (Units.ne_zero (J.scaleGenerator ⟨0, ht⟩))).2
      have hzero_lt : (⟨0, ht⟩ : Fin t) < i := by
        change 0 < i.val
        by_contra h
        apply hi
        apply Fin.ext
        exact Nat.eq_zero_of_not_pos h
      have hlt : ordUnit K (J.scaleGenerator ⟨0, ht⟩) <
          ordUnit K (J.scaleGenerator i) :=
        J.scaleOrder_strict hzero_lt
      simpa only [coe_ordUnit] using
        (WithTop.coe_le_coe.mpr hlt.le)
  · rw [← J.scaleIdeal_eq ⟨0, ht⟩]
    exact le_iSup
      (fun i ↦ scaleIdeal (J.component i).space (J.component i).lattice)
      ⟨0, ht⟩

/-- For a nonempty property-A Jordan decomposition, the first component norm
generates the norm ideal of the whole lattice. -/
theorem normIdeal_eq_first (J : JordanDecomposition q L t)
    (hA : J.HasPropertyA) (ht : 0 < t) :
    normIdeal q L =
      principalIdeal (K := K) (J.normGenerator ⟨0, ht⟩ : K) := by
  rw [J.toOrthogonalDecomposition.normIdeal_eq_iSup_component]
  apply le_antisymm
  · apply iSup_le
    intro i
    rw [J.normIdeal_eq i]
    by_cases hi : i = ⟨0, ht⟩
    · subst i
      exact le_rfl
    · apply (principalIdeal_le_iff_ord_ge
          (Units.ne_zero (J.normGenerator i))
          (Units.ne_zero (J.normGenerator ⟨0, ht⟩))).2
      have hzero_lt : (⟨0, ht⟩ : Fin t) < i := by
        change 0 < i.val
        by_contra h
        apply hi
        apply Fin.ext
        exact Nat.eq_zero_of_not_pos h
      have hgap := hA.2 hzero_lt
      have hlt : ordUnit K (J.normGenerator ⟨0, ht⟩) <
          ordUnit K (J.normGenerator i) := by
        omega
      simpa only [coe_ordUnit] using
        (WithTop.coe_le_coe.mpr hlt.le)
  · rw [← J.normIdeal_eq ⟨0, ht⟩]
    exact le_iSup
      (fun i ↦ normIdeal (J.component i).space (J.component i).lattice)
      ⟨0, ht⟩

/-- Pairing a vector of the first Jordan component with any vector of the
ambient lattice lies in the first modular scale. -/
theorem firstComponent_pairing (J : JordanDecomposition q L t) (ht : 0 < t)
    (y : (J.component ⟨0, ht⟩).carrier)
    (hy : y ∈ (J.component ⟨0, ht⟩).lattice)
    (x : V) (hx : x ∈ L) :
    q.bilin (y : V) x ∈
      principalIdeal (K := K) (J.scaleGenerator ⟨0, ht⟩ : K) := by
  rw [← J.scaleIdeal_eq_first ht]
  exact bilin_mem_scaleIdeal_of_mem q L
    (J.toOrthogonalDecomposition.component_ambientSubmodule_le ⟨0, ht⟩
      ⟨y, hy, rfl⟩) hx

/-- The orthogonal projection of an integral vector to the first Jordan
component is integral in that component. -/
theorem firstCarrierProjection_mem_lattice
    [FiniteDimensional K V]
    (J : JordanDecomposition q L t) (ht : 0 < t)
    (x : V) (hx : x ∈ L) :
    (J.component ⟨0, ht⟩).carrierProjection x ∈
      (J.component ⟨0, ht⟩).lattice := by
  exact (J.component ⟨0, ht⟩).carrierProjection_mem_lattice_of_pairing
    (J.modular ⟨0, ht⟩)
    (fun y hy w hw ↦ J.firstComponent_pairing ht y hy w hw) hx

/-- If the first-component projection is divisible by the uniformizer inside
that component, then its quadratic value is one uniformizer deeper than the
first component norm ideal. -/
theorem firstCarrierProjection_quadratic_mem_nextNorm_of_mem_rescale
    [FiniteDimensional K V]
    (J : JordanDecomposition q L t) (ht : 0 < t) (x : V)
    (hscaled : (J.component ⟨0, ht⟩).carrierProjection x ∈
      rescale (uniformizerUnit K) (J.component ⟨0, ht⟩).lattice) :
    q.quadratic ((J.component ⟨0, ht⟩).carrierProjection x : V) ∈
      principalIdeal (K := K)
        (((J.normGenerator ⟨0, ht⟩) * uniformizerUnit K : Kˣ) : K) := by
  let C := J.component ⟨0, ht⟩
  let p : C.carrier := C.carrierProjection x
  change p ∈ rescale (uniformizerUnit K) C.lattice at hscaled
  rw [mem_rescale_iff] at hscaled
  rcases hscaled with ⟨w, hw, hp⟩
  have hqw : C.space.quadratic w ∈
      normIdeal C.space C.lattice :=
    quadratic_mem_normIdeal_of_mem C.space C.lattice hw
  rw [show normIdeal C.space C.lattice =
      principalIdeal (K := K) (J.normGenerator ⟨0, ht⟩ : K) by
        simpa [C] using J.normIdeal_eq ⟨0, ht⟩,
    principalIdeal, Submodule.mem_span_singleton] at hqw
  rcases hqw with ⟨c, hc⟩
  let piO : IntegerRing K :=
    ⟨uniformizer K, (mem_integerRing_iff K).2 (by
      rw [Dyadic.IsIntegral, ord_uniformizer]
      norm_num)⟩
  rw [principalIdeal, Submodule.mem_span_singleton]
  refine ⟨piO * c, ?_⟩
  have hpV : (uniformizer K) • (w : V) = (p : V) := by
    simpa [coe_uniformizerUnit] using congrArg Subtype.val hp
  have hrestrict : C.space.quadratic w = q.quadratic (w : V) :=
    rfl
  have hcK' : algebraMap (IntegerRing K) K c *
      (J.normGenerator ⟨0, ht⟩ : K) = q.quadratic (w : V) := by
    simpa only [Algebra.smul_def, hrestrict] using hc
  have hcK : (c : K) * (J.normGenerator ⟨0, ht⟩ : K) =
      q.quadratic (w : V) := by
    rw [ValuationSubring.algebraMap_apply (IntegerRing K) c] at hcK'
    exact hcK'
  have hpiOc : ((piO * c : IntegerRing K) : K) =
      uniformizer K * (c : K) :=
    rfl
  change (((piO * c : IntegerRing K) : K) *
      (((J.normGenerator ⟨0, ht⟩) * uniformizerUnit K : Kˣ) : K)) =
        q.quadratic (p : V)
  rw [← hpV, q.quadratic_smul]
  rw [hpiOc]
  simp only [coe_uniformizerUnit, Units.val_mul]
  rw [← hcK]
  ring

/-- The complementary projection attached to the first Jordan component is
an integral vector of the ambient lattice. -/
theorem firstOrthogonalProjection_mem_lattice
    [FiniteDimensional K V]
    (J : JordanDecomposition q L t) (ht : 0 < t)
    (x : V) (hx : x ∈ L) :
    ((J.component ⟨0, ht⟩).orthogonalProjection x : V) ∈ L := by
  exact (J.component ⟨0, ht⟩).orthogonalProjection_mem_lattice
    (J.toOrthogonalDecomposition.component_ambientSubmodule_le ⟨0, ht⟩)
    (J.modular ⟨0, ht⟩)
    (fun y hy w hw ↦ J.firstComponent_pairing ht y hy w hw) hx

/-- In a property-A Jordan decomposition, the complementary projection of an
integral vector has quadratic value in the ideal one uniformizer deeper than
the first component norm. -/
theorem firstOrthogonalProjection_quadratic_mem_nextNorm
    [FiniteDimensional K V]
    (J : JordanDecomposition q L t) (hA : J.HasPropertyA) (ht : 0 < t)
    (x : V) (hx : x ∈ L) :
    q.quadratic
        ((J.component ⟨0, ht⟩).orthogonalProjection x : V) ∈
      principalIdeal (K := K)
        (((J.normGenerator ⟨0, ht⟩) * uniformizerUnit K : Kˣ) : K) := by
  let i0 : Fin t := ⟨0, ht⟩
  let z : (J.component i0).orthogonalCarrier :=
    (J.component i0).orthogonalProjection x
  have hzL : (z : V) ∈ L := by
    simpa [i0, z] using
      J.firstOrthogonalProjection_mem_lattice ht x hx
  have hzTail : (z : V) ∈
      ⨆ j : {j : Fin t // j ≠ i0},
        (J.component j.1).ambientSubmodule :=
    J.toOrthogonalDecomposition.mem_iSup_ne_of_mem_orthogonalCarrier
      i0 z hzL
  have hqTail : q.quadratic (z : V) ∈
      ⨆ j : {j : Fin t // j ≠ i0},
        normIdeal (J.component j.1).space
          (J.component j.1).lattice :=
    J.toOrthogonalDecomposition.quadratic_mem_iSup_component_normIdeal
      (fun j : {j : Fin t // j ≠ i0} ↦ j.1)
      Subtype.val_injective hzTail
  apply (show
      (⨆ j : {j : Fin t // j ≠ i0},
          normIdeal (J.component j.1).space
            (J.component j.1).lattice) ≤
        principalIdeal (K := K)
          (((J.normGenerator i0) * uniformizerUnit K : Kˣ) : K)
      from ?_) hqTail
  apply iSup_le
  intro j
  rw [J.normIdeal_eq j.1]
  apply (principalIdeal_le_iff_ord_ge
    (Units.ne_zero (J.normGenerator j.1))
    (Units.ne_zero (J.normGenerator i0 * uniformizerUnit K))).2
  have hi0j : i0 < j.1 := by
    change 0 < j.1.val
    by_contra h
    apply j.2
    apply Fin.ext
    simpa [i0] using Nat.eq_zero_of_not_pos h
  have hgap := (hA.2 hi0j).1
  have hpi : ordUnit K (uniformizerUnit K) = 1 := by
    apply WithTop.coe_injective
    rw [coe_ordUnit, coe_uniformizerUnit, ord_uniformizer]
    rfl
  have horder :
      ordUnit K (J.normGenerator i0 * uniformizerUnit K) ≤
        ordUnit K (J.normGenerator j.1) := by
    rw [ordUnit_mul, hpi]
    omega
  simpa only [coe_ordUnit] using WithTop.coe_le_coe.mpr horder

end JordanDecomposition
end Lattice

end Bong
