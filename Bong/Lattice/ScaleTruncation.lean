/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.BasisUnits
import Bong.Lattice.DeterminantBasis
import Bong.Lattice.OrthogonalDecompositionDual
import Bong.Lattice.OrthogonalDecompositionIdeals
import Bong.Lattice.PowerIdeal

/-!
# O'Meara scale truncations

For a lattice `L` and an integral scale order `r`, O'Meara's auxiliary
lattice `L^r` is the intrinsic intersection

`L ⊓ π^r L♯`.

This is the lattice whose norm is denoted `n(L^s)` in Beli (2003),
Section 4.  The construction is independent of a Jordan decomposition; a
Jordan decomposition is used later only to calculate its norm component by
component.
-/

namespace Bong

open Dyadic
open Module

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]

namespace Lattice

/-- The intersection of two full lattices, bundled again as a full lattice. -/
noncomputable def inf (L M : Lattice K V) : Lattice K V := by
  letI : Module.Finite K V := L.moduleFinite
  exact {
    toSubmodule := L.toSubmodule ⊓ M.toSubmodule
    fg := Submodule.IsLattice.fg (A := K)
    span_eq_top := Submodule.IsLattice.span_eq_top (A := K) }

@[simp]
theorem toSubmodule_inf (L M : Lattice K V) :
    (inf L M).toSubmodule = L.toSubmodule ⊓ M.toSubmodule :=
  rfl

@[simp]
theorem mem_inf_iff (L M : Lattice K V) (x : V) :
    x ∈ inf L M ↔ x ∈ L ∧ x ∈ M :=
  Iff.rfl

/-- The scalar used in the intrinsic definition of `L^r`. -/
noncomputable def scaleTruncationUnit (r : Int) : Kˣ :=
  Dyadic.uniformizerPowerUnit K r

/-- O'Meara's auxiliary scale-truncation lattice `L^r = L ∩ π^r L♯`. -/
noncomputable def scaleTruncation
    (q : QuadraticSpace K V) (L : Lattice K V) (r : Int) :
    Lattice K V :=
  inf L (rescale (scaleTruncationUnit (K := K) r) (dualLattice q L))

@[simp]
theorem mem_scaleTruncation_iff_inf
    (q : QuadraticSpace K V) (L : Lattice K V) (r : Int) (x : V) :
    x ∈ scaleTruncation q L r ↔
      x ∈ L ∧
        x ∈ rescale (scaleTruncationUnit (K := K) r) (dualLattice q L) :=
  Iff.rfl

/-- In a basis, the intersection of the unscaled lattice and a diagonal
rescaling is obtained by retaining precisely the positive rescaling factors. -/
noncomputable def positivePartUnit (a : Kˣ) : Kˣ :=
  if 0 < ordUnit K a then a else 1

@[simp]
theorem ordUnit_positivePartUnit (a : Kˣ) :
    ordUnit K (positivePartUnit a) = max 0 (ordUnit K a) := by
  unfold positivePartUnit
  by_cases ha : 0 < ordUnit K a
  · rw [if_pos ha, max_eq_right ha.le]
  · rw [if_neg ha, max_eq_left (le_of_not_gt ha)]
    simp [ordUnit]

private theorem integral_and_inv_smul_integral_iff_positivePart
    (a : Kˣ) (z : K) :
    z ∈ IntegerRing K ∧ ((a⁻¹ : Kˣ) : K) * z ∈ IntegerRing K ↔
      (((positivePartUnit a)⁻¹ : Kˣ) : K) * z ∈ IntegerRing K := by
  rw [mem_integerRing_iff, mem_integerRing_iff, mem_integerRing_iff]
  change (0 : WithTop Int) ≤ ord K z ∧
      0 ≤ ord K (((a⁻¹ : Kˣ) : K) * z) ↔
    0 ≤ ord K ((((positivePartUnit a)⁻¹ : Kˣ) : K) * z)
  by_cases hz : z = 0
  · subst z
    simp
  · let zu : Kˣ := Units.mk0 z hz
    have hzord : ord K z = (ordUnit K zu : WithTop Int) := by
      rw [coe_ordUnit]
      rfl
    rw [ord_mul, ord_mul, ← coe_ordUnit, ← coe_ordUnit,
      ordUnit_inv, ordUnit_inv, ordUnit_positivePartUnit, hzord]
    norm_cast
    omega

/-- Coordinatewise intersection formula for a diagonally rescaled basis
lattice. -/
theorem inf_basisLattice_unitsSMul
    {I : Type w} [Finite I]
    (b : Basis I K V) (a : I → Kˣ) :
    inf (basisLattice b) (basisLattice (b.unitsSMul a)) =
      basisLattice (b.unitsSMul (fun i ↦ positivePartUnit (a i))) := by
  apply Lattice.ext
  apply Submodule.ext
  intro x
  change (x ∈ basisLattice b ∧ x ∈ basisLattice (b.unitsSMul a)) ↔
    x ∈ basisLattice (b.unitsSMul (fun i ↦ positivePartUnit (a i)))
  rw [
    mem_basisLattice_iff_repr_mem_integerRing,
    mem_basisLattice_iff_repr_mem_integerRing,
    mem_basisLattice_iff_repr_mem_integerRing]
  simp only [Basis.repr_unitsSMul, Units.smul_def]
  constructor
  · rintro ⟨hx, hax⟩ i
    exact (integral_and_inv_smul_integral_iff_positivePart
      (a i) (b.repr x i)).mp ⟨hx i, hax i⟩
  · intro hx
    constructor <;> intro i
    · exact (integral_and_inv_smul_integral_iff_positivePart
        (a i) (b.repr x i)).mpr (hx i) |>.1
    · exact (integral_and_inv_smul_integral_iff_positivePart
        (a i) (b.repr x i)).mpr (hx i) |>.2

namespace QuadraticSublattice

variable {q : QuadraticSpace K V}

/-- Rescale only the integral lattice inside a fixed nondegenerate carrier. -/
noncomputable def rescaleLattice (C : QuadraticSublattice q) (a : Kˣ) :
    QuadraticSublattice q where
  carrier := C.carrier
  nondegenerate := C.nondegenerate
  lattice := Lattice.rescale a C.lattice

@[simp]
theorem rescaleLattice_carrier (C : QuadraticSublattice q) (a : Kˣ) :
    (C.rescaleLattice a).carrier = C.carrier :=
  rfl

@[simp]
theorem rescaleLattice_space (C : QuadraticSublattice q) (a : Kˣ) :
    (C.rescaleLattice a).space = C.space :=
  rfl

@[simp]
theorem rescaleLattice_lattice (C : QuadraticSublattice q) (a : Kˣ) :
    (C.rescaleLattice a).lattice = Lattice.rescale a C.lattice :=
  rfl

/-- The ambient module of a rescaled component is generated by the
correspondingly rescaled chosen component basis. -/
theorem rescaleLattice_ambientSubmodule_eq_span
    (C : QuadraticSublattice q) (a : Kˣ) :
    (C.rescaleLattice a).ambientSubmodule =
      Submodule.span (IntegerRing K)
        (Set.range fun i ↦
          (a : K) • ((C.lattice.ambientBasis i : C.carrier) : V)) := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    change C.carrier at y
    change y ∈ Lattice.rescale a C.lattice at hy
    rw [Lattice.mem_rescale_iff] at hy
    rcases hy with ⟨z, hz, rfl⟩
    have hzSpan : z ∈ Submodule.span (IntegerRing K)
        (Set.range C.lattice.ambientBasis) := by
      rw [← C.lattice.toSubmodule_eq_span_ambientBasis]
      exact hz
    refine Submodule.span_induction
      (p := fun z _ ↦
        (a : K) • ((z : C.carrier) : V) ∈
          Submodule.span (IntegerRing K)
            (Set.range fun i ↦
              (a : K) • ((C.lattice.ambientBasis i : C.carrier) : V)))
      ?_ ?_ ?_ ?_ hzSpan
    · rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨i, rfl⟩
    · simp
    · intro y z _ _ hy hz
      simpa only [Submodule.coe_add, smul_add] using
        (Submodule.span (IntegerRing K)
          (Set.range fun i ↦
            (a : K) • ((C.lattice.ambientBasis i : C.carrier) : V))).add_mem
          hy hz
    · intro c z _ hz
      have hmem := (Submodule.span (IntegerRing K)
        (Set.range fun i ↦
          (a : K) • ((C.lattice.ambientBasis i : C.carrier) : V))).smul_mem c hz
      change (c : K) • ((a : K) • ((z : C.carrier) : V)) ∈ _ at hmem
      change (a : K) • ((c : K) • ((z : C.carrier) : V)) ∈ _
      rwa [smul_comm]
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨⟨(a : K) • C.lattice.ambientBasis i,
      C.carrier.smul_mem (a : K) (C.lattice.ambientBasis i).property⟩, ?_, rfl⟩
    change (a : K) • C.lattice.ambientBasis i ∈
      Lattice.rescale a C.lattice
    apply Lattice.smul_mem_rescale
    rw [C.lattice.ambientBasis_apply]
    exact (C.lattice.integralBasis i).property

end QuadraticSublattice

namespace OrthogonalDecomposition

variable {q : QuadraticSpace K V} {L : Lattice K V} {t : Nat}

/-- The ambient basis obtained by rescaling every component lattice by its
own nonzero scalar. -/
noncomputable def componentwiseRescaleBasis
    (D : OrthogonalDecomposition q L t) (a : Fin t → Kˣ) :
    Basis (Σ i : Fin t, (D.component i).lattice.BasisIndex) K V :=
  D.componentAmbientBasis.unitsSMul (fun z ↦ a z.1)

/-- The full ambient lattice obtained by rescaling the components of an
orthogonal decomposition independently. -/
noncomputable def componentwiseRescaleLattice
    (D : OrthogonalDecomposition q L t) (a : Fin t → Kˣ) :
    Lattice K V :=
  basisLattice (D.componentwiseRescaleBasis a)

@[simp]
theorem componentwiseRescaleBasis_apply
    (D : OrthogonalDecomposition q L t) (a : Fin t → Kˣ)
    (z : Σ i : Fin t, (D.component i).lattice.BasisIndex) :
    D.componentwiseRescaleBasis a z =
      (a z.1 : K) •
        (((D.component z.1).lattice.ambientBasis z.2 :
          (D.component z.1).carrier) : V) := by
  rw [componentwiseRescaleBasis, Basis.unitsSMul_apply,
    D.componentAmbientBasis_apply]
  rfl

/-- The componentwise lattice has the evident rescaled orthogonal
decomposition. -/
noncomputable def componentwiseRescale
    (D : OrthogonalDecomposition q L t) (a : Fin t → Kˣ) :
    OrthogonalDecomposition q (D.componentwiseRescaleLattice a) t where
  component := fun i ↦ (D.component i).rescaleLattice (a i)
  orthogonal := by
    intro i j hij x y
    exact D.orthogonal i j hij x y
  sum_eq := by
    apply le_antisymm
    · apply iSup_le
      intro i
      rw [(D.component i).rescaleLattice_ambientSubmodule_eq_span,
        Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      apply Submodule.subset_span
      exact ⟨⟨i, j⟩, by simp⟩
    · change Submodule.span (IntegerRing K)
          (Set.range (D.componentwiseRescaleBasis a)) ≤ _
      rw [Submodule.span_le]
      rintro _ ⟨z, rfl⟩
      apply le_iSup
        (fun i ↦ ((D.component i).rescaleLattice (a i)).ambientSubmodule)
        z.1
      rw [(D.component z.1).rescaleLattice_ambientSubmodule_eq_span]
      exact Submodule.subset_span ⟨z.2, by
        rw [D.componentwiseRescaleBasis_apply]⟩

@[simp]
theorem componentwiseRescale_component
    (D : OrthogonalDecomposition q L t) (a : Fin t → Kˣ) (i : Fin t) :
    (D.componentwiseRescale a).component i =
      (D.component i).rescaleLattice (a i) :=
  rfl

theorem componentwiseRescaleLattice_one
    (D : OrthogonalDecomposition q L t) :
    D.componentwiseRescaleLattice (fun _ ↦ 1) = L := by
  have hb : D.componentwiseRescaleBasis (fun _ ↦ 1) =
      D.componentAmbientBasis := by
    ext z
    simp [D.componentwiseRescaleBasis_apply]
  rw [componentwiseRescaleLattice, hb,
    D.basisLattice_componentAmbientBasis]

/-- The componentwise dual lattices sum to the ambient dual without the
order-reversing reindexing used for reverse Jordan decompositions. -/
theorem dualSum_sameIndex (D : OrthogonalDecomposition q L t) :
    (⨆ i, (D.component i).dual.ambientSubmodule) =
      (dualLattice q L).toSubmodule := by
  rw [← D.reverseDualSum]
  apply le_antisymm
  · apply iSup_le
    intro i
    have h := le_iSup
      (fun j ↦ (D.reverseDualComponent j).ambientSubmodule) (Fin.rev i)
    simpa [reverseDualComponent] using h
  · apply iSup_le
    intro i
    have h := le_iSup
      (fun j ↦ (D.component j).dual.ambientSubmodule) (Fin.rev i)
    simpa [reverseDualComponent] using h

/-- For a modular component, rescaling by the inverse modular parameter
gives its component dual, also after embedding in the ambient space. -/
theorem rescaleLattice_ambientSubmodule_eq_dual
    (D : OrthogonalDecomposition q L t) (i : Fin t) (s : Kˣ)
    (hmodular : IsModular (D.component i).space
      (D.component i).lattice s) :
    ((D.component i).rescaleLattice s⁻¹).ambientSubmodule =
      (D.component i).dual.ambientSubmodule := by
  change (rescale s⁻¹ (D.component i).lattice).toSubmodule.map
      ((Submodule.subtype (D.component i).carrier).restrictScalars
        (IntegerRing K)) =
    (dualLattice (D.component i).space
      (D.component i).lattice).toSubmodule.map
      ((Submodule.subtype (D.component i).carrier).restrictScalars
        (IntegerRing K))
  rw [hmodular]

/-- A modular orthogonal decomposition calculates the ambient dual by
inverting the component modular parameters. -/
theorem componentwiseRescaleLattice_inv_eq_dual
    (D : OrthogonalDecomposition q L t) (s : Fin t → Kˣ)
    (hmodular : ∀ i, IsModular (D.component i).space
      (D.component i).lattice (s i)) :
    D.componentwiseRescaleLattice (fun i ↦ (s i)⁻¹) =
      dualLattice q L := by
  apply Lattice.ext
  rw [← (D.componentwiseRescale (fun i ↦ (s i)⁻¹)).sum_eq,
    ← D.dualSum_sameIndex]
  congr 1
  funext i
  exact D.rescaleLattice_ambientSubmodule_eq_dual i (s i) (hmodular i)

/-- A common rescaling distributes through an independently rescaled
component family. -/
theorem rescale_componentwiseRescaleLattice
    (D : OrthogonalDecomposition q L t) (c : Kˣ) (a : Fin t → Kˣ) :
    rescale c (D.componentwiseRescaleLattice a) =
      D.componentwiseRescaleLattice (fun i ↦ c * a i) := by
  rw [componentwiseRescaleLattice, componentwiseRescaleLattice,
    rescale_basisLattice]
  congr 1
  ext z
  rw [Basis.smul_apply, D.componentwiseRescaleBasis_apply,
    D.componentwiseRescaleBasis_apply]
  simp only [Units.smul_def, Units.val_mul]
  rw [mul_smul]

/-- Rescaling the ambient dual of a modular orthogonal decomposition is a
componentwise rescaling of the original decomposition. -/
theorem rescale_dualLattice_eq_componentwiseRescaleLattice
    (D : OrthogonalDecomposition q L t) (s : Fin t → Kˣ)
    (hmodular : ∀ i, IsModular (D.component i).space
      (D.component i).lattice (s i)) (c : Kˣ) :
    rescale c (dualLattice q L) =
      D.componentwiseRescaleLattice (fun i ↦ c * (s i)⁻¹) := by
  rw [← D.componentwiseRescaleLattice_inv_eq_dual s hmodular,
    D.rescale_componentwiseRescaleLattice]

end OrthogonalDecomposition

namespace JordanDecomposition

variable {q : QuadraticSpace K V} {L : Lattice K V} {t : Nat}

/-- The component factor in the calculation of `L^r`: a component below
the target scale is raised to the target, while a component already at or
above it is unchanged. -/
noncomputable def scaleTruncationFactor
    (J : JordanDecomposition q L t) (r : Int) (i : Fin t) : Kˣ :=
  positivePartUnit
    (scaleTruncationUnit (K := K) r * (J.scaleGenerator i)⁻¹)

@[simp]
theorem ordUnit_scaleTruncationFactor
    (J : JordanDecomposition q L t) (r : Int) (i : Fin t) :
    ordUnit K (J.scaleTruncationFactor r i) =
      max 0 (r - ordUnit K (J.scaleGenerator i)) := by
  rw [scaleTruncationFactor, ordUnit_positivePartUnit,
    ordUnit_mul, ordUnit_inv]
  change max 0
      (ordUnit K (scaleTruncationUnit (K := K) r) -
        ordUnit K (J.scaleGenerator i)) = _
  rw [scaleTruncationUnit,
    Dyadic.ordUnit_uniformizerPowerUnit]

/-- A Jordan decomposition computes the intrinsic scale truncation by
rescaling each component with its positive target-scale difference. -/
theorem scaleTruncation_eq_componentwiseRescaleLattice
    (J : JordanDecomposition q L t) (r : Int) :
    scaleTruncation q L r =
      J.toOrthogonalDecomposition.componentwiseRescaleLattice
        (J.scaleTruncationFactor r) := by
  let D := J.toOrthogonalDecomposition
  let f : Fin t → Kˣ := fun i ↦
    scaleTruncationUnit (K := K) r * (J.scaleGenerator i)⁻¹
  have hdual :
      rescale (scaleTruncationUnit (K := K) r) (dualLattice q L) =
        D.componentwiseRescaleLattice f := by
    exact D.rescale_dualLattice_eq_componentwiseRescaleLattice
      J.scaleGenerator J.modular (scaleTruncationUnit (K := K) r)
  rw [scaleTruncation, hdual]
  rw (occs := .pos [1]) [← D.basisLattice_componentAmbientBasis]
  change inf (basisLattice D.componentAmbientBasis)
      (basisLattice (D.componentAmbientBasis.unitsSMul
        (fun z ↦ f z.1))) =
    basisLattice (D.componentAmbientBasis.unitsSMul
      (fun z ↦ J.scaleTruncationFactor r z.1))
  simpa only [scaleTruncationFactor, f] using
    inf_basisLattice_unitsSMul D.componentAmbientBasis (fun z ↦ f z.1)

/-- At the scale of a component, that component is not rescaled in the
intrinsic truncation. -/
@[simp]
theorem scaleTruncationFactor_self
    (J : JordanDecomposition q L t) (i : Fin t) :
    J.scaleTruncationFactor (ordUnit K (J.scaleGenerator i)) i = 1 := by
  simp [scaleTruncationFactor, positivePartUnit,
    scaleTruncationUnit, ordUnit_mul, ordUnit_inv]

/-- The componentwise calculation of `L^r`, bundled as an orthogonal
decomposition of the intrinsic lattice rather than merely as an equality of
lattices. -/
noncomputable def scaleTruncationDecomposition
    (J : JordanDecomposition q L t) (r : Int) :
    OrthogonalDecomposition q (scaleTruncation q L r) t where
  component := fun i ↦
    (J.component i).rescaleLattice (J.scaleTruncationFactor r i)
  orthogonal := by
    intro i j hij x y
    exact J.toOrthogonalDecomposition.orthogonal i j hij x y
  sum_eq := by
    rw [J.scaleTruncation_eq_componentwiseRescaleLattice]
    exact (J.toOrthogonalDecomposition.componentwiseRescale
      (J.scaleTruncationFactor r)).sum_eq

@[simp]
theorem scaleTruncationDecomposition_component
    (J : JordanDecomposition q L t) (r : Int) (i : Fin t) :
    (J.scaleTruncationDecomposition r).component i =
      (J.component i).rescaleLattice (J.scaleTruncationFactor r i) := by
  rfl

/-- In the scale layer attached to `i`, the `i`th Jordan component occurs
literally, with its original lattice. -/
@[simp]
theorem scaleTruncationDecomposition_component_self
    (J : JordanDecomposition q L t) (i : Fin t) :
    (J.scaleTruncationDecomposition
        (ordUnit K (J.scaleGenerator i))).component i = J.component i := by
  rw [J.scaleTruncationDecomposition_component,
    J.scaleTruncationFactor_self]
  cases hC : J.component i with
  | mk carrier nondegenerate lattice =>
      simp [QuadraticSublattice.rescaleLattice, Lattice.rescale_one]

/-- The volume jump of the intrinsic scale truncation is the sum of the
positive scale differences, weighted by the Jordan component ranks. -/
theorem volumeOrder_scaleTruncation
    (J : JordanDecomposition q L t) (r : Int) :
    volumeOrder q (scaleTruncation q L r) =
      volumeOrder q L + 2 * ∑ i,
        (J.componentRank i : Int) *
          max 0 (r - ordUnit K (J.scaleGenerator i)) := by
  classical
  letI (i : Fin t) : Fintype (J.component i).lattice.BasisIndex :=
    Fintype.ofFinite _
  rw [J.scaleTruncation_eq_componentwiseRescaleLattice,
    OrthogonalDecomposition.componentwiseRescaleLattice,
    OrthogonalDecomposition.componentwiseRescaleBasis,
    volumeOrder_basisLattice_unitsSMul,
    J.toOrthogonalDecomposition.basisLattice_componentAmbientBasis]
  congr 2
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [J.ordUnit_scaleTruncationFactor, Finset.sum_const,
    nsmul_eq_mul]
  rw [Finset.card_univ]
  rw [← Module.finrank_eq_card_basis
    (J.component i).lattice.ambientBasis]
  rfl

end JordanDecomposition

end Lattice

end Bong
