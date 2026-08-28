/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.AsymmetricBinaryModular
import Bong.Lattice.BasisIsometry
import Bong.Lattice.DualIsometry
import Bong.Lattice.ModularPrimitivePairing
import Bong.Lattice.ModularParameter
import Bong.Lattice.ModularSplitting
import Bong.Lattice.OmearaChangeOfComplement
import Bong.Lattice.OrthogonalDecompositionProduct
import Bong.Lattice.PrimitiveVector

/-!
# O'Meara 82:16 for primitive isotropic vectors

In an `a`-modular lattice, a primitive isotropic vector has a lattice
partner pairing exactly to `a`.  The pair spans a binary `a`-modular
sublattice and O'Meara 82:15 splits it from the ambient lattice.  We also
identify the binary summand with the scaled plane `a A(alpha, 0)`.  This is
the inductive step behind the use of 82:17 in Corollary 93:14a.
-/

namespace Bong

open Dyadic
open Module

namespace Lattice

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {a : Kˣ} {x : V}

/-- The partner produced by O'Meara 82:16. -/
structure Omeara8216Data
    (q : QuadraticSpace K V) (L : Lattice K V) (a : Kˣ) (x : V) where
  partner : V
  partner_mem : partner ∈ L
  pairing_eq : q.bilin x partner = (a : K)

/-- A primitive vector in an `a`-modular lattice has a partner pairing
exactly to the chosen modular generator. -/
noncomputable def omeara8216Data
    (hmodular : IsModular q L a) (hx : x ∈ L)
    (hprimitive : x ∉ rescale (uniformizerUnit K) L) :
    Omeara8216Data q L a x := by
  let hexists :=
    hmodular.exists_pairing_eq_of_not_mem_rescale hx hprimitive
  exact
    { partner := Classical.choose hexists
      partner_mem := (Classical.choose_spec hexists).1
      pairing_eq := (Classical.choose_spec hexists).2 }

namespace Omeara8216Data

variable (D : Omeara8216Data q L a x)

theorem pairing_ne : q.bilin x D.partner ≠ 0 := by
  rw [D.pairing_eq]
  exact Units.ne_zero a

theorem left_strict (hisotropic : q.quadratic x = 0) :
    ord K (q.bilin x D.partner) < ord K (q.quadratic x) := by
  rw [D.pairing_eq, hisotropic, ord_zero]
  exact lt_top_iff_ne_top.mpr
    ((ord_eq_top_iff K).not.mpr (Units.ne_zero a))

theorem right_weak (hmodular : IsModular q L a) :
    ord K (q.bilin x D.partner) ≤ ord K (q.quadratic D.partner) := by
  rw [D.pairing_eq]
  apply ord_le_of_mem_principalIdeal (Units.ne_zero a)
  exact hmodular.scaleIdeal_le_principal
    (bilin_mem_scaleIdeal_of_mem q L D.partner_mem D.partner_mem)

/-- The binary sublattice spanned by the primitive isotropic vector and its
82:16 partner. -/
noncomputable def component (hmodular : IsModular q L a)
    (hisotropic : q.quadratic x = 0) : QuadraticSublattice q :=
  asymmetricBinaryScaleComponent (q := q) D.pairing_ne
    (D.left_strict hisotropic) (D.right_weak hmodular)

theorem component_contained (hmodular : IsModular q L a)
    (hisotropic : q.quadratic x = 0) (hx : x ∈ L) :
    (D.component hmodular hisotropic).ambientSubmodule ≤ L.toSubmodule :=
  asymmetricBinaryScaleComponent_ambientSubmodule_le D.pairing_ne
    (D.left_strict hisotropic) (D.right_weak hmodular) hx D.partner_mem

theorem component_modular (hmodular : IsModular q L a)
    (hisotropic : q.quadratic x = 0) :
    IsModular (D.component hmodular hisotropic).space
      (D.component hmodular hisotropic).lattice a := by
  have ha : Units.mk0 (q.bilin x D.partner) D.pairing_ne = a :=
    Units.ext D.pairing_eq
  change IsModular
    (asymmetricBinaryScaleComponent (q := q) D.pairing_ne
      (D.left_strict hisotropic) (D.right_weak hmodular)).space
    (asymmetricBinaryScaleComponent (q := q) D.pairing_ne
      (D.left_strict hisotropic) (D.right_weak hmodular)).lattice a
  apply (asymmetricBinaryScaleComponent_isModular D.pairing_ne
    (D.left_strict hisotropic) (D.right_weak hmodular)).of_principalIdeal_eq
  exact congrArg (fun s : Kˣ ↦ principalIdeal (K := K) (s : K)) ha

/-- O'Meara 82:16: the primitive isotropic pair splits the modular
lattice. -/
noncomputable def splitting (hmodular : IsModular q L a)
    (hisotropic : q.quadratic x = 0) (hx : x ∈ L) :
    OrthogonalDecomposition q L 2 :=
  omearaModularSplittingOfScaleIdealLe
    (D.component hmodular hisotropic)
    (D.component_contained hmodular hisotropic hx)
    (D.component_modular hmodular hisotropic)
    hmodular.scaleIdeal_le_principal

/-- The coefficient `alpha = a⁻¹ Q(y)` of the plane
`a A(alpha, 0)`. -/
noncomputable def planeCoefficient : K :=
  (a : K)⁻¹ * q.quadratic D.partner

/-- The binary summand of 82:16 is the scaled O'Meara plane
`a A(alpha,0)`, with `alpha = a⁻¹ Q(y)`. -/
noncomputable def planeIsometry (hmodular : IsModular q L a)
    (hisotropic : q.quadratic x = 0) :
    Isometry
      ((QuadraticSpace.omearaPlane D.planeCoefficient).rescaleUnit a)
      (D.component hmodular hisotropic).space
      (hyperbolicPlaneLattice (K := K))
      (D.component hmodular hisotropic).lattice := by
  let hxy := D.pairing_ne
  let hleft := D.left_strict hisotropic
  let hright := D.right_weak hmodular
  let P := BONG.binaryPairSpan (K := K) x D.partner
  let hli := binaryPair_linearIndependent_of_left_strict hxy hleft hright
  let b : Basis (Fin 2) K P :=
    BONG.binaryPairBasis (K := K) x D.partner hli
  let C : QuadraticSublattice q :=
    asymmetricBinaryScaleComponent (q := q) hxy hleft hright
  let swap : Fin 2 ≃ Fin 2 := Equiv.swap 0 1
  let c : Basis (Fin 2) K P := b.reindex swap
  let sourceBasis : Basis (Fin 2) K (Fin 2 → K) := Pi.basisFun K (Fin 2)
  have hc0 : (c 0 : V) = D.partner := by
    simp only [c, Basis.coe_reindex, Function.comp_apply]
    rw [show swap.symm 0 = 1 by simp [swap]]
    change ((b 1 : P) : V) = D.partner
    rw [show ((b 1 : P) : V) = BONG.binaryPairFamily x D.partner 1 by
      exact BONG.coe_binaryPairBasis x D.partner hli 1]
    exact BONG.binaryPairFamily_one x D.partner
  have hc1 : (c 1 : V) = x := by
    simp only [c, Basis.coe_reindex, Function.comp_apply]
    rw [show swap.symm 1 = 0 by simp [swap]]
    change ((b 0 : P) : V) = x
    rw [show ((b 0 : P) : V) = BONG.binaryPairFamily x D.partner 0 by
      exact BONG.coe_binaryPairBasis x D.partner hli 0]
    exact BONG.binaryPairFamily_zero x D.partner
  have hgram : ∀ i j,
      C.space.bilin (c i) (c j) =
        ((QuadraticSpace.omearaPlane D.planeCoefficient).rescaleUnit a).bilin
          (sourceBasis i) (sourceBasis j) := by
    intro i j
    fin_cases i <;> fin_cases j
    · change q.bilin (c 0 : V) (c 0 : V) = _
      rw [hc0]
      simp [sourceBasis,
        QuadraticSpace.rescaleUnit_bilin_apply,
        QuadraticSpace.omearaPlane_bilin_apply, planeCoefficient,
        QuadraticSpace.quadratic]
    · change q.bilin (c 0 : V) (c 1 : V) = _
      rw [hc0, hc1, q.isSymm.eq D.partner x, D.pairing_eq]
      simp [sourceBasis, QuadraticSpace.rescaleUnit_bilin_apply,
        QuadraticSpace.omearaPlane_bilin_apply]
    · change q.bilin (c 1 : V) (c 0 : V) = _
      rw [hc0, hc1, D.pairing_eq]
      simp [sourceBasis, QuadraticSpace.rescaleUnit_bilin_apply,
        QuadraticSpace.omearaPlane_bilin_apply]
    · change q.bilin (c 1 : V) (c 1 : V) = _
      rw [hc1]
      change q.quadratic x = _
      rw [hisotropic]
      simp [sourceBasis, QuadraticSpace.rescaleUnit_bilin_apply,
        QuadraticSpace.omearaPlane_bilin_apply]
  let raw := Classical.choice
    (basisLattice_isIsometric_of_gram_eq
      ((QuadraticSpace.omearaPlane D.planeCoefficient).rescaleUnit a)
      C.space sourceBasis c hgram)
  have hc : basisLattice c = C.lattice := by
    calc
      basisLattice c = basisLattice b := basisLattice_reindex b swap
      _ = C.lattice := by rfl
  let identify := Isometry.ofLatticeEq C.space hc
  change Isometry
    ((QuadraticSpace.omearaPlane D.planeCoefficient).rescaleUnit a)
    C.space
    (hyperbolicPlaneLattice (K := K))
    C.lattice
  simpa only [hyperbolicPlaneLattice, sourceBasis] using
    raw.trans identify

end Omeara8216Data

/-! ## Applying 82:16 to a nonzero isotropic line -/

/-- A primitive lattice representative selected on a nonzero isotropic
ambient line. -/
structure Omeara8216LineData
    (q : QuadraticSpace K V) (L : Lattice K V) (a : Kˣ) (z : V) where
  scale : Kˣ
  vector_mem : (scale : K) • z ∈ L
  vector_primitive :
    (scale : K) • z ∉ rescale (uniformizerUnit K) L
  partnerData : Omeara8216Data q L a ((scale : K) • z)

/-- Every nonzero isotropic line in an `a`-modular lattice has the primitive
representative needed by O'Meara 82:16. -/
noncomputable def omeara8216LineData
    (hmodular : IsModular q L a) {z : V} (hz : z ≠ 0) :
    Omeara8216LineData q L a z := by
  let hexists :=
    exists_unit_smul_mem_not_mem_uniformizer_rescale L hz
  let t := Classical.choose hexists
  have ht := Classical.choose_spec hexists
  exact
    { scale := t
      vector_mem := ht.1
      vector_primitive := ht.2
      partnerData := omeara8216Data hmodular ht.1 ht.2 }

namespace Omeara8216LineData

variable {z : V} (E : Omeara8216LineData q L a z)

/-- The selected primitive representative of the isotropic line. -/
noncomputable def vector : V := (E.scale : K) • z

theorem vector_isotropic (hisotropic : q.quadratic z = 0) :
    q.quadratic E.vector = 0 := by
  rw [vector, q.quadratic_smul, hisotropic, mul_zero]

/-- The exact modular partner attached to the selected representative. -/
noncomputable def pairingData : Omeara8216Data q L a E.vector :=
  E.partnerData

/-- The integral binary splitting produced from the isotropic line. -/
noncomputable def splitting (hmodular : IsModular q L a)
    (hisotropic : q.quadratic z = 0) : OrthogonalDecomposition q L 2 :=
  E.pairingData.splitting hmodular
    (E.vector_isotropic hisotropic) E.vector_mem

@[simp]
theorem splitting_zero (hmodular : IsModular q L a)
    (hisotropic : q.quadratic z = 0) :
    (E.splitting hmodular hisotropic).component 0 =
      E.pairingData.component hmodular
        (E.vector_isotropic hisotropic) :=
  rfl

/-- The binary component is the scaled plane `a A(alpha,0)`. -/
noncomputable def planeIsometry (hmodular : IsModular q L a)
    (hisotropic : q.quadratic z = 0) :
    Isometry
      ((QuadraticSpace.omearaPlane
        E.pairingData.planeCoefficient).rescaleUnit a)
      ((E.splitting hmodular hisotropic).component 0).space
      (hyperbolicPlaneLattice (K := K))
      ((E.splitting hmodular hisotropic).component 0).lattice := by
  rw [E.splitting_zero hmodular hisotropic]
  exact E.pairingData.planeIsometry hmodular
    (E.vector_isotropic hisotropic)

/-- The orthogonal complement left by 82:16 remains `a`-modular. -/
theorem complement_modular (hmodular : IsModular q L a)
    (hisotropic : q.quadratic z = 0) :
    IsModular ((E.splitting hmodular hisotropic).component 1).space
      ((E.splitting hmodular hisotropic).component 1).lattice a :=
  (E.splitting hmodular hisotropic).component_modular_of_ambient
    hmodular 1

end Omeara8216LineData

end Lattice

end Bong
