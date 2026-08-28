/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Dyadic.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# The normalized additive valuation

This file exposes the valuation stored in `Bong.DyadicContext` through a stable
project-level API.  Later BONG files should use `Bong.Dyadic.ord` rather than
depending directly on a concrete local-field implementation.
-/

namespace Bong.Dyadic

private abbrev ValuationCodomain :=
  Multiplicative (OrderDual (WithTop Int))

private abbrev MultiplicativeIntWithZero :=
  WithZero (Multiplicative (OrderDual Int))

/-- The two standard encodings of the multiplicative value monoid are equivalent. -/
private def valuationCodomainEquiv :
    ValuationCodomain ≃* MultiplicativeIntWithZero where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' x y := by
    cases x <;> cases y <;> rfl

private def intOrderDualAddEquiv : Int ≃+ OrderDual Int where
  toFun := OrderDual.toDual
  invFun := OrderDual.ofDual
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The unit group of the normalized valuation codomain is cyclic. -/
instance valuationCodomainUnitsIsCyclic : IsCyclic ValuationCodomainˣ := by
  letI : IsAddCyclic (OrderDual Int) :=
    isAddCyclic_of_surjective intOrderDualAddEquiv.toAddMonoidHom
      intOrderDualAddEquiv.surjective
  let e : ValuationCodomainˣ ≃* MultiplicativeIntWithZeroˣ :=
    Units.mapEquiv valuationCodomainEquiv
  exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective

variable (K : Type*) [Field K] [CharZero K] [ValuativeRel K] [TopologicalSpace K]
  [DyadicContext K]

/-- The normalized additive valuation, with `ord 0 = ∞`. -/
noncomputable def ord : AddValuation K (WithTop ℤ) :=
  DyadicContext.ord

noncomputable instance ordCompatible :
    (AddValuation.toValuation (ord K)).Compatible := by
  change (AddValuation.toValuation (DyadicContext.ord (K := K))).Compatible
  exact DyadicContext.ordCompatible

/-- The uniformizer selected by the ambient dyadic context. -/
noncomputable def uniformizer : K :=
  DyadicContext.uniformizer

@[simp]
theorem ord_zero : ord K 0 = ⊤ :=
  AddValuation.map_zero (ord K)

@[simp]
theorem ord_one : ord K 1 = 0 :=
  AddValuation.map_one (ord K)

@[simp]
theorem ord_mul (x y : K) : ord K (x * y) = ord K x + ord K y :=
  AddValuation.map_mul (ord K) x y

@[simp]
theorem ord_neg (x : K) : ord K (-x) = ord K x :=
  AddValuation.map_neg (ord K) x

theorem min_ord_le_ord_add (x y : K) : min (ord K x) (ord K y) ≤ ord K (x + y) :=
  AddValuation.map_add (ord K) x y

@[simp]
theorem ord_pow (x : K) (n : ℕ) : ord K (x ^ n) = n • ord K x :=
  AddValuation.map_pow (ord K) x n

@[simp]
theorem ord_eq_top_iff {x : K} : ord K x = ⊤ ↔ x = 0 :=
  AddValuation.top_iff (ord K)

@[simp]
theorem ord_uniformizer : ord K (uniformizer K) = 1 :=
  DyadicContext.ordUniformizer

theorem ord_two_pos : 0 < ord K (2 : K) :=
  DyadicContext.ordTwoPos

theorem ord_two_ne_top : ord K (2 : K) ≠ ⊤ := by
  intro h
  have : (2 : K) = 0 := (ord_eq_top_iff K).mp h
  norm_num at this

/-- The absolute ramification index `e = ord(2)`. -/
noncomputable def ramificationIndex : ℕ :=
  Int.toNat ((ord K (2 : K)).untop (ord_two_ne_top K))

theorem ramificationIndex_spec :
    (((ramificationIndex K : ℕ) : ℤ) : WithTop ℤ) = ord K (2 : K) := by
  have hcoe :
      (((ord K (2 : K)).untop (ord_two_ne_top K) : ℤ) : WithTop ℤ) = ord K (2 : K) :=
    WithTop.coe_untop _ _
  have hnonneg : 0 ≤ (ord K (2 : K)).untop (ord_two_ne_top K) := by
    apply WithTop.coe_le_coe.mp
    rw [hcoe]
    exact (ord_two_pos K).le
  rw [ramificationIndex, Int.toNat_of_nonneg hnonneg]
  exact hcoe

theorem ramificationIndex_pos : 0 < ramificationIndex K := by
  have hpos :
      (0 : WithTop ℤ) < (((ramificationIndex K : ℕ) : ℤ) : WithTop ℤ) := by
    rw [ramificationIndex_spec]
    exact ord_two_pos K
  exact_mod_cast WithTop.coe_lt_coe.mp hpos

theorem uniformizer_ne_zero : uniformizer K ≠ 0 := by
  intro h
  have htop : ord K (uniformizer K) = ⊤ := (ord_eq_top_iff K).2 h
  rw [ord_uniformizer K] at htop
  simp at htop

/-- The selected uniformizer, regarded as a nonzero field element. -/
noncomputable def uniformizerUnit : Kˣ :=
  Units.mk0 (uniformizer K) (uniformizer_ne_zero K)

@[simp]
theorem coe_uniformizerUnit : (uniformizerUnit K : K) = uniformizer K :=
  rfl

/-- The valuation of an integral power of a nonzero field element. -/
theorem ord_coe_unit_zpow (u : Kˣ) (m : Int) :
    ord K ((u ^ m : Kˣ) : K) = m • ord K (u : K) := by
  cases m with
  | ofNat n =>
      simp
  | negSucc n =>
      simp [zpow_negSucc, AddValuation.map_inv]

/-- The finite additive valuation of a nonzero field element. -/
noncomputable def ordUnit (u : Kˣ) : Int :=
  (ord K (u : K)).untop ((ord_eq_top_iff K).not.mpr (Units.ne_zero u))

@[simp]
theorem coe_ordUnit (u : Kˣ) :
    (ordUnit K u : WithTop Int) = ord K (u : K) :=
  WithTop.coe_untop _ _

@[simp]
theorem ordUnit_mul (a b : Kˣ) :
    ordUnit K (a * b) = ordUnit K a + ordUnit K b := by
  apply WithTop.coe_injective
  simp only [coe_ordUnit, Units.val_mul, ord_mul, WithTop.coe_add]

@[simp]
theorem ordUnit_inv (a : Kˣ) : ordUnit K a⁻¹ = -ordUnit K a := by
  apply WithTop.coe_injective
  simp [coe_ordUnit, AddValuation.map_inv]

@[simp]
theorem ordUnit_neg (a : Kˣ) : ordUnit K (-a) = ordUnit K a := by
  apply WithTop.coe_injective
  simp only [coe_ordUnit, Units.val_neg, ord_neg]

@[simp]
theorem ordUnit_pow (a : Kˣ) (m : Nat) :
    ordUnit K (a ^ m) = m * ordUnit K a := by
  induction m with
  | zero => simp [ordUnit]
  | succ m ih =>
      rw [pow_succ, ordUnit_mul, ih]
      push_cast
      ring

/-- Multiplicative and additive conventions encode the same valuative preorder. -/
theorem vle_iff_ord_ge {x y : K} : x ≤ᵥ y ↔ ord K y ≤ ord K x := by
  simpa only [AddValuation.toValuation_apply, Multiplicative.ofAdd_le,
    OrderDual.toDual_le_toDual] using
    (Valuation.vle_iff_le (AddValuation.toValuation (ord K)) (x := x) (y := y))

/-- Elements of the valuation ring have nonnegative additive valuation. -/
def IsIntegral (x : K) : Prop :=
  0 ≤ ord K x

/-- Integral elements are closed under addition. -/
theorem isIntegral_add {x y : K}
    (hx : IsIntegral K x) (hy : IsIntegral K y) :
    IsIntegral K (x + y) := by
  exact (le_min hx hy).trans (min_ord_le_ord_add K x y)

/-- Integral elements are closed under negation. -/
theorem isIntegral_neg {x : K} (hx : IsIntegral K x) :
    IsIntegral K (-x) := by
  simpa [IsIntegral] using hx

/-- Integral elements are closed under subtraction. -/
theorem isIntegral_sub {x y : K}
    (hx : IsIntegral K x) (hy : IsIntegral K y) :
    IsIntegral K (x - y) := by
  simpa [sub_eq_add_neg] using
    isIntegral_add K hx (isIntegral_neg K hy)

/-- Integral elements are closed under multiplication. -/
theorem isIntegral_mul {x y : K}
    (hx : IsIntegral K x) (hy : IsIntegral K y) :
    IsIntegral K (x * y) := by
  rw [IsIntegral, ord_mul]
  exact add_nonneg hx hy

/-- Valuation units have additive valuation zero. -/
def IsValuationUnit (x : K) : Prop :=
  ord K x = 0

theorem isValuationUnit_iff_ordUnit_eq_zero (a : Kˣ) :
    IsValuationUnit K (a : K) ↔ ordUnit K a = 0 := by
  constructor
  · intro ha
    change ord K (a : K) = 0 at ha
    apply WithTop.coe_injective
    simpa [coe_ordUnit] using ha
  · intro ha
    rw [IsValuationUnit, ← coe_ordUnit, ha]
    rfl

/-- The maximal ideal consists of the elements of positive additive valuation. -/
def IsInMaximalIdeal (x : K) : Prop :=
  0 < ord K x

/-- The maximal ideal is closed under addition. -/
theorem isInMaximalIdeal_add {x y : K}
    (hx : IsInMaximalIdeal K x) (hy : IsInMaximalIdeal K y) :
    IsInMaximalIdeal K (x + y) := by
  have hmin := min_ord_le_ord_add K x y
  exact (lt_min hx hy).trans_le hmin

/-- Multiplying an element of the maximal ideal by an integral element stays
in the maximal ideal. -/
theorem isInMaximalIdeal_mul_isIntegral {x y : K}
    (hx : IsInMaximalIdeal K x) (hy : IsIntegral K y) :
    IsInMaximalIdeal K (x * y) := by
  rw [IsInMaximalIdeal, ord_mul]
  exact add_pos_of_pos_of_nonneg hx hy

/-- The symmetric form of maximal-ideal absorption. -/
theorem isIntegral_mul_isInMaximalIdeal {x y : K}
    (hx : IsIntegral K x) (hy : IsInMaximalIdeal K y) :
    IsInMaximalIdeal K (x * y) := by
  rw [mul_comm]
  exact isInMaximalIdeal_mul_isIntegral K hy hx

theorem two_isInMaximalIdeal : IsInMaximalIdeal K (2 : K) :=
  ord_two_pos K

/-- The residue field is perfect in the one form needed below: every
valuation-unit residue class has a square root.  This holds for the finite
residue fields of nonarchimedean local fields. -/
class PerfectResidueFieldLaws : Prop where
  exists_unit_squareRoot_mod_maximal
      (u : Kˣ) (hu : IsValuationUnit K (u : K)) :
    ∃ z : K,
      IsValuationUnit K z ∧
        IsInMaximalIdeal K (z ^ 2 - (u : K))

/-- A dyadic local field has perfect residue field.  The proof transports
finiteness from the canonical valuation attached to `ValuativeRel` to the
normalized project valuation, then uses the Frobenius automorphism in
characteristic two. -/
noncomputable instance perfectResidueFieldLaws : PerfectResidueFieldLaws K := by
  let v := AddValuation.toValuation (ord K)
  let A := v.valuationSubring
  have hA : A = (ValuativeRel.valuation K).valuationSubring := by
    apply (Valuation.isEquiv_iff_valuationSubring _ _).mp
    exact ValuativeRel.isEquiv _ _
  letI : Finite (IsLocalRing.ResidueField A) := by
    rw [hA]
    change Finite (IsLocalRing.ResidueField
      (ValuativeRel.valuation K).integer)
    infer_instance
  let k := IsLocalRing.ResidueField A
  have htwoA : (2 : A) ∈ IsLocalRing.maximalIdeal A := by
    apply (Valuation.mem_maximalIdeal_iff K v).mpr
    change Multiplicative.ofAdd (OrderDual.toDual (ord K (2 : K))) <
      Multiplicative.ofAdd (OrderDual.toDual 0)
    simpa only [Multiplicative.ofAdd_lt, OrderDual.toDual_lt_toDual] using
      ord_two_pos K
  have htwoZero : (2 : k) = 0 := by
    change IsLocalRing.residue A (2 : A) = 0
    exact (IsLocalRing.residue_eq_zero_iff (2 : A)).mpr htwoA
  letI : CharP k 2 :=
    (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr htwoZero
  letI : ExpChar k 2 := ExpChar.prime Nat.prime_two
  letI : PerfectRing k 2 :=
    PerfectRing.ofFiniteOfIsReduced (R := k) (p := 2)
  refine ⟨fun u hu ↦ ?_⟩
  have huv : v (u : K) = 1 := by
    change Multiplicative.ofAdd (OrderDual.toDual (ord K (u : K))) =
      Multiplicative.ofAdd (OrderDual.toDual 0)
    rw [hu]
  let uG : A.unitGroup :=
    ⟨u, (Valuation.mem_unitGroup_iff K v u).mpr huv⟩
  let uBar : kˣ := A.unitGroupToResidueFieldUnits uG
  obtain ⟨zBar, hzBar⟩ :=
    surjective_frobenius k 2 (uBar : k)
  have hzBarSq : zBar ^ 2 = (uBar : k) := by
    simpa only [frobenius_def] using hzBar
  have hzBarNe : zBar ≠ 0 := by
    intro hz
    apply Units.ne_zero uBar
    simpa [hz] using hzBarSq.symm
  let zBarU : kˣ := Units.mk0 zBar hzBarNe
  have hzBarUSq : zBarU ^ 2 = uBar := by
    apply Units.ext
    exact hzBarSq
  obtain ⟨zG, hzG⟩ :=
    A.surjective_unitGroupToResidueFieldUnits zBarU
  let zAU : Aˣ := A.unitGroupMulEquiv zG
  let uAU : Aˣ := A.unitGroupMulEquiv uG
  have hmapSq : A.unitGroupToResidueFieldUnits (zG ^ 2) =
      A.unitGroupToResidueFieldUnits uG := by
    rw [map_pow, hzG, hzBarUSq]
  have hresSq : IsLocalRing.residue A ((zAU : A) ^ 2) =
      IsLocalRing.residue A (uAU : A) := by
    have h := congrArg (fun x : kˣ ↦ (x : k)) hmapSq
    exact h
  let dA : A := (zAU : A) ^ 2 - (uAU : A)
  have hdResidue : IsLocalRing.residue A dA = 0 := by
    change IsLocalRing.residue A
      ((zAU : A) ^ 2 - (uAU : A)) = 0
    rw [map_sub, hresSq, sub_self]
  have hdMax : dA ∈ IsLocalRing.maximalIdeal A :=
    (IsLocalRing.residue_eq_zero_iff dA).mp hdResidue
  refine ⟨((zG : A.unitGroup) : Kˣ), ?_, ?_⟩
  · have hzv : v ((zG : A.unitGroup) : Kˣ) = 1 :=
      (Valuation.mem_unitGroup_iff K v _).mp zG.property
    change ord K (((zG : A.unitGroup) : Kˣ) : K) = 0
    change Multiplicative.ofAdd
      (OrderDual.toDual
        (ord K (((zG : A.unitGroup) : Kˣ) : K))) =
          Multiplicative.ofAdd (OrderDual.toDual 0) at hzv
    simpa using congrArg
      (fun x ↦ OrderDual.ofDual (Multiplicative.toAdd x)) hzv
  · have hdv := (Valuation.mem_maximalIdeal_iff K v).mp hdMax
    change Multiplicative.ofAdd (OrderDual.toDual (ord K (dA : K))) <
      Multiplicative.ofAdd (OrderDual.toDual 0) at hdv
    change 0 < ord K
      ((((zG : A.unitGroup) : Kˣ) : K) ^ 2 - (u : K))
    simpa [dA, zAU, uAU, uG] using
      (show 0 < ord K (dA : K) by
        simpa only [Multiplicative.ofAdd_lt,
          OrderDual.toDual_lt_toDual] using hdv)

variable [PerfectResidueFieldLaws K]

/-- A valuation-unit residue class has a valuation-unit square-root lift. -/
theorem exists_unit_squareRoot_mod_maximal
    (u : Kˣ) (hu : IsValuationUnit K (u : K)) :
    ∃ z : K,
      IsValuationUnit K z ∧
        IsInMaximalIdeal K (z ^ 2 - (u : K)) :=
  PerfectResidueFieldLaws.exists_unit_squareRoot_mod_maximal u hu

end Bong.Dyadic
