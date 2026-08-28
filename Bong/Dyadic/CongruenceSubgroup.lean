/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Dyadic.HilbertSymbol
import Bong.Dyadic.UnitSquareClass
import Bong.Lattice.PowerIdeal

/-!
# Principal-unit and square-class congruence subgroups

This file formalizes the groups denoted `(1 + 𝔭ⁿ)Fˣ²`, `𝓞ˣFˣ²`, and
`N(a)` in Beli (2003), Definitions 4 and 6.  The exponent of a principal-unit
subgroup is a natural number, as in all uses in those definitions.
-/

namespace Bong.Dyadic

universe u

variable (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- The canonical homomorphism from nonzero field elements to square classes. -/
noncomputable def squareClassHom : Kˣ →* SquareClass K :=
  QuotientGroup.mk' (Subgroup.square Kˣ)

@[simp]
theorem squareClassHom_apply (a : Kˣ) :
    squareClassHom K a = squareClass K a :=
  rfl

/-- Valuation units congruent to `1` modulo `𝔭ⁿ`. -/
noncomputable def principalUnitSubgroup (n : Nat) : Subgroup Kˣ where
  carrier := {u |
    IsValuationUnit K (u : K) ∧
      (u : K) - 1 ∈ Lattice.powerIdeal (K := K) (n : Int)}
  one_mem' := by
    constructor
    · simp [IsValuationUnit]
    · simp
  mul_mem' := by
    intro a b ha hb
    constructor
    · exact (valuationUnitSubgroup K).mul_mem ha.1 hb.1
    · have haIntegral : (a : K) ∈ IntegerRing K := by
        apply (mem_integerRing_iff K).2
        rw [IsIntegral, ha.1]
      let aO : IntegerRing K := ⟨(a : K), haIntegral⟩
      have hmul := (Lattice.powerIdeal (K := K) (n : Int)).smul_mem
        aO hb.2
      change (a : K) * ((b : K) - 1) ∈
        Lattice.powerIdeal (K := K) (n : Int) at hmul
      convert (Lattice.powerIdeal (K := K) (n : Int)).add_mem
        hmul ha.2 using 1
      simp only [Units.val_mul]
      ring
  inv_mem' := by
    intro a ha
    change IsValuationUnit K (a : K) ∧
      (a : K) - 1 ∈ Lattice.powerIdeal (K := K) (n : Int) at ha
    constructor
    · exact (valuationUnitSubgroup K).inv_mem ha.1
    · apply (Lattice.mem_powerIdeal_iff (K := K) (n : Int) _).2
      have haError :=
        (Lattice.mem_powerIdeal_iff (K := K) (n : Int) _).1 ha.2
      have heq : (a : K)⁻¹ - 1 =
          -((a : K)⁻¹ * ((a : K) - 1)) := by
        field_simp [Units.ne_zero a]
        ring
      rw [Units.val_inv_eq_inv_val, heq, ord_neg, ord_mul,
        AddValuation.map_inv, ha.1]
      simpa using haError

@[simp]
theorem mem_principalUnitSubgroup_iff (n : Nat) (u : Kˣ) :
    u ∈ principalUnitSubgroup K n ↔
      IsValuationUnit K (u : K) ∧
        (u : K) - 1 ∈ Lattice.powerIdeal (K := K) (n : Int) :=
  Iff.rfl

/-- Deeper principal-unit filtrations are smaller. -/
theorem principalUnitSubgroup_anti {m n : Nat} (hmn : m ≤ n) :
    principalUnitSubgroup K n ≤ principalUnitSubgroup K m := by
  intro u hu
  refine ⟨hu.1, ?_⟩
  exact (Lattice.powerIdeal_le_iff (K := K) (n : Int) (m : Int)).2
    (by exact_mod_cast hmn) hu.2

/-- Depth-zero principal units are exactly all valuation units. -/
theorem principalUnitSubgroup_zero :
    principalUnitSubgroup K 0 = valuationUnitSubgroup K := by
  ext u
  constructor
  · exact fun hu => hu.1
  · intro hu
    refine ⟨hu, ?_⟩
    rw [Lattice.mem_powerIdeal_iff]
    have hadd := min_ord_le_ord_add K (u : K) (-1)
    have huOrder : ord K (u : K) = 0 := hu
    rw [ord_neg, ord_one, huOrder] at hadd
    simpa [sub_eq_add_neg] using hadd

/-- The square classes represented by valuation units, denoted
`𝓞ˣFˣ² / Fˣ²` by Beli. -/
noncomputable def valuationUnitSquareClassSubgroup :
    Subgroup (SquareClass K) :=
  (valuationUnitSubgroup K).map (squareClassHom K)

/-- The square classes represented by principal units of depth `n`, denoted
`(1 + 𝔭ⁿ)Fˣ² / Fˣ²`. -/
noncomputable def principalUnitSquareClassSubgroup (n : Nat) :
    Subgroup (SquareClass K) :=
  (principalUnitSubgroup K n).map (squareClassHom K)

/-- Beli's extended convention for `(1 + p^n) F^times^2`.

For positive `n` this is the ordinary principal-unit square-class subgroup.
At depth zero Beli explicitly sets the group equal to all field square
classes, rather than to the image of `1 + O`.  Keeping this convention in a
separate definition prevents the genuine principal-unit filtration from
acquiring a false depth-zero endpoint. -/
noncomputable def beliCongruenceSquareClassSubgroup (n : Nat) :
    Subgroup (SquareClass K) :=
  if n = 0 then ⊤ else principalUnitSquareClassSubgroup K n

@[simp]
theorem beliCongruenceSquareClassSubgroup_zero :
    beliCongruenceSquareClassSubgroup K 0 = ⊤ := by
  simp [beliCongruenceSquareClassSubgroup]

theorem beliCongruenceSquareClassSubgroup_of_pos
    {n : Nat} (hn : 0 < n) :
    beliCongruenceSquareClassSubgroup K n =
      principalUnitSquareClassSubgroup K n := by
  simp [beliCongruenceSquareClassSubgroup, Nat.ne_of_gt hn]

/-- The ordinary principal-unit square-class group is contained in Beli's
extended congruence group at the same depth.  The only nontrivial endpoint is
depth zero, where Beli's convention makes the target the whole square-class
group. -/
theorem principalUnitSquareClassSubgroup_le_beliCongruence
    (n : Nat) :
    principalUnitSquareClassSubgroup K n ≤
      beliCongruenceSquareClassSubgroup K n := by
  by_cases hn : n = 0
  · subst n
    simp
  · rw [beliCongruenceSquareClassSubgroup_of_pos K
      (Nat.pos_of_ne_zero hn)]

/-- Beli's extended congruence filtration is decreasing, including its
depth-zero top endpoint. -/
theorem beliCongruenceSquareClassSubgroup_anti
    {m n : Nat} (hmn : m ≤ n) :
    beliCongruenceSquareClassSubgroup K n ≤
      beliCongruenceSquareClassSubgroup K m := by
  by_cases hm : m = 0
  · subst m
    simp
  · have hmPos : 0 < m := Nat.pos_of_ne_zero hm
    have hnPos : 0 < n := lt_of_lt_of_le hmPos hmn
    rw [beliCongruenceSquareClassSubgroup_of_pos K hmPos,
      beliCongruenceSquareClassSubgroup_of_pos K hnPos]
    exact Subgroup.map_mono (principalUnitSubgroup_anti K hmn)

/-- The square-class image of the quadratic norm group `N(a)`. -/
noncomputable def quadraticNormSquareClassSubgroup (a : Kˣ) :
    Subgroup (SquareClass K) :=
  (quadraticNormGroup K a).map (squareClassHom K)

/-- The principal-unit square-class filtration is decreasing. -/
theorem principalUnitSquareClassSubgroup_anti {m n : Nat} (hmn : m ≤ n) :
    principalUnitSquareClassSubgroup K n ≤
      principalUnitSquareClassSubgroup K m :=
  Subgroup.map_mono (principalUnitSubgroup_anti K hmn)

/-- Every principal-unit square class is represented by a valuation unit. -/
theorem principalUnitSquareClassSubgroup_le_valuationUnit (n : Nat) :
    principalUnitSquareClassSubgroup K n ≤
      valuationUnitSquareClassSubgroup K := by
  apply Subgroup.map_mono
  intro u hu
  exact hu.1

/-- At depth zero the principal-unit square classes are all unit square
classes. -/
theorem principalUnitSquareClassSubgroup_zero :
    principalUnitSquareClassSubgroup K 0 =
      valuationUnitSquareClassSubgroup K := by
  unfold principalUnitSquareClassSubgroup
    valuationUnitSquareClassSubgroup
  rw [principalUnitSubgroup_zero]

/-- The even-step collapse in the dyadic principal-unit square-class
filtration: for even `0 < n < 2e`, depth `n` already equals depth `n+1`.
This is the Hensel-theoretic input used in Beli (2003), Lemma 3.13(ii). -/
class PrincipalUnitSquareClassFiltrationLaws : Prop where
  eq_succ_of_even
      (n : Nat) (hpos : 0 < n)
      (hlt : n < 2 * ramificationIndex K) (heven : Even n) :
      principalUnitSquareClassSubgroup K n =
        principalUnitSquareClassSubgroup K (n + 1)

/-- Public form of the even-step collapse in the principal-unit filtration. -/
theorem principalUnitSquareClassSubgroup_eq_succ_of_even
    [PrincipalUnitSquareClassFiltrationLaws K]
    (n : Nat) (hpos : 0 < n)
    (hlt : n < 2 * ramificationIndex K) (heven : Even n) :
    principalUnitSquareClassSubgroup K n =
      principalUnitSquareClassSubgroup K (n + 1) :=
  PrincipalUnitSquareClassFiltrationLaws.eq_succ_of_even
    n hpos hlt heven

/-- Beli's unit square-class group `𝓞ˣ / 𝓞ˣ²`. -/
abbrev ValuationUnitClass :=
  valuationUnitSubgroup K ⧸ Subgroup.square (valuationUnitSubgroup K)

/-- The quotient homomorphism from valuation units to unit square classes. -/
noncomputable def valuationUnitClassHom :
    valuationUnitSubgroup K →* ValuationUnitClass K :=
  QuotientGroup.mk' (Subgroup.square (valuationUnitSubgroup K))

/-- A square of a valuation unit remains a square after forgetting that its
square root has valuation zero. -/
theorem valuationUnitSubgroup_square_map_le_square :
    (Subgroup.square (valuationUnitSubgroup K)).map
        (valuationUnitSubgroup K).subtype ≤
      Subgroup.square Kˣ := by
  simpa [valuationUnitSquareSubgroup] using
    valuationUnitSquareSubgroup_le_square K

/-- The canonical map from Beli's unit square-class group
`𝓞ˣ / 𝓞ˣ²` to the field square-class group `Kˣ / Kˣ²`. -/
noncomputable def valuationUnitClassToSquareClass :
    ValuationUnitClass K →* SquareClass K :=
  QuotientGroup.map (Subgroup.square (valuationUnitSubgroup K))
    (Subgroup.square Kˣ) (valuationUnitSubgroup K).subtype
    ((Subgroup.map_le_iff_le_comap).1
      (valuationUnitSubgroup_square_map_le_square K))

@[simp]
theorem valuationUnitClassToSquareClass_apply
    (u : valuationUnitSubgroup K) :
    valuationUnitClassToSquareClass K (valuationUnitClassHom K u) =
      squareClass K (u : Kˣ) :=
  rfl

/-- The canonical map from unit square classes to field square classes is
injective: a square root of a valuation unit necessarily has valuation zero. -/
theorem valuationUnitClassToSquareClass_injective :
    Function.Injective (valuationUnitClassToSquareClass K) := by
  intro c d hcd
  obtain ⟨u, rfl⟩ := Quotient.exists_rep c
  obtain ⟨v, rfl⟩ := Quotient.exists_rep d
  change QuotientGroup.mk' (Subgroup.square Kˣ) (u : Kˣ) =
    QuotientGroup.mk' (Subgroup.square Kˣ) (v : Kˣ) at hcd
  rw [QuotientGroup.mk'_eq_mk'] at hcd
  rcases hcd with ⟨s, hs, husv⟩
  change IsSquare s at hs
  rcases hs with ⟨t, hst⟩
  have hsUnit : IsValuationUnit K (s : K) := by
    rw [isValuationUnit_iff_ordUnit_eq_zero]
    have hord := congrArg (ordUnit K) husv
    have huOrder :=
      (isValuationUnit_iff_ordUnit_eq_zero K (u : Kˣ)).1 u.property
    have hvOrder :=
      (isValuationUnit_iff_ordUnit_eq_zero K (v : Kˣ)).1 v.property
    rw [ordUnit_mul, huOrder, hvOrder] at hord
    omega
  have htOrder : ordUnit K t = 0 := by
    have hsOrder :=
      (isValuationUnit_iff_ordUnit_eq_zero K s).1 hsUnit
    rw [hst, ordUnit_mul] at hsOrder
    omega
  have htUnit : IsValuationUnit K (t : K) :=
    (isValuationUnit_iff_ordUnit_eq_zero K t).2 htOrder
  let tUnit : valuationUnitSubgroup K := ⟨t, htUnit⟩
  change
    QuotientGroup.mk' (Subgroup.square (valuationUnitSubgroup K)) u =
      QuotientGroup.mk' (Subgroup.square (valuationUnitSubgroup K)) v
  rw [QuotientGroup.mk'_eq_mk']
  refine ⟨tUnit ^ 2, ?_, ?_⟩
  · exact (Subgroup.mem_square).2 ⟨tUnit, pow_two tUnit⟩
  · apply Subtype.ext
    change (u : Kˣ) * t ^ 2 = (v : Kˣ)
    rw [pow_two, ← hst]
    exact husv

/-- The field-square-class image of a subgroup of Beli's unit square-class
group. -/
noncomputable def valuationUnitClassSubgroupSquareImage
    (H : Subgroup (ValuationUnitClass K)) : Subgroup (SquareClass K) :=
  H.map (valuationUnitClassToSquareClass K)

theorem valuationUnitClassToSquareClass_mem_image
    {H : Subgroup (ValuationUnitClass K)} {c : ValuationUnitClass K}
    (hc : c ∈ H) :
    valuationUnitClassToSquareClass K c ∈
      valuationUnitClassSubgroupSquareImage K H :=
  ⟨c, hc, rfl⟩

/-- A principal-unit subgroup regarded as a subgroup of all valuation units. -/
noncomputable def principalUnitSubgroupInUnits (n : Nat) :
    Subgroup (valuationUnitSubgroup K) :=
  (principalUnitSubgroup K n).comap (valuationUnitSubgroup K).subtype

/-- Beli's subgroup `(1 + 𝔭ⁿ)𝓞ˣ² / 𝓞ˣ²`. -/
noncomputable def principalUnitValuationClassSubgroup (n : Nat) :
    Subgroup (ValuationUnitClass K) :=
  (principalUnitSubgroupInUnits K n).map (valuationUnitClassHom K)

/-- A valuation-unit square class whose relative quadratic defect has depth
at least `n` is represented by a principal unit of depth `n`. -/
theorem valuationUnitClassHom_mem_principalUnitValuationClassSubgroup_of_defect
    (u : valuationUnitSubgroup K) (n : Nat)
    (hdefect : (n : ℕ∞) ≤ quadraticDefect K (u : Kˣ)) :
    valuationUnitClassHom K u ∈
      principalUnitValuationClassSubgroup K n := by
  by_cases hn : n = 0
  · subst n
    refine ⟨u, ?_, rfl⟩
    change (u : Kˣ) ∈ principalUnitSubgroup K 0
    rw [principalUnitSubgroup_zero]
    exact u.property
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    rcases (isQuadraticApproximation_iff_le_defect K).2 hdefect with
      ⟨x, hx⟩
    have hxne : x ≠ 0 := by
      intro hxzero
      subst x
      have : n = 0 := by simpa using hx
      exact hn this
    let xu : Kˣ := Units.mk0 x hxne
    let v : Kˣ := xu ^ 2 * (u : Kˣ)⁻¹
    have herror : (n : WithTop Int) ≤ ord K (1 - (v : K)) := by
      simpa [v, xu, div_eq_mul_inv] using hx
    have herrorPos : (0 : WithTop Int) < ord K (1 - (v : K)) := by
      exact (show (0 : WithTop Int) < n by exact_mod_cast hnpos).trans_le herror
    have hvOrder : ord K (v : K) = 0 := by
      have hlt : ord K (1 : K) < ord K (1 - (v : K)) := by
        simpa only [ord_one] using herrorPos
      have hsub := (ord K).map_sub_eq_of_lt_left hlt
      have heq : 1 - (1 - (v : K)) = (v : K) := by ring
      rw [heq] at hsub
      simpa using hsub
    have hvUnit : IsValuationUnit K (v : K) := hvOrder
    let vu : valuationUnitSubgroup K := ⟨v, hvUnit⟩
    have hvPrincipal : (v : Kˣ) ∈ principalUnitSubgroup K n := by
      refine ⟨hvUnit, ?_⟩
      apply (Lattice.mem_powerIdeal_iff (K := K) (n : Int)
        ((v : K) - 1)).2
      have hneg : ord K ((v : K) - 1) = ord K (1 - (v : K)) := by
        have heq : (v : K) - 1 = -(1 - (v : K)) := by ring
        rw [heq, ord_neg]
      rw [hneg]
      exact herror
    have hvMem : valuationUnitClassHom K vu ∈
        principalUnitValuationClassSubgroup K n :=
      ⟨vu, hvPrincipal, rfl⟩
    have hxuOrder : ordUnit K xu = 0 := by
      have hvOrderUnit : ordUnit K v = 0 :=
        (isValuationUnit_iff_ordUnit_eq_zero K v).1 hvUnit
      have huOrder : ordUnit K (u : Kˣ) = 0 :=
        (isValuationUnit_iff_ordUnit_eq_zero K (u : Kˣ)).1 u.property
      dsimp only [v] at hvOrderUnit
      rw [ordUnit_mul, ordUnit_pow, ordUnit_inv, huOrder] at hvOrderUnit
      omega
    have hxuUnit : IsValuationUnit K (xu : K) :=
      (isValuationUnit_iff_ordUnit_eq_zero K xu).2 hxuOrder
    let t : valuationUnitSubgroup K :=
      ⟨xu * (u : Kˣ)⁻¹, (valuationUnitSubgroup K).mul_mem hxuUnit
        ((valuationUnitSubgroup K).inv_mem u.property)⟩
    have hclass : valuationUnitClassHom K u =
        valuationUnitClassHom K vu := by
      change QuotientGroup.mk' (Subgroup.square (valuationUnitSubgroup K)) u =
        QuotientGroup.mk' (Subgroup.square (valuationUnitSubgroup K)) vu
      rw [QuotientGroup.mk'_eq_mk']
      refine ⟨t ^ 2, (Subgroup.mem_square).2 ⟨t, pow_two t⟩, ?_⟩
      apply Subtype.ext
      change (u : Kˣ) * (xu * (u : Kˣ)⁻¹) ^ 2 = v
      dsimp only [v]
      simp [pow_two, mul_assoc, mul_left_comm, mul_comm]
    rwa [hclass]

/-- The valuation-unit part of the norm group, before quotienting by unit
squares. -/
noncomputable def quadraticNormUnitSubgroup (a : Kˣ) :
    Subgroup (valuationUnitSubgroup K) :=
  (quadraticNormGroup K a).comap (valuationUnitSubgroup K).subtype

/-- The image of the valuation-unit norm group in `𝓞ˣ / 𝓞ˣ²`. -/
noncomputable def quadraticNormValuationClassSubgroup (a : Kˣ) :
    Subgroup (ValuationUnitClass K) :=
  (quadraticNormUnitSubgroup K a).map (valuationUnitClassHom K)

/-- Mapping a principal-unit subgroup from unit square classes to field square
classes gives the same principal-unit filtration subgroup. -/
theorem valuationUnitClassSubgroupSquareImage_principalUnit (n : Nat) :
    valuationUnitClassSubgroupSquareImage K
        (principalUnitValuationClassSubgroup K n) =
      principalUnitSquareClassSubgroup K n := by
  ext z
  constructor
  · rintro ⟨c, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨(u : Kˣ), hu, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    let u : valuationUnitSubgroup K := ⟨a, ha.1⟩
    refine ⟨valuationUnitClassHom K u, ?_, ?_⟩
    · refine ⟨u, ?_, rfl⟩
      exact ha
    · rfl

/-- The canonical embedding preserves intersections of unit-square-class
subgroups. -/
theorem valuationUnitClassSubgroupSquareImage_inf
    (H J : Subgroup (ValuationUnitClass K)) :
    valuationUnitClassSubgroupSquareImage K (H ⊓ J) =
      valuationUnitClassSubgroupSquareImage K H ⊓
        valuationUnitClassSubgroupSquareImage K J := by
  exact Subgroup.map_inf H J (valuationUnitClassToSquareClass K)
    (valuationUnitClassToSquareClass_injective K)

/-- Mapping the valuation-unit part of a quadratic norm group gives the
intersection of its field-square-class image with the unit square classes. -/
theorem valuationUnitClassSubgroupSquareImage_quadraticNorm
    (parameter : Kˣ) :
    valuationUnitClassSubgroupSquareImage K
        (quadraticNormValuationClassSubgroup K parameter) =
      valuationUnitSquareClassSubgroup K ⊓
        quadraticNormSquareClassSubgroup K parameter := by
  ext z
  constructor
  · rintro ⟨c, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨⟨(u : Kˣ), u.property, rfl⟩,
      ⟨(u : Kˣ), hu, rfl⟩⟩
  · rintro ⟨⟨u, hu, huz⟩, ⟨a, ha, haz⟩⟩
    have hclass : squareClass K u = squareClass K a :=
      huz.trans haz.symm
    change QuotientGroup.mk' (Subgroup.square Kˣ) u =
      QuotientGroup.mk' (Subgroup.square Kˣ) a at hclass
    rw [QuotientGroup.mk'_eq_mk'] at hclass
    rcases hclass with ⟨s, hs, husa⟩
    change IsSquare s at hs
    have hsNorm : s ∈ quadraticNormGroup K parameter :=
      isQuadraticNorm_of_isSquare_right K hs
    have huNorm : u ∈ quadraticNormGroup K parameter := by
      have hprod := (quadraticNormGroup K parameter).mul_mem ha
        ((quadraticNormGroup K parameter).inv_mem hsNorm)
      have heq : a * s⁻¹ = u := by
        rw [← husa]
        simp
      rwa [heq] at hprod
    let uUnit : valuationUnitSubgroup K := ⟨u, hu⟩
    refine ⟨valuationUnitClassHom K uUnit, ?_, ?_⟩
    · exact ⟨uUnit, huNorm, rfl⟩
    · exact huz

@[simp]
theorem valuationUnitClassSubgroupSquareImage_bot :
    valuationUnitClassSubgroupSquareImage K ⊥ = ⊥ :=
  Subgroup.map_bot (valuationUnitClassToSquareClass K)

/-- The exact field-square-class image of the low-defect branch in Beli's
Definition 6. -/
theorem valuationUnitClassSubgroupSquareImage_principalUnit_inf_norm
    (n : Nat) (parameter : Kˣ) :
    valuationUnitClassSubgroupSquareImage K
        (principalUnitValuationClassSubgroup K n ⊓
          quadraticNormValuationClassSubgroup K parameter) =
      principalUnitSquareClassSubgroup K n ⊓
        quadraticNormSquareClassSubgroup K parameter := by
  rw [valuationUnitClassSubgroupSquareImage_inf,
    valuationUnitClassSubgroupSquareImage_principalUnit,
    valuationUnitClassSubgroupSquareImage_quadraticNorm]
  rw [← inf_assoc,
    inf_eq_left.mpr
      (principalUnitSquareClassSubgroup_le_valuationUnit K n)]

/-- The principal-unit filtration descends to `𝓞ˣ / 𝓞ˣ²`. -/
theorem principalUnitValuationClassSubgroup_anti
    {m n : Nat} (hmn : m ≤ n) :
    principalUnitValuationClassSubgroup K n ≤
      principalUnitValuationClassSubgroup K m := by
  apply Subgroup.map_mono
  apply Subgroup.comap_mono
  exact principalUnitSubgroup_anti K hmn

/-- The even-step collapse also holds in Beli's unit-square-class quotient.
This is reflected from field square classes through the injective canonical
map. -/
theorem principalUnitValuationClassSubgroup_eq_succ_of_even
    [PrincipalUnitSquareClassFiltrationLaws K]
    (n : Nat) (hpos : 0 < n)
    (hlt : n < 2 * ramificationIndex K) (heven : Even n) :
    principalUnitValuationClassSubgroup K n =
      principalUnitValuationClassSubgroup K (n + 1) := by
  let f := valuationUnitClassToSquareClass K
  have hf : Function.Injective f :=
    valuationUnitClassToSquareClass_injective K
  have himage :
      (principalUnitValuationClassSubgroup K n).map f =
        (principalUnitValuationClassSubgroup K (n + 1)).map f := by
    change valuationUnitClassSubgroupSquareImage K
        (principalUnitValuationClassSubgroup K n) =
      valuationUnitClassSubgroupSquareImage K
        (principalUnitValuationClassSubgroup K (n + 1))
    rw [valuationUnitClassSubgroupSquareImage_principalUnit,
      valuationUnitClassSubgroupSquareImage_principalUnit]
    exact principalUnitSquareClassSubgroup_eq_succ_of_even
      K n hpos hlt heven
  ext c
  constructor
  · intro hc
    have hfc : f c ∈
        (principalUnitValuationClassSubgroup K (n + 1)).map f := by
      rw [← himage]
      exact ⟨c, hc, rfl⟩
    rcases hfc with ⟨d, hd, hdc⟩
    simpa [hf hdc] using hd
  · intro hc
    have hfc : f c ∈
        (principalUnitValuationClassSubgroup K n).map f := by
      rw [himage]
      exact ⟨c, hc, rfl⟩
    rcases hfc with ⟨d, hd, hdc⟩
    simpa [hf hdc] using hd

end Bong.Dyadic
