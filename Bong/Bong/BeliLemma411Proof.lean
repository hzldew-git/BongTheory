/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.BeliLemma411
import Bong.Bong.AdjacentNormGeneratorChange
import Bong.Bong.BeliLemma67Proof
import Bong.Bong.BinaryNormGeneratorLocalProof
import Bong.Bong.BinarySpinorLocalProof
import Bong.Bong.BeliLemma47Proof
import Bong.Bong.BeliLemma49Proof
import Bong.Bong.BeliLemma41AdaptedBinary
import Bong.Bong.BeliLemma43MaximalNormProof
import Bong.Bong.MaximalNormSplittingDual

/-!
# Proof of Beli (2003), Lemma 4.11

The proof follows the two cases in the paper.  An odd exceptional adjacent
gap gives a quadratic norm group.  A nonsquare multiplier from either
neighbor gives a distinct quadratic norm group, so the two index-two groups
generate all square classes.  In the even low-defect case, an odd neighboring
gap reduces to the first case; for an even neighboring gap the distinguished
discriminant unit is the multiplier.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- If the full square-class group is contained in a quadratic norm group,
the defining parameter is a square. -/
private theorem isSquare_of_top_le_quadraticNormSquareClassSubgroup
    (a : Kˣ)
    (h : (⊤ : Subgroup (SquareClass K)) ≤
      quadraticNormSquareClassSubgroup K a) :
    IsSquare a := by
  apply (hilbertSymbol_left_trivial_iff_isSquare (K := K) a).1
  intro x
  have hx : squareClass K x ∈ quadraticNormSquareClassSubgroup K a :=
    h trivial
  rw [quadraticNormSquareClassSubgroup_eq_ker] at hx
  exact hx

/-- Two quadratic norm hyperplanes generate all square classes when the first
parameter and the product of the two parameters are both nonsquares. -/
private theorem quadraticNormSquareClassSubgroup_sup_eq_top
    (a b : Kˣ) (ha : ¬IsSquare a) (hab : ¬IsSquare (a * b)) :
    quadraticNormSquareClassSubgroup K a ⊔
        quadraticNormSquareClassSubgroup K b = ⊤ := by
  have hnot : ¬quadraticNormSquareClassSubgroup K b ≤
      quadraticNormSquareClassSubgroup K a := by
    intro hle
    have hinf : quadraticNormSquareClassSubgroup K b ⊓
        (⊤ : Subgroup (SquareClass K)) ≤
          quadraticNormSquareClassSubgroup K a := by
      simpa using hle
    rcases (quadraticNorm_inf_le_quadraticNorm_iff
        K b a ⊤).1 hinf with htop | hproduct
    · exact ha (isSquare_of_top_le_quadraticNormSquareClassSubgroup
        (K := K) a htop)
    · apply hab
      have hsquare := isSquare_of_top_le_quadraticNormSquareClassSubgroup
        (K := K) (b * a) hproduct
      simpa [mul_comm] using hsquare
  have hnotKer : ¬quadraticNormSquareClassSubgroup K b ≤
      (squareClassHilbertCharacter K a).ker := by
    rw [← quadraticNormSquareClassSubgroup_eq_ker K a]
    exact hnot
  rw [quadraticNormSquareClassSubgroup_eq_ker]
  simpa using inf_ker_sup_eq_of_le_of_not_le
    (squareClassHilbertCharacter K a) ⊤
      (quadraticNormSquareClassSubgroup K b) le_top hnotKer

namespace BONG

/-- A unit multiplier supplied by either existing neighboring adjacent pair. -/
private def IsNeighborNormGeneratorMultiplier
    (b : BONG V q L n) (i : Fin n) (hpair : i.val + 1 < n)
    (z : valuationUnitSubgroup K) : Prop :=
  (∃ hleft : 1 ≤ i.val,
    valuationUnitClassHom K z ∈ beliNormGeneratorGroup K
      (b.valueUnit i / b.valueUnit ⟨i.val - 1, by omega⟩)) ∨
  (∃ hright : i.val + 2 < n,
    valuationUnitClassHom K z ∈ beliNormGeneratorGroup K
      (b.valueUnit ⟨i.val + 2, hright⟩ /
        b.valueUnit ⟨i.val + 1, hpair⟩))

/-- A failure of property B supplies an exceptional pair together with an
actual (hence non-vacuous) neighboring gap below `2e + 1`.  Unlike the
rank-at-least-three wrapper used for Lemma 6.7, this formulation also covers
the small ranks occurring in Lemma 4.11. -/
private theorem exists_propertyBViolation
    (b : BONG V q L (n + 1))
    (hA : b.HasPropertyA) (hnotB : ¬b.HasPropertyB) :
    ∃ i : Fin n, b.propertyBTrigger i ∧
      ((∃ j : Fin (n + 1), j.val + 1 = i.val ∧
        b.order i.castSucc - b.order j <
          2 * (ramificationIndex K : Int) + 1) ∨
      (∃ k : Fin (n + 1), i.val + 2 = k.val ∧
        b.order k - b.order i.succ <
          2 * (ramificationIndex K : Int) + 1)) := by
  classical
  by_contra hnone
  apply hnotB
  refine ⟨hA, ?_⟩
  intro i hi
  constructor
  · intro j hj
    by_contra hgap
    apply hnone
    refine ⟨i, hi, Or.inl ⟨j, hj, ?_⟩⟩
    exact lt_of_not_ge hgap
  · intro k hk
    by_contra hgap
    apply hnone
    refine ⟨i, hi, Or.inr ⟨k, hk, ?_⟩⟩
    exact lt_of_not_ge hgap

/-- A failed left-neighbor bound supplies a nonsquare multiplier from that
neighbor's norm-generator group. -/
private theorem exists_left_neighbor_multiplier
    (b : BONG V q L n) (i : Fin n) (hpair : i.val + 1 < n)
    (j : Fin n) (hj : j.val + 1 = i.val)
    (hgap : b.order i - b.order j <
      2 * (ramificationIndex K : Int) + 1) :
    ∃ z : valuationUnitSubgroup K,
      IsNeighborNormGeneratorMultiplier b i hpair z ∧
        ¬IsSquare (z : Kˣ) := by
  have hjPair : j.val + 1 < n := by omega
  let a : Kˣ := b.adjacentParameter j hjPair
  have ha : IsBinaryParameterAdmissible a :=
    b.adjacentParameter_isBinaryParameterAdmissible j hjPair
  have hsuccessor :
      (⟨j.val + 1, hjPair⟩ : Fin n) = i := by
    ext
    simpa using hj
  have haOrder : ordUnit K a = b.order i - b.order j := by
    dsimp only [a]
    rw [b.ordUnit_adjacentParameter, hsuccessor]
  have haUpper : ordUnit K a ≤
      2 * (ramificationIndex K : Int) := by
    rw [haOrder]
    omega
  rcases exists_nonsquare_mem_beliNormGeneratorGroup_of_admissible_order_le_twoE
      (K := K) a ha haUpper with ⟨z, hz, hzNotSquare⟩
  have hleft : 1 ≤ i.val := by omega
  refine ⟨z, Or.inl ⟨hleft, ?_⟩, hzNotSquare⟩
  have hjIndex :
      j = ⟨i.val - 1, by omega⟩ := by
    apply Fin.ext
    change j.val = i.val - 1
    omega
  have haEq : a =
      b.valueUnit i / b.valueUnit ⟨i.val - 1, by omega⟩ := by
    unfold a adjacentParameter
    congr 1
    · exact congrArg b.valueUnit hsuccessor
    · exact congrArg b.valueUnit hjIndex
  rwa [← haEq]

/-- A failed right-neighbor bound supplies a nonsquare multiplier from that
neighbor's norm-generator group. -/
private theorem exists_right_neighbor_multiplier
    (b : BONG V q L n) (i : Fin n) (hpair : i.val + 1 < n)
    (k : Fin n) (hk : i.val + 2 = k.val)
    (hgap : b.order k - b.order ⟨i.val + 1, hpair⟩ <
      2 * (ramificationIndex K : Int) + 1) :
    ∃ z : valuationUnitSubgroup K,
      IsNeighborNormGeneratorMultiplier b i hpair z ∧
        ¬IsSquare (z : Kˣ) := by
  let i1 : Fin n := ⟨i.val + 1, hpair⟩
  have hkLt := k.isLt
  have hiPair : i1.val + 1 < n := by
    dsimp only [i1]
    omega
  let a : Kˣ := b.adjacentParameter i1 hiPair
  have ha : IsBinaryParameterAdmissible a :=
    b.adjacentParameter_isBinaryParameterAdmissible i1 hiPair
  have hsuccessor :
      (⟨i1.val + 1, hiPair⟩ : Fin n) = k := by
    ext
    dsimp only [i1]
    simpa using hk
  have haOrder : ordUnit K a = b.order k - b.order i1 := by
    dsimp only [a]
    rw [b.ordUnit_adjacentParameter, hsuccessor]
  have haUpper : ordUnit K a ≤
      2 * (ramificationIndex K : Int) := by
    rw [haOrder]
    dsimp only [i1]
    omega
  rcases exists_nonsquare_mem_beliNormGeneratorGroup_of_admissible_order_le_twoE
      (K := K) a ha haUpper with ⟨z, hz, hzNotSquare⟩
  refine ⟨z, Or.inr ⟨by omega, ?_⟩, hzNotSquare⟩
  have haEq : a =
      b.valueUnit ⟨i.val + 2, by omega⟩ /
        b.valueUnit ⟨i.val + 1, hpair⟩ := by
    unfold a adjacentParameter
    congr 1
  rwa [← haEq]

/-- In the even-trigger branch, property A and an actual failed neighboring
bound force the normalized central defect to be strictly below `2e`. -/
private theorem normalizedDefect_lt_twoE_of_neighborFailure
    (b : BONG V q L (n + 1)) (hA : b.HasPropertyA)
    (i : Fin n) (d : Nat)
    (hRd : 2 * (d : Int) ≤
      2 * (ramificationIndex K : Int) -
        (b.order i.succ - b.order i.castSucc))
    (hneighbor :
      (∃ j : Fin (n + 1), j.val + 1 = i.val ∧
        b.order i.castSucc - b.order j <
          2 * (ramificationIndex K : Int) + 1) ∨
      (∃ k : Fin (n + 1), i.val + 2 = k.val ∧
        b.order k - b.order i.succ <
          2 * (ramificationIndex K : Int) + 1)) :
    d < 2 * ramificationIndex K := by
  by_contra hnot
  have hdLowerNat : 2 * ramificationIndex K ≤ d :=
    Nat.le_of_not_gt hnot
  have hdLower : (2 * ramificationIndex K : Int) ≤ d := by
    exact_mod_cast hdLowerNat
  rcases hneighbor with ⟨j, hj, hjGap⟩ | ⟨k, hk, hkGap⟩
  · have hjEnd :
        (⟨j.val + 2, by omega⟩ : Fin (n + 1)) = i.succ := by
      apply Fin.ext
      simp only [Fin.val_mk, Fin.val_succ]
      omega
    have htwoStep : b.order j < b.order i.succ := by
      have h := hA j (by omega)
      rwa [hjEnd] at h
    omega
  · have hkLt := k.isLt
    have hiBound : i.castSucc.val + 2 < n + 1 := by
      change i.val + 2 < n + 1
      omega
    have hiEnd :
        (⟨i.castSucc.val + 2, hiBound⟩ : Fin (n + 1)) = k := by
      apply Fin.ext
      simp only [Fin.val_mk, Fin.val_castSucc]
      omega
    have htwoStep : b.order i.castSucc < b.order k := by
      have h := hA i.castSucc (by omega)
      rwa [hiEnd] at h
    omega

/-- For an even failed left-neighbor gap, the discriminant unit is the
left-neighbor multiplier used in the even central argument. -/
private theorem discriminant_is_left_neighbor_multiplier
    (b : BONG V q L n) (i : Fin n) (hpair : i.val + 1 < n)
    (j : Fin n) (hj : j.val + 1 = i.val)
    (hgapEven : Even (b.order i - b.order j))
    (hgapUpper : b.order i - b.order j <
      2 * (ramificationIndex K : Int) + 1) :
    IsNeighborNormGeneratorMultiplier b i hpair
      (discriminantValuationUnit (K := K)) := by
  have hjPair : j.val + 1 < n := by omega
  let a : Kˣ := b.adjacentParameter j hjPair
  have hsuccessor :
      (⟨j.val + 1, hjPair⟩ : Fin n) = i := by
    apply Fin.ext
    simpa using hj
  have haOrder : ordUnit K a = b.order i - b.order j := by
    dsimp only [a]
    rw [b.ordUnit_adjacentParameter, hsuccessor]
  have haEven : Even (ordUnit K a) := by rwa [haOrder]
  have haUpper : ordUnit K a ≤
      2 * (ramificationIndex K : Int) := by
    rw [haOrder]
    omega
  have hmem :=
    discriminantUnitClass_mem_beliNormGeneratorGroup_of_even_order_le_twoE
      (K := K) a haEven haUpper
  have hleft : 1 ≤ i.val := by omega
  refine Or.inl ⟨hleft, ?_⟩
  have hjIndex : j = ⟨i.val - 1, by omega⟩ := by
    apply Fin.ext
    change j.val = i.val - 1
    omega
  have haEq : a =
      b.valueUnit i / b.valueUnit ⟨i.val - 1, by omega⟩ := by
    unfold a adjacentParameter
    congr 1
    · exact congrArg b.valueUnit hsuccessor
    · exact congrArg b.valueUnit hjIndex
  rwa [← haEq]

/-- For an even failed right-neighbor gap, the discriminant unit is the
right-neighbor multiplier used in the even central argument. -/
private theorem discriminant_is_right_neighbor_multiplier
    (b : BONG V q L n) (i : Fin n) (hpair : i.val + 1 < n)
    (k : Fin n) (hk : i.val + 2 = k.val)
    (hgapEven : Even
      (b.order k - b.order ⟨i.val + 1, hpair⟩))
    (hgapUpper : b.order k - b.order ⟨i.val + 1, hpair⟩ <
      2 * (ramificationIndex K : Int) + 1) :
    IsNeighborNormGeneratorMultiplier b i hpair
      (discriminantValuationUnit (K := K)) := by
  let i1 : Fin n := ⟨i.val + 1, hpair⟩
  have hkLt := k.isLt
  have hiPair : i1.val + 1 < n := by
    dsimp only [i1]
    omega
  let a : Kˣ := b.adjacentParameter i1 hiPair
  have hsuccessor :
      (⟨i1.val + 1, hiPair⟩ : Fin n) = k := by
    apply Fin.ext
    dsimp only [i1]
    simpa using hk
  have haOrder : ordUnit K a = b.order k - b.order i1 := by
    dsimp only [a]
    rw [b.ordUnit_adjacentParameter, hsuccessor]
  have haEven : Even (ordUnit K a) := by
    rw [haOrder]
    simpa only [i1] using hgapEven
  have haUpper : ordUnit K a ≤
      2 * (ramificationIndex K : Int) := by
    rw [haOrder]
    simpa only [i1] using (show
      b.order k - b.order ⟨i.val + 1, hpair⟩ ≤
        2 * (ramificationIndex K : Int) by omega)
  have hmem :=
    discriminantUnitClass_mem_beliNormGeneratorGroup_of_even_order_le_twoE
      (K := K) a haEven haUpper
  refine Or.inr ⟨by omega, ?_⟩
  have haEq : a =
      b.valueUnit ⟨i.val + 2, by omega⟩ /
        b.valueUnit ⟨i.val + 1, hpair⟩ := by
    unfold a adjacentParameter
    congr 1
  rwa [← haEq]

/-- The odd-gap argument in the first paragraph of Beli (2003), Lemma 4.11. -/
private theorem spinorNormImage_eq_univ_of_odd_adjacent
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BinarySpinorLocalLaws.{u, v} K]
    (b : BONG V q L n) (hgood : b.IsGood)
    (i : Fin n) (hpair : i.val + 1 < n)
    (hodd : Odd (b.order ⟨i.val + 1, hpair⟩ - b.order i))
    (hupper : b.order ⟨i.val + 1, hpair⟩ - b.order i ≤
      2 * (ramificationIndex K : Int) + 1)
    (z : valuationUnitSubgroup K)
    (hz : IsNeighborNormGeneratorMultiplier b i hpair z)
    (hzNotSquare : ¬IsSquare (z : Kˣ)) :
    Lattice.spinorNormImage (q := q) (L := L) = Set.univ := by
  let a : Kˣ := b.adjacentParameter i hpair
  have haAdmissible : IsBinaryParameterAdmissible a :=
    b.adjacentParameter_isBinaryParameterAdmissible i hpair
  have haOrder : ordUnit K a =
      b.order ⟨i.val + 1, hpair⟩ - b.order i := by
    exact b.ordUnit_adjacentParameter i hpair
  have haOdd : Odd (ordUnit K a) := by rwa [haOrder]
  have haUpper : ordUnit K a ≤
      2 * (ramificationIndex K : Int) + 1 := by rwa [haOrder]
  have hzaAdmissible : IsBinaryParameterAdmissible ((z : Kˣ) * a) := by
    apply b.isBinaryParameterAdmissible_mul_adjacentParameter_of_adjacentMultiplier
      hgood i hpair z
    exact hz
  have hzOrder : ordUnit K (z : Kˣ) = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K (z : Kˣ)).1 z.property
  have hzaOrder : ordUnit K ((z : Kˣ) * a) = ordUnit K a := by
    rw [ordUnit_mul, hzOrder, zero_add]
  have hzaOdd : Odd (ordUnit K ((z : Kˣ) * a)) := by
    rwa [hzaOrder]
  have hzaUpper : ordUnit K ((z : Kˣ) * a) ≤
      2 * (ramificationIndex K : Int) + 1 := by
    rwa [hzaOrder]
  have hgroupA : beliSpinorGroup K (unitSquareClass K a) =
      quadraticNormSquareClassSubgroup K (-a) := by
    rw [beliSpinorGroup_unitSquareClass]
    exact beliSpinorGroupRepresentative_eq_norm_of_odd_trigger
      (K := K) a haAdmissible haOdd haUpper
  have hgroupZA : beliSpinorGroup K
      (unitSquareClass K ((z : Kˣ) * a)) =
        quadraticNormSquareClassSubgroup K (-((z : Kˣ) * a)) := by
    rw [beliSpinorGroup_unitSquareClass]
    exact beliSpinorGroupRepresentative_eq_norm_of_odd_trigger
      (K := K) ((z : Kˣ) * a) hzaAdmissible hzaOdd hzaUpper
  have hminusANotSquare : ¬IsSquare (-a) := by
    intro hsquare
    have htop := quadraticDefect_eq_top_of_isSquare (K := K) hsquare
    have hzero := quadraticDefect_eq_zero_of_odd_ordUnit (K := K) (-a) (by
      simpa using haOdd)
    rw [hzero] at htop
    exact ENat.zero_ne_top htop
  have hproductNotSquare :
      ¬IsSquare ((-a) * (-((z : Kˣ) * a))) := by
    intro hsquare
    have haSquare : IsSquare (a ^ 2) := ⟨a, by simp [pow_two]⟩
    have hzSquare := hsquare.div haSquare
    apply hzNotSquare
    have heq : (-a) * (-((z : Kˣ) * a)) / a ^ 2 = (z : Kˣ) := by
      apply Units.ext
      simp only [Units.val_div_eq_div_val, Units.val_mul, Units.val_neg,
        Units.val_pow_eq_pow_val]
      field_simp [Units.ne_zero a]
    rwa [heq] at hzSquare
  have hsup : quadraticNormSquareClassSubgroup K (-a) ⊔
      quadraticNormSquareClassSubgroup K (-((z : Kˣ) * a)) = ⊤ :=
    quadraticNormSquareClassSubgroup_sup_eq_top
      (K := K) (-a) (-((z : Kˣ) * a))
        hminusANotSquare hproductNotSquare
  have hleft : quadraticNormSquareClassSubgroup K (-a) ≤
      Lattice.spinorNormImageSubgroup (q := q) (L := L) := by
    intro c hc
    change c ∈ Lattice.spinorNormImage (q := q) (L := L)
    apply b.beliCorollary410_ii hgood i hpair
    rw [adjacentUnitSquareClass]
    change c ∈ beliSpinorGroup K (unitSquareClass K a)
    rwa [hgroupA]
  have hright : quadraticNormSquareClassSubgroup K (-((z : Kˣ) * a)) ≤
      Lattice.spinorNormImageSubgroup (q := q) (L := L) := by
    intro c hc
    change c ∈ Lattice.spinorNormImage (q := q) (L := L)
    apply b.beliCorollary410_iii hgood i hpair z
    · exact hz
    · rwa [hgroupZA]
  have htop : Lattice.spinorNormImageSubgroup (q := q) (L := L) = ⊤ := by
    apply top_unique
    rw [← hsup]
    exact sup_le hleft hright
  rw [← Lattice.coe_spinorNormImageSubgroup, htop]
  rfl

/-- The even-gap argument in the second paragraph of Beli (2003), Lemma
4.11.  The central defect is strictly below the discriminant defect, so
multiplication by the distinguished discriminant unit preserves that defect
but changes the associated quadratic norm hyperplane. -/
private theorem spinorNormImage_eq_univ_of_even_adjacent
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BinarySpinorLocalLaws.{u, v} K]
    (b : BONG V q L n) (hgood : b.IsGood)
    (i : Fin n) (hpair : i.val + 1 < n)
    (heven : Even (b.order ⟨i.val + 1, hpair⟩ - b.order i))
    (d : Nat)
    (hparameterDefect : beliParameterDefect K
        (b.adjacentParameter i hpair) = (d : ℕ∞))
    (hRd : 2 * (d : Int) ≤
      2 * (ramificationIndex K : Int) -
        (b.order ⟨i.val + 1, hpair⟩ - b.order i))
    (hdLt : d < 2 * ramificationIndex K)
    (hz : IsNeighborNormGeneratorMultiplier b i hpair
      (discriminantValuationUnit (K := K))) :
    Lattice.spinorNormImage (q := q) (L := L) = Set.univ := by
  let a : Kˣ := b.adjacentParameter i hpair
  let delta : valuationUnitSubgroup K :=
    discriminantValuationUnit (K := K)
  have haAdmissible : IsBinaryParameterAdmissible a :=
    b.adjacentParameter_isBinaryParameterAdmissible i hpair
  have haOrder : ordUnit K a =
      b.order ⟨i.val + 1, hpair⟩ - b.order i :=
    b.ordUnit_adjacentParameter i hpair
  have haUpper : ordUnit K a ≤
      2 * (ramificationIndex K : Int) := by
    rw [haOrder]
    omega
  have haLow : 2 * beliParameterDefect K a ≤
      (beliSpinorCaseIIILowerCutoff K a : ℕ∞) := by
    rw [hparameterDefect]
    norm_cast
    unfold beliSpinorCaseIIILowerCutoff
    rw [haOrder]
    have hnonneg : 0 ≤
        2 * (ramificationIndex K : Int) -
          (b.order ⟨i.val + 1, hpair⟩ - b.order i) := by
      omega
    have hcutCast :
        (Int.toNat
            (2 * (ramificationIndex K : Int) -
              (b.order ⟨i.val + 1, hpair⟩ - b.order i)) : Int) =
          2 * (ramificationIndex K : Int) -
            (b.order ⟨i.val + 1, hpair⟩ - b.order i) :=
      Int.toNat_of_nonneg hnonneg
    omega
  have haFinite : beliParameterDefect K a ≠ ⊤ := by
    rw [hparameterDefect]
    exact ENat.coe_ne_top d
  have hzaAdmissible :
      IsBinaryParameterAdmissible ((delta : Kˣ) * a) := by
    apply b.isBinaryParameterAdmissible_mul_adjacentParameter_of_adjacentMultiplier
      hgood i hpair delta
    exact hz
  have hdeltaOrder : ordUnit K (delta : Kˣ) = 0 :=
    (isValuationUnit_iff_ordUnit_eq_zero K (delta : Kˣ)).1 delta.property
  have hzaOrder : ordUnit K ((delta : Kˣ) * a) = ordUnit K a := by
    rw [ordUnit_mul, hdeltaOrder, zero_add]
  have hdeltaDefect : quadraticDefect K (delta : Kˣ) =
      ((2 * ramificationIndex K : Nat) : ℕ∞) := by
    change quadraticDefect K
        (DyadicDiscriminantClassLaws.discriminantUnit (K := K)) = _
    exact DyadicDiscriminantClassLaws.discriminant_defect
  have hminusADefect : quadraticDefect K (-a) = (d : ℕ∞) := by
    exact hparameterDefect
  have hdefectLt : quadraticDefect K (-a) <
      quadraticDefect K (delta : Kˣ) := by
    rw [hminusADefect, hdeltaDefect]
    exact_mod_cast hdLt
  have hnegativeProduct :
      -((delta : Kˣ) * a) = (delta : Kˣ) * (-a) := by
    apply Units.ext
    simp
  have hzaDefect : beliParameterDefect K ((delta : Kˣ) * a) =
      (d : ℕ∞) := by
    unfold beliParameterDefect
    rw [hnegativeProduct,
      quadraticDefect_mul_eq_right_of_lt_left (K := K) hdefectLt,
      hminusADefect]
  have hzaUpper : ordUnit K ((delta : Kˣ) * a) ≤
      2 * (ramificationIndex K : Int) := by
    rwa [hzaOrder]
  have hcutoffEq :
      beliSpinorCaseIIILowerCutoff K ((delta : Kˣ) * a) =
        beliSpinorCaseIIILowerCutoff K a := by
    unfold beliSpinorCaseIIILowerCutoff
    rw [hzaOrder]
  have hzaLow : 2 * beliParameterDefect K ((delta : Kˣ) * a) ≤
      (beliSpinorCaseIIILowerCutoff K ((delta : Kˣ) * a) : ℕ∞) := by
    rw [hzaDefect, hcutoffEq, ← hparameterDefect]
    exact haLow
  have hzaFinite : beliParameterDefect K ((delta : Kˣ) * a) ≠ ⊤ := by
    rw [hzaDefect]
    exact ENat.coe_ne_top d
  have hgroupA : beliSpinorGroup K (unitSquareClass K a) =
      quadraticNormSquareClassSubgroup K (-a) := by
    rw [beliSpinorGroup_unitSquareClass]
    exact beliSpinorGroupRepresentative_eq_norm_of_low_defect
      (K := K) a haAdmissible haUpper haLow haFinite
  have hgroupDeltaA : beliSpinorGroup K
      (unitSquareClass K ((delta : Kˣ) * a)) =
        quadraticNormSquareClassSubgroup K
          (-((delta : Kˣ) * a)) := by
    rw [beliSpinorGroup_unitSquareClass]
    exact beliSpinorGroupRepresentative_eq_norm_of_low_defect
      (K := K) ((delta : Kˣ) * a) hzaAdmissible hzaUpper
        hzaLow hzaFinite
  have hminusANotSquare : ¬IsSquare (-a) := by
    intro hsquare
    apply haFinite
    unfold beliParameterDefect
    exact quadraticDefect_eq_top_of_isSquare (K := K) hsquare
  have hproductNotSquare :
      ¬IsSquare ((-a) * (-((delta : Kˣ) * a))) := by
    intro hsquare
    have haSquare : IsSquare (a ^ 2) := ⟨a, by simp [pow_two]⟩
    have hdeltaSquare := hsquare.div haSquare
    apply discriminantValuationUnit_not_isSquare (K := K)
    have heq : (-a) * (-((delta : Kˣ) * a)) / a ^ 2 =
        (delta : Kˣ) := by
      apply Units.ext
      simp only [Units.val_div_eq_div_val, Units.val_mul, Units.val_neg,
        Units.val_pow_eq_pow_val]
      field_simp [Units.ne_zero a]
    rwa [heq] at hdeltaSquare
  have hsup : quadraticNormSquareClassSubgroup K (-a) ⊔
      quadraticNormSquareClassSubgroup K (-((delta : Kˣ) * a)) = ⊤ :=
    quadraticNormSquareClassSubgroup_sup_eq_top
      (K := K) (-a) (-((delta : Kˣ) * a))
        hminusANotSquare hproductNotSquare
  have hleft : quadraticNormSquareClassSubgroup K (-a) ≤
      Lattice.spinorNormImageSubgroup (q := q) (L := L) := by
    intro c hc
    change c ∈ Lattice.spinorNormImage (q := q) (L := L)
    apply b.beliCorollary410_ii hgood i hpair
    rw [adjacentUnitSquareClass]
    change c ∈ beliSpinorGroup K (unitSquareClass K a)
    rwa [hgroupA]
  have hright :
      quadraticNormSquareClassSubgroup K (-((delta : Kˣ) * a)) ≤
        Lattice.spinorNormImageSubgroup (q := q) (L := L) := by
    intro c hc
    change c ∈ Lattice.spinorNormImage (q := q) (L := L)
    apply b.beliCorollary410_iii hgood i hpair delta
    · exact hz
    · rwa [hgroupDeltaA]
  have htop : Lattice.spinorNormImageSubgroup (q := q) (L := L) = ⊤ := by
    apply top_unique
    rw [← hsup]
    exact sup_le hleft hright
  rw [← Lattice.coe_spinorNormImageSubgroup, htop]
  rfl

/-- Beli (2003), Lemma 4.11, with every local multiplier constructed from
the preceding binary norm-generator results. -/
theorem spinorNormImage_eq_univ_of_propertyA_not_propertyB
    [BinaryNormGeneratorLocalLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BinarySpinorLocalLaws.{u, v} K]
    (b : BONG V q L (n + 1))
    (hA : b.HasPropertyA) (hnotB : ¬b.HasPropertyB) :
    Lattice.spinorNormImage (q := q) (L := L) = Set.univ := by
  rcases exists_propertyBViolation (K := K) b hA hnotB with
    ⟨i, htrigger, hneighbor⟩
  have hgood : b.IsGood := hA.isGood
  let c : Fin (n + 1) := i.castSucc
  let r : Fin (n + 1) := i.succ
  have hpair : c.val + 1 < n + 1 := by
    dsimp only [c]
    simpa using i.isLt
  have hnext : (⟨c.val + 1, hpair⟩ : Fin (n + 1)) = r := by
    apply Fin.ext
    simp [c, r]
  change
    (b.order i.succ - b.order i.castSucc ≤
        2 * (ramificationIndex K : Int) + 1 ∧
      Odd (b.order i.succ - b.order i.castSucc)) ∨
    (Even (b.order i.succ - b.order i.castSucc) ∧
      b.normalizedAdjacentDefectOrder i ≤
        ((((ramificationIndex K : ℚ) -
          ((b.order i.succ - b.order i.castSucc : Int) : ℚ) / 2) : ℚ) :
            WithTop ℚ)) at htrigger
  rcases htrigger with ⟨hcentralUpper, hcentralOdd⟩ |
      ⟨hcentralEven, hdefectBound⟩
  · rcases hneighbor with ⟨j, hj, hjGap⟩ | ⟨k, hk, hkGap⟩
    · rcases exists_left_neighbor_multiplier (K := K) b c hpair j
          (by simpa [c] using hj) (by simpa [c] using hjGap) with
        ⟨z, hz, hzNotSquare⟩
      apply spinorNormImage_eq_univ_of_odd_adjacent
        (K := K) b hgood c hpair hcentralOdd hcentralUpper z hz hzNotSquare
    · rcases exists_right_neighbor_multiplier (K := K) b c hpair k
          (by simpa [c] using hk) (by simpa [r, hnext] using hkGap) with
        ⟨z, hz, hzNotSquare⟩
      apply spinorNormImage_eq_univ_of_odd_adjacent
        (K := K) b hgood c hpair hcentralOdd hcentralUpper z hz hzNotSquare
  · rcases normalizedDefect_bounds_of_even_trigger
        (K := K) b i hcentralEven hdefectBound with ⟨d, hd, hRd⟩
    have hparameterDefect :
        beliParameterDefect K (b.adjacentParameter c hpair) = (d : ℕ∞) := by
      have h := adjacentParameterDefect_eq_normalizedDefect_of_even
        (K := K) b i hcentralEven
      rw [hd] at h
      simpa only [c] using h
    have hdLt : d < 2 * ramificationIndex K :=
      normalizedDefect_lt_twoE_of_neighborFailure
        (K := K) b hA i d hRd hneighbor
    have hcentralAtMostTwoE :
        b.order r - b.order c ≤ 2 * (ramificationIndex K : Int) := by
      dsimp only [c, r]
      omega
    have hcentralEvenCore :
        Even (b.order ⟨c.val + 1, hpair⟩ - b.order c) := by
      rw [hnext]
      simpa only [c, r] using hcentralEven
    have hRdCore : 2 * (d : Int) ≤
        2 * (ramificationIndex K : Int) -
          (b.order ⟨c.val + 1, hpair⟩ - b.order c) := by
      rw [hnext]
      simpa only [c, r] using hRd
    rcases hneighbor with ⟨j, hj, hjGap⟩ | ⟨k, hk, hkGap⟩
    · rcases Int.even_or_odd (b.order c - b.order j) with
        hjEven | hjOdd
      · have hz := discriminant_is_left_neighbor_multiplier
          (K := K) b c hpair j (by simpa [c] using hj) hjEven
            (by simpa [c] using hjGap)
        apply spinorNormImage_eq_univ_of_even_adjacent
          (K := K) b hgood c hpair
        · exact hcentralEvenCore
        · exact hparameterDefect
        · exact hRdCore
        · exact hdLt
        · exact hz
      · have hjPair : j.val + 1 < n + 1 := by omega
        have hjEnd :
            (⟨j.val + 1, hjPair⟩ : Fin (n + 1)) = c := by
          apply Fin.ext
          simpa [c] using hj
        have hjRightEnd : j.val + 2 = r.val := by
          simp only [r, Fin.val_succ]
          omega
        have hcentralStrict : b.order r - b.order c <
            2 * (ramificationIndex K : Int) + 1 := by omega
        rcases exists_right_neighbor_multiplier (K := K) b j hjPair r
            hjRightEnd (by rwa [hjEnd]) with ⟨z, hz, hzNotSquare⟩
        have hjOddCore :
            Odd (b.order ⟨j.val + 1, hjPair⟩ - b.order j) := by
          rw [hjEnd]
          exact hjOdd
        have hjUpperCore :
            b.order ⟨j.val + 1, hjPair⟩ - b.order j ≤
              2 * (ramificationIndex K : Int) + 1 := by
          rw [hjEnd]
          exact le_of_lt hjGap
        apply spinorNormImage_eq_univ_of_odd_adjacent
          (K := K) b hgood j hjPair hjOddCore hjUpperCore
            z hz hzNotSquare
    · let rpair : Fin (n + 1) := r
      have hkLt := k.isLt
      have hrPair : rpair.val + 1 < n + 1 := by
        change i.val + 2 < n + 1
        omega
      have hrEnd :
          (⟨rpair.val + 1, hrPair⟩ : Fin (n + 1)) = k := by
        apply Fin.ext
        dsimp only [rpair, r]
        simpa using hk
      rcases Int.even_or_odd (b.order k - b.order rpair) with
        hkEven | hkOdd
      · have hkEvenCore : Even
            (b.order k - b.order ⟨c.val + 1, hpair⟩) := by
          rw [hnext]
          simpa only [rpair] using hkEven
        have hkGapCore :
            b.order k - b.order ⟨c.val + 1, hpair⟩ <
              2 * (ramificationIndex K : Int) + 1 := by
          rw [hnext]
          simpa only [rpair] using hkGap
        have hz := discriminant_is_right_neighbor_multiplier
          (K := K) b c hpair k (by simpa [c] using hk)
            hkEvenCore hkGapCore
        apply spinorNormImage_eq_univ_of_even_adjacent
          (K := K) b hgood c hpair
        · exact hcentralEvenCore
        · exact hparameterDefect
        · exact hRdCore
        · exact hdLt
        · exact hz
      · have hleftIndex : c.val + 1 = rpair.val := by
          simp [c, r, rpair]
        have hcentralStrict : b.order rpair - b.order c <
            2 * (ramificationIndex K : Int) + 1 := by
          simpa only [rpair] using (lt_of_le_of_lt hcentralAtMostTwoE
            (lt_add_one _))
        rcases exists_left_neighbor_multiplier (K := K) b rpair hrPair c
            hleftIndex hcentralStrict with ⟨z, hz, hzNotSquare⟩
        have hkOddCore :
            Odd (b.order ⟨rpair.val + 1, hrPair⟩ - b.order rpair) := by
          rw [hrEnd]
          exact hkOdd
        have hkUpperCore :
            b.order ⟨rpair.val + 1, hrPair⟩ - b.order rpair ≤
              2 * (ramificationIndex K : Int) + 1 := by
          rw [hrEnd]
          simpa only [rpair, r] using le_of_lt hkGap
        apply spinorNormImage_eq_univ_of_odd_adjacent
          (K := K) b hgood rpair hrPair hkOddCore hkUpperCore
            z hz hzNotSquare

end BONG

/-- The law interface for Beli (2003), Lemma 4.11 is discharged by the
explicit odd/even neighboring-pair proof above. -/
noncomputable instance beliLemma411LawsProved :
    BeliLemma411Laws.{u, v} K where
  full_spinorNormImage_of_propertyA_not_propertyB := by
    intro V _instAdd _instModule q L n b hA hnotB
    letI : BinaryNormGeneratorLocalLaws.{u, v} K :=
      binaryNormGeneratorLocalLawsProved
    letI : BONGReverseDualLaws.{u, v} K :=
      bongReverseDualLawsOfBeli
    letI : BeliLemma49Laws.{u, v} K :=
      BONG.beliLemma49LawsOfReverseDual
    exact b.spinorNormImage_eq_univ_of_propertyA_not_propertyB hA hnotB

end Bong
