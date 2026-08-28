/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Corollary713
import Bong.Bong.Beli2019Lemma717Boundary
import Bong.Bong.Beli2019Lemma718TowerReplacement
import Bong.Bong.BeliCorollary44ThreeBlockProof

/-!
# Beli (2019), Lemma 7.18(iii): realization of the type-III normal form

The canonical prefix is first split from its nonempty suffix and replaced,
block by block, by the literal index-uniformizer sublattice.  Corollary 7.13
then supplies the alternate good BONG on that same product lattice, and the
product is mapped back to the original ambient quadratic space.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- The complete constructive output of Lemma 7.18(iii). -/
structure Lemma718TypeIIIRealization
    (a : GoodBONG q L (n + 3)) (R : Int) (s : Nat) where
  target : Lattice K V
  lattice_le : target ≤ L
  bong : GoodBONG q target (n + 3)
  normalForm : Lemma718TypeIIINormalForm a bong R s

/-- Even entries of a canonical source prefix are the canonical high
coefficient. -/
theorem lemma718CanonicalSource_even
    (a : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (hsRank : s ≤ n + 3) (hsEven : Even s)
    (sourcePair : ∀ (j : Nat) (hj : 2 * j + 1 < s),
      a.valueUnit ⟨2 * j, by omega⟩ =
          lemma718CanonicalHigh (K := K) R ∧
        a.valueUnit ⟨2 * j + 1, by omega⟩ =
          lemma718CanonicalLow (K := K) R)
    (i : Fin (n + 3)) (his : i.val < s) (hiEven : Even i.val) :
    a.valueUnit i = lemma718CanonicalHigh (K := K) R := by
  rcases hsEven with ⟨t, ht⟩
  rcases hiEven with ⟨j, hj⟩
  have hp := (sourcePair j (by omega)).1
  have hindex : i = (⟨2 * j, by omega⟩ : Fin (n + 3)) := by
    apply Fin.ext
    simpa [two_mul] using hj
  rw [hindex]
  exact hp

/-- Odd entries of a canonical source prefix are the canonical low
coefficient. -/
theorem lemma718CanonicalSource_odd
    (a : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (hsRank : s ≤ n + 3)
    (sourcePair : ∀ (j : Nat) (hj : 2 * j + 1 < s),
      a.valueUnit ⟨2 * j, by omega⟩ =
          lemma718CanonicalHigh (K := K) R ∧
        a.valueUnit ⟨2 * j + 1, by omega⟩ =
          lemma718CanonicalLow (K := K) R)
    (i : Fin (n + 3)) (his : i.val < s) (hiOdd : Odd i.val) :
    a.valueUnit i = lemma718CanonicalLow (K := K) R := by
  rcases hiOdd with ⟨j, hj⟩
  have hp := (sourcePair j (by omega)).2
  have hindex : i = (⟨2 * j + 1, by omega⟩ : Fin (n + 3)) := by
    apply Fin.ext
    omega
  rw [hindex]
  exact hp

/-- Construct the type-III replacement lattice and its exact normal form. -/
theorem exists_lemma718TypeIIIRealization
    [corollary44V : BeliCorollary44Laws.{u, v} K]
    [defect : QuadraticDefectLaws K]
    [hilbert : HilbertSymbolLaws K]
    [diagonal : DyadicDiagonalClassificationLaws K]
    [perfect : PerfectResidueFieldLaws K]
    [structural : BONGStructuralLaws.{u, u} K]
    [weight : Beli2009WeightIdealData.{u, u} K]
    [unaryBinary : Beli2019UnaryBinaryJordanLaws.{u} K]
    [jordanOrder : Beli2009JordanWeightOrderLaws.{u, u} K]
    [alphaBase : Beli2006AlphaLaws.{u, u} K]
    [constructionBase : BeliLemma43ConstructionLaws.{u, u} K]
    [sectionTwoBase : Beli2006SectionTwoLaws.{u, u} K]
    [classification : GoodBONGClassificationLaws.{u, u, u} K]
    [sectionFourV : BONGReverseDualLaws.{u, v} K]
    [constructionV : BeliLemma43ConstructionLaws.{u, v} K]
    [sectionTwoV : Beli2006SectionTwoLaws.{u, v} K]
    (a : GoodBONG q L (n + 3)) (R : Int) (s : Nat)
    (stopping : Lemma717StoppingData a R s)
    (typeIII : Lemma717IsTypeIII a R s)
    (sourcePair : ∀ (j : Nat) (hj : 2 * j + 1 < s),
      a.valueUnit ⟨2 * j, by
        have hs := stopping.le_rank
        omega⟩ = lemma718CanonicalHigh (K := K) R ∧
      a.valueUnit ⟨2 * j + 1, by
        have hs := stopping.le_rank
        omega⟩ = lemma718CanonicalLow (K := K) R) :
    Nonempty (Lemma718TypeIIIRealization a R s) := by
  classical
  rcases typeIII with ⟨hsHead, hhead⟩
  have hsRank := stopping.le_rank
  have hsTwo := stopping.two_le
  have hcutOrder : a.order ⟨s - 1, by omega⟩ ≤
      a.order ⟨s, hsHead⟩ := by
    rw [stopping.terminal, hhead]
    have hepos := ramificationIndex_pos (K := K)
    omega
  let boundary : Fin (n + 3) := ⟨s - 1, by omega⟩
  have hnext : boundary.val + 1 < n + 3 := by
    simp only [boundary]
    omega
  have hsplit : a.toBONG.HasTwoBlockSplit s hsRank := by
    have hboundaryOrder : a.toBONG.order boundary ≤
        a.toBONG.order ⟨boundary.val + 1, hnext⟩ := by
      calc
        a.toBONG.order boundary =
            a.toBONG.order ⟨s - 1, by omega⟩ := rfl
        _ ≤ a.toBONG.order ⟨s, hsHead⟩ := hcutOrder
        _ = a.toBONG.order ⟨boundary.val + 1, hnext⟩ := by
          congr 1
          apply Fin.ext
          simp only [boundary, Fin.val_mk]
          omega
    have h := a.toBONG.beliCorollary44_i_unconditional a.good boundary hnext
      hboundaryOrder
    have hcutEq : boundary.val + 1 = s := by
      simp only [boundary]
      omega
    simpa only [hcutEq] using h
  let S : TwoBlockSplitWitness a.toBONG s hsRank := Classical.choice hsplit
  let left := S.left.toGoodBONG a.good
  have hleftValue (i : Fin s) : left.valueUnit i =
      a.valueUnit ⟨i.val, by omega⟩ := by
    change S.left.bong.valueUnit i = _
    rw [S.left.valueUnit_eq]
    congr 1
    apply Fin.ext
    rw [S.left.sourceIndex_val]
    simp
  have Dleft : Lemma718CanonicalPrefixData left R s := by
    refine {
      even := stopping.even
      two_le := stopping.two_le
      le_rank := le_rfl
      sourcePair := ?_
      suffixHead := ?_
      suffixSecond := ?_ }
    · intro j hj
      constructor
      · rw [hleftValue]
        have h := (sourcePair j hj).1
        simpa only using h
      · rw [hleftValue]
        have h := (sourcePair j hj).2
        simpa only using h
    · intro hs
      omega
    · intro hs
      omega
  rcases left.exists_lemma718CanonicalPrefixReplacement R s Dleft with ⟨E⟩
  have hprefix (i : Fin s) : E.bong.valueUnit i =
      if Even i.val then lemma718IndexPHigh (K := K) R
      else lemma718IndexPLow (K := K) R := by
    rw [E.valueUnit, if_pos i.isLt]
    rcases Nat.even_or_odd i.val with hiEven | hiOdd
    · rw [if_pos hiEven, hleftValue]
      have hiBound : i.val < n + 3 := lt_of_lt_of_le i.isLt hsRank
      let sourceIndex : Fin (n + 3) := ⟨i.val, hiBound⟩
      have hsource := lemma718CanonicalSource_even a R s hsRank
        stopping.even sourcePair sourceIndex i.isLt hiEven
      have hsource' : a.valueUnit ⟨i.val, by omega⟩ =
          lemma718CanonicalHigh (K := K) R := by
        simpa only [sourceIndex] using hsource
      rw [hsource']
      exact (lemma718IndexPHigh_eq_uniformizer_mul R).symm
    · rw [if_neg (Nat.not_even_iff_odd.mpr hiOdd), hleftValue]
      have hiBound : i.val < n + 3 := lt_of_lt_of_le i.isLt hsRank
      let sourceIndex : Fin (n + 3) := ⟨i.val, hiBound⟩
      have hsource := lemma718CanonicalSource_odd a R s hsRank
        sourcePair sourceIndex i.isLt hiOdd
      have hsource' : a.valueUnit ⟨i.val, by omega⟩ =
          lemma718CanonicalLow (K := K) R := by
        simpa only [sourceIndex] using hsource
      rw [hsource']
      exact (lemma718IndexPLow_eq_uniformizer_mul R).symm
  let m := (n + 3) - s - 1
  have hrightLength : (n + 3) - s = m + 1 := by
    dsimp [m]
    omega
  let rightRaw := S.right.toGoodBONG a.good
  let right := rightRaw.castLength hrightLength
  have hrightValue (i : Fin (m + 1)) : right.valueUnit i =
      a.valueUnit ⟨s + i.val, by omega⟩ := by
    let iraw : Fin ((n + 3) - s) :=
      ⟨i.val, by rw [hrightLength]; exact i.isLt⟩
    calc
      right.valueUnit i = rightRaw.valueUnit iraw := by
        simpa only [right, iraw] using
          lemma718_valueUnit_castLength rightRaw hrightLength i
      _ = a.valueUnit (S.right.sourceIndex iraw) :=
        lemma718_segmentGood_valueUnit S.right iraw
      _ = a.valueUnit ⟨s + i.val, by omega⟩ := by
        congr 1
  have hrightOrder (i : Fin (m + 1)) : right.order i =
      a.order ⟨s + i.val, by omega⟩ := by
    let iraw : Fin ((n + 3) - s) :=
      ⟨i.val, by rw [hrightLength]; exact i.isLt⟩
    calc
      right.order i = rightRaw.order iraw := by
        simpa only [right, iraw] using
          GoodBONG.order_castLength rightRaw hrightLength i
      _ = a.order (S.right.sourceIndex iraw) :=
        lemma718_segmentGood_order S.right iraw
      _ = a.order ⟨s + i.val, by omega⟩ := by
        congr 1
  have hrightHead : right.order (0 : Fin (m + 1)) = R := by
    rw [hrightOrder]
    have hindex : (⟨s + (0 : Fin (m + 1)).val, by omega⟩ :
        Fin (n + 3)) = ⟨s, hsHead⟩ := by
      apply Fin.ext
      simp
    rw [hindex, hhead]
  have hrightSecond : ∀ hm : 0 < m,
      R - 2 * (ramificationIndex K : Int) + 2 ≤
        right.order ⟨1, by omega⟩ := by
    intro hm
    rw [hrightOrder]
    have hsSecond : s + 1 < n + 3 := by
      dsimp [m] at hm
      omega
    have h := lemma717_typeIII_suffixSecond_ge a R s stopping
      ⟨hsHead, hhead⟩ hsSecond
    have hindex : (⟨s + (⟨1, by omega⟩ : Fin (m + 1)).val,
        by omega⟩ : Fin (n + 3)) = ⟨s + 1, hsSecond⟩ := by
      apply Fin.ext
      rfl
    rw [hindex]
    exact h
  rcases (@exists_corollary713Realization.{u, v, v}
      K _ _ _ _ _
      S.left.carrier _ _ S.right.carrier _ _
      (q.restrict S.left.carrier S.left.nondegenerate)
      (q.restrict S.right.carrier S.right.nondegenerate)
      E.target S.right.lattice s m
      defect hilbert diagonal perfect structural weight unaryBinary jordanOrder
      alphaBase constructionBase sectionTwoBase classification
      corollary44V corollary44V
      sectionFourV sectionFourV sectionFourV constructionV sectionTwoV
      E.bong right R stopping.even stopping.two_le hprefix
      hrightHead hrightSecond) with ⟨C⟩
  let N := Lattice.map S.toProductLatticeIsometry.toLinearEquiv
    (Lattice.product E.target S.right.lattice)
  let g : Lattice.Isometry
      ((q.restrict S.left.carrier S.left.nondegenerate).orthogonalSum
        (q.restrict S.right.carrier S.right.nondegenerate)) q
      (Lattice.product E.target S.right.lattice) N := by
    simpa only [N, Lattice.Isometry.toQuadraticSpaceIsometry] using
      Lattice.Isometry.toMap _
        S.toProductLatticeIsometry.toQuadraticSpaceIsometry _
  let raw := C.bong.mapLatticeIsometry g
  have htotal : (m + 1) + s = n + 3 := by
    dsimp [m]
    omega
  let b := raw.castLength htotal
  have hle : N ≤ L := by
    intro y hy
    have hzTarget := (Lattice.mem_map_iff
      S.toProductLatticeIsometry.toLinearEquiv
      (Lattice.product E.target S.right.lattice) y).1 hy
    have hzProduct :
        S.toProductLatticeIsometry.toLinearEquiv.symm y ∈
          Lattice.product S.left.lattice S.right.lattice :=
      Lattice.mem_product_iff.mpr
        ⟨E.lattice_le (Lattice.mem_product_iff.mp hzTarget).1,
          (Lattice.mem_product_iff.mp hzTarget).2⟩
    have hmapped := (S.toProductLatticeIsometry.map_mem _).1 hzProduct
    simpa using hmapped
  have hbRaw (i : Fin (n + 3)) : b.valueUnit i =
      raw.valueUnit ⟨i.val, by rw [htotal]; exact i.isLt⟩ := by
    simpa only [b] using lemma718_valueUnit_castLength raw htotal i
  have hrawC (i : Fin ((m + 1) + s)) : raw.valueUnit i =
      C.bong.valueUnit i := by
    simpa only [raw, GoodBONG.valueUnit_mapLatticeIsometry]
  exact ⟨{
    target := N
    lattice_le := hle
    bong := b
    normalForm := {
      stopping := stopping
      typeIII := ⟨hsHead, hhead⟩
      sourcePair := sourcePair
      targetValues := by
        intro i
        rw [hbRaw, hrawC]
        by_cases his : i.val < s
        · let k : Fin s := ⟨i.val, his⟩
          have hindex : (⟨i.val, by rw [htotal]; exact i.isLt⟩ :
              Fin ((m + 1) + s)) =
              orthogonalProductLeftIndex (m + 1) k := by
            apply Fin.ext
            rfl
          rw [hindex, C.valueUnit_left]
          rcases Nat.even_or_odd i.val with hiEven | hiOdd
          · rw [corollary713PrefixValues, if_pos hiEven,
              lemma718TypeIIITargetValues_even a s i hiEven]
            exact (lemma718CanonicalSource_even a R s hsRank
              stopping.even sourcePair i his hiEven).symm
          · rw [corollary713PrefixValues,
              if_neg (Nat.not_even_iff_odd.mpr hiOdd),
              lemma718TypeIIITargetValues_changed a s i his hiOdd,
              lemma718CanonicalSource_odd a R s hsRank
                sourcePair i his hiOdd]
        · have hsi : s ≤ i.val := by omega
          let k : Fin (m + 1) := ⟨i.val - s, by
            dsimp [m]
            omega⟩
          have hindex : (⟨i.val, by rw [htotal]; exact i.isLt⟩ :
              Fin ((m + 1) + s)) =
              orthogonalProductRightIndex s k := by
            apply Fin.ext
            simp [k, orthogonalProductRightIndex]
            omega
          rw [hindex, C.valueUnit_right, hrightValue,
            lemma718TypeIIITargetValues_suffix a s i hsi]
          congr 1
          apply Fin.ext
          simp [k]
          omega } }⟩

end BONG.GoodBONG

end Bong
