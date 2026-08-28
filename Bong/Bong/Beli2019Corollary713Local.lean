/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma712ILocal
import Bong.Bong.Beli2019Lemma718HyperbolicBlock
import Bong.Bong.Beli2019Lemma718OrderProfiles
import Bong.Bong.BeliCorollary44ThreeBlockProof
import Bong.Bong.TwoBlockProductIsometry
import Bong.Lattice.OrthogonalProductIsometry

namespace Bong

open Dyadic

universe u v w

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {J : Lattice K V} {A : Lattice K W} {s : Nat}

noncomputable def castTwoBlockSplitCut
    {X : Type v} [AddCommGroup X] [Module K X]
    {f : QuadraticSpace K X} {M : Lattice K X} {n cut cut' : Nat}
    {b : BONG X f M n} {hcut : cut ≤ n} {hcut' : cut' ≤ n}
    (S : BONG.TwoBlockSplitWitness b cut hcut) (h : cut = cut') :
    BONG.TwoBlockSplitWitness b cut' hcut' := by
  subst cut'
  exact S

/-- The coefficient family produced on the transformed even prefix. -/
noncomputable def corollary713PrefixValues (R : Int) (i : Fin s) : Kˣ :=
  if Even i.val then lemma718CanonicalHigh (K := K) R
  else uniformizerUnit K ^ 2 * lemma718CanonicalLow (K := K) R

noncomputable def corollary713Low (R : Int) : Kˣ :=
  uniformizerUnit K ^ 2 * lemma718CanonicalLow (K := K) R

@[simp] theorem corollary713PrefixValues_eq_low
    (R : Int) (i : Fin s) (hi : ¬ Even i.val) :
    corollary713PrefixValues (K := K) R i = corollary713Low (K := K) R := by
  simp [corollary713PrefixValues, corollary713Low, hi]

@[simp] theorem corollary713PrefixValues_eq_high
    (R : Int) (i : Fin s) (hi : Even i.val) :
    corollary713PrefixValues (K := K) R i =
      lemma718CanonicalHigh (K := K) R := by
  simp [corollary713PrefixValues, hi]

theorem ordUnit_corollary713Low (R : Int) :
    ordUnit K (corollary713Low (K := K) R) =
      R - 2 * (ramificationIndex K : Int) + 2 := by
  unfold corollary713Low
  have hpi : ordUnit K (uniformizerUnit K) = 1 := by
    simpa [uniformizerPowerUnit] using
      (ordUnit_uniformizerPowerUnit (K := K) (1 : Int))
  rw [ordUnit_mul, ordUnit_pow, hpi, ordUnit_lemma718CanonicalLow]
  omega

theorem lemma712I_second_eq_corollary713Low (R : Int) :
    -(uniformizerPowerUnit K
        (2 - 2 * (ramificationIndex K : Int)) *
      lemma718CanonicalHigh (K := K) R) =
      corollary713Low (K := K) R := by
  unfold lemma718CanonicalHigh corollary713Low lemma718CanonicalLow
  rw [mul_neg]
  congr 1
  unfold uniformizerPowerUnit
  rw [show uniformizerUnit K ^ (2 - 2 * (ramificationIndex K : Int)) *
      uniformizerUnit K ^ R =
      uniformizerUnit K ^
        ((2 - 2 * (ramificationIndex K : Int)) + R) by
    rw [← zpow_add]]
  rw [show uniformizerUnit K ^ 2 *
      uniformizerUnit K ^ (R - 2 * (ramificationIndex K : Int)) =
      uniformizerUnit K ^
        ((2 : Int) + (R - 2 * (ramificationIndex K : Int))) by
    change uniformizerUnit K ^ (2 : Int) * _ = _
    rw [← zpow_add]]
  congr 1
  omega

structure Corollary713LocalRealization
    (j : GoodBONG q J s) (x : GoodBONG r A 1) (R : Int) where
  bong : GoodBONG (q.orthogonalSum r) (Lattice.product J A) (s + 1)
  valueUnit_prefix (i : Fin s) :
    bong.valueUnit ⟨i.val, by omega⟩ =
      corollary713PrefixValues (K := K) R i
  valueUnit_last :
    bong.valueUnit ⟨s, by omega⟩ = x.valueUnit 0

theorem valueUnit_castLength_local
    {X : Type v} [AddCommGroup X] [Module K X]
    {f : QuadraticSpace K X} {M : Lattice K X} {m n : Nat}
    (b : GoodBONG f M m) (h : m = n) (i : Fin n) :
    (b.castLength h).valueUnit i = b.valueUnit ⟨i.val, by omega⟩ := by
  subst n
  rfl

theorem binaryUnitSquareClass_eq_negativeQuarter_of_indexPValues
    (j : GoodBONG q J 2) (R : Int)
    (hzero : j.valueUnit 0 = lemma718IndexPHigh (K := K) R)
    (hone : j.valueUnit 1 = lemma718IndexPLow (K := K) R) :
    j.toBONG.binaryUnitSquareClass =
      unitSquareClass K (negativeQuarterUnit K) := by
  change unitSquareClass K (j.valueUnit 1 / j.valueUnit 0) = _
  rw [hzero, hone]
  rw [lemma718IndexPParameter_eq]
  apply unitSquareClass_uniformizerPower_mul_eq_negativeQuarter
  · change ord K ((-1 : Kˣ) : K) = 0
    simp
  · rfl
  · exact ⟨1, by simp⟩

theorem exists_corollary713LocalRealization
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicDiagonalClassificationLaws K]
    [PerfectResidueFieldLaws K]
    [BONGStructuralLaws.{u, u} K]
    [Beli2009WeightIdealData.{u, u} K]
    [Beli2019UnaryBinaryJordanLaws.{u} K]
    [Beli2009JordanWeightOrderLaws.{u, u} K]
    [Beli2006AlphaLaws.{u, u} K]
    [BeliLemma43ConstructionLaws.{u, u} K]
    [Beli2006SectionTwoLaws.{u, u} K]
    [GoodBONGClassificationLaws.{u, u, u} K]
    [lawsV : BeliCorollary44Laws.{u, v} K]
    [lawsProduct : BeliCorollary44Laws.{u, max v w} K]
    (j : GoodBONG q J s) (x : GoodBONG r A 1) (R : Int)
    (hsEven : Even s) (hsTwo : 2 ≤ s)
    (hprefix : ∀ i : Fin s,
      j.valueUnit i = if Even i.val then
        lemma718IndexPHigh (K := K) R
      else lemma718IndexPLow (K := K) R)
    (hhead : x.order 0 = R) :
    Nonempty (Corollary713LocalRealization j x R) := by
  induction s using Nat.strong_induction_on generalizing V W q r J A with
  | h s ih =>
      by_cases hsEq : s = 2
      · subst s
        have hjZero : j.valueUnit 0 = lemma718IndexPHigh (K := K) R := by
          simpa using hprefix 0
        have hjOne : j.valueUnit 1 = lemma718IndexPLow (K := K) R := by
          simpa using hprefix 1
        have hp : j.order 0 = x.order 0 + 1 := by
          rw [GoodBONG.order, j.toBONG.order_eq_ordUnit]
          change ordUnit K (j.valueUnit 0) = x.order 0 + 1
          rw [hjZero, hhead]
          unfold lemma718IndexPHigh
          rw [ordUnit_uniformizerPowerUnit]
        have hclass :=
          binaryUnitSquareClass_eq_negativeQuarter_of_indexPValues
            j R hjZero hjOne
        let ε : Kˣ := lemma718CanonicalHigh (K := K) R / x.valueUnit 0
        have hεOrder : ordUnit K ε = 0 := by
          dsimp only [ε]
          rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv,
            ordUnit_lemma718CanonicalHigh]
          change R - x.order 0 = 0
          rw [hhead]
          omega
        have hεUnit : IsValuationUnit K (ε : K) :=
          (isValuationUnit_iff_ordUnit_eq_zero K ε).2 hεOrder
        rcases j.exists_lemma712I_localGoodBONG x hp hclass ε hεUnit with
          ⟨b, hb⟩
        refine ⟨⟨b.castLength (by omega), ?_, ?_⟩⟩
        · intro i
          have hi : i.val = 0 ∨ i.val = 1 := by omega
          rcases hi with hi | hi
          · have hieq : i = 0 := Fin.ext hi
            subst i
            change b.valueUnit 0 = _
            rw [hb 0, lemma712ITargetValues_zero]
            dsimp only [ε]
            simp
          · have hieq : i = 1 := Fin.ext hi
            subst i
            change b.valueUnit 1 = _
            rw [hb 1, lemma712ITargetValues_one]
            have haeps : x.valueUnit 0 * ε =
                lemma718CanonicalHigh (K := K) R := by
              dsimp only [ε]
              simp
            rw [mul_assoc, haeps,
              lemma712I_second_eq_corollary713Low]
            simp [corollary713PrefixValues, corollary713Low]
        · change b.valueUnit 2 = x.valueUnit 0
          simpa using hb 2
      · have hsFour : 4 ≤ s := by
          rcases hsEven with ⟨k, hk⟩
          omega
        let one : Fin s := ⟨1, by omega⟩
        have honeOrder : j.order one =
            R - 2 * (ramificationIndex K : Int) + 1 := by
          rw [GoodBONG.order, j.toBONG.order_eq_ordUnit]
          change ordUnit K (j.valueUnit one) = _
          rw [hprefix one]
          rw [if_neg (by norm_num : ¬ Even (1 : Nat))]
          unfold lemma718IndexPLow
          rw [ordUnit_neg, ordUnit_uniformizerPowerUnit]
        let two : Fin s := ⟨2, by omega⟩
        have htwoOrder : j.order two = R + 1 := by
          rw [GoodBONG.order, j.toBONG.order_eq_ordUnit]
          change ordUnit K (j.valueUnit two) = _
          rw [hprefix two]
          rw [if_pos (by norm_num : Even (2 : Nat))]
          unfold lemma718IndexPHigh
          rw [ordUnit_uniformizerPowerUnit]
        have h12 : j.order one ≤ j.order two := by
          rw [honeOrder, htwoOrder]
          have he := ramificationIndex_pos (K := K)
          omega
        have hsplitRaw := j.toBONG.beliCorollary44_i_unconditional
          j.good one (by simp [one]; omega) h12
        have hsplit : j.toBONG.HasTwoBlockSplit 2 (by omega) := by
          simpa [one] using hsplitRaw
        rcases hsplit with ⟨S⟩
        let left := S.left.toGoodBONG j.good
        let right := S.right.toGoodBONG j.good
        have hrightEven : Even (s - 2) := by
          rcases hsEven with ⟨k, hk⟩
          refine ⟨k - 1, ?_⟩
          omega
        have hrightTwo : 2 ≤ s - 2 := by omega
        have hrightPrefix : ∀ i : Fin (s - 2),
            right.valueUnit i = if Even i.val then
              lemma718IndexPHigh (K := K) R
            else lemma718IndexPLow (K := K) R := by
          intro i
          change S.right.bong.valueUnit i = _
          rw [S.right.valueUnit_eq]
          change j.valueUnit (S.right.sourceIndex i) = _
          rw [hprefix]
          simp only [SegmentWitness.sourceIndex_val]
          have hparity : Even (2 + i.val) ↔ Even i.val := by
            simp [Nat.even_add]
          by_cases hi : Even i.val
          · rw [if_pos hi, if_pos (hparity.2 hi)]
          · have hnot : ¬ Even (2 + i.val) := fun htwo ↦
              hi (hparity.1 htwo)
            rw [if_neg hi, if_neg hnot]
        have hsSubLt : s - 2 < s := Nat.sub_lt (by omega) (by omega)
        rcases ih (s - 2) hsSubLt right x hrightEven hrightTwo
            hrightPrefix hhead with ⟨E⟩
        have hcut : s - 2 ≤ s - 2 + 1 := Nat.le_succ _
        have hprefixLastBound : s - 3 < s - 2 :=
          Nat.sub_lt_sub_left (m := s) (n := 3) (k := 2)
            (lt_of_lt_of_le (by norm_num : 2 < 4) hsFour)
            (by norm_num)
        have hcutLastBound : s - 3 < s - 2 + 1 :=
          hprefixLastBound.trans (Nat.lt_succ_self _)
        let cutLast : Fin (s - 2 + 1) := ⟨s - 3, hcutLastBound⟩
        have hcutLastVal : cutLast.val = s - 3 := rfl
        have hcutEq : cutLast.val + 1 = s - 2 := by
          rw [hcutLastVal]
          have hsThree : 3 ≤ s := by omega
          have hsTwo' : 2 ≤ s := hsTwo
          have hsSubThree := Nat.sub_add_cancel hsThree
          have hsSubTwo := Nat.sub_add_cancel hsTwo'
          apply Nat.add_right_cancel (m := 2)
          calc
            (s - 3 + 1) + 2 = s - 3 + 3 := by omega
            _ = s := hsSubThree
            _ = s - 2 + 2 := hsSubTwo.symm
        have hcutLastOrder : E.bong.order cutLast =
            R - 2 * (ramificationIndex K : Int) + 2 := by
          rw [GoodBONG.order, E.bong.toBONG.order_eq_ordUnit]
          change ordUnit K (E.bong.valueUnit cutLast) = _
          let prefixIndex : Fin (s - 2) := ⟨s - 3, hprefixLastBound⟩
          have hprefixOuter : prefixIndex.val < s - 2 + 1 := by
            exact hcutLastBound
          have hindex : cutLast =
              (⟨prefixIndex.val, hprefixOuter⟩ : Fin (s - 2 + 1)) :=
            Fin.ext rfl
          rw [hindex, E.valueUnit_prefix prefixIndex]
          have hodd : ¬ Even (s - 3) := by
            apply Nat.not_even_iff_odd.mpr
            exact Nat.Even.sub_odd (by omega) hsEven
              (⟨1, by norm_num⟩ : Odd (3 : Nat))
          rw [corollary713PrefixValues_eq_low R _ hodd,
            ordUnit_corollary713Low]
        have hELastOrder : E.bong.order ⟨s - 2, by omega⟩ = R := by
          rw [GoodBONG.order, E.bong.toBONG.order_eq_ordUnit]
          change ordUnit K (E.bong.valueUnit ⟨s - 2, by omega⟩) = R
          rw [E.valueUnit_last]
          change x.order 0 = R
          exact hhead
        have hnextBound : cutLast.val + 1 < s - 2 + 1 := by
          rw [hcutEq]
          exact Nat.lt_succ_self _
        have hsplitOrder : E.bong.order cutLast ≤
            E.bong.order ⟨cutLast.val + 1, hnextBound⟩ := by
          have hnext : (⟨cutLast.val + 1, hnextBound⟩ : Fin (s - 2 + 1)) =
              ⟨s - 2, by omega⟩ := by
            apply Fin.ext
            exact hcutEq
          have hnextOrder : E.bong.order
              ⟨cutLast.val + 1, hnextBound⟩ = R := by
            rw [hnext, hELastOrder]
          calc
            E.bong.order cutLast =
                R - 2 * (ramificationIndex K : Int) + 2 := hcutLastOrder
            _ ≤ R := by
              have he : (1 : Int) ≤ (ramificationIndex K : Int) := by
                exact_mod_cast ramificationIndex_pos (K := K)
              omega
            _ = E.bong.order ⟨cutLast.val + 1, hnextBound⟩ :=
              hnextOrder.symm
        have hsplitERaw := E.bong.toBONG.beliCorollary44_i_unconditional
          E.bong.good cutLast hnextBound hsplitOrder
        have hcutBound : s - 2 ≤ s - 2 + 1 := Nat.le_succ _
        rcases hsplitERaw with ⟨Uraw⟩
        let U : E.bong.toBONG.TwoBlockSplitWitness (s - 2) hcutBound :=
          castTwoBlockSplitCut Uraw hcutEq
        let canonical := U.left.toGoodBONG E.bong.good
        let lineRaw := U.right.toGoodBONG E.bong.good
        have hlineLength : (s - 2 + 1) - (s - 2) = 1 :=
          Nat.add_sub_cancel_left (s - 2) 1
        let line := lineRaw.castLength hlineLength
        have hlineValue : line.valueUnit 0 = x.valueUnit 0 := by
          rw [show line = lineRaw.castLength hlineLength by rfl,
            valueUnit_castLength_local]
          let zeroRaw : Fin ((s - 2 + 1) - (s - 2)) :=
            ⟨0, by rw [hlineLength]; norm_num⟩
          change U.right.bong.valueUnit zeroRaw = _
          rw [U.right.valueUnit_eq]
          have hidx : U.right.sourceIndex zeroRaw =
              ⟨s - 2, by omega⟩ := by
            apply Fin.ext
            change (s - 2) + 0 = s - 2
            simp
          rw [hidx]
          change E.bong.valueUnit ⟨s - 2, by omega⟩ = x.valueUnit 0
          rw [E.valueUnit_last]
        have hlineOrder : line.order 0 = R := by
          rw [GoodBONG.order, line.toBONG.order_eq_ordUnit]
          change ordUnit K (line.valueUnit 0) = R
          rw [hlineValue]
          change x.order 0 = R
          exact hhead
        have hleftZero : left.valueUnit 0 =
            lemma718IndexPHigh (K := K) R := by
          change S.left.bong.valueUnit 0 = _
          rw [S.left.valueUnit_eq]
          change j.valueUnit (S.left.sourceIndex 0) = _
          have hsPos : 0 < s := lt_of_lt_of_le (by norm_num : 0 < 2) hsTwo
          have hidx : S.left.sourceIndex (0 : Fin 2) =
              (⟨0, hsPos⟩ : Fin s) :=
            Fin.ext rfl
          rw [hidx, hprefix]
          simp
        have hleftOne : left.valueUnit 1 =
            lemma718IndexPLow (K := K) R := by
          change S.left.bong.valueUnit 1 = _
          rw [S.left.valueUnit_eq]
          change j.valueUnit (S.left.sourceIndex 1) = _
          have hsOne : 1 < s := lt_of_lt_of_le (by norm_num : 1 < 2) hsTwo
          have hidx : S.left.sourceIndex (1 : Fin 2) =
              (⟨1, hsOne⟩ : Fin s) :=
            Fin.ext rfl
          rw [hidx, hprefix]
          simp
        have hp : left.order 0 = line.order 0 + 1 := by
          rw [GoodBONG.order, left.toBONG.order_eq_ordUnit]
          change ordUnit K (left.valueUnit 0) = line.order 0 + 1
          rw [hleftZero, hlineOrder]
          unfold lemma718IndexPHigh
          rw [ordUnit_uniformizerPowerUnit]
        have hclass :=
          binaryUnitSquareClass_eq_negativeQuarter_of_indexPValues
            left R hleftZero hleftOne
        let ε : Kˣ := lemma718CanonicalHigh (K := K) R / line.valueUnit 0
        have hεOrder : ordUnit K ε = 0 := by
          dsimp only [ε]
          rw [div_eq_mul_inv, ordUnit_mul, ordUnit_inv,
            ordUnit_lemma718CanonicalHigh]
          change R - line.order 0 = 0
          rw [hlineOrder]
          exact sub_self R
        have hεUnit : IsValuationUnit K (ε : K) :=
          (isValuationUnit_iff_ordUnit_eq_zero K ε).2 hεOrder
        rcases left.exists_lemma712I_localGoodBONG line hp hclass ε hεUnit with
          ⟨localBlock, hlocal⟩
        have hcanonicalPrefix : ∀ i : Fin (s - 2),
            canonical.valueUnit i =
              corollary713PrefixValues (K := K) R i := by
          intro i
          change U.left.bong.valueUnit i = _
          rw [U.left.valueUnit_eq]
          have hidx : U.left.sourceIndex i = ⟨i.val, by omega⟩ := by
            apply Fin.ext
            simp [SegmentWitness.sourceIndex]
          rw [hidx]
          exact E.valueUnit_prefix i
        have hcanonicalPenultimate : canonical.order ⟨s - 4, by omega⟩ = R := by
          rw [GoodBONG.order, canonical.toBONG.order_eq_ordUnit]
          change ordUnit K (canonical.valueUnit ⟨s - 4, by omega⟩) = R
          rw [hcanonicalPrefix]
          have heven : Even (s - 4) := by
            exact (Nat.even_sub hsFour).2
              ⟨fun _ ↦ (⟨2, by norm_num⟩ : Even (4 : Nat)), fun _ ↦ hsEven⟩
          rw [corollary713PrefixValues_eq_high R _ heven,
            ordUnit_lemma718CanonicalHigh]
        have hcanonicalLast : canonical.order ⟨s - 3, by omega⟩ =
            R - 2 * (ramificationIndex K : Int) + 2 := by
          rw [GoodBONG.order, canonical.toBONG.order_eq_ordUnit]
          change ordUnit K (canonical.valueUnit ⟨s - 3, by omega⟩) = _
          rw [hcanonicalPrefix]
          have hodd : ¬ Even (s - 3) := by
            apply Nat.not_even_iff_odd.mpr
            exact Nat.Even.sub_odd (by omega) hsEven
              (⟨1, by norm_num⟩ : Odd (3 : Nat))
          rw [corollary713PrefixValues_eq_low R _ hodd,
            ordUnit_corollary713Low]
        have hlocalZero : localBlock.order 0 = R := by
          rw [GoodBONG.order, localBlock.toBONG.order_eq_ordUnit]
          change ordUnit K (localBlock.valueUnit 0) = R
          rw [hlocal 0, lemma712ITargetValues_zero]
          dsimp only [ε]
          simp
        have hlocalOne : localBlock.order 1 =
            R - 2 * (ramificationIndex K : Int) + 2 := by
          rw [GoodBONG.order, localBlock.toBONG.order_eq_ordUnit]
          change ordUnit K (localBlock.valueUnit 1) = _
          rw [hlocal 1, lemma712ITargetValues_one]
          have haeps : line.valueUnit 0 * ε =
              lemma718CanonicalHigh (K := K) R := by
            dsimp only [ε]
            simp
          rw [mul_assoc, haeps,
            lemma712I_second_eq_corollary713Low,
            ordUnit_corollary713Low]
        have hcanonicalPenultimate' :
            canonical.order ⟨(s - 2) - 2, by omega⟩ = R := by
          have hidx : (⟨(s - 2) - 2, by omega⟩ : Fin (s - 2)) =
              ⟨s - 4, by omega⟩ := by
            apply Fin.ext
            norm_num [Nat.sub_sub]
          rw [hidx, hcanonicalPenultimate]
        have hcanonicalLast' :
            canonical.order ⟨(s - 2) - 1, by omega⟩ =
              R - 2 * (ramificationIndex K : Int) + 2 := by
          have hidx : (⟨(s - 2) - 1, by omega⟩ : Fin (s - 2)) =
              ⟨s - 3, by omega⟩ := by
            apply Fin.ext
            norm_num [Nat.sub_sub]
          rw [hidx, hcanonicalLast]
        let assembled := canonical.orthogonalProductRight_of_endpointBounds
          localBlock (by omega)
          (by rw [hcanonicalPenultimate', hlocalZero])
          (by rw [hcanonicalLast', hlocalZero];
              have he : (1 : Int) ≤ (ramificationIndex K : Int) := by
                exact_mod_cast ramificationIndex_pos (K := K)
              omega)
          (by
            intro hm
            have hidx : (⟨1, hm⟩ : Fin 3) = (1 : Fin 3) := Fin.ext rfl
            rw [hcanonicalLast', hidx, hlocalOne])
        let eForm :=
          (q.restrict S.right.carrier S.right.nondegenerate).orthogonalSum r
        let rotate := Lattice.orthogonalProductRotateLeft
          (q := eForm.restrict U.left.carrier U.left.nondegenerate)
          (r := q.restrict S.left.carrier S.left.nondegenerate)
          (s := eForm.restrict U.right.carrier U.right.nondegenerate)
          (L := U.left.lattice) (M := S.left.lattice)
          (N := U.right.lattice)
        let assoc := Lattice.orthogonalProductAssoc
          (q := q.restrict S.left.carrier S.left.nondegenerate)
          (r := eForm.restrict U.left.carrier U.left.nondegenerate)
          (s := eForm.restrict U.right.carrier U.right.nondegenerate)
          (L := S.left.lattice) (M := U.left.lattice)
          (N := U.right.lattice)
        let identifyE :=
          (Lattice.Isometry.refl
            (q.restrict S.left.carrier S.left.nondegenerate)
            S.left.lattice).orthogonalProductBasic U.toProductLatticeIsometry
        let toSplitProduct := rotate.trans (assoc.trans identifyE)
        let reassocBack := (Lattice.orthogonalProductAssoc
          (q := q.restrict S.left.carrier S.left.nondegenerate)
          (r := q.restrict S.right.carrier S.right.nondegenerate)
          (s := r)
          (L := S.left.lattice) (M := S.right.lattice) (N := A)).symm
        let identifyJ := S.toProductLatticeIsometry.orthogonalProductBasic
          (Lattice.Isometry.refl r A)
        let totalIso := toSplitProduct.trans (reassocBack.trans identifyJ)
        let resultRaw := assembled.mapLatticeIsometry totalIso
        have hresultLength : 3 + (s - 2) = s + 1 := by omega
        let result := resultRaw.castLength hresultLength
        refine ⟨⟨result, ?_, ?_⟩⟩
        · intro i
          rw [show result = resultRaw.castLength hresultLength by rfl,
            valueUnit_castLength_local]
          change resultRaw.valueUnit ⟨i.val, by omega⟩ = _
          rw [show resultRaw = assembled.mapLatticeIsometry totalIso by rfl,
            GoodBONG.valueUnit_mapLatticeIsometry]
          change assembled.valueUnit ⟨i.val, by omega⟩ = _
          by_cases hi : i.val < s - 2
          · have hidx : (⟨i.val, by omega⟩ : Fin (3 + (s - 2))) =
                orthogonalProductLeftIndex 3 ⟨i.val, hi⟩ := Fin.ext rfl
            rw [hidx]
            simp only [assembled,
              GoodBONG.valueUnit_orthogonalProductRight_of_endpointBounds_left]
            exact hcanonicalPrefix ⟨i.val, hi⟩
          · have hiRange : i.val = s - 2 ∨ i.val = s - 1 := by omega
            rcases hiRange with hi0 | hi1
            · have hidx : (⟨i.val, by omega⟩ : Fin (3 + (s - 2))) =
                  orthogonalProductRightIndex (s - 2) (0 : Fin 3) :=
                Fin.ext (by simp [hi0])
              rw [hidx]
              simp only [assembled,
                GoodBONG.valueUnit_orthogonalProductRight_of_endpointBounds_right]
              rw [hlocal 0, lemma712ITargetValues_zero]
              dsimp only [ε]
              simp
              have heven : Even i.val := by
                rw [hi0]
                exact (Nat.even_sub hsTwo).2
                  ⟨fun _ ↦ (⟨1, by norm_num⟩ : Even (2 : Nat)),
                    fun _ ↦ hsEven⟩
              rw [corollary713PrefixValues_eq_high R i heven]
            · have hidx : (⟨i.val, by omega⟩ : Fin (3 + (s - 2))) =
                  orthogonalProductRightIndex (s - 2) (1 : Fin 3) :=
                Fin.ext (by simp [hi1, Nat.sub_add_cancel hsTwo])
              rw [hidx]
              simp only [assembled,
                GoodBONG.valueUnit_orthogonalProductRight_of_endpointBounds_right]
              rw [hlocal 1, lemma712ITargetValues_one]
              have haeps : line.valueUnit 0 * ε =
                  lemma718CanonicalHigh (K := K) R := by
                dsimp only [ε]
                simp
              rw [mul_assoc, haeps,
                lemma712I_second_eq_corollary713Low]
              have hodd : ¬ Even i.val := by
                rw [hi1]
                apply Nat.not_even_iff_odd.mpr
                exact Nat.Even.sub_odd
                  (le_trans (by norm_num) hsTwo) hsEven
                  (⟨0, by norm_num⟩ : Odd (1 : Nat))
              rw [corollary713PrefixValues_eq_low R i hodd]
        · rw [show result = resultRaw.castLength hresultLength by rfl,
            valueUnit_castLength_local]
          change resultRaw.valueUnit ⟨s, by omega⟩ = _
          rw [show resultRaw = assembled.mapLatticeIsometry totalIso by rfl,
            GoodBONG.valueUnit_mapLatticeIsometry]
          change assembled.valueUnit ⟨s, by omega⟩ = _
          have hidx : (⟨s, by omega⟩ : Fin (3 + (s - 2))) =
              orthogonalProductRightIndex (s - 2) (2 : Fin 3) :=
            Fin.ext (by simp [Nat.sub_add_cancel hsTwo])
          rw [hidx]
          simp only [assembled,
            GoodBONG.valueUnit_orthogonalProductRight_of_endpointBounds_right]
          rw [hlocal 2, lemma712ITargetValues_two, hlineValue]

end BONG.GoodBONG

end Bong
