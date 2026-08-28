/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma32ProfileSeeds
import Bong.Bong.Beli2019ApproximationDual
import Bong.Bong.WeakJordanReverseDual
import Bong.Bong.JordanEffectiveNormGenerator
import Bong.Bong.StructuralProof
import Bong.Lattice.JordanReverseDualDeterminant
import Bong.Lattice.JordanReverseDualInvariants

/-!
# Beli (2019), Corollary 3.3 with a prescribed Jordan determinant

The reverse-dual approximation theorem naturally returns the determinant
seed of a prefix in the reverse Jordan decomposition.  This file identifies
that seed, in the ordinary field square-class group, with the complementary
suffix determinant of the original decomposition.  Splitting the original
lattice into its prefix and suffix then gives the prescribed form

`A * det(F(K₀ ⊥ ... ⊥ K_p))`

used in the last case of Lemma 5.13(i).  The proof treats the last component
separately, where the complementary suffix is the zero-dimensional lattice.
-/

namespace Bong

open Dyadic Module
open scoped BigOperators

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG.WeakJordanOrderProfileWitness

private theorem squareClass_mul_local (a b : Kˣ) :
    squareClass K (a * b) = squareClass K a * squareClass K b :=
  rfl

private theorem squareClass_inv_local (a : Kˣ) :
    squareClass K a⁻¹ = squareClass K a := by
  have h := squareClass_mul_square K a a⁻¹
  have heq : a * a⁻¹ ^ 2 = a⁻¹ := by group
  rw [heq] at h
  exact h

private theorem squareClass_mul_self_local (a : Kˣ) :
    squareClass K a * squareClass K a = 1 := by
  rw [← squareClass_mul_local]
  have h := squareClass_mul_square K (1 : Kˣ) a
  have hone : squareClass K (1 : Kˣ) = 1 := rfl
  simpa only [pow_two, one_mul, hone] using h

private theorem exists_mul_square_eq_of_squareClass_eq_local
    (a b : Kˣ) (h : squareClass K a = squareClass K b) :
    ∃ s : Kˣ, a * s ^ 2 = b := by
  change QuotientGroup.mk' (Subgroup.square Kˣ) a =
    QuotientGroup.mk' (Subgroup.square Kˣ) b at h
  rw [QuotientGroup.mk'_eq_mk'] at h
  rcases h with ⟨z, hz, haz⟩
  change IsSquare z at hz
  rcases hz with ⟨s, rfl⟩
  exact ⟨s, by simpa only [pow_two] using haz⟩

private theorem squareClass_prefix_mul_suffix_eq_valueProduct_local
    {n t : Nat} (b : BONG V q L n)
    (J : Lattice.JordanDecomposition q L t) (k : Nat) :
    squareClass K
        ((J.toOrthogonalDecomposition.prefixQuadraticSublattice k
            |>.refinedDeterminantUnit) *
          (J.toOrthogonalDecomposition.suffixQuadraticSublattice k
            |>.refinedDeterminantUnit)) =
      squareClass K b.valueProduct := by
  have hdet := Lattice.determinantClass_eq_of_isometry
    (J.toOrthogonalDecomposition.prefixSuffixLatticeIsometry k)
  rw [Lattice.determinantClass_orthogonalProduct] at hdet
  change
      unitSquareClass K
          (J.toOrthogonalDecomposition.prefixQuadraticSublattice k
            |>.refinedDeterminantUnit) *
        unitSquareClass K
          (J.toOrthogonalDecomposition.suffixQuadraticSublattice k
            |>.refinedDeterminantUnit) =
      Lattice.determinantClass q L at hdet
  rw [← unitSquareClass_mul] at hdet
  have hmap := congrArg (unitSquareClassToSquareClass K) hdet
  calc
    squareClass K
        ((J.toOrthogonalDecomposition.prefixQuadraticSublattice k
            |>.refinedDeterminantUnit) *
          (J.toOrthogonalDecomposition.suffixQuadraticSublattice k
            |>.refinedDeterminantUnit)) =
        unitSquareClassToSquareClass K (Lattice.determinantClass q L) := by
          simpa only [unitSquareClassToSquareClass_apply] using hmap
    _ = squareClass K b.valueProduct :=
      Lattice.determinantClass_toSquareClass_eq_valueProduct b

private theorem suffixCarrier_subsingleton_of_length_le_cut_local
    {t : Nat} (D : Lattice.OrthogonalDecomposition q L t)
    (k : Nat) (h : t ≤ k) : Subsingleton (D.suffixCarrier k) := by
  letI : IsEmpty (D.SuffixIndex k) :=
    ⟨fun i ↦ (not_lt_of_ge (h.trans i.property)) i.1.isLt⟩
  have hcarrier : D.suffixCarrier k = ⊥ := by
    unfold Lattice.OrthogonalDecomposition.suffixCarrier
    exact iSup_of_empty _
  constructor
  intro x y
  apply Subtype.ext
  have hx : (x : V) = 0 := by
    have hx' : (x : V) ∈ (⊥ : Submodule K V) := by
      rw [← hcarrier]
      exact x.property
    simpa only [Submodule.mem_bot] using hx'
  have hy : (y : V) = 0 := by
    have hy' : (y : V) ∈ (⊥ : Submodule K V) := by
      rw [← hcarrier]
      exact y.property
    simpa only [Submodule.mem_bot] using hy'
  rw [hx, hy]

private theorem reversePrefixRank_add_prefixThroughRank_eq_total
    {t : Nat} (f : Fin t → Nat) (p : Fin t) :
    (∑ i ∈ Finset.Iio (Fin.rev p), f (Fin.rev i)) +
        ((∑ i ∈ Finset.Iio p, f i) + f p) =
      ∑ i, f i := by
  have hrev :
      (∑ i ∈ Finset.Iio (Fin.rev p), f (Fin.rev i)) =
        ∑ i ∈ Finset.Ioi p, f i := by
    apply Finset.sum_bijective Fin.rev Fin.revPerm.bijective
    · intro i
      simp only [Finset.mem_Iio, Finset.mem_Ioi]
      have h := Fin.rev_lt_rev (i := Fin.rev p) (j := i)
      simpa using h.symm
    · intro i hi
      rfl
  have hdisjoint : Disjoint (Finset.Iio p) (Finset.Ioi p) := by
    rw [Finset.disjoint_left]
    intro i hi hj
    simp only [Finset.mem_Iio] at hi
    simp only [Finset.mem_Ioi] at hj
    exact (not_lt_of_ge hi.le) hj
  have herase : (Finset.univ.erase p : Finset (Fin t)) =
      Finset.Iio p ∪ Finset.Ioi p := by
    ext i
    simp only [Finset.mem_erase, Finset.mem_univ,
      Finset.mem_union, Finset.mem_Iio, Finset.mem_Ioi, and_true]
    constructor
    · exact lt_or_gt_of_ne
    · rintro (h | h)
      · exact ne_of_lt h
      · exact (ne_of_lt h).symm
  have hunion := Finset.sum_union hdisjoint (f := f)
  rw [← herase] at hunion
  have heraseSum := Finset.sum_erase_add Finset.univ f
    (Finset.mem_univ p)
  rw [hrev]
  omega

theorem reverseDual_componentStart_add_componentStop_eq_length
    {n t : Nat} {b : BONG V q L n}
    {W : Lattice.WeakJordanDecomposition q L t}
    (w : WeakJordanOrderProfileWitness b W) (p : Fin t) :
    let Wd := W.reverseDual
    let startDual := ∑ i ∈ Finset.Iio (Fin.rev p),
      finrank K (Wd.component i).carrier
    startDual + w.componentStop p = n := by
  dsimp only
  have hpartition := reversePrefixRank_add_prefixThroughRank_eq_total
    (fun i ↦ finrank K (W.component i).carrier) p
  have htotal := w.sum_componentRank_eq_length
  change
    (∑ i ∈ Finset.Iio (Fin.rev p),
        finrank K (W.component (Fin.rev i)).carrier) +
      ((∑ i ∈ Finset.Iio p,
          finrank K (W.component i).carrier) +
        finrank K (W.component p).carrier) = n
  exact hpartition.trans htotal

set_option maxHeartbeats 0 in
theorem corollary33_prescribedPrefixApproximation
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    {m t : Nat} (a : BONG.GoodBONG q L (m + 2))
    (W : Lattice.WeakJordanDecomposition q L t)
    (hW : W.HasImproperEvenRank)
    (hstrict : StrictMono (fun i ↦ ordUnit K (W.scaleGenerator i)))
    (P : JordanOrderProfileWitness a.toBONG (W.toJordan hstrict))
    (p : Fin t) (A : Kˣ)
    (hA : Lattice.IsNormGeneratorValue q
      ((W.toJordan hstrict).fundamentalLattice p) A)
    (hrank : 2 ≤ (W.toJordan hstrict).componentRank p) :
    let w := WeakJordanOrderProfileWitness.ofStrict W hstrict P
    let C := w.jordanBlockCoordinates hW p
    a.IsPrefixApproximation (C.stop - 1)
      (A * ((W.toJordan hstrict).toOrthogonalDecomposition
        |>.prefixQuadraticSublattice (p.val + 1)
        |>.refinedDeterminantUnit)) := by
  dsimp only
  let J := W.toJordan hstrict
  let w := WeakJordanOrderProfileWitness.ofStrict W hstrict P
  let C := w.jordanBlockCoordinates hW p
  obtain ⟨c, _hvectors, hvalues, _horders, halpha⟩ :=
    a.exists_reverseDual_with_alpha
  let Wd := W.reverseDual
  let hWd : Wd.HasImproperEvenRank := hW.reverseDual W
  let hstrictD : StrictMono (fun i ↦ ordUnit K (Wd.scaleGenerator i)) :=
    W.reverseDual_scaleOrder_strict hstrict
  let Jd := Wd.toJordan hstrictD
  let Q : JordanOrderProfileWitness c.toBONG Jd :=
    Classical.choice (c.toBONG.beliLemma47_profile c.good Jd)
  let wd := WeakJordanOrderProfileWitness.ofStrict Wd hstrictD Q
  let pd : Fin t := Fin.rev p
  let E := wd.jordanBlockCoordinates hWd pd
  have hstartStop : E.start + C.stop = m + 2 := by
    have h := w.reverseDual_componentStart_add_componentStop_eq_length p
    simpa only [E, C, wd, Wd,
      WeakJordanOrderProfileWitness.jordanBlockCoordinates,
      WeakJordanOrderProfileWitness.componentStart] using h
  have hErank : 2 ≤ Jd.componentRank pd := by
    change 2 ≤ finrank K ((W.reverseDual).component (Fin.rev p)).carrier
    rw [Lattice.WeakJordanDecomposition.reverseDual_component]
    rw [Fin.rev_rev]
    change 2 ≤ finrank K (W.component p).carrier
    change 2 ≤ finrank K (W.component p).carrier at hrank
    exact hrank
  have hEodd : E.start + 1 < E.stop := by
    change E.start + 1 < E.start + Jd.componentRank pd
    omega
  let s : Kˣ := W.scaleGenerator p
  let Ad : Kˣ := s⁻¹ ^ 2 * A
  have hAd : Lattice.IsNormGeneratorValue q (Jd.fundamentalLattice pd) Ad := by
    change Lattice.IsNormGeneratorValue q
      (J.reverseDual.fundamentalLattice pd) Ad
    rw [J.reverseDual_fundamentalLattice]
    simp only [pd, Fin.rev_rev]
    have hscaled := hA.rescale_of_finrank_pos
      (c := s⁻¹) (J.ambient_finrank_pos_of_index p)
    simpa only [Ad, s, J,
      Lattice.WeakJordanDecomposition.toJordan_scaleGenerator] using hscaled
  let determinant := strictDeterminantSeedDataAny
    Wd hWd hstrictD Q pd
  let seeds := strictJordanApproximationSeedsWithAny
    Wd hWd hstrictD Q pd determinant Ad hAd
  have hdual : c.IsPrefixApproximation (E.start + 1)
      (Ad * determinant.leftDet) := by
    have h := seeds.oddApproximation 0 hEodd
    simpa only [seeds, E, wd, Nat.mul_zero, add_zero, pow_zero, one_mul,
      strictJordanApproximationSeedsWithAny_normGenerator,
      strictJordanApproximationSeedsWithAny_leftDet] using h
  have hiDual : E.start + 1 ≤ m + 2 := by
    exact (by omega : E.start + 1 < E.stop).le.trans E.stop_le
  have htransport := a.isPrefixApproximation_of_reverseDual c hvalues halpha
    (E.start + 1) hiDual (Ad * determinant.leftDet) hdual
  have hindex : m + 2 - (E.start + 1) = C.stop - 1 := by omega
  rw [hindex] at htransport
  change a.IsPrefixApproximation (C.stop - 1)
    (Ad * determinant.leftDet * c.toBONG.prefixProduct (m + 2)) at htransport
  have hunits : ∀ i,
      c.toBONG.valueUnit i = (a.toBONG.valueUnit (Fin.rev i))⁻¹ := by
    intro i
    apply Units.ext
    change c.value i = ((a.toBONG.valueUnit (Fin.rev i))⁻¹ : K)
    exact hvalues i
  have hreverseFull :=
    a.toBONG.prefixProduct_mul_valueProduct_of_reverseValues c.toBONG
      hunits (m + 2) (by omega)
  have hreverseFull' :
      c.toBONG.prefixProduct (m + 2) * a.toBONG.valueProduct = 1 := by
    simpa only [Nat.sub_self, BONG.prefixProduct_zero] using hreverseFull
  have hcFullEq :
      c.toBONG.prefixProduct (m + 2) = a.toBONG.valueProduct⁻¹ :=
    eq_inv_of_mul_eq_one_left hreverseFull'
  have hcFullClass :
      squareClass K (c.toBONG.prefixProduct (m + 2)) =
        squareClass K a.toBONG.valueProduct := by
    rw [hcFullEq, squareClass_inv_local]
  have hAdClass : squareClass K Ad = squareClass K A := by
    have h := squareClass_mul_square K A s⁻¹
    have heq : A * s⁻¹ ^ 2 = Ad := by
      unfold Ad
      ac_rfl
    rw [heq] at h
    exact h
  cases t with
  | zero => exact Fin.elim0 p
  | succ d =>
      let JP := J.toOrthogonalDecomposition
        |>.prefixQuadraticSublattice (p.val + 1)
      let JS := J.toOrthogonalDecomposition
        |>.suffixQuadraticSublattice (p.val + 1)
      let dP : Kˣ := JP.refinedDeterminantUnit
      let dS : Kˣ := JS.refinedDeterminantUnit
      have hsplit := squareClass_prefix_mul_suffix_eq_valueProduct_local
        a.toBONG J (p.val + 1)
      have hsplit' :
          squareClass K a.toBONG.valueProduct =
            squareClass K dP * squareClass K dS := by
        calc
          squareClass K a.toBONG.valueProduct = squareClass K (dP * dS) := by
            simpa only [dP, dS, JP, JS] using hsplit.symm
          _ = squareClass K dP * squareClass K dS :=
            squareClass_mul_local dP dS
      by_cases hpLast : p.val = d
      · have hpdZero : pd.val = 0 := by
          simp only [pd, Fin.rev, Fin.val_mk]
          omega
        have hleftEq :=
          strictDeterminantSeedDataAny_leftDet_of_component_zero
            Wd hWd hstrictD Q pd hpdZero
        change determinant.leftDet = 1 at hleftEq
        have hleftClass : squareClass K determinant.leftDet = 1 := by
          rw [hleftEq]
          rfl
        have hsub : Subsingleton JS.carrier := by
          change Subsingleton
            (J.toOrthogonalDecomposition.suffixCarrier (p.val + 1))
          exact suffixCarrier_subsingleton_of_length_le_cut_local
            J.toOrthogonalDecomposition (p.val + 1) (by omega)
        have hSUnit : unitSquareClass K dS = 1 := by
          change Lattice.determinantClass JS.space JS.lattice = 1
          exact Lattice.determinantClass_eq_one_of_subsingleton
            JS.space JS.lattice hsub
        have hSClass : squareClass K dS = 1 := by
          have hmap := congrArg (unitSquareClassToSquareClass K) hSUnit
          simpa only [unitSquareClassToSquareClass_apply, map_one] using hmap
        have hPFull :
            squareClass K dP = squareClass K a.toBONG.valueProduct := by
          rw [hSClass, mul_one] at hsplit'
          exact hsplit'.symm
        have htargetClass :
            squareClass K
                (Ad * determinant.leftDet * c.toBONG.prefixProduct (m + 2)) =
              squareClass K (A * dP) := by
          calc
            squareClass K
                (Ad * determinant.leftDet * c.toBONG.prefixProduct (m + 2)) =
                squareClass K Ad * squareClass K determinant.leftDet *
                  squareClass K (c.toBONG.prefixProduct (m + 2)) := by
              rw [squareClass_mul_local, squareClass_mul_local]
            _ = squareClass K A * 1 * squareClass K a.toBONG.valueProduct := by
              rw [hAdClass, hleftClass, hcFullClass]
            _ = squareClass K A * squareClass K dP := by
              rw [mul_one, ← hPFull]
            _ = squareClass K (A * dP) :=
              (squareClass_mul_local A dP).symm
        obtain ⟨u, hu⟩ := exists_mul_square_eq_of_squareClass_eq_local
          (Ad * determinant.leftDet * c.toBONG.prefixProduct (m + 2))
          (A * dP) htargetClass
        change a.IsPrefixApproximation (C.stop - 1) (A * dP)
        rw [← hu]
        exact (a.isPrefixApproximation_mul_square_iff
          (C.stop - 1)
          (Ad * determinant.leftDet * c.toBONG.prefixProduct (m + 2)) u).2
            htransport
      · have hpLt : p.val < d := by omega
        let j : Fin d := ⟨p.val, hpLt⟩
        have hpdNe : pd.val ≠ 0 := by
          simp only [pd, Fin.rev, Fin.val_mk]
          omega
        have hleftEq :=
          strictDeterminantSeedDataAny_leftDet_of_component_ne_zero
            Wd hWd hstrictD Q pd hpdNe
        change determinant.leftDet =
          (Jd.toOrthogonalDecomposition.prefixQuadraticSublattice pd.val
            |>.refinedDeterminantUnit) at hleftEq
        have hpdCount : pd.val = (Fin.rev j).val + 1 := by
          simp only [pd, j, Fin.rev, Fin.val_mk]
          omega
        have hreverseClass := J.reverseDualBoundaryPrefix_determinantClass j
        have hleftUnit :
            unitSquareClass K determinant.leftDet =
              (unitSquareClass K dS)⁻¹ := by
          rw [hleftEq]
          change
            Lattice.determinantClass
                (J.reverseDual.toOrthogonalDecomposition
                  |>.prefixQuadraticSublattice pd.val |>.space)
                (J.reverseDual.toOrthogonalDecomposition
                  |>.prefixQuadraticSublattice pd.val |>.lattice) =
              (Lattice.determinantClass JS.space JS.lattice)⁻¹
          rw [hpdCount]
          simpa only [JS, j] using hreverseClass
        have hleftInvClass :
            squareClass K determinant.leftDet =
              (squareClass K dS)⁻¹ := by
          have hmap := congrArg (unitSquareClassToSquareClass K) hleftUnit
          simpa only [unitSquareClassToSquareClass_apply, map_inv] using hmap
        have hSInv : (squareClass K dS)⁻¹ = squareClass K dS := by
          have h := squareClass_inv_local dS
          change (squareClass K dS)⁻¹ = squareClass K dS at h
          exact h
        have hleftClass :
            squareClass K determinant.leftDet = squareClass K dS :=
          hleftInvClass.trans hSInv
        have htargetClass :
            squareClass K
                (Ad * determinant.leftDet * c.toBONG.prefixProduct (m + 2)) =
              squareClass K (A * dP) := by
          calc
            squareClass K
                (Ad * determinant.leftDet * c.toBONG.prefixProduct (m + 2)) =
                squareClass K Ad * squareClass K determinant.leftDet *
                  squareClass K (c.toBONG.prefixProduct (m + 2)) := by
              rw [squareClass_mul_local, squareClass_mul_local]
            _ = squareClass K A * squareClass K dS *
                squareClass K a.toBONG.valueProduct := by
              rw [hAdClass, hleftClass, hcFullClass]
            _ = squareClass K A * squareClass K dS *
                (squareClass K dP * squareClass K dS) := by
              rw [hsplit']
            _ = squareClass K A * squareClass K dP *
                (squareClass K dS * squareClass K dS) := by
              ac_rfl
            _ = squareClass K A * squareClass K dP := by
              rw [squareClass_mul_self_local, mul_one]
            _ = squareClass K (A * dP) :=
              (squareClass_mul_local A dP).symm
        obtain ⟨u, hu⟩ := exists_mul_square_eq_of_squareClass_eq_local
          (Ad * determinant.leftDet * c.toBONG.prefixProduct (m + 2))
          (A * dP) htargetClass
        change a.IsPrefixApproximation (C.stop - 1) (A * dP)
        rw [← hu]
        exact (a.isPrefixApproximation_mul_square_iff
          (C.stop - 1)
          (Ad * determinant.leftDet * c.toBONG.prefixProduct (m + 2)) u).2
            htransport

end BONG.WeakJordanOrderProfileWitness

end Bong
