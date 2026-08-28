/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Corollary811

/-!
# Beli (2019), Corollary 8.9

Corollary 8.9 is the right-end dual of Lemma 8.8.  This file first records
the concrete right-end transformation and proves the reverse-dual
construction.  The paper-facing exceptional alternatives are then obtained
by transporting the three alternatives of Lemma 8.8.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {N : Nat}

/-- The complementary final-gap value
`e - (Rₙ - Rₙ₋₁) / 2`. -/
noncomputable def lemma89ComplementaryDefect
    (b : GoodBONG q L (N + 2)) : ℚ :=
  (ramificationIndex K : ℚ) -
    (b.orderGap (Fin.last N) : ℚ) / 2

/-- The bracketed defect `d[-aₙ₋₁aₙ]`, written as the complementary
boundary instance of the global truncated-prefix defect. -/
noncomputable def lemma89LastCappedDefect
    (b : GoodBONG q L (N + 2)) : WithTop ℚ :=
  b.truncatedPrefixDefect b (-1) N (N + 2)

/-- The final three diagonal coefficients, listed in reverse order.  This
ordering is the one produced literally by reverse duality; reversal of the
three coordinates does not change isotropy. -/
noncomputable def lemma89LastThreeValues
    (b : GoodBONG q L (N + 2)) (hthree : 3 ≤ N + 2) : Fin 3 → K :=
  fun i => b.value (Fin.rev ⟨i.1, i.2.trans_le hthree⟩)

/-- The terminal ternary segment is anisotropic. -/
def Lemma89LastThreeAnisotropic
    (b : GoodBONG q L (N + 2)) (hthree : 3 ≤ N + 2) : Prop :=
  ∀ x : Fin 3 → K,
    diagonalQuadratic (b.lemma89LastThreeValues hthree) x = 0 → x = 0

/-- Corollary 8.9(a): the final alpha is not a valuation-unit defect. -/
def Beli2019Corollary89ExceptionA
    (b : GoodBONG q L (N + 2)) : Prop :=
  ¬IsValuationUnitDefect (K := K) (b.alphaValue (Fin.last N))

/-- Corollary 8.9(b), including its rank-three qualification. -/
structure Beli2019Corollary89ExceptionB
    (b : GoodBONG q L (N + 2)) : Prop where
  residueTwo : ¬HasResidueFieldMoreThanTwoElements (K := K)
  cappedDefect_eq :
    b.lemma89LastCappedDefect =
      (b.lemma89ComplementaryDefect : WithTop ℚ)
  previousAlpha_strict : ∀ hthree : 3 ≤ N + 2,
    b.lemma89ComplementaryDefect <
      b.alphaValue ⟨N - 1, by omega⟩

/-- Corollary 8.9(c), with the earlier-alpha clause available only in rank
at least four. -/
structure Beli2019Corollary89ExceptionC
    (b : GoodBONG q L (N + 2)) : Prop where
  residueTwo : ¬HasResidueFieldMoreThanTwoElements (K := K)
  rank_three : 3 ≤ N + 2
  outerOrders_eq :
    b.order ⟨N - 1, by omega⟩ = b.order (Fin.last (N + 1))
  earlierAlpha_strict : ∀ hfour : 4 ≤ N + 2,
    b.halfGapValue (Fin.last N) <
      b.alphaValue ⟨N - 2, by omega⟩
  lastThree_anisotropic : b.Lemma89LastThreeAnisotropic rank_three

/-- The full exceptional alternative printed in Corollary 8.9. -/
def Beli2019Corollary89Exceptional
    (b : GoodBONG q L (N + 2)) : Prop :=
  b.AttainsHalfGap (Fin.last N) ∧
    (b.Beli2019Corollary89ExceptionA ∨
      Nonempty b.Beli2019Corollary89ExceptionB ∨
      Nonempty b.Beli2019Corollary89ExceptionC)

omit [CharZero K] [ValuativeRel K] [TopologicalSpace K]
    [DyadicContext K] in
/-- Inverting every nonzero coefficient of a diagonal form preserves
anisotropy.  The coordinate change is `xᵢ ↦ xᵢ / aᵢ`. -/
theorem diagonalAnisotropic_inverse_iff {m : Nat} (a : Fin m → Kˣ) :
    (∀ x : Fin m → K,
      diagonalQuadratic (fun i => (a i : K)) x = 0 → x = 0) ↔
    (∀ x : Fin m → K,
      diagonalQuadratic (fun i => ((a i)⁻¹ : K)) x = 0 → x = 0) := by
  have forward : ∀ coefficients : Fin m → Kˣ,
      (∀ x : Fin m → K,
        diagonalQuadratic (fun i => (coefficients i : K)) x = 0 → x = 0) →
      ∀ x : Fin m → K,
        diagonalQuadratic (fun i => ((coefficients i)⁻¹ : K)) x = 0 →
          x = 0 := by
    intro coefficients hanisotropic x hx
    let y : Fin m → K := fun i => x i / (coefficients i : K)
    have hterm : ∀ i,
        (coefficients i : K) * y i ^ 2 =
          ((coefficients i)⁻¹ : K) * x i ^ 2 := by
      intro i
      dsimp only [y]
      field_simp [Units.ne_zero (coefficients i)]
    have hyQuadratic :
        diagonalQuadratic (fun i => (coefficients i : K)) y = 0 := by
      unfold diagonalQuadratic at hx ⊢
      rw [Finset.sum_congr rfl (fun i _ ↦ hterm i)]
      exact hx
    have hy := hanisotropic y hyQuadratic
    funext i
    have hi := congrFun hy i
    dsimp only [y] at hi
    exact (div_eq_zero_iff.mp hi).resolve_right
      (Units.ne_zero (coefficients i))
  constructor
  · exact forward a
  · intro hinverse
    have hinverse' : ∀ x : Fin m → K,
        diagonalQuadratic (fun i => (((a i)⁻¹ : Kˣ) : K)) x = 0 →
          x = 0 := by
      simpa only [Units.val_inv_eq_inv_val] using hinverse
    have h := forward (fun i => (a i)⁻¹) hinverse'
    simpa only [Units.val_inv_eq_inv_val, inv_inv] using h

/-- The complementary boundary is unchanged by reverse duality. -/
theorem lemma88ComplementaryDefect_eq_lemma89_of_reverseDual
    (b : GoodBONG q L (N + 2))
    (c : GoodBONG q (Lattice.dualLattice q L) (N + 2))
    (hcOrders : ∀ j, c.order j = -b.order (Fin.rev j)) :
    c.lemma88ComplementaryDefect = b.lemma89ComplementaryDefect := by
  have hrevCast : Fin.rev ((0 : Fin (N + 1)).castSucc) =
      Fin.last (N + 1) := by
    apply Fin.ext
    simp
  have hrevSucc : Fin.rev ((0 : Fin (N + 1)).succ) =
      (Fin.last N).castSucc := by
    apply Fin.ext
    simp
  have hlastSucc : (Fin.last N).succ = Fin.last (N + 1) := by
    apply Fin.ext
    simp
  unfold lemma88ComplementaryDefect lemma89ComplementaryDefect orderGap
  rw [hcOrders, hcOrders, hrevCast, hrevSucc, hlastSucc]
  push_cast
  ring

/-- The first bracketed defect of the reverse dual is the last bracketed
defect of the original BONG. -/
theorem lemma88FirstCappedDefect_eq_lemma89_of_reverseDual
    (b : GoodBONG q L (N + 2))
    (c : GoodBONG q (Lattice.dualLattice q L) (N + 2))
    (hcValues : ∀ j,
      c.valueUnit j = (b.valueUnit (Fin.rev j))⁻¹)
    (hcAlphas : ∀ j, c.alphaValue j = b.alphaValue (Fin.rev j)) :
    c.lemma88FirstCappedDefect = b.lemma89LastCappedDefect := by
  have h := truncatedPrefixDefect_reverseDual_swap_general
    (n := N + 1) b b c c hcValues hcValues hcAlphas hcAlphas
      0 2 (by omega) (by omega) (-1)
  have hleft : N + 1 + 1 - 2 = N := by omega
  have hright : N + 1 + 1 - 0 = N + 2 := by omega
  simpa only [lemma88FirstCappedDefect, lemma89LastCappedDefect,
    hleft, hright] using h

/-- The first half-gap equality of the reverse dual is the final half-gap
equality of the original BONG. -/
theorem attainsHalfGap_zero_iff_last_of_reverseDual
    (b : GoodBONG q L (N + 2))
    (c : GoodBONG q (Lattice.dualLattice q L) (N + 2))
    (hcOrders : ∀ j, c.order j = -b.order (Fin.rev j))
    (hcAlphas : ∀ j, c.alphaValue j = b.alphaValue (Fin.rev j)) :
    c.AttainsHalfGap (0 : Fin (N + 1)) ↔
      b.AttainsHalfGap (Fin.last N) := by
  have hrevAlpha : Fin.rev (0 : Fin (N + 1)) = Fin.last N := by
    apply Fin.ext
    simp
  have hrevZero : Fin.rev (0 : Fin (N + 2)) = Fin.last (N + 1) := by
    apply Fin.ext
    simp
  have hrevOne : Fin.rev (1 : Fin (N + 2)) =
      (Fin.last N).castSucc := by
    apply Fin.ext
    simp
  have hrevCast : Fin.rev ((0 : Fin (N + 1)).castSucc) =
      Fin.last (N + 1) := by
    apply Fin.ext
    simp
  have hrevSucc : Fin.rev ((0 : Fin (N + 1)).succ) =
      (Fin.last N).castSucc := by
    apply Fin.ext
    simp
  have hlastSucc : (Fin.last N).succ = Fin.last (N + 1) := by
    apply Fin.ext
    simp
  unfold AttainsHalfGap halfGapValue orderGap
  rw [hcAlphas, hrevAlpha, hcOrders, hcOrders, hrevCast, hrevSucc,
    hlastSucc]
  push_cast
  constructor <;> intro h <;> linarith

/-- The first half-gap value of the reverse dual is the final half-gap value
of the original BONG. -/
theorem halfGapValue_zero_eq_last_of_reverseDual
    (b : GoodBONG q L (N + 2))
    (c : GoodBONG q (Lattice.dualLattice q L) (N + 2))
    (hcOrders : ∀ j, c.order j = -b.order (Fin.rev j)) :
    c.halfGapValue (0 : Fin (N + 1)) =
      b.halfGapValue (Fin.last N) := by
  have hrevCast : Fin.rev ((0 : Fin (N + 1)).castSucc) =
      Fin.last (N + 1) := by
    apply Fin.ext
    simp
  have hrevSucc : Fin.rev ((0 : Fin (N + 1)).succ) =
      (Fin.last N).castSucc := by
    apply Fin.ext
    simp
  have hlastSucc : (Fin.last N).succ = Fin.last (N + 1) := by
    apply Fin.ext
    simp
  unfold halfGapValue orderGap
  rw [hcOrders, hcOrders, hrevCast, hrevSucc, hlastSucc]
  push_cast
  ring

/-- Anisotropy of the reverse-dual first ternary segment is equivalent to
anisotropy of the original terminal ternary segment. -/
theorem lemma88FirstThreeAnisotropic_iff_lemma89_of_reverseDual
    (b : GoodBONG q L (N + 2))
    (c : GoodBONG q (Lattice.dualLattice q L) (N + 2))
    (hcValues : ∀ j,
      c.valueUnit j = (b.valueUnit (Fin.rev j))⁻¹)
    (hthree : 3 ≤ N + 2) :
    c.Lemma88FirstThreeAnisotropic hthree ↔
      b.Lemma89LastThreeAnisotropic hthree := by
  let coefficients : Fin 3 → Kˣ := fun i =>
    b.valueUnit (Fin.rev ⟨i.1, i.2.trans_le hthree⟩)
  have hcCoefficients : c.lemma88FirstThreeValues hthree =
      fun i => ((coefficients i)⁻¹ : K) := by
    funext i
    change c.value ⟨i.1, i.2.trans_le hthree⟩ =
      ((coefficients i)⁻¹ : K)
    rw [← c.coe_valueUnit, hcValues]
    rfl
  have hbCoefficients : b.lemma89LastThreeValues hthree =
      fun i => (coefficients i : K) := by
    rfl
  unfold Lemma88FirstThreeAnisotropic Lemma89LastThreeAnisotropic
  rw [hcCoefficients, hbCoefficients]
  exact (diagonalAnisotropic_inverse_iff coefficients).symm

/-- Exception (a) is transported exactly by reverse duality. -/
theorem lemma88ExceptionA_iff_corollary89ExceptionA_of_reverseDual
    (b : GoodBONG q L (N + 2))
    (c : GoodBONG q (Lattice.dualLattice q L) (N + 2))
    (hcAlphas : ∀ j, c.alphaValue j = b.alphaValue (Fin.rev j)) :
    c.Beli2019Lemma88ExceptionA ↔ b.Beli2019Corollary89ExceptionA := by
  have hrevAlpha : Fin.rev (0 : Fin (N + 1)) = Fin.last N := by
    apply Fin.ext
    simp
  unfold Beli2019Lemma88ExceptionA Beli2019Corollary89ExceptionA
  rw [hcAlphas, hrevAlpha]

/-- Exception (b) is transported exactly by reverse duality. -/
theorem lemma88ExceptionB_iff_corollary89ExceptionB_of_reverseDual
    (b : GoodBONG q L (N + 2))
    (c : GoodBONG q (Lattice.dualLattice q L) (N + 2))
    (hcValues : ∀ j,
      c.valueUnit j = (b.valueUnit (Fin.rev j))⁻¹)
    (hcOrders : ∀ j, c.order j = -b.order (Fin.rev j))
    (hcAlphas : ∀ j, c.alphaValue j = b.alphaValue (Fin.rev j)) :
    c.Beli2019Lemma88ExceptionB ↔ b.Beli2019Corollary89ExceptionB := by
  have hcomplementary :=
    b.lemma88ComplementaryDefect_eq_lemma89_of_reverseDual c hcOrders
  have hcapped :=
    b.lemma88FirstCappedDefect_eq_lemma89_of_reverseDual
      c hcValues hcAlphas
  constructor
  · intro E
    refine {
      residueTwo := E.residueTwo
      cappedDefect_eq := ?_
      previousAlpha_strict := ?_
    }
    · rw [← hcapped, ← hcomplementary]
      exact E.cappedDefect_eq
    · intro hthree
      have hrevPrevious : Fin.rev (⟨1, by omega⟩ : Fin (N + 1)) =
          (⟨N - 1, by omega⟩ : Fin (N + 1)) := by
        apply Fin.ext
        simp
      have h := E.nextAlpha_strict hthree
      rw [hcomplementary, hcAlphas, hrevPrevious] at h
      exact h
  · intro E
    refine {
      residueTwo := E.residueTwo
      cappedDefect_eq := ?_
      nextAlpha_strict := ?_
    }
    · rw [hcapped, hcomplementary]
      exact E.cappedDefect_eq
    · intro hthree
      have hrevPrevious : Fin.rev (⟨1, by omega⟩ : Fin (N + 1)) =
          (⟨N - 1, by omega⟩ : Fin (N + 1)) := by
        apply Fin.ext
        simp
      rw [hcomplementary, hcAlphas, hrevPrevious]
      exact E.previousAlpha_strict hthree

/-- Exception (c) is transported exactly by reverse duality. -/
theorem lemma88ExceptionC_iff_corollary89ExceptionC_of_reverseDual
    (b : GoodBONG q L (N + 2))
    (c : GoodBONG q (Lattice.dualLattice q L) (N + 2))
    (hcValues : ∀ j,
      c.valueUnit j = (b.valueUnit (Fin.rev j))⁻¹)
    (hcOrders : ∀ j, c.order j = -b.order (Fin.rev j))
    (hcAlphas : ∀ j, c.alphaValue j = b.alphaValue (Fin.rev j)) :
    c.Beli2019Lemma88ExceptionC ↔ b.Beli2019Corollary89ExceptionC := by
  have hhalf := b.halfGapValue_zero_eq_last_of_reverseDual c hcOrders
  constructor
  · intro E
    have hthree : 3 ≤ N + 2 := E.rank_three
    have htwo : 2 < N + 2 := by omega
    have hrevZero : Fin.rev (0 : Fin (N + 2)) = Fin.last (N + 1) := by
      apply Fin.ext
      simp
    have hrevTwo : Fin.rev (⟨2, htwo⟩ : Fin (N + 2)) =
        (⟨N - 1, by omega⟩ : Fin (N + 2)) := by
      apply Fin.ext
      change N + 1 - 2 = N - 1
      omega
    refine {
      residueTwo := E.residueTwo
      rank_three := E.rank_three
      outerOrders_eq := ?_
      earlierAlpha_strict := ?_
      lastThree_anisotropic :=
        (b.lemma88FirstThreeAnisotropic_iff_lemma89_of_reverseDual
          c hcValues E.rank_three).mp E.firstThree_anisotropic
    }
    · have houter := E.outerOrders_eq
      rw [hcOrders, hcOrders, hrevZero, hrevTwo] at houter
      omega
    · intro hfour
      have hrevEarlier : Fin.rev (⟨2, by omega⟩ : Fin (N + 1)) =
          (⟨N - 2, by omega⟩ : Fin (N + 1)) := by
        apply Fin.ext
        simp
      have h := E.laterAlpha_strict hfour
      rw [hhalf, hcAlphas, hrevEarlier] at h
      exact h
  · intro E
    have hthree : 3 ≤ N + 2 := E.rank_three
    have htwo : 2 < N + 2 := by omega
    have hrevZero : Fin.rev (0 : Fin (N + 2)) = Fin.last (N + 1) := by
      apply Fin.ext
      simp
    have hrevTwo : Fin.rev (⟨2, htwo⟩ : Fin (N + 2)) =
        (⟨N - 1, by omega⟩ : Fin (N + 2)) := by
      apply Fin.ext
      change N + 1 - 2 = N - 1
      omega
    refine {
      residueTwo := E.residueTwo
      rank_three := E.rank_three
      outerOrders_eq := ?_
      laterAlpha_strict := ?_
      firstThree_anisotropic :=
        (b.lemma88FirstThreeAnisotropic_iff_lemma89_of_reverseDual
          c hcValues E.rank_three).mpr E.lastThree_anisotropic
    }
    · rw [hcOrders, hcOrders, hrevZero, hrevTwo]
      have houter := E.outerOrders_eq
      omega
    · intro hfour
      have hrevEarlier : Fin.rev (⟨2, by omega⟩ : Fin (N + 1)) =
          (⟨N - 2, by omega⟩ : Fin (N + 1)) := by
        apply Fin.ext
        simp
      rw [hhalf, hcAlphas, hrevEarlier]
      exact E.earlierAlpha_strict hfour

/-- The complete exceptional alternative of Lemma 8.8 is exactly the
right-end exceptional alternative of Corollary 8.9. -/
theorem lemma88Exceptional_iff_corollary89Exceptional_of_reverseDual
    (b : GoodBONG q L (N + 2))
    (c : GoodBONG q (Lattice.dualLattice q L) (N + 2))
    (hcValues : ∀ j,
      c.valueUnit j = (b.valueUnit (Fin.rev j))⁻¹)
    (hcOrders : ∀ j, c.order j = -b.order (Fin.rev j))
    (hcAlphas : ∀ j, c.alphaValue j = b.alphaValue (Fin.rev j)) :
    c.Beli2019Lemma88Exceptional ↔
      b.Beli2019Corollary89Exceptional := by
  have hhalf := b.attainsHalfGap_zero_iff_last_of_reverseDual
    c hcOrders hcAlphas
  have hA := b.lemma88ExceptionA_iff_corollary89ExceptionA_of_reverseDual
    c hcAlphas
  have hB := b.lemma88ExceptionB_iff_corollary89ExceptionB_of_reverseDual
    c hcValues hcOrders hcAlphas
  have hC := b.lemma88ExceptionC_iff_corollary89ExceptionC_of_reverseDual
    c hcValues hcOrders hcAlphas
  constructor
  · rintro ⟨hboundary, hException⟩
    refine ⟨hhalf.mp hboundary, ?_⟩
    rcases hException with A | B | C
    · exact Or.inl (hA.mp A)
    · rcases B with ⟨B⟩
      exact Or.inr (Or.inl ⟨hB.mp B⟩)
    · rcases C with ⟨C⟩
      exact Or.inr (Or.inr ⟨hC.mp C⟩)
  · rintro ⟨hboundary, hException⟩
    refine ⟨hhalf.mpr hboundary, ?_⟩
    rcases hException with A | B | C
    · exact Or.inl (hA.mpr A)
    · rcases B with ⟨B⟩
      exact Or.inr (Or.inl ⟨hB.mpr B⟩)
    · rcases C with ⟨C⟩
      exact Or.inr (Or.inr ⟨hC.mpr C⟩)

/-- The concrete conclusion of Corollary 8.9: the last coefficient is
multiplied by a valuation unit whose defect is the final alpha. -/
structure Beli2019LastValueTransform
    (b : GoodBONG q L (N + 2)) where
  epsilon : Kˣ
  epsilon_isValuationUnit : IsValuationUnit K (epsilon : K)
  epsilon_defect :
    defectOrder (K := K) epsilon =
      (b.alphaValue (Fin.last N) : WithTop ℚ)
  transformed : GoodBONG q L (N + 2)
  lastValue_eq :
    transformed.valueUnit (Fin.last (N + 1)) =
      epsilon * b.valueUnit (Fin.last (N + 1))

/-- Reverse duality turns any nonexceptional instance of Lemma 8.8 into the
right-end transformation asserted by Corollary 8.9. -/
theorem beli2019LastValueTransform_of_reverseDual
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [DiagonalCodimensionOneCancellationLaws K]
    (b : GoodBONG q L (N + 2))
    (c : GoodBONG q (Lattice.dualLattice q L) (N + 2))
    (hcValues : ∀ j,
      c.valueUnit j = (b.valueUnit (Fin.rev j))⁻¹)
    (hcAlphas : ∀ j, c.alphaValue j = b.alphaValue (Fin.rev j))
    (hnotExceptional : ¬c.Beli2019Lemma88Exceptional) :
    Nonempty b.Beli2019LastValueTransform := by
  rcases c.beli2019Lemma88_sufficiency hnotExceptional with ⟨T⟩
  rcases T.transformed.exists_reverseDual_with_alpha with
    ⟨d, _hdVectors, hdValuesRaw, _hdOrders, _hdAlphas⟩
  have hdValues : ∀ j,
      d.valueUnit j = (T.transformed.valueUnit (Fin.rev j))⁻¹ := by
    intro j
    change d.toBONG.valueUnit j =
      (T.transformed.toBONG.valueUnit (Fin.rev j))⁻¹
    apply Units.ext
    exact hdValuesRaw j
  let hbidual : Lattice.dualLattice q (Lattice.dualLattice q L) = L :=
    Lattice.dualLattice_dualLattice q L
  let transformed : GoodBONG q L (N + 2) := d.castLattice hbidual
  let epsilon : Kˣ := T.epsilon⁻¹
  have hrevLastValue : Fin.rev (Fin.last (N + 1)) =
      (0 : Fin (N + 2)) := by
    apply Fin.ext
    simp
  have hrevZero : Fin.rev (0 : Fin (N + 2)) =
      Fin.last (N + 1) := by
    apply Fin.ext
    simp
  have hrevLastAlpha : Fin.rev (0 : Fin (N + 1)) = Fin.last N := by
    apply Fin.ext
    simp
  refine ⟨{
    epsilon := epsilon
    epsilon_isValuationUnit := ?_
    epsilon_defect := ?_
    transformed := transformed
    lastValue_eq := ?_
  }⟩
  · simpa only [epsilon, IsValuationUnit, Units.val_inv_eq_inv_val,
      AddValuation.map_inv, neg_eq_zero] using T.epsilon_isValuationUnit
  · dsimp only [epsilon]
    rw [defectOrder_inv, T.epsilon_defect, hcAlphas, hrevLastAlpha]
  · simp only [transformed, valueUnit_castLattice]
    rw [hdValues, hrevLastValue, T.firstValue_eq, mul_inv_rev,
      hcValues, hrevZero, inv_inv]
    simpa only [epsilon, mul_comm]

/-- Existence form of the reverse-dual reduction.  It exposes the chosen
dual BONG so that callers can discharge the three exceptional alternatives
directly from right-end hypotheses. -/
theorem exists_reverseDual_for_beli2019Corollary89
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [DiagonalCodimensionOneCancellationLaws K]
    (b : GoodBONG q L (N + 2)) :
    ∃ c : GoodBONG q (Lattice.dualLattice q L) (N + 2),
      (∀ j, c.valueUnit j = (b.valueUnit (Fin.rev j))⁻¹) ∧
      (∀ j, c.order j = -b.order (Fin.rev j)) ∧
      (∀ j, c.alphaValue j = b.alphaValue (Fin.rev j)) ∧
      (¬c.Beli2019Lemma88Exceptional →
        Nonempty b.Beli2019LastValueTransform) := by
  rcases b.exists_reverseDual_with_alpha with
    ⟨c, _hcVectors, hcValuesRaw, hcOrders, hcAlphas⟩
  have hcValues : ∀ j,
      c.valueUnit j = (b.valueUnit (Fin.rev j))⁻¹ := by
    intro j
    change c.toBONG.valueUnit j =
      (b.toBONG.valueUnit (Fin.rev j))⁻¹
    apply Units.ext
    exact hcValuesRaw j
  refine ⟨c, hcValues, hcOrders, hcAlphas, ?_⟩
  intro hnotExceptional
  exact b.beli2019LastValueTransform_of_reverseDual
    c hcValues hcAlphas hnotExceptional

/-- Beli (2019), Corollary 8.9: outside the three printed right-end
exceptions, the final coefficient can be multiplied by a valuation unit of
defect equal to the final alpha. -/
theorem beli2019Corollary89
    [QuadraticDefectLaws K]
    [HilbertSymbolLaws K]
    [DyadicResidueDefectProductLaws K]
    [DyadicHilbertDefectChoiceLaws K]
    [UnitQuadraticDefectParityLaws K]
    [DyadicUnitDefectSpectrumLaws K]
    [DyadicDiscriminantClassLaws K]
    [DyadicUnramifiedNormLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [Beli2009AlphaParityLaws.{u, v} K]
    [Beli2009AlphaLocalizationLaws.{u, v} K]
    [BeliLemma43ConstructionLaws.{u, v} K]
    [Beli2006SectionTwoLaws.{u, v} K]
    [GoodBONGClassificationLaws.{u, v, v} K]
    [DyadicBinaryFirstScalingLaws.{u, v} K]
    [DyadicQuaternaryFirstScalingLaws.{u, v} K]
    [BeliLemma49Laws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [DiagonalCodimensionOneCancellationLaws K]
    (b : GoodBONG q L (N + 2))
    (hnotExceptional : ¬b.Beli2019Corollary89Exceptional) :
    Nonempty b.Beli2019LastValueTransform := by
  rcases b.exists_reverseDual_for_beli2019Corollary89 with
    ⟨c, hcValues, hcOrders, hcAlphas, htransform⟩
  apply htransform
  intro E
  apply hnotExceptional
  exact (b.lemma88Exceptional_iff_corollary89Exceptional_of_reverseDual
    c hcValues hcOrders hcAlphas).mp E

end BONG.GoodBONG

end Bong
