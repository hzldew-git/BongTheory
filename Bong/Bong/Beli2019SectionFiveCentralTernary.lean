/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFiveCentralHighRank
import Bong.Lattice.Omeara9315TernaryGenerators

/-!
# The proper ternary adjacency in Beli (2019), Section 5

This file closes the exceptional ordinary adjacency in Section 5.14.  The
source case-(ii) approximation keeps one line from a proper ternary Jordan
component, while the target case-(iii) approximation removes an orthogonal
line from the same component.  O'Meara 93:15 supplies two orthogonal norm
generators, and the concrete Lemma 3.7 models turn their orthogonality into
the required carrier inclusion.
-/

namespace Bong

open Dyadic Module
open BONG.GoodBONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {M N : Lattice K V}

namespace Lattice.Beli2019Lemma51Data

/-- The integral identity isometry induced by literal equality of two ambient
quadratic sublattices. -/
private noncomputable def equalComponentIsometry
    (C E : Lattice.QuadraticSublattice q) (h : C = E) :
    Lattice.Isometry C.space E.space C.lattice E.lattice := by
  subst E
  exact Lattice.Isometry.refl C.space C.lattice

@[simp]
private theorem equalComponentIsometry_coe
    (C E : Lattice.QuadraticSublattice q) (h : C = E) (z : C.carrier) :
    ((equalComponentIsometry C E h).toLinearEquiv z : V) = (z : V) := by
  subst E
  rfl

set_option maxHeartbeats 0 in
/-- The global-zero proper-ternary endpoint is impossible as soon as the
direct even-coordinate comparison at the coordinate two steps to the right
is available.  This isolates the order-theoretic core from the particular
aligned or unary-shift profile comparison used to prove that bound. -/
theorem centralCertificate_of_sourceFirst_at_two_of_orderLe
    (D : Beli2019Lemma51Data q M N)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (htrigger : a.centralAlphaTrigger b i)
    (hsourceBefore :
      ((D.smallWeakProfileWitness b).indexEquiv
        (⟨i.val - 2, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 <
          D.smallSelectedPosition)
    (hindex : i.val = 2)
    (hsourceFirst :
      let I : Fin (n + 2) := ⟨i.val - 2, by
        have := i.lt_large
        omega⟩
      let R := D.smallStrictCoordinateResolution b I hsourceBefore.le
      I.val = R.coordinates.start)
    (hsourceRank :
      let I : Fin (n + 2) := ⟨i.val - 2, by
        have := i.lt_large
        omega⟩
      let R := D.smallStrictCoordinateResolution b I hsourceBefore.le
      R.jordan.componentRank R.component = 3)
    (hdirect : a.order ⟨i.val, i.lt_large⟩ ≤
      b.order ⟨i.val, i.lt_large⟩) :
    BONG.GoodBONG.Beli2019SectionFiveCentralCertificate a b i := by
  let ISource : Fin (n + 2) := ⟨i.val - 2, by
    have := i.lt_large
    omega⟩
  let INext : Fin (n + 2) := ⟨i.val, i.lt_large⟩
  let Rsource := D.smallStrictCoordinateResolution b ISource hsourceBefore.le
  change ISource.val = Rsource.coordinates.start at hsourceFirst
  change Rsource.jordan.componentRank Rsource.component = 3 at hsourceRank
  have hperiodRaw := Rsource.coordinates.order_add_two_eq ISource.val
    (by rw [hsourceFirst]) (by
      have hstop : Rsource.coordinates.stop =
          Rsource.coordinates.start +
            Rsource.jordan.componentRank Rsource.component := rfl
      rw [hstop, hsourceFirst, hsourceRank]
      omega)
  have hperiod : b.order ISource = b.order INext := by
    convert hperiodRaw using 1 <;> apply congrArg b.order <;>
      apply Fin.ext <;>
        simp only [BONG.GoodBONG.JordanBlockCoordinates.index_val] <;>
          dsimp only [ISource, INext, Fin.val_mk] <;> omega
  unfold BONG.GoodBONG.centralAlphaTrigger at htrigger
  have hstrict : b.order ISource < a.order INext := by
    simpa only [ISource, INext] using htrigger.1
  have hdirect' : a.order INext ≤ b.order INext := by
    simpa only [INext] using hdirect
  exact False.elim (not_lt_of_ge (hdirect'.trans hperiod.symm.le) hstrict)

set_option maxHeartbeats 0 in
/-- The apparent global-zero endpoint of the proper ternary adjacency is
vacuous.  The source orders at local coordinates zero and two agree, while
the aligned even-coordinate comparison puts the target order at coordinate
two below the latter source order.  This contradicts the first strict
inequality in the central trigger. -/
theorem weakAligned_centralCertificate_of_sourceFirst_at_two
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (htrigger : a.centralAlphaTrigger b i)
    (hsourceBefore :
      ((D.smallWeakProfileWitness b).indexEquiv
        (⟨i.val - 2, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 <
          D.smallSelectedPosition)
    (hindex : i.val = 2)
    (hsourceFirst :
      let I : Fin (n + 2) := ⟨i.val - 2, by
        have := i.lt_large
        omega⟩
      let R := D.smallStrictCoordinateResolution b I hsourceBefore.le
      I.val = R.coordinates.start)
    (hsourceRank :
      let I : Fin (n + 2) := ⟨i.val - 2, by
        have := i.lt_large
        omega⟩
      let R := D.smallStrictCoordinateResolution b I hsourceBefore.le
      R.jordan.componentRank R.component = 3) :
    BONG.GoodBONG.Beli2019SectionFiveCentralCertificate a b i := by
  classical
  let ISource : Fin (n + 2) := ⟨i.val - 2, by
    have := i.lt_large
    omega⟩
  let ITarget : Fin (n + 2) := ⟨i.val - 1, by
    have := i.lt_large
    omega⟩
  let INext : Fin (n + 2) := ⟨i.val, i.lt_large⟩
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  let Rsource := D.smallStrictCoordinateResolution b ISource hsourceBefore.le
  change ISource.val = Rsource.coordinates.start at hsourceFirst
  change Rsource.jordan.componentRank Rsource.component = 3 at hsourceRank
  have hsourceOffset : Rsource.localCoordinateOffset = 0 :=
    D.smallStrictCoordinateResolution_localCoordinateOffset_eq_zero
      b ISource hsourceBefore.le
  have hsourceComponent : Rsource.strictWeak.component Rsource.component =
      D.smallAlmostJordan.component (y.indexEquiv ISource).1 := by
    simpa only [Rsource, y] using
      D.smallStrictCoordinateResolution_component_eq_of_lt
        b ISource hsourceBefore.le (by
          simpa only [y, ISource] using hsourceBefore)
  have hsourceCoordinates :=
    Rsource.coordinates_eq_weak_of_offset_zero_of_component_eq
      hsourceOffset hsourceComponent
  have hsourceStart : Rsource.coordinates.start =
      y.componentStart (y.indexEquiv ISource).1 := by
    simpa only [y] using hsourceCoordinates.1
  have hsourceWeakRank : finrank K
      (D.smallAlmostJordan.component (y.indexEquiv ISource).1).carrier = 3 := by
    change finrank K (Rsource.strictWeak.component Rsource.component).carrier = 3
      at hsourceRank
    rw [hsourceComponent] at hsourceRank
    exact hsourceRank
  have hsourceGlobal := y.index_val_eq_componentStart_add_local ISource
  change ISource.val = y.componentStart (y.indexEquiv ISource).1 +
    (y.indexEquiv ISource).2.val at hsourceGlobal
  have hsourceLocalZero : (y.indexEquiv ISource).2.val = 0 := by
    have hIzero : ISource.val = 0 := by
      dsimp only [ISource, Fin.val_mk]
      omega
    have hstartZero : y.componentStart (y.indexEquiv ISource).1 = 0 := by
      rw [← hsourceStart, ← hsourceFirst, hIzero]
    omega
  have hfirstStep := y.indexEquiv_global_succ_eq_local_succ
    ISource ITarget (by
      dsimp only [ISource, ITarget, Fin.val_mk]
      omega) (by omega)
  have htargetComponent : (y.indexEquiv ITarget).1 =
      (y.indexEquiv ISource).1 := by
    simpa only using congrArg Sigma.fst hfirstStep
  have htargetLocal : (y.indexEquiv ITarget).2.val = 1 := by
    have h := congrArg (fun z ↦ z.2.val) hfirstStep
    simpa only [Fin.val_mk, hsourceLocalZero] using h
  have htargetWeakRank : finrank K
      (D.smallAlmostJordan.component (y.indexEquiv ITarget).1).carrier = 3 := by
    exact congrArg
      (fun p ↦ finrank K (D.smallAlmostJordan.component p).carrier)
      htargetComponent |>.trans hsourceWeakRank
  have hsecondStep := y.indexEquiv_global_succ_eq_local_succ
    ITarget INext (by
      dsimp only [ITarget, INext, Fin.val_mk]
      omega) (by omega)
  have hnextSmallComponent : (y.indexEquiv INext).1 =
      (y.indexEquiv ISource).1 := by
    have h := congrArg Sigma.fst hsecondStep
    have h' : (y.indexEquiv INext).1 =
        (y.indexEquiv ITarget).1 := by simpa only using h
    exact h'.trans htargetComponent
  have hnextSmallLocal : (y.indexEquiv INext).2.val = 2 := by
    have h := congrArg (fun z ↦ z.2.val) hsecondStep
    simpa only [Fin.val_mk, htargetLocal] using h
  have hcoordinatesRaw := D.weakProfile_coordinates_eq
    hselected a b INext
  have hcoordinates :
      (x.indexEquiv INext).1 = (y.indexEquiv INext).1 ∧
        (x.indexEquiv INext).2.val = (y.indexEquiv INext).2.val := by
    simpa only [x, y] using hcoordinatesRaw
  have hlargeComponentLe : (x.indexEquiv INext).1 ≤
      D.largeSelectedPosition := by
    have hsourceBefore' := hsourceBefore
    change (y.indexEquiv ISource).1.val <
      D.smallSelectedPosition.val at hsourceBefore'
    have hxy := congrArg Fin.val hcoordinates.1
    have hnext := congrArg Fin.val hnextSmallComponent
    have hselectedVal := congrArg Fin.val hselected
    change (x.indexEquiv INext).1.val ≤ D.largeSelectedPosition.val
    omega
  have hlargeEven : Even (x.indexEquiv INext).2.val := by
    rw [hcoordinates.2, hnextSmallLocal]
    norm_num
  have hdirect : a.order INext ≤ b.order INext :=
    D.weakAligned_order_le_of_component_le_selected_of_local_even
      hselected a b INext hlargeComponentLe hlargeEven
  have hperiodRaw := Rsource.coordinates.order_add_two_eq ISource.val
    (by rw [hsourceFirst]) (by
      have hstop : Rsource.coordinates.stop =
          Rsource.coordinates.start +
            Rsource.jordan.componentRank Rsource.component := rfl
      rw [hstop, hsourceFirst, hsourceRank]
      omega)
  have hperiod : b.order ISource = b.order INext := by
    convert hperiodRaw using 1 <;> apply congrArg b.order <;>
      apply Fin.ext <;>
        simp only [BONG.GoodBONG.JordanBlockCoordinates.index_val] <;>
          dsimp only [ISource, INext, Fin.val_mk] <;> omega
  unfold BONG.GoodBONG.centralAlphaTrigger at htrigger
  have hstrict : b.order ISource < a.order INext := by
    simpa only [ISource, INext] using htrigger.1
  exact False.elim (not_lt_of_ge (hdirect.trans hperiod.symm.le) hstrict)

set_option maxHeartbeats 0 in
/-- The proper ternary exceptional adjacency in Beli's Section 5.14, stated
over the local component and prefix identifications actually used in the
proof. -/
theorem centralCertificate_of_sourceFirst_targetPenultimate_ternary_of_prefixAlignment
    [DyadicDiscriminantClassLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (htrigger : a.centralAlphaTrigger b i)
    (hsourceBefore :
      ((D.smallWeakProfileWitness b).indexEquiv
        (⟨i.val - 2, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 <
          D.smallSelectedPosition)
    (htargetBefore :
      ((D.largeWeakProfileWitness a).indexEquiv
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 <
          D.largeSelectedPosition)
    (hnotCollisionLeft : ¬ ∃ c : Fin D.complementComponentCount,
      ordUnit K (D.complementStrictWeak.scaleGenerator c) =
          ordUnit K D.input.block.enlargedScaleGenerator ∧
        ((D.largeWeakProfileWitness a).indexEquiv
          (⟨i.val - 1, by have := i.lt_large; omega⟩ :
            Fin (n + 2))).1 = D.largeCommonPosition c)
    (hsourcePositive : 0 < i.val - 2)
    (hsourceFirst :
      let I : Fin (n + 2) := ⟨i.val - 2, by
        have := i.lt_large
        omega⟩
      let R := D.smallStrictCoordinateResolution b I hsourceBefore.le
      I.val = R.coordinates.start)
    (htargetPenultimate :
      let I : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      let R := D.largeStrictCoordinateResolution a I htargetBefore.le
      I.val + 2 = R.coordinates.stop)
    (hsameWeak :
      ((D.smallWeakProfileWitness b).indexEquiv
          (⟨i.val - 2, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 =
        ((D.smallWeakProfileWitness b).indexEquiv
          (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).1)
    (htargetCoordinates :
      let ITarget : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      ((D.largeWeakProfileWitness a).indexEquiv ITarget).1 =
        ((D.smallWeakProfileWitness b).indexEquiv ITarget).1)
    (hcomponentAlignment :
      let ITarget : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      D.largeAlmostJordan.component
          ((D.largeWeakProfileWitness a).indexEquiv ITarget).1 =
        D.smallAlmostJordan.component
          ((D.largeWeakProfileWitness a).indexEquiv ITarget).1)
    (hprefixCarrier :
      let ISource : Fin (n + 2) := ⟨i.val - 2, by
        have := i.lt_large
        omega⟩
      D.largeAlmostJordan.toOrthogonalDecomposition.prefixCarrier
          ((D.smallWeakProfileWitness b).indexEquiv ISource).1.val =
        D.smallAlmostJordan.toOrthogonalDecomposition.prefixCarrier
          ((D.smallWeakProfileWitness b).indexEquiv ISource).1.val)
    (hsourceRank :
      let I : Fin (n + 2) := ⟨i.val - 2, by
        have := i.lt_large
        omega⟩
      let R := D.smallStrictCoordinateResolution b I hsourceBefore.le
      R.jordan.componentRank R.component = 3)
    (htargetRank :
      let I : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      let R := D.largeStrictCoordinateResolution a I htargetBefore.le
      R.jordan.componentRank R.component = 3) :
    BONG.GoodBONG.Beli2019SectionFiveCentralCertificate a b i := by
  classical
  let gSource : Fin (n + 1) := ⟨i.val - 2, by
    have := i.lt_large
    omega⟩
  let gTarget : Fin (n + 1) := ⟨i.val - 1, by
    have := i.lt_large
    omega⟩
  let ISource : Fin (n + 2) := gSource.castSucc
  let ITarget : Fin (n + 2) := gTarget.castSucc
  let x := D.largeWeakProfileWitness a
  let y := D.smallWeakProfileWitness b
  let Rsource := D.smallStrictCoordinateResolution b ISource hsourceBefore.le
  let Rtarget := D.largeStrictCoordinateResolution a ITarget htargetBefore.le
  change ISource.val = Rsource.coordinates.start at hsourceFirst
  change ITarget.val + 2 = Rtarget.coordinates.stop at htargetPenultimate
  change Rsource.jordan.componentRank Rsource.component = 3 at hsourceRank
  change Rtarget.jordan.componentRank Rtarget.component = 3 at htargetRank
  have hsourceOffset : Rsource.localCoordinateOffset = 0 :=
    D.smallStrictCoordinateResolution_localCoordinateOffset_eq_zero
      b ISource hsourceBefore.le
  have htargetOffset : Rtarget.localCoordinateOffset = 0 :=
    D.largeStrictCoordinateResolution_localCoordinateOffset_eq_zero_of_lt
      a ITarget htargetBefore.le htargetBefore
  have hsourceComponent : Rsource.strictWeak.component Rsource.component =
      D.smallAlmostJordan.component (y.indexEquiv ISource).1 := by
    simpa only [Rsource, y] using
      D.smallStrictCoordinateResolution_component_eq_of_lt
        b ISource hsourceBefore.le hsourceBefore
  have htargetComponent : Rtarget.strictWeak.component Rtarget.component =
      D.largeAlmostJordan.component (x.indexEquiv ITarget).1 := by
    simpa only [Rtarget, x] using
      D.largeStrictCoordinateResolution_component_eq_of_lt_of_notCollisionLeft
        a ITarget htargetBefore.le htargetBefore (by
          simpa only [x, ITarget, gTarget, Fin.castSucc_mk] using
            hnotCollisionLeft)
  have htargetXY : (x.indexEquiv ITarget).1 =
      (y.indexEquiv ITarget).1 := by
    simpa only [x, y, ITarget, gTarget, Fin.castSucc_mk] using
      htargetCoordinates
  have hpositionEq : (x.indexEquiv ITarget).1 =
      (y.indexEquiv ISource).1 := by
    exact htargetXY.trans hsameWeak.symm
  have htargetPositionBefore : (x.indexEquiv ITarget).1 ≠
      D.largeSelectedPosition := ne_of_lt htargetBefore
  have hcomponentEq : Rtarget.jordan.component Rtarget.component =
      Rsource.jordan.component Rsource.component := by
    change Rtarget.strictWeak.component Rtarget.component =
      Rsource.strictWeak.component Rsource.component
    calc
      Rtarget.strictWeak.component Rtarget.component =
          D.largeAlmostJordan.component (x.indexEquiv ITarget).1 :=
        htargetComponent
      _ = D.smallAlmostJordan.component (x.indexEquiv ITarget).1 := by
        simpa only [x, ITarget, gTarget, Fin.castSucc_mk] using
          hcomponentAlignment
      _ = D.smallAlmostJordan.component (y.indexEquiv ISource).1 := by
        rw [hpositionEq]
      _ = Rsource.strictWeak.component Rsource.component :=
        hsourceComponent.symm
  let pair := Lattice.TernaryOrthogonalNormGeneratorPairData.ofModular
    (q := (Rsource.jordan.component Rsource.component).space)
    (L := (Rsource.jordan.component Rsource.component).lattice)
    (Rsource.jordan.scaleGenerator Rsource.component)
    (Rsource.jordan.modular Rsource.component) hsourceRank
  have hsourceOdd : Odd (Rsource.jordan.componentRank Rsource.component) := by
    rw [hsourceRank]
    norm_num
  let Gsource := BONG.RepresentedFundamentalNormGenerator.ofOddComponentNormGenerator
    Rsource.strictWeak Rsource.hasImproperEvenRank Rsource.scaleOrder_strict
      Rsource.component hsourceOdd pair.first pair.first_generator
  have hsourceValue :
      (Rsource.jordan.component Rsource.component).space.quadratic pair.first =
        (Gsource.value : K) := by
    rfl
  let identify := equalComponentIsometry
    (Rsource.jordan.component Rsource.component)
    (Rtarget.jordan.component Rtarget.component) hcomponentEq.symm
  let secondTarget : (Rtarget.jordan.component Rtarget.component).carrier :=
    identify.toLinearEquiv pair.second
  have hsecondGenerator : Lattice.IsNormGenerator
      (Rtarget.jordan.component Rtarget.component).space
      (Rtarget.jordan.component Rtarget.component).lattice secondTarget := by
    exact pair.second_generator.mapLatticeIsometry identify
  have htargetOdd : Odd (Rtarget.jordan.componentRank Rtarget.component) := by
    rw [htargetRank]
    norm_num
  let Gtarget := BONG.RepresentedFundamentalNormGenerator.ofOddComponentNormGenerator
    Rtarget.strictWeak Rtarget.hasImproperEvenRank Rtarget.scaleOrder_strict
      Rtarget.component htargetOdd secondTarget hsecondGenerator
  have htargetValue :
      (Rtarget.jordan.component Rtarget.component).space.quadratic secondTarget =
        (Gtarget.value : K) := by
    rfl
  have htargetNext : Rtarget.component.val + 1 < Rtarget.componentCount := by
    have hraw :=
      D.largeStrictCoordinateResolution_component_succ_lt_of_lt_of_notCollisionLeft
        a ITarget htargetBefore.le htargetBefore (by
          simpa only [x, ITarget, gTarget, Fin.castSucc_mk] using
            hnotCollisionLeft)
    simpa only [Rtarget] using hraw
  have htargetPositive : 0 < ITarget.val := by
    dsimp only [ITarget, gTarget, Fin.castSucc_mk, Fin.val_mk]
    have hi := i.one_lt
    omega
  have htargetStart : Rtarget.coordinates.start = ITarget.val - 1 := by
    have hstopFormula : Rtarget.coordinates.stop =
        Rtarget.coordinates.start +
          Rtarget.jordan.componentRank Rtarget.component := rfl
    omega
  have htargetInside : (ITarget.val - 1) + 2 <
      Rtarget.coordinates.stop := by
    omega
  have htargetPeriod := Rtarget.coordinates.order_add_two_eq
    (ITarget.val - 1) (by rw [htargetStart]) htargetInside
  have htargetOuter : a.order
        ⟨gTarget.val - 1, by have := gTarget.isLt; omega⟩ =
      a.order ⟨gTarget.val + 1, by have := gTarget.isLt; omega⟩ := by
    have hleftIndex (h : ITarget.val - 1 < Rtarget.coordinates.stop) :
        Rtarget.coordinates.index (ITarget.val - 1) h =
          (⟨gTarget.val - 1, by have := gTarget.isLt; omega⟩ :
            Fin (n + 2)) := by
      apply Fin.ext
      rfl
    have hrightIndex (h : (ITarget.val - 1) + 2 <
        Rtarget.coordinates.stop) :
        Rtarget.coordinates.index ((ITarget.val - 1) + 2) h =
          (⟨gTarget.val + 1, by have := gTarget.isLt; omega⟩ :
            Fin (n + 2)) := by
      apply Fin.ext
      change (ITarget.val - 1) + 2 = gTarget.val + 1
      dsimp only [ITarget, gTarget, Fin.castSucc_mk, Fin.val_mk]
      omega
    simpa only [hleftIndex, hrightIndex] using htargetPeriod
  rcases Rtarget.exists_spaceModel_iii_of_penultimate_with_generator
      gTarget rfl htargetPositive htargetPenultimate (by omega) htargetNext
        Gtarget secondTarget htargetValue htargetOuter
    with ⟨target, htargetMem⟩
  have hsourcePrefixEq :
      Rsource.jordan.toOrthogonalDecomposition.prefixCarrier
          Rsource.component.val =
        D.smallAlmostJordan.toOrthogonalDecomposition.prefixCarrier
          (y.indexEquiv ISource).1.val :=
    Rsource.prefixCarrier_eq_weakPrefix_of_offset_zero hsourceOffset
  have htargetPrefixEq :
      Rtarget.jordan.toOrthogonalDecomposition.prefixCarrier
          Rtarget.component.val =
        D.largeAlmostJordan.toOrthogonalDecomposition.prefixCarrier
          (x.indexEquiv ITarget).1.val :=
    Rtarget.prefixCarrier_eq_weakPrefix_of_offset_zero htargetOffset
  have halignedPrefix :
      D.largeAlmostJordan.toOrthogonalDecomposition.prefixCarrier
          (y.indexEquiv ISource).1.val =
        D.smallAlmostJordan.toOrthogonalDecomposition.prefixCarrier
          (y.indexEquiv ISource).1.val := by
    simpa only [y, ISource, gSource, Fin.castSucc_mk] using hprefixCarrier
  have hprefixEq :
      Rsource.jordan.toOrthogonalDecomposition.prefixCarrier
          Rsource.component.val =
        Rtarget.jordan.toOrthogonalDecomposition.prefixCarrier
          Rtarget.component.val := by
    calc
      Rsource.jordan.toOrthogonalDecomposition.prefixCarrier
          Rsource.component.val =
        D.smallAlmostJordan.toOrthogonalDecomposition.prefixCarrier
          (y.indexEquiv ISource).1.val := hsourcePrefixEq
      _ = D.largeAlmostJordan.toOrthogonalDecomposition.prefixCarrier
          (y.indexEquiv ISource).1.val := halignedPrefix.symm
      _ = D.largeAlmostJordan.toOrthogonalDecomposition.prefixCarrier
          (x.indexEquiv ITarget).1.val := by rw [hpositionEq]
      _ = Rtarget.jordan.toOrthogonalDecomposition.prefixCarrier
          Rtarget.component.val := htargetPrefixEq.symm
  have hprefixInTarget :
      Rsource.jordan.toOrthogonalDecomposition.prefixCarrier
          Rsource.component.val ≤ target.carrier := by
    intro z hz
    have hzBefore : z ∈
        Rtarget.jordan.toOrthogonalDecomposition.prefixCarrier
          Rtarget.component.val := by
      rw [← hprefixEq]
      exact hz
    have hzComplete : z ∈
        Rtarget.jordan.toOrthogonalDecomposition.prefixCarrier
          (Rtarget.component.val + 1) :=
      Rtarget.jordan.toOrthogonalDecomposition.prefixCarrier_mono
        (by omega) hzBefore
    apply htargetMem z hzComplete
    let z' : (Rtarget.jordan.toOrthogonalDecomposition
        |>.prefixQuadraticSublattice Rtarget.component.val).carrier :=
      ⟨z, hzBefore⟩
    exact Rtarget.jordan.toOrthogonalDecomposition.prefix_orthogonal_component
      Rtarget.component z' secondTarget
  have hfirstTargetComponent : (pair.first : V) ∈
      (Rtarget.jordan.component Rtarget.component).carrier := by
    rw [hcomponentEq]
    exact pair.first.property
  have hfirstTargetPrefix : (pair.first : V) ∈
      Rtarget.jordan.toOrthogonalDecomposition.prefixCarrier
        (Rtarget.component.val + 1) :=
    Rtarget.jordan.toOrthogonalDecomposition.component_carrier_le_prefixCarrier
      Rtarget.component (by omega) hfirstTargetComponent
  have hpairOrthogonal : q.bilin (pair.first : V) (secondTarget : V) = 0 := by
    have hp := pair.orthogonal
    change q.bilin (pair.first : V) (pair.second : V) = 0 at hp
    simpa only [secondTarget, identify, equalComponentIsometry_coe] using hp
  have hfirstInTarget : (pair.first : V) ∈ target.carrier :=
    htargetMem (pair.first : V) hfirstTargetPrefix hpairOrthogonal
  have hsourceInternal : gSource.val + 1 < n + 1 := by
    dsimp only [gSource, Fin.val_mk]
    have hi := i.lt_large
    omega
  have hsourceInside : ISource.val + 2 < Rsource.coordinates.stop := by
    have hstopFormula : Rsource.coordinates.stop =
        Rsource.coordinates.start +
          Rsource.jordan.componentRank Rsource.component := rfl
    omega
  have hsourcePeriod := Rsource.coordinates.order_add_two_eq ISource.val
    (by rw [hsourceFirst]) hsourceInside
  have hsourceOuter : b.order gSource.castSucc =
      b.order (⟨gSource.val + 1, hsourceInternal⟩ : Fin (n + 1)).succ := by
    have hleftIndex (h : ISource.val < Rsource.coordinates.stop) :
        Rsource.coordinates.index ISource.val h = gSource.castSucc := by
      apply Fin.ext
      rfl
    have hrightIndex (h : ISource.val + 2 < Rsource.coordinates.stop) :
        Rsource.coordinates.index (ISource.val + 2) h =
          (⟨gSource.val + 1, hsourceInternal⟩ : Fin (n + 1)).succ := by
      apply Fin.ext
      rfl
    simpa only [hleftIndex, hrightIndex] using hsourcePeriod
  have hsourcePositive' : 0 < ISource.val := by
    simpa only [ISource, gSource, Fin.castSucc_mk, Fin.val_mk] using
      hsourcePositive
  rcases Rsource.exists_spaceModel_ii_of_first_interior_with_generator_carrier_le
      gSource rfl hsourcePositive' hsourceFirst (by omega) Gsource pair.first
        hsourceValue hsourceInternal hsourceOuter target.carrier
          hprefixInTarget hfirstInTarget
    with ⟨source, hcarrier⟩
  exact .represented
    (BONG.GoodBONG.centralRepresentation_of_approximationModels
      a b hdefect i htrigger target source hcarrier)

set_option maxHeartbeats 0 in
/-- Aligned specialization of the proper ternary exceptional adjacency. -/
theorem weakAligned_centralCertificate_of_sourceFirst_targetPenultimate_ternary
    [DyadicDiscriminantClassLaws K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    [Beli2006AlphaLaws.{u, v} K]
    [BeliLemma47Laws.{u, v} K]
    (D : Beli2019Lemma51Data q M N)
    (hselected : D.smallSelectedPosition = D.largeSelectedPosition)
    {n : Nat} (a : BONG.GoodBONG q M (n + 2))
    (b : BONG.GoodBONG q N (n + 2))
    (hdefect : a.RepresentationDefectCondition b)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (htrigger : a.centralAlphaTrigger b i)
    (hsourceBefore :
      ((D.smallWeakProfileWitness b).indexEquiv
        (⟨i.val - 2, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 <
          D.smallSelectedPosition)
    (htargetBefore :
      ((D.largeWeakProfileWitness a).indexEquiv
        (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 <
          D.largeSelectedPosition)
    (hnotCollisionLeft : ¬ ∃ c : Fin D.complementComponentCount,
      ordUnit K (D.complementStrictWeak.scaleGenerator c) =
          ordUnit K D.input.block.enlargedScaleGenerator ∧
        ((D.largeWeakProfileWitness a).indexEquiv
          (⟨i.val - 1, by have := i.lt_large; omega⟩ :
            Fin (n + 2))).1 = D.largeCommonPosition c)
    (hsourcePositive : 0 < i.val - 2)
    (hsourceFirst :
      let I : Fin (n + 2) := ⟨i.val - 2, by
        have := i.lt_large
        omega⟩
      let R := D.smallStrictCoordinateResolution b I hsourceBefore.le
      I.val = R.coordinates.start)
    (htargetPenultimate :
      let I : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      let R := D.largeStrictCoordinateResolution a I htargetBefore.le
      I.val + 2 = R.coordinates.stop)
    (hsameWeak :
      ((D.smallWeakProfileWitness b).indexEquiv
          (⟨i.val - 2, by have := i.lt_large; omega⟩ : Fin (n + 2))).1 =
        ((D.smallWeakProfileWitness b).indexEquiv
          (⟨i.val - 1, by have := i.lt_large; omega⟩ : Fin (n + 2))).1)
    (hsourceRank :
      let I : Fin (n + 2) := ⟨i.val - 2, by
        have := i.lt_large
        omega⟩
      let R := D.smallStrictCoordinateResolution b I hsourceBefore.le
      R.jordan.componentRank R.component = 3)
    (htargetRank :
      let I : Fin (n + 2) := ⟨i.val - 1, by
        have := i.lt_large
        omega⟩
      let R := D.largeStrictCoordinateResolution a I htargetBefore.le
      R.jordan.componentRank R.component = 3) :
    BONG.GoodBONG.Beli2019SectionFiveCentralCertificate a b i := by
  let ITarget : Fin (n + 2) := ⟨i.val - 1, by
    have := i.lt_large
    omega⟩
  let ISource : Fin (n + 2) := ⟨i.val - 2, by
    have := i.lt_large
    omega⟩
  have htargetCoordinates := D.weakProfile_coordinates_eq
    hselected a b ITarget
  have hcomponentAlignment := D.aligned_component_eq hselected
    ((D.largeWeakProfileWitness a).indexEquiv ITarget).1
      (by simpa only [ITarget] using ne_of_lt htargetBefore)
  have hprefixCarrier := D.aligned_prefixCarrier_eq hselected
    ((D.smallWeakProfileWitness b).indexEquiv ISource).1.val
  exact D.centralCertificate_of_sourceFirst_targetPenultimate_ternary_of_prefixAlignment
    a b hdefect i htrigger hsourceBefore htargetBefore hnotCollisionLeft
      hsourcePositive hsourceFirst htargetPenultimate hsameWeak
      (by simpa only [ITarget] using htargetCoordinates.1)
      (by simpa only [ITarget] using hcomponentAlignment)
      (by simpa only [ISource] using hprefixCarrier)
      hsourceRank htargetRank

end Lattice.Beli2019Lemma51Data

end Bong
