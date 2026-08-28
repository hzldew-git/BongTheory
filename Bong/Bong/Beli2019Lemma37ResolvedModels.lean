/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019Lemma37ResolvedCoordinates
import Bong.Bong.Beli2019Lemma37Models
import Bong.Bong.Beli2019Lemma37BinaryModels
import Bong.Bong.Beli2019Lemma37Endpoints
import Bong.Lattice.OrthogonalDecompositionPrefixCarrier

/-!
# Represented fundamental generators in the resolved Lemma 3.7 models

An O'Meara fundamental norm-generator value is a statement about the norm
group and norm ideal of `L^(s)`.  It need not, from that statement alone, be
a quadratic value of the displayed Jordan component.  Beli's exceptional
binary case explicitly imposes the extra condition `A_k \in Q(L_k)`.

This file keeps that extra datum visible.  From it we choose the actual
component vector and build the geometric one-after and one-before models used
in Lemma 3.7(ii) and (iii).  No representation hypothesis is hidden in the
definition of a scalar fundamental norm generator.
-/

namespace Bong

open Dyadic Module
open BONG.GoodBONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [DyadicDiscriminantClassLaws K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG

/-- A fundamental norm-generator value which is actually represented by the
displayed Jordan component.  The last field is exactly Beli's additional
condition `A_k \in Q(L_k)`. -/
structure RepresentedFundamentalNormGenerator {t : Nat}
    (J : Lattice.JordanDecomposition q L t) (p : Fin t) where
  value : Kˣ
  fundamental : Lattice.IsNormGeneratorValue q (J.fundamentalLattice p) value
  componentValue : (value : K) ∈ Lattice.quadraticValueSet
    (J.component p).space (J.component p).lattice

namespace RepresentedFundamentalNormGenerator

variable {t : Nat} {J : Lattice.JordanDecomposition q L t} {p : Fin t}

/-- If the displayed Jordan component itself attains the effective norm of
its intrinsic fundamental truncation, its chosen norm-generator vector gives
the represented fundamental generator required in Lemma 3.7(ii)--(iv). -/
noncomputable def ofComponentMinimum
    (W : Lattice.WeakJordanDecomposition q L t)
    (hstrict : StrictMono (fun i ↦ ordUnit K (W.scaleGenerator i)))
    (p : Fin t)
    (hmin : JordanProfileOrder.adjustedAt W.scaleOrderFamily
        W.normOrderFamily (ordUnit K (W.scaleGenerator p)) p =
      W.effectiveNormOrderAt p (ordUnit K (W.scaleGenerator p))) :
    RepresentedFundamentalNormGenerator (W.toJordan hstrict) p where
  value := W.normGeneratorUnit p
  fundamental := by
    have hgenerator := W.adjustedNormGeneratorUnit_spec hstrict p p
      (ordUnit K (W.scaleGenerator p)) hmin
    simpa only [Lattice.JordanDecomposition.fundamentalLattice,
      Lattice.JordanDecomposition.fundamentalScaleOrder,
      Lattice.WeakJordanDecomposition.toJordan_scaleGenerator,
      W.adjustedNormGeneratorUnit_eq_of_le hstrict
        (ordUnit K (W.scaleGenerator p)) p le_rfl] using hgenerator
  componentValue := by
    change ((W.normGeneratorUnit p : Kˣ) : K) ∈
      Lattice.quadraticValueSet (W.component p).space
        (W.component p).lattice
    apply (Lattice.mem_quadraticValueSet_iff
      (W.component p).space (W.component p).lattice
      ((W.normGeneratorUnit p : Kˣ) : K)).2
    refine ⟨W.normGeneratorVector p, ?_, ?_⟩
    · exact (W.normGeneratorVector_spec p).1.mem
    · change (W.component p).space.quadratic
          (W.normGeneratorVector p) = (W.normGeneratorUnit p : K)
      rfl

/-- An odd-rank Jordan component is necessarily proper under O'Meara's
improper-even-rank invariant.  Hence its own chosen norm generator attains
the effective norm of the intrinsic scale truncation and is represented by
the displayed component. -/
noncomputable def ofOddComponent
    (W : Lattice.WeakJordanDecomposition q L t)
    (hW : W.HasImproperEvenRank)
    (hstrict : StrictMono (fun i ↦ ordUnit K (W.scaleGenerator i)))
    (p : Fin t)
    (hodd : Odd ((W.toJordan hstrict).componentRank p)) :
    RepresentedFundamentalNormGenerator (W.toJordan hstrict) p := by
  have heffective : W.effectiveNormOrderAt p
      (ordUnit K (W.scaleGenerator p)) =
        ordUnit K (W.scaleGenerator p) := by
    apply le_antisymm
    · apply le_of_not_gt
      intro hlt
      have heven := hW.componentRank_even_of_lt_effectiveNormOrderAt
        W p p hlt
      change Even ((W.toJordan hstrict).componentRank p) at heven
      rcases hodd with ⟨k, hk⟩
      rcases heven with ⟨l, hl⟩
      omega
    · exact W.targetScale_le_effectiveNormOrderAt p _
  have hnorm : ordUnit K (W.normGeneratorUnit p) =
      ordUnit K (W.scaleGenerator p) := by
    apply le_antisymm
    · apply le_of_not_gt
      intro hlt
      have heven := hW p hlt
      change Even ((W.toJordan hstrict).componentRank p) at heven
      rcases hodd with ⟨k, hk⟩
      rcases heven with ⟨l, hl⟩
      omega
    · exact W.scaleOrder_le_normOrder p
  apply ofComponentMinimum W hstrict p
  simp [JordanProfileOrder.adjustedAt,
    Lattice.WeakJordanDecomposition.scaleOrderFamily,
    Lattice.WeakJordanDecomposition.normOrderFamily,
    hnorm, heffective]

set_option maxHeartbeats 0 in
/-- Any actual norm-generator vector in an odd Jordan component is also a
represented norm generator of the intrinsic fundamental lattice.  This is the
choice-flexible form of `ofOddComponent`: Section 5 needs to prescribe two
different orthogonal generators supplied by O'Meara 93:15, rather than use the
decomposition's fixed `normGeneratorVector`. -/
noncomputable def ofOddComponentNormGenerator
    (W : Lattice.WeakJordanDecomposition q L t)
    (hW : W.HasImproperEvenRank)
    (hstrict : StrictMono (fun i ↦ ordUnit K (W.scaleGenerator i)))
    (p : Fin t)
    (hodd : Odd ((W.toJordan hstrict).componentRank p))
    (x : ((W.toJordan hstrict).component p).carrier)
    (hx : Lattice.IsNormGenerator
      ((W.toJordan hstrict).component p).space
      ((W.toJordan hstrict).component p).lattice x) :
    RepresentedFundamentalNormGenerator (W.toJordan hstrict) p := by
  have heffectiveAt : W.effectiveNormOrderAt p
      (ordUnit K (W.scaleGenerator p)) =
        ordUnit K (W.scaleGenerator p) := by
    apply le_antisymm
    · apply le_of_not_gt
      intro hlt
      have heven := hW.componentRank_even_of_lt_effectiveNormOrderAt
        W p p hlt
      change Even ((W.toJordan hstrict).componentRank p) at heven
      rcases hodd with ⟨k, hk⟩
      rcases heven with ⟨l, hl⟩
      omega
    · exact W.targetScale_le_effectiveNormOrderAt p _
  have hnorm : ordUnit K (W.normGeneratorUnit p) =
      ordUnit K (W.scaleGenerator p) := by
    apply le_antisymm
    · apply le_of_not_gt
      intro hlt
      have heven := hW p hlt
      change Even ((W.toJordan hstrict).componentRank p) at heven
      rcases hodd with ⟨k, hk⟩
      rcases heven with ⟨l, hl⟩
      omega
    · exact W.scaleOrder_le_normOrder p
  have heffective : BONG.jordanEffectiveNormOrder (W.toJordan hstrict) p =
      ordUnit K ((W.toJordan hstrict).normGenerator p) := by
    unfold BONG.jordanEffectiveNormOrder
    rw [Lattice.WeakJordanDecomposition.effectiveNormOrderAt_toJordan]
    simpa only [Lattice.WeakJordanDecomposition.toJordan_scaleGenerator,
      Lattice.WeakJordanDecomposition.toJordan_normGenerator] using
      heffectiveAt.trans hnorm.symm
  have hpositive : 0 < finrank K
      ((W.toJordan hstrict).component p).carrier := by
    rcases hodd with ⟨k, hk⟩
    change 0 < (W.toJordan hstrict).componentRank p
    omega
  have hxne : ((W.toJordan hstrict).component p).space.quadratic x ≠ 0 :=
    hx.isAnisotropic_of_finrank_pos hpositive
  let A : Kˣ := Units.mk0
    (((W.toJordan hstrict).component p).space.quadratic x) hxne
  have hcomponentGenerator : Lattice.IsNormGeneratorValue
      ((W.toJordan hstrict).component p).space
      ((W.toJordan hstrict).component p).lattice A := by
    simpa only [A, Units.val_mk0] using hx.isNormGeneratorValue hxne
  refine
    { value := A
      fundamental := (W.toJordan hstrict).isNormGeneratorValue_fundamentalLattice
        p hcomponentGenerator heffective
      componentValue := ?_ }
  apply (Lattice.mem_quadraticValueSet_iff
    ((W.toJordan hstrict).component p).space
    ((W.toJordan hstrict).component p).lattice (A : K)).2
  exact ⟨x, hx.mem, by simp only [A, Units.val_mk0]⟩

set_option maxHeartbeats 0 in
/-- A prescribed norm-generator vector in any Jordan component gives a
represented fundamental generator as soon as that component attains the
effective norm of its intrinsic scale truncation.  This is the parity-free
core of `ofOddComponentNormGenerator`; collision amalgamations use it with a
vector supported in one of the two old summands. -/
noncomputable def ofComponentNormGenerator
    (W : Lattice.WeakJordanDecomposition q L t)
    (hstrict : StrictMono (fun i ↦ ordUnit K (W.scaleGenerator i)))
    (p : Fin t)
    (x : ((W.toJordan hstrict).component p).carrier)
    (hx : Lattice.IsNormGenerator
      ((W.toJordan hstrict).component p).space
      ((W.toJordan hstrict).component p).lattice x)
    (heffective : BONG.jordanEffectiveNormOrder (W.toJordan hstrict) p =
      ordUnit K ((W.toJordan hstrict).normGenerator p)) :
    RepresentedFundamentalNormGenerator (W.toJordan hstrict) p := by
  have hpositive : 0 < finrank K
      ((W.toJordan hstrict).component p).carrier :=
    W.component_finrank_pos p
  have hxne : ((W.toJordan hstrict).component p).space.quadratic x ≠ 0 :=
    hx.isAnisotropic_of_finrank_pos hpositive
  let A : Kˣ := Units.mk0
    (((W.toJordan hstrict).component p).space.quadratic x) hxne
  have hcomponentGenerator : Lattice.IsNormGeneratorValue
      ((W.toJordan hstrict).component p).space
      ((W.toJordan hstrict).component p).lattice A := by
    simpa only [A, Units.val_mk0] using hx.isNormGeneratorValue hxne
  refine
    { value := A
      fundamental := (W.toJordan hstrict).isNormGeneratorValue_fundamentalLattice
        p hcomponentGenerator heffective
      componentValue := ?_ }
  apply (Lattice.mem_quadraticValueSet_iff
    ((W.toJordan hstrict).component p).space
    ((W.toJordan hstrict).component p).lattice (A : K)).2
  exact ⟨x, hx.mem, by simp only [A, Units.val_mk0]⟩

/-- A component vector realizing the represented fundamental generator. -/
noncomputable def vector
    (G : RepresentedFundamentalNormGenerator J p) : (J.component p).carrier :=
  Classical.choose <|
    (Lattice.mem_quadraticValueSet_iff
      (J.component p).space (J.component p).lattice (G.value : K)).1
        G.componentValue

/-- The chosen realizing vector is integral in its Jordan component. -/
theorem vector_mem
    (G : RepresentedFundamentalNormGenerator J p) :
    G.vector ∈ (J.component p).lattice :=
  (Classical.choose_spec <|
    (Lattice.mem_quadraticValueSet_iff
      (J.component p).space (J.component p).lattice (G.value : K)).1
        G.componentValue).1

/-- The chosen vector has the prescribed component quadratic value. -/
theorem quadratic_vector
    (G : RepresentedFundamentalNormGenerator J p) :
    (J.component p).space.quadratic G.vector = (G.value : K) :=
  (Classical.choose_spec <|
    (Lattice.mem_quadraticValueSet_iff
      (J.component p).space (J.component p).lattice (G.value : K)).1
        G.componentValue).2

/-- The same quadratic-value identity in the ambient space. -/
theorem quadratic_ambientVector
    (G : RepresentedFundamentalNormGenerator J p) :
    q.quadratic (G.vector : V) = (G.value : K) := by
  exact G.quadratic_vector

/-- The realizing component vector belongs to every component prefix whose
cut lies strictly after the selected component. -/
theorem vector_mem_prefixCarrier
    (G : RepresentedFundamentalNormGenerator J p) {k : Nat}
    (hpk : p.val < k) :
    (G.vector : V) ∈ J.toOrthogonalDecomposition.prefixCarrier k :=
  J.toOrthogonalDecomposition.component_carrier_le_prefixCarrier p hpk
    G.vector.property

/-- The concrete component vector embeds its scaled line into every Jordan
prefix containing that component. -/
theorem prefixSpace_represents_scaledLine
    (G : RepresentedFundamentalNormGenerator J p) {k : Nat}
    (hpk : p.val < k) :
    (J.toOrthogonalDecomposition.prefixQuadraticSublattice k).space.Represents
      (QuadraticSpace.scaledLine G.value) := by
  let C := J.toOrthogonalDecomposition.prefixQuadraticSublattice k
  let x : C.carrier := ⟨(G.vector : V), G.vector_mem_prefixCarrier hpk⟩
  have hxq : C.space.quadratic x = (G.value : K) := by
    exact G.quadratic_ambientVector
  have hxne : x ≠ 0 := by
    intro hx
    rw [hx, QuadraticSpace.quadratic_zero] at hxq
    exact (Units.ne_zero G.value) hxq.symm
  refine ⟨{
    toLinearMap :=
      { toFun := fun c ↦ c • x
        map_add' := by intro c d; exact add_smul c d x
        map_smul' := by intro c d; exact smul_assoc c d x }
    injective := smul_left_injective K hxne
    map_bilin := ?_ }⟩
  intro c d
  change C.space.bilin (c • x) (d • x) = (G.value : K) * c * d
  simp only [LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right]
  change d * (c * C.space.quadratic x) = (G.value : K) * c * d
  rw [hxq]
  ring

/-- The realizing component vector is orthogonal to the prefix immediately
before its component. -/
theorem prefix_orthogonal_vector
    (G : RepresentedFundamentalNormGenerator J p)
    (y : (J.toOrthogonalDecomposition
      |>.prefixQuadraticSublattice p.val).carrier) :
    q.bilin (y : V) (G.vector : V) = 0 :=
  J.toOrthogonalDecomposition.prefix_orthogonal_component p y G.vector

end RepresentedFundamentalNormGenerator

namespace JordanOrderProfileWitness.PrescribedJordanComparison

set_option maxHeartbeats 0 in
/-- A represented fundamental generator in the component to the right of a
Jordan boundary gives the concrete Lemma 3.7(ii) model. -/
noncomputable def beli2019Lemma37Model_ii_ofRepresentedFundamental
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    {n t : Nat}
    (a : BONG.GoodBONG q L (n + 2))
    (W : Lattice.WeakJordanDecomposition q L (t + 1))
    (hW : W.HasImproperEvenRank)
    (hstrict : StrictMono (fun i ↦ ordUnit K (W.scaleGenerator i)))
    (P : BONG.JordanOrderProfileWitness a.toBONG (W.toJordan hstrict))
    (z : Fin t)
    (G : BONG.RepresentedFundamentalNormGenerator (W.toJordan hstrict)
      (Lattice.JordanDecomposition.boundaryRightIndex z))
    (hrank : 1 < (W.toJordan hstrict).componentRank
      (Lattice.JordanDecomposition.boundaryRightIndex z))
    (hinternal : (P.boundaryOneAfterIndex z hrank).val + 1 < n + 1)
    (houter : a.order (P.boundaryOneAfterIndex z hrank).castSucc =
      a.order (⟨(P.boundaryOneAfterIndex z hrank).val + 1,
        hinternal⟩ : Fin (n + 1)).succ) :
    BONG.GoodBONG.SpaceApproximationModel a
      (P.boundaryOneAfterIndex z hrank) := by
  let J := W.toJordan hstrict
  let p := Lattice.JordanDecomposition.boundaryRightIndex z
  have hpval : p.val = z.val + 1 := rfl
  have horth : ∀ y : (J.toOrthogonalDecomposition
      |>.prefixQuadraticSublattice (z.val + 1)).carrier,
      q.bilin (y : V) (G.vector : V) = 0 := by
    intro y
    let y' : (J.toOrthogonalDecomposition
        |>.prefixQuadraticSublattice p.val).carrier :=
      ⟨(y : V), by simpa only [hpval] using y.property⟩
    exact G.prefix_orthogonal_vector y'
  exact beli2019Lemma37Model_ii_ofOrthogonalVector
    a W hW hstrict P z G.value G.fundamental hrank hinternal houter
      (G.vector : V) G.quadratic_ambientVector horth

set_option maxHeartbeats 0 in
/-- A represented fundamental generator in the component to the left of a
Jordan boundary gives the concrete Lemma 3.7(iii) model. -/
noncomputable def beli2019Lemma37Model_iii_ofRepresentedFundamental
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    {n t : Nat}
    (a : BONG.GoodBONG q L (n + 2))
    (W : Lattice.WeakJordanDecomposition q L (t + 1))
    (hW : W.HasImproperEvenRank)
    (hstrict : StrictMono (fun i ↦ ordUnit K (W.scaleGenerator i)))
    (P : BONG.JordanOrderProfileWitness a.toBONG (W.toJordan hstrict))
    (z : Fin t)
    (G : BONG.RepresentedFundamentalNormGenerator (W.toJordan hstrict)
      (Lattice.JordanDecomposition.boundaryLeftIndex z))
    (hrank : 1 < (W.toJordan hstrict).componentRank
      (Lattice.JordanDecomposition.boundaryLeftIndex z))
    (hpositive : 0 < (P.boundaryOneBeforeIndex z hrank).val)
    (houter : a.order
        ⟨(P.boundaryOneBeforeIndex z hrank).val - 1, by omega⟩ =
      a.order
        ⟨(P.boundaryOneBeforeIndex z hrank).val + 1, by omega⟩) :
    BONG.GoodBONG.SpaceApproximationModel a
      (P.boundaryOneBeforeIndex z hrank) := by
  let J := W.toJordan hstrict
  let p := Lattice.JordanDecomposition.boundaryLeftIndex z
  have hpval : p.val = z.val := rfl
  have hxmem : (G.vector : V) ∈
      J.toOrthogonalDecomposition.prefixCarrier (z.val + 1) := by
    apply G.vector_mem_prefixCarrier
    rw [hpval]
    omega
  let x : (J.toOrthogonalDecomposition
      |>.prefixQuadraticSublattice (z.val + 1)).carrier :=
    ⟨(G.vector : V), hxmem⟩
  have hxA : (J.prefixSpace (z.val + 1)).quadratic x = (G.value : K) := by
    exact G.quadratic_vector
  exact beli2019Lemma37Model_iii_ofRepresentedVector
    a W hW hstrict P z G.value G.fundamental x hxA hrank hpositive houter

end JordanOrderProfileWitness.PrescribedJordanComparison

end BONG

end Bong
