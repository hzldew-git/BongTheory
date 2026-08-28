import Bong.Bong.Beli2019Lemma34OneAfter
import Bong.Bong.Beli2019Corollary33Jordan
import Bong.Bong.DiagonalRepresentationDeterminant

namespace Bong

open Dyadic Module
open BONG.GoodBONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [DyadicDiscriminantClassLaws K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG.JordanOrderProfileWitness

omit [DyadicDiscriminantClassLaws K] in
theorem boundaryIndex_pos_of_leftComponentRank_gt_one
    {n t : Nat} {a : BONG.GoodBONG q L (n + 2)}
    {J : Lattice.JordanDecomposition q L (t + 1)}
    (P : JordanOrderProfileWitness a.toBONG J) (z : Fin t)
    (hrank : 1 < J.componentRank
      (Lattice.JordanDecomposition.boundaryLeftIndex z)) :
    0 < (P.boundaryIndex z).val := by
  let li : Fin (t + 1) :=
    Lattice.JordanDecomposition.boundaryLeftIndex z
  let ri : Fin (t + 1) :=
    Lattice.JordanDecomposition.boundaryRightIndex z
  have hprefix := P.boundaryIndex_succ_val_eq_componentRankPrefix z
  have hmem : li ∈ Finset.Iio ri := by
    simp only [Finset.mem_Iio]
    change z.val < z.val + 1
    omega
  have hle : J.componentRank li ≤
      ∑ k ∈ Finset.Iio ri, J.componentRank k := by
    exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hmem
  change 1 < J.componentRank li at hrank
  change (P.boundaryIndex z).val + 1 =
    ∑ k ∈ Finset.Iio ri, J.componentRank k at hprefix
  omega

noncomputable def boundaryOneBeforeIndex
    {n t : Nat} {a : BONG.GoodBONG q L (n + 2)}
    {J : Lattice.JordanDecomposition q L (t + 1)}
    (P : JordanOrderProfileWitness a.toBONG J) (z : Fin t)
    (hrank : 1 < J.componentRank
      (Lattice.JordanDecomposition.boundaryLeftIndex z)) : Fin (n + 1) :=
  ⟨(P.boundaryIndex z).val - 1, by
    have hpos := P.boundaryIndex_pos_of_leftComponentRank_gt_one z hrank
    have hlt := (P.boundaryIndex z).isLt
    omega⟩

omit [DyadicDiscriminantClassLaws K] in
theorem boundaryOneBeforeIndex_succ_val
    {n t : Nat} {a : BONG.GoodBONG q L (n + 2)}
    {J : Lattice.JordanDecomposition q L (t + 1)}
    (P : JordanOrderProfileWitness a.toBONG J) (z : Fin t)
    (hrank : 1 < J.componentRank
      (Lattice.JordanDecomposition.boundaryLeftIndex z)) :
    (P.boundaryOneBeforeIndex z hrank).val + 1 =
      (P.boundaryIndex z).val := by
  have hpos := P.boundaryIndex_pos_of_leftComponentRank_gt_one z hrank
  simp only [boundaryOneBeforeIndex]
  omega

/-- Explicit geometric meaning of Beli's notation
`F L_(k) ⊥ [A_k]`: the chosen coefficients diagonalize a complement of
the represented norm-generator line inside the prescribed Jordan prefix.
This is data, not a local-classification law. -/
structure BoundaryOneBeforeModel
    {n t : Nat} {a : BONG.GoodBONG q L (n + 2)}
    {J : Lattice.JordanDecomposition q L (t + 1)}
    (P : JordanOrderProfileWitness a.toBONG J) (z : Fin t) (A : Kˣ) where
  units : Fin (P.boundaryIndex z).val → Kˣ
  splitIsometry :
    QuadraticSpace.Isometry
      ((QuadraticSpace.finiteDiagonal
          (diagonalUnitCoefficients units)
          (QuadraticSpace.diagonalUnitCoefficients_ne_zero units))
        |>.orthogonalSum (QuadraticSpace.scaledLine A))
      (J.prefixSpace (z.val + 1))

namespace BoundaryOneBeforeModel

variable {n t : Nat} {a : BONG.GoodBONG q L (n + 2)}
  {J : Lattice.JordanDecomposition q L (t + 1)}
  {P : JordanOrderProfileWitness a.toBONG J} {z : Fin t} {A : Kˣ}

noncomputable def rankEquiv
    (_M : BoundaryOneBeforeModel P z A)
    (hrank : 1 < J.componentRank
      (Lattice.JordanDecomposition.boundaryLeftIndex z)) :
    Fin ((P.boundaryOneBeforeIndex z hrank).val + 1) ≃
      Fin (P.boundaryIndex z).val :=
  finCongr (P.boundaryOneBeforeIndex_succ_val z hrank)

noncomputable def approximationUnits
    (M : BoundaryOneBeforeModel P z A)
    (hrank : 1 < J.componentRank
      (Lattice.JordanDecomposition.boundaryLeftIndex z)) :
    Fin ((P.boundaryOneBeforeIndex z hrank).val + 1) → Kˣ :=
  M.units ∘ M.rankEquiv hrank

omit [DyadicDiscriminantClassLaws K] in
theorem diagonalUnitDeterminant_approximationUnits
    (M : BoundaryOneBeforeModel P z A)
    (hrank : 1 < J.componentRank
      (Lattice.JordanDecomposition.boundaryLeftIndex z)) :
    diagonalUnitDeterminant (M.approximationUnits hrank) =
      diagonalUnitDeterminant M.units := by
  unfold diagonalUnitDeterminant approximationUnits
  exact (M.rankEquiv hrank).prod_comp M.units

noncomputable def extendedDiagonalIsometry
    (M : BoundaryOneBeforeModel P z A) :
    QuadraticSpace.Isometry
      (QuadraticSpace.finiteDiagonal
        (diagonalUnitCoefficients (Fin.snoc M.units A))
        (QuadraticSpace.diagonalUnitCoefficients_ne_zero
          (Fin.snoc M.units A)))
      (QuadraticSpace.finiteDiagonal
        (diagonalUnitCoefficients (P.boundaryPrefixDiagonalUnits z))
        (QuadraticSpace.diagonalUnitCoefficients_ne_zero
          (P.boundaryPrefixDiagonalUnits z))) :=
  (QuadraticSpace.finiteDiagonalOrthogonalSumScaledLineIsometry
      M.units A).symm
    |>.trans M.splitIsometry
    |>.trans (P.boundaryPrefixDiagonalizationIsometry z)

omit [DyadicDiscriminantClassLaws K] in
theorem units_eq_boundaryDeterminant_mul_line_mul_square
    (M : BoundaryOneBeforeModel P z A) :
    ∃ u : Kˣ,
      diagonalUnitDeterminant M.units =
        (A * diagonalUnitDeterminant
          (P.boundaryPrefixDiagonalUnits z)) * u ^ 2 := by
  have hrep : DiagonalRepresents
      (diagonalUnitCoefficients (Fin.snoc M.units A))
      (diagonalUnitCoefficients (P.boundaryPrefixDiagonalUnits z)) := by
    apply (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
      (Fin.snoc M.units A) (P.boundaryPrefixDiagonalUnits z)).1
    exact ⟨M.extendedDiagonalIsometry.toRepresentation⟩
  obtain ⟨p, hp⟩ :=
    DiagonalRepresents.exists_prod_eq_mul_square_of_sameRank hrep
  have hpUnits : diagonalUnitDeterminant (Fin.snoc M.units A) =
      diagonalUnitDeterminant (P.boundaryPrefixDiagonalUnits z) * p ^ 2 := by
    apply Units.ext
    change Units.coeHom K
        (∏ i, (Fin.snoc M.units A :
          Fin ((P.boundaryIndex z).val + 1) → Kˣ) i) =
      Units.coeHom K (∏ i, P.boundaryPrefixDiagonalUnits z i) *
        (p : K) ^ 2
    rw [map_prod (Units.coeHom K) (Fin.snoc M.units A) Finset.univ,
      map_prod (Units.coeHom K) (P.boundaryPrefixDiagonalUnits z)
        Finset.univ]
    exact hp
  rw [diagonalUnitDeterminant_snoc] at hpUnits
  refine ⟨A⁻¹ * p, ?_⟩
  have hA : A * A⁻¹ ^ 2 = A⁻¹ := by group
  calc
    diagonalUnitDeterminant M.units =
        (diagonalUnitDeterminant (P.boundaryPrefixDiagonalUnits z) *
          p ^ 2) * A⁻¹ := by rw [← hpUnits]; simp
    _ = (A * diagonalUnitDeterminant
          (P.boundaryPrefixDiagonalUnits z)) * (A⁻¹ * p) ^ 2 := by
      rw [mul_pow]
      rw [show (A * diagonalUnitDeterminant
          (P.boundaryPrefixDiagonalUnits z)) * (A⁻¹ ^ 2 * p ^ 2) =
        (diagonalUnitDeterminant (P.boundaryPrefixDiagonalUnits z) *
          p ^ 2) * (A * A⁻¹ ^ 2) by ac_rfl, hA]

omit [DyadicDiscriminantClassLaws K] in
theorem units_eq_line_mul_refinedDeterminant_mul_square
    (M : BoundaryOneBeforeModel P z A) :
    ∃ u : Kˣ,
      diagonalUnitDeterminant M.units =
        (A * (J.toOrthogonalDecomposition.prefixQuadraticSublattice
          (z.val + 1)).refinedDeterminantUnit) * u ^ 2 := by
  let dP : Kˣ :=
    (J.toOrthogonalDecomposition.prefixQuadraticSublattice
      (z.val + 1)).refinedDeterminantUnit
  change ∃ u : Kˣ,
    diagonalUnitDeterminant M.units = (A * dP) * u ^ 2
  obtain ⟨u, hu⟩ := M.units_eq_boundaryDeterminant_mul_line_mul_square
  obtain ⟨s, hs⟩ :=
    P.boundaryPrefixDiagonalUnits_eq_refinedDeterminant_mul_square z
  have hs' : diagonalUnitDeterminant
      (P.boundaryPrefixDiagonalUnits z) = dP * s ^ 2 := by
    simpa only [dP] using hs
  refine ⟨s * u, ?_⟩
  rw [hu, hs', mul_pow]
  ac_rfl

omit [DyadicDiscriminantClassLaws K] in
theorem approximationUnits_eq_line_mul_refinedDeterminant_mul_square
    (M : BoundaryOneBeforeModel P z A)
    (hrank : 1 < J.componentRank
      (Lattice.JordanDecomposition.boundaryLeftIndex z)) :
    ∃ u : Kˣ,
      diagonalUnitDeterminant (M.approximationUnits hrank) =
        (A * (J.toOrthogonalDecomposition.prefixQuadraticSublattice
          (z.val + 1)).refinedDeterminantUnit) * u ^ 2 := by
  rw [M.diagonalUnitDeterminant_approximationUnits hrank]
  exact M.units_eq_line_mul_refinedDeterminant_mul_square

end BoundaryOneBeforeModel

namespace PrescribedJordanComparison

variable {n t : Nat} {a : BONG.GoodBONG q L (n + 2)}
  {J : Lattice.JordanDecomposition q L (t + 1)}

set_option maxHeartbeats 0 in
theorem oneBefore_rightRepresentation_of_conditionIII
    (C : PrescribedJordanComparison a J)
    (P : JordanOrderProfileWitness a.toBONG J) (z : Fin t)
    (A : Kˣ)
    (hA : Lattice.IsNormGeneratorValue q
      (J.fundamentalLattice
        (Lattice.JordanDecomposition.boundaryLeftIndex z)) A)
    (M : BoundaryOneBeforeModel P z A)
    (hcontainment : J.fundamentalIdeal z <
      J.fourNormOverWeightIdeal
        (Lattice.JordanDecomposition.boundaryLeftIndex z)) :
    DiagonalRepresents
      (diagonalUnitCoefficients M.units)
      (a.prefixValues ((P.boundaryIndex z).val + 1) (by omega)) := by
  letI : Module.Finite K V := L.moduleFinite
  let S := C.adapted
  let h := C.componentCount_eq
  let Js := S.sourceJordanSucc h
  let Ps := S.sourceProfileSucc h
  let li : Fin (t + 1) :=
    Lattice.JordanDecomposition.boundaryLeftIndex z
  let Ap0 :=
    Lattice.JordanDecomposition.canonicalFundamentalNormGeneratorChoice J
  let Ap := Ap0.replaceAt li A hA
  have htrigger : J.fundamentalIdeal z <
      J.fourNormOverWeightIdealWith Ap li := by
    rw [J.fourNormOverWeightIdealWith_eq_canonical]
    exact hcontainment
  have hembedding := (C.conditionsFromPrescribed Ap).2.2 z htrigger
  have hAvalue : Ap.value li = A := by simp [Ap]
  rw [hAvalue] at hembedding
  unfold Lattice.QuadraticSublattice.EmbedsIntoOrthogonalSum
    QuadraticSpace.EmbedsInto at hembedding
  let model := QuadraticSpace.finiteDiagonal
    (diagonalUnitCoefficients M.units)
    (QuadraticSpace.diagonalUnitCoefficients_ne_zero M.units)
  let targetJs := Js.prefixSpace (z.val + 1)
  let line := QuadraticSpace.scaledLine A
  have htotal : (targetJs.orthogonalSum line).Represents
      (model.orthogonalSum line) := by
    rcases hembedding with ⟨f⟩
    exact ⟨f.trans M.splitIsometry.toRepresentation⟩
  have hswapped : (line.orthogonalSum targetJs).Represents
      (line.orthogonalSum model) := by
    exact (QuadraticSpace.represents_iff_of_isometries
      (QuadraticSpace.orthogonalSumSwap model line)
      (QuadraticSpace.orthogonalSumSwap targetJs line)).1 htotal
  have hcancelled : targetJs.Represents model := by
    exact QuadraticSpace.orthogonalSumCancelRepresents line line
      model targetJs (QuadraticSpace.Isometry.refl line) hswapped
  have hdiagSpace :=
    (QuadraticSpace.represents_iff_of_isometries
      (QuadraticSpace.Isometry.refl model)
      ((S.sourcePrefixExactDiagonalIsometry h z).symm)).1 hcancelled
  have hdiag : DiagonalRepresents
      (diagonalUnitCoefficients M.units)
      (diagonalUnitCoefficients
        (a.prefixValueUnits ((Ps.boundaryIndex z).val + 1) (by omega))) := by
    apply (QuadraticSpace.finiteDiagonal_represents_iff_diagonalRepresents
      M.units
      (a.prefixValueUnits ((Ps.boundaryIndex z).val + 1) (by omega))).1
    unfold model GoodBONG.prefixExactDiagonalSpace at hdiagSpace
    convert hdiagSpace using 1 <;> rfl
  have hdiag' : DiagonalRepresents
      (diagonalUnitCoefficients M.units)
      (a.prefixValues ((Ps.boundaryIndex z).val + 1) (by omega)) := by
    simpa only [a.diagonalUnitCoefficients_prefixValueUnits] using hdiag
  have hboundary : Ps.boundaryIndex z = P.boundaryIndex z :=
    C.boundaryIndex_eq P z
  exact BONG.GoodBONG.targetPrefixRepresents_cast
    (diagonalUnitCoefficients M.units) a (by rw [hboundary]) hdiag'

set_option maxHeartbeats 0 in
theorem oneBefore_rightRepresentation_of_conditionIII_reindexed
    (C : PrescribedJordanComparison a J)
    (P : JordanOrderProfileWitness a.toBONG J) (z : Fin t)
    (A : Kˣ)
    (hA : Lattice.IsNormGeneratorValue q
      (J.fundamentalLattice
        (Lattice.JordanDecomposition.boundaryLeftIndex z)) A)
    (M : BoundaryOneBeforeModel P z A)
    (hrank : 1 < J.componentRank
      (Lattice.JordanDecomposition.boundaryLeftIndex z))
    (hcontainment : J.fundamentalIdeal z <
      J.fourNormOverWeightIdeal
        (Lattice.JordanDecomposition.boundaryLeftIndex z)) :
    DiagonalRepresents
      (diagonalUnitCoefficients (M.approximationUnits hrank))
      (a.prefixValues ((P.boundaryIndex z).val + 1) (by omega)) := by
  have hrep := C.oneBefore_rightRepresentation_of_conditionIII
    P z A hA M hcontainment
  have hreindexed := hrep.reindexSource (M.rankEquiv hrank)
  change DiagonalRepresents
    (fun i ↦ (M.units (M.rankEquiv hrank i) : K))
    (a.prefixValues ((P.boundaryIndex z).val + 1) (by omega))
  exact hreindexed

set_option maxHeartbeats 0 in
theorem oneBefore_rightRepresentation
    (C : PrescribedJordanComparison a J)
    (P : JordanOrderProfileWitness a.toBONG J) (z : Fin t)
    (A : Kˣ)
    (hA : Lattice.IsNormGeneratorValue q
      (J.fundamentalLattice
        (Lattice.JordanDecomposition.boundaryLeftIndex z)) A)
    (M : BoundaryOneBeforeModel P z A)
    (hrank : 1 < J.componentRank
      (Lattice.JordanDecomposition.boundaryLeftIndex z)) :
    a.rightApproximationTrigger (P.boundaryOneBeforeIndex z hrank) →
      DiagonalRepresents
        (diagonalUnitCoefficients (M.approximationUnits hrank))
        (a.prefixValues
          ((P.boundaryOneBeforeIndex z hrank).val + 2) (by omega)) := by
  intro htrigger
  rcases htrigger with hterminal | ⟨hinternal, hsum⟩
  · have hsucc := P.boundaryOneBeforeIndex_succ_val z hrank
    have hlt := (P.boundaryIndex z).isLt
    omega
  · let S := C.adapted
    let h := C.componentCount_eq
    let Js := S.sourceJordanSucc h
    let Ps := S.sourceProfileSucc h
    let i := P.boundaryIndex z
    have hpositive : 0 < i.val :=
      P.boundaryIndex_pos_of_leftComponentRank_gt_one z hrank
    have hboundary : Ps.boundaryIndex z = P.boundaryIndex z :=
      C.boundaryIndex_eq P z
    have hprevious :
        (⟨i.val - 1, by omega⟩ : Fin (n + 1)) =
          P.boundaryOneBeforeIndex z hrank := by
      apply Fin.ext
      simp only [i, boundaryOneBeforeIndex]
    have hcurrent :
        (⟨(P.boundaryOneBeforeIndex z hrank).val + 1,
          hinternal⟩ : Fin (n + 1)) = i := by
      apply Fin.ext
      exact P.boundaryOneBeforeIndex_succ_val z hrank
    have hsum' : 2 * (ramificationIndex K : ℚ) <
        a.alphaValue ⟨i.val - 1, by omega⟩ + a.alphaValue i := by
      rw [hprevious, ← hcurrent]
      exact hsum
    rcases S.internalTrigger_has_adjacentContainment h i hpositive hsum' with
      ⟨z0, hindex, _hcontainment⟩ | ⟨z0, hindex, hcontainment⟩
    · have hvalue : (Ps.boundaryIndex z0).val + 1 =
          (Ps.boundaryIndex z).val := by
        rw [hboundary]
        exact hindex.symm
      have hz0lt : z0 < z := by
        rcases lt_trichotomy z0 z with hlt | heq | hgt
        · exact hlt
        · subst z0
          omega
        · have hb := boundaryIndex_strictMono Ps hgt
          omega
      have hadjacent : z0.val + 1 = z.val := by
        by_contra hne
        have hgap : z0.val + 1 < z.val := by omega
        let middle : Fin t := ⟨z0.val + 1, by omega⟩
        have hleft : z0 < middle := by
          change z0.val < z0.val + 1
          omega
        have hright : middle < z := by
          change z0.val + 1 < z.val
          exact hgap
        have hb₁ := boundaryIndex_strictMono Ps hleft
        have hb₂ := boundaryIndex_strictMono Ps hright
        omega
      let c : Fin (t + 1) :=
        Lattice.JordanDecomposition.boundaryLeftIndex z
      have hrankS : Js.componentRank c = 1 := by
        have hprev := Ps.boundaryIndex_succ_val_eq_componentRankPrefix z0
        have hcurr := Ps.boundaryIndex_succ_val_eq_componentRankPrefix z
        change (Ps.boundaryIndex z0).val + 1 =
          ∑ k ∈ Finset.Iio
            (Lattice.JordanDecomposition.boundaryRightIndex z0),
              Js.componentRank k at hprev
        change (Ps.boundaryIndex z).val + 1 =
          ∑ k ∈ Finset.Iio
            (Lattice.JordanDecomposition.boundaryRightIndex z),
              Js.componentRank k at hcurr
        have hcprev :
            Lattice.JordanDecomposition.boundaryRightIndex z0 = c := by
          apply Fin.ext
          change z0.val + 1 = z.val
          exact hadjacent
        have hIio : Finset.Iio
            (Lattice.JordanDecomposition.boundaryRightIndex z) =
          insert c (Finset.Iio
            (Lattice.JordanDecomposition.boundaryRightIndex z0)) := by
          ext k
          simp only [Finset.mem_Iio, Finset.mem_insert]
          change (k.val < z.val + 1 ↔ k = c ∨ k.val < z0.val + 1)
          constructor
          · intro hk
            by_cases heq : k.val = z.val
            · exact Or.inl (Fin.ext heq)
            · exact Or.inr (by omega)
          · rintro (rfl | hk)
            · simp [c, Lattice.JordanDecomposition.boundaryLeftIndex]
            · omega
        have hnot : c ∉ Finset.Iio
            (Lattice.JordanDecomposition.boundaryRightIndex z0) := by
          simp only [Finset.mem_Iio, not_lt]
          rw [hcprev]
        rw [hIio, Finset.sum_insert hnot] at hcurr
        omega
      have hrankSgt : 1 < Js.componentRank c := by
        have hrs := C.sameType.componentRank_eq c
        rw [C.sameType.indexEquiv_apply_eq_self] at hrs
        rw [← hrs]
        exact hrank
      omega
    · have hz0 : z0 = z := by
        apply (boundaryIndex_strictMono Ps).injective
        apply Fin.ext
        rw [hboundary]
        exact hindex.symm
      subst z0
      have hrep :=
        C.oneBefore_rightRepresentation_of_conditionIII_reindexed
          P z A hA M hrank (by
            rw [C.sameType.fundamentalIdeal_eq z,
              C.sameType.fourNormOverWeightIdeal_eq
                (Lattice.JordanDecomposition.boundaryLeftIndex z)]
            exact hcontainment)
      exact BONG.GoodBONG.targetPrefixRepresents_cast
        (diagonalUnitCoefficients (M.approximationUnits hrank)) a
        (by
          have hsucc := P.boundaryOneBeforeIndex_succ_val z hrank
          omega) hrep

omit [DyadicDiscriminantClassLaws K] in
set_option maxHeartbeats 0 in
theorem boundaryOneBeforeDiagonalUnits_isPrefixApproximation
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    (a : BONG.GoodBONG q L (n + 2))
    (W : Lattice.WeakJordanDecomposition q L (t + 1))
    (hW : W.HasImproperEvenRank)
    (hstrict : StrictMono (fun i ↦ ordUnit K (W.scaleGenerator i)))
    (P : JordanOrderProfileWitness a.toBONG (W.toJordan hstrict))
    (z : Fin t) (A : Kˣ)
    (hA : Lattice.IsNormGeneratorValue q
      ((W.toJordan hstrict).fundamentalLattice
        (Lattice.JordanDecomposition.boundaryLeftIndex z)) A)
    (M : BoundaryOneBeforeModel P z A)
    (hrank : 1 < (W.toJordan hstrict).componentRank
      (Lattice.JordanDecomposition.boundaryLeftIndex z)) :
    a.IsPrefixApproximation
      ((P.boundaryOneBeforeIndex z hrank).val + 1)
      (diagonalUnitDeterminant (M.approximationUnits hrank)) := by
  let J := W.toJordan hstrict
  let p : Fin (t + 1) :=
    Lattice.JordanDecomposition.boundaryLeftIndex z
  let w := BONG.WeakJordanOrderProfileWitness.ofStrict W hstrict P
  let Cb := w.jordanBlockCoordinates hW p
  have hstop : Cb.stop = (P.boundaryIndex z).val + 1 := by
    change w.componentStart p + finrank K (W.component p).carrier =
      (P.boundaryIndex z).val + 1
    have hb := P.boundaryIndex_succ_val_eq_componentRankPrefix z
    change (P.boundaryIndex z).val + 1 =
      ∑ k ∈ Finset.Iio
        (Lattice.JordanDecomposition.boundaryRightIndex z),
          finrank K (W.component k).carrier at hb
    have hsum :
        (∑ k ∈ Finset.Iio
          (Lattice.JordanDecomposition.boundaryRightIndex z),
            finrank K (W.component k).carrier) =
          w.componentStart p + finrank K (W.component p).carrier := by
      let ri : Fin (t + 1) :=
        Lattice.JordanDecomposition.boundaryRightIndex z
      have hIio : Finset.Iio ri = insert p (Finset.Iio p) := by
        ext k
        simp only [Finset.mem_Iio, Finset.mem_insert]
        change (k.val < z.val + 1 ↔ k = p ∨ k.val < z.val)
        constructor
        · intro hk
          by_cases heq : k.val = z.val
          · exact Or.inl (Fin.ext heq)
          · exact Or.inr (by omega)
        · rintro (rfl | hk)
          · simp [p, Lattice.JordanDecomposition.boundaryLeftIndex]
          · omega
      rw [hIio, Finset.sum_insert (by simp)]
      change finrank K (W.component p).carrier + w.componentStart p = _
      omega
    omega
  have hrank' : 2 ≤ J.componentRank p := by
    change 2 ≤ (W.toJordan hstrict).componentRank
      (Lattice.JordanDecomposition.boundaryLeftIndex z)
    omega
  have hbaseRaw :=
    BONG.WeakJordanOrderProfileWitness.corollary33_prescribedPrefixApproximation
      a W hW hstrict P p A hA hrank'
  let dP : Kˣ :=
    (J.toOrthogonalDecomposition.prefixQuadraticSublattice
      (z.val + 1)).refinedDeterminantUnit
  have hbase : a.IsPrefixApproximation (P.boundaryIndex z).val
      (A * dP) := by
    change a.IsPrefixApproximation (Cb.stop - 1)
      (A * (J.toOrthogonalDecomposition.prefixQuadraticSublattice
        (p.val + 1)).refinedDeterminantUnit) at hbaseRaw
    have hpval : p.val + 1 = z.val + 1 := by rfl
    rw [hstop, hpval] at hbaseRaw
    have hindex : (P.boundaryIndex z).val + 1 - 1 =
        (P.boundaryIndex z).val := by omega
    rw [hindex] at hbaseRaw
    simpa only [dP] using hbaseRaw
  obtain ⟨u, hu⟩ :=
    M.approximationUnits_eq_line_mul_refinedDeterminant_mul_square hrank
  change a.IsPrefixApproximation
    ((P.boundaryOneBeforeIndex z hrank).val + 1)
    (diagonalUnitDeterminant (M.approximationUnits hrank))
  rw [hu]
  apply (a.isPrefixApproximation_mul_square_iff
    ((P.boundaryOneBeforeIndex z hrank).val + 1) (A * dP) u).2
  have hindex := P.boundaryOneBeforeIndex_succ_val z hrank
  simpa only [hindex] using hbase

set_option maxHeartbeats 0 in
/-- Beli (2019), Lemma 3.4(iii): one place before a full Jordan boundary,
the complement of a represented norm-generator line is a right space
approximation. -/
theorem beli2019Lemma34_iii
    [Beli2006AlphaLaws.{u, v} K] [BeliLemma47Laws.{u, v} K]
    (a : BONG.GoodBONG q L (n + 2))
    (W : Lattice.WeakJordanDecomposition q L (t + 1))
    (hW : W.HasImproperEvenRank)
    (hstrict : StrictMono (fun i ↦ ordUnit K (W.scaleGenerator i)))
    (P : JordanOrderProfileWitness a.toBONG (W.toJordan hstrict))
    (z : Fin t) (A : Kˣ)
    (hA : Lattice.IsNormGeneratorValue q
      ((W.toJordan hstrict).fundamentalLattice
        (Lattice.JordanDecomposition.boundaryLeftIndex z)) A)
    (M : BoundaryOneBeforeModel P z A)
    (hrank : 1 < (W.toJordan hstrict).componentRank
      (Lattice.JordanDecomposition.boundaryLeftIndex z)) :
    a.IsRightSpaceApproximation (P.boundaryOneBeforeIndex z hrank)
      (M.approximationUnits hrank) := by
  let J := W.toJordan hstrict
  let C := PrescribedJordanComparison.ofProfile a J
  constructor
  · exact boundaryOneBeforeDiagonalUnits_isPrefixApproximation
      a W hW hstrict P z A hA M hrank
  · exact C.oneBefore_rightRepresentation P z A hA M hrank

end PrescribedJordanComparison

end BONG.JordanOrderProfileWitness

end Bong
