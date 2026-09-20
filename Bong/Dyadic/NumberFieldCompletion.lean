/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import Bong.Dyadic.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Finite completions of number fields as local fields

Mathlib constructs the completion of a number field at a nonzero prime and
its complete discrete valuation ring.  This file supplies the remaining
finite-residue-field and local-compactness bridge needed by the concrete BONG
development.

The key point is that the natural map from the number-field integer ring to
the residue field of the completed valuation ring is surjective.  Density
first approximates a completed integer by an element of the number field;
the Dedekind-domain approximation theorem then replaces that element by an
integer with the same residue.
-/

namespace Bong.NumberFieldCompletion

open NumberField IsDedekindDomain Filter
open scoped Topology WithZero

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- The canonical valuation subring used by the general local-compactness
criterion. -/
noncomputable abbrev integerRing
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :=
  Valuation.integer (Valued.v : Valuation (p.adicCompletion K) _)

/-- The number-field integer ring maps into the canonical valuation subring
of the finite completion. -/
noncomputable def integerEmbedding
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    𝓞 K →+* integerRing p :=
  (algebraMap (𝓞 K) (p.adicCompletion K)).codRestrict
    (integerRing p) (fun r => by
      change Valued.v
        ((algebraMap (𝓞 K) K r : K) : p.adicCompletion K) ≤ 1
      rw [IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_coe K p,
        p.valuation_of_algebraMap]
      exact p.intValuation_le_one r)

/-- The residue map from the number-field integer ring to the residue field
of its finite completion. -/
noncomputable def residueMap
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    𝓞 K →+* IsLocalRing.ResidueField (integerRing p) :=
  (IsLocalRing.residue (integerRing p)).comp (integerEmbedding p)

/-- The prime defining the completion lies in the kernel of the completed
residue map. -/
theorem asIdeal_le_ker_residueMap
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    p.asIdeal ≤ RingHom.ker (residueMap p) := by
  intro r hr
  change IsLocalRing.residue (integerRing p) (integerEmbedding p r) = 0
  rw [IsLocalRing.residue_eq_zero_iff]
  apply (Valuation.mem_maximalIdeal_iff
    (v := (Valued.v : Valuation (p.adicCompletion K) _))).2
  change Valued.v ((integerEmbedding p r : integerRing p) :
    p.adicCompletion K) < 1
  change Valued.v ((algebraMap (𝓞 K) K r : K) : p.adicCompletion K) < 1
  rw [IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_coe K p,
    p.valuation_of_algebraMap]
  exact (p.intValuation_lt_one_iff_mem r).2 hr

/-- Every residue class of the completed valuation ring is represented by an
element of the original number-field integer ring. -/
theorem residueMap_surjective
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    Function.Surjective (residueMap p) := by
  intro z
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
  have hnhds :
      {y : p.adicCompletion K | Valued.v (y - (x : p.adicCompletion K)) < 1} ∈
        𝓝 (x : p.adicCompletion K) := by
    rw [Valued.mem_nhds]
    refine ⟨1, ?_⟩
    intro y hy
    exact (Valuation.restrict_lt_iff_lt_embedding
      (Valued.v : Valuation (p.adicCompletion K) _)).1 hy
  obtain ⟨y, hy⟩ := (p.denseRange_algebraMap K).mem_nhds hnhds
  have hyIntegral : p.valuation K y ≤ 1 := by
    rw [← IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_coe K p]
    calc
      Valued.v ((y : K) : p.adicCompletion K) =
          Valued.v
            ((((y : K) : p.adicCompletion K) -
              (x : p.adicCompletion K)) + (x : p.adicCompletion K)) := by
            ring_nf
      _ ≤ max
          (Valued.v
            (((y : K) : p.adicCompletion K) - (x : p.adicCompletion K)))
          (Valued.v (x : p.adicCompletion K)) :=
        Valuation.map_add _ _ _
      _ ≤ 1 := max_le hy.le x.property
  obtain ⟨r, hr⟩ :=
    p.exists_valuation_sub_lt_of_integer hyIntegral 1
  have hr' :
      Valued.v
        (((algebraMap (𝓞 K) K r : K) : p.adicCompletion K) -
          ((y : K) : p.adicCompletion K)) < 1 := by
    rw [show
      (((algebraMap (𝓞 K) K r : K) : p.adicCompletion K) -
          ((y : K) : p.adicCompletion K)) =
        (((algebraMap (𝓞 K) K r - y : K) : p.adicCompletion K)) by
      change
        NumberField.FinitePlace.embedding (K := K) p
            (algebraMap (𝓞 K) K r) -
          NumberField.FinitePlace.embedding (K := K) p y =
        NumberField.FinitePlace.embedding (K := K) p
          (algebraMap (𝓞 K) K r - y)
      exact
        (NumberField.FinitePlace.embedding (K := K) p).map_sub _ _ |>.symm]
    rw [IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_coe K p]
    exact hr
  have htotal :
      Valued.v
        (((algebraMap (𝓞 K) K r : K) : p.adicCompletion K) -
          (x : p.adicCompletion K)) < 1 := by
    calc
      Valued.v
          (((algebraMap (𝓞 K) K r : K) : p.adicCompletion K) -
            (x : p.adicCompletion K)) =
        Valued.v
          (((((algebraMap (𝓞 K) K r : K) : p.adicCompletion K) -
              ((y : K) : p.adicCompletion K)) +
            (((y : K) : p.adicCompletion K) -
              (x : p.adicCompletion K)))) := by
          ring_nf
      _ ≤ max
          (Valued.v
            (((algebraMap (𝓞 K) K r : K) : p.adicCompletion K) -
              ((y : K) : p.adicCompletion K)))
          (Valued.v
            (((y : K) : p.adicCompletion K) -
              (x : p.adicCompletion K))) :=
        Valuation.map_add _ _ _
      _ < 1 := max_lt hr' hy
  refine ⟨r, ?_⟩
  change IsLocalRing.residue (integerRing p) (integerEmbedding p r) =
    IsLocalRing.residue (integerRing p) x
  change Ideal.Quotient.mk
      (IsLocalRing.maximalIdeal (integerRing p)) (integerEmbedding p r) =
    Ideal.Quotient.mk
      (IsLocalRing.maximalIdeal (integerRing p)) x
  rw [Ideal.Quotient.eq]
  apply (Valuation.mem_maximalIdeal_iff
    (v := (Valued.v : Valuation (p.adicCompletion K) _))).2
  change Valued.v
      (((integerEmbedding p r : integerRing p) : p.adicCompletion K) -
        (x : p.adicCompletion K)) < 1
  change Valued.v
      (((algebraMap (𝓞 K) K r : K) : p.adicCompletion K) -
        (x : p.adicCompletion K)) < 1
  exact htotal

/-- The map from the defining residue ring to the completed residue field. -/
noncomputable def residueQuotientMap
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    (𝓞 K ⧸ p.asIdeal) →+*
      IsLocalRing.ResidueField (integerRing p) :=
  Ideal.Quotient.lift p.asIdeal (residueMap p)
    (fun _ hr => asIdeal_le_ker_residueMap p hr)

/-- The defining residue ring surjects onto the completed residue field. -/
theorem residueQuotientMap_surjective
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    Function.Surjective (residueQuotientMap p) := by
  intro z
  obtain ⟨r, rfl⟩ := residueMap_surjective p z
  refine ⟨Ideal.Quotient.mk p.asIdeal r, ?_⟩
  exact Ideal.Quotient.lift_mk p.asIdeal (residueMap p) _

/-- The residue field of a number-field finite completion is finite. -/
noncomputable instance finiteResidueField
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    Finite (IsLocalRing.ResidueField (integerRing p)) := by
  letI : Finite (𝓞 K ⧸ p.asIdeal) :=
    p.asIdeal.finiteQuotientOfFreeOfNeBot p.ne_bot
  exact Finite.of_surjective (residueQuotientMap p)
    (residueQuotientMap_surjective p)

/-- The canonical valuation subring of a finite completion is principal. -/
noncomputable instance integerRingIsPrincipalIdealRing
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    IsPrincipalIdealRing (integerRing p) := by
  rw [(Valuation.integer.integers
      (Valued.v : Valuation (p.adicCompletion K) _)).isPrincipalIdealRing_iff_not_denselyOrdered,
    WithZero.denselyOrdered_set_iff_subsingleton]
  simpa using
    (Valued.v : Valuation (p.adicCompletion K) _).toMonoidWithZeroHom.range_nontrivial

/-- The canonical valuation subring of a finite completion is a DVR. -/
noncomputable instance integerRingIsDiscreteValuationRing
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    IsDiscreteValuationRing (integerRing p) :=
  (Valued.v : Valuation (p.adicCompletion K) _).valuationSubring_isDiscreteValuationRing

/- A number-field finite completion is proper.  The long declaration name in
the general criterion is kept verbatim for auditability. -/
set_option linter.style.longLine false in
noncomputable instance properSpace
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    ProperSpace (p.adicCompletion K) := by
  apply
    (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
      (K := p.adicCompletion K)).2
  exact ⟨inferInstance, inferInstance, finiteResidueField p⟩

/-- A number-field finite completion is locally compact. -/
noncomputable instance locallyCompactSpace
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    LocallyCompactSpace (p.adicCompletion K) := by
  infer_instance

/-- The characteristic-zero structure transported from the dense number
field embedding. -/
noncomputable instance charZero
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    CharZero (p.adicCompletion K) :=
  Algebra.charZero_of_charZero K (p.adicCompletion K)

/-- The valuative relation induced by the canonical completed valuation. -/
noncomputable instance valuativeRel
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    ValuativeRel (p.adicCompletion K) :=
  ValuativeRel.ofValuation
    (Valued.v : Valuation (p.adicCompletion K) _)

/-- The canonical completed valuation is compatible with the induced
valuative relation. -/
noncomputable instance valuationCompatible
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    (Valued.v : Valuation (p.adicCompletion K) _).Compatible :=
  Valuation.Compatible.ofValuation _

/-- The induced valuative relation is nontrivial. -/
noncomputable instance valuativeRelIsNontrivial
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    ValuativeRel.IsNontrivial (p.adicCompletion K) :=
  (ValuativeRel.isNontrivial_iff_isNontrivial
    (Valued.v : Valuation (p.adicCompletion K) _)).2 inferInstance

/-- The existing completion topology is the topology induced by the
canonical valuation. -/
noncomputable instance isValuativeTopology
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    IsValuativeTopology (p.adicCompletion K) :=
  IsValuativeTopology.of_mem_nhds_zero_iff_vle
    (Valued.v : Valuation (p.adicCompletion K) _)
    (Valued.is_topological_valuation (R := p.adicCompletion K) _)

/-- Every finite completion of a number field is a nonarchimedean local
field for its canonical completed valuation. -/
noncomputable instance isNonarchimedeanLocalField
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    IsNonarchimedeanLocalField (p.adicCompletion K) where
  toIsValuativeTopology := isValuativeTopology p
  toLocallyCompactSpace := locallyCompactSpace p
  toIsNontrivial := valuativeRelIsNontrivial p

/-! ## Normalized additive valuation and the dyadic specialization -/

/-- The normalized additive order attached to the canonical multiplicative
valuation. -/
noncomputable def adicOrderValue
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (x : p.adicCompletion K) : WithTop Int := by
  classical
  exact if x = 0 then ⊤
    else ((-(Valued.v x).log : Int) : WithTop Int)

/-- The normalized additive valuation on a number-field finite completion. -/
noncomputable def adicOrder
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    AddValuation (p.adicCompletion K) (WithTop Int) :=
  AddValuation.of (adicOrderValue p)
    (by simp [adicOrderValue])
    (by simp [adicOrderValue])
    (fun x y => by
      classical
      by_cases hx : x = 0
      · subst x
        simp [adicOrderValue]
      by_cases hy : y = 0
      · subst y
        simp [adicOrderValue, hx]
      by_cases hsum : x + y = 0
      · simp [adicOrderValue, hsum]
      simp only [adicOrderValue, if_neg hx, if_neg hy, if_neg hsum]
      norm_cast
      have hvx : Valued.v x ≠ 0 := by simpa using hx
      have hvy : Valued.v y ≠ 0 := by simpa using hy
      have hvsum : Valued.v (x + y) ≠ 0 := by simpa using hsum
      by_cases hxy : Valued.v x ≤ Valued.v y
      · have hlogxy : (Valued.v x).log ≤ (Valued.v y).log :=
          (WithZero.log_le_log hvx hvy).2 hxy
        rw [min_eq_right (neg_le_neg hlogxy)]
        apply neg_le_neg
        apply (WithZero.log_le_log hvsum hvy).2
        simpa [max_eq_right hxy] using Valuation.map_add
          (Valued.v : Valuation (p.adicCompletion K) _) x y
      · have hyx : Valued.v y ≤ Valued.v x := le_of_not_ge hxy
        have hlogyx : (Valued.v y).log ≤ (Valued.v x).log :=
          (WithZero.log_le_log hvy hvx).2 hyx
        rw [min_eq_left (neg_le_neg hlogyx)]
        apply neg_le_neg
        apply (WithZero.log_le_log hvsum hvx).2
        simpa [max_eq_left hyx] using Valuation.map_add
          (Valued.v : Valuation (p.adicCompletion K) _) x y)
    (fun x y => by
      classical
      by_cases hx : x = 0
      · subst x
        simp [adicOrderValue]
      by_cases hy : y = 0
      · subst y
        simp [adicOrderValue, hx]
      have hxy : x * y ≠ 0 := mul_ne_zero hx hy
      simp only [adicOrderValue, if_neg hxy, if_neg hx, if_neg hy]
      norm_cast
      rw [map_mul, WithZero.log_mul]
      · ring
      · simpa using hx
      · simpa using hy)

@[simp]
theorem adicOrder_apply_of_ne_zero
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    {x : p.adicCompletion K} (hx : x ≠ 0) :
    adicOrder p x =
      ((-(Valued.v x).log : Int) : WithTop Int) := by
  simp [adicOrder, adicOrderValue, hx]

/-- The normalized additive valuation induces the canonical valuative
relation on the completion. -/
theorem adicOrderCompatible
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    (AddValuation.toValuation (adicOrder p)).Compatible := by
  constructor
  intro x y
  change Valued.v x ≤ Valued.v y ↔ adicOrder p y ≤ adicOrder p x
  by_cases hx : x = 0
  · subst x
    simp [adicOrder, adicOrderValue]
  by_cases hy : y = 0
  · subst y
    simp [adicOrder, adicOrderValue, hx]
  simp only [adicOrder_apply_of_ne_zero p hx,
    adicOrder_apply_of_ne_zero p hy, WithTop.coe_le_coe,
    neg_le_neg_iff]
  exact (WithZero.log_le_log (by simpa using hx) (by simpa using hy)).symm

/-- A chosen element whose completed multiplicative valuation is
`exp (-1)`. -/
noncomputable def uniformizer
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    p.adicCompletion K :=
  Classical.choose
    (p.valuedAdicCompletion_surjective K (WithZero.exp (-1 : Int)))

@[simp]
theorem valuation_uniformizer
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    Valued.v (uniformizer p) = WithZero.exp (-1 : Int) :=
  Classical.choose_spec
    (p.valuedAdicCompletion_surjective K (WithZero.exp (-1 : Int)))

theorem uniformizer_ne_zero
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    uniformizer p ≠ 0 := by
  intro h
  have hv := valuation_uniformizer p
  rw [h, map_zero] at hv
  exact WithZero.exp_ne_zero hv.symm

@[simp]
theorem adicOrder_uniformizer
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    adicOrder p (uniformizer p) = 1 := by
  rw [adicOrder_apply_of_ne_zero p (uniformizer_ne_zero p),
    valuation_uniformizer]
  norm_num

/-- A prime of the number-field integer ring is dyadic when it contains the
rational integer two. -/
def IsDyadic
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : Prop :=
  (2 : 𝓞 K) ∈ p.asIdeal

/-- At a dyadic prime the normalized additive order of `2` is positive. -/
theorem adicOrder_two_pos
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hp : IsDyadic p) :
    0 < adicOrder p (2 : p.adicCompletion K) := by
  have htwo : (2 : p.adicCompletion K) ≠ 0 := by norm_num
  rw [adicOrder_apply_of_ne_zero p htwo]
  norm_cast
  have hvTwoNe : Valued.v (2 : p.adicCompletion K) ≠ 0 := by
    exact
      ((Valued.v : Valuation (p.adicCompletion K) _).map_eq_zero_iff).not.mpr
        htwo
  have hvTwoLt : Valued.v (2 : p.adicCompletion K) < 1 := by
    calc
      Valued.v (2 : p.adicCompletion K) =
          p.valuation K (2 : K) := by
            rw [show (2 : p.adicCompletion K) =
              ((2 : K) : p.adicCompletion K) by
                symm
                simpa [NumberField.FinitePlace.embedding_apply] using
                  (map_ofNat (NumberField.FinitePlace.embedding (K := K) p) 2)]
            exact
              IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_coe
                K p (2 : K)
      _ = p.intValuation (2 : 𝓞 K) := by
        rw [show (2 : K) = algebraMap (𝓞 K) K (2 : 𝓞 K) by
          symm
          simpa using (map_ofNat (algebraMap (𝓞 K) K) 2)]
        exact p.valuation_of_algebraMap (2 : 𝓞 K)
      _ < 1 := (p.intValuation_lt_one_iff_mem (2 : 𝓞 K)).2 hp
  have hlog : (Valued.v (2 : p.adicCompletion K)).log < 0 := by
    simpa using (WithZero.log_lt_log hvTwoNe (one_ne_zero :
      (1 : WithZero (Multiplicative Int)) ≠ 0)).2 hvTwoLt
  omega

/-- A dyadic finite prime gives the concrete `DyadicContext` required by the
BONG development. -/
@[reducible]
noncomputable def dyadicContext
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hp : IsDyadic p) : DyadicContext (p.adicCompletion K) where
  toIsNonarchimedeanLocalField := isNonarchimedeanLocalField p
  ord := adicOrder p
  ordCompatible := adicOrderCompatible p
  uniformizer := uniformizer p
  ordUniformizer := adicOrder_uniformizer p
  ordTwoPos := adicOrder_two_pos p hp

end Bong.NumberFieldCompletion
