import Bong.Bong.Beli2019Lemma35
import Bong.Bong.Beli2009ConcreteJordanChain
import Bong.Bong.Beli2009JordanEndpointAmalgamation
import Bong.Bong.Beli2009RepresentationBridge
import Bong.Bong.DiagonalSquareIsometry

namespace Bong

open Dyadic Module
open BONG.GoodBONG

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V}

namespace BONG

/-- The binary construction in Beli (2019), Lemma 3.7(iv): a represented
norm-generator value in a modular binary lattice has a complementary
norm-generator coefficient in the same diagonal space. -/
structure BinaryNormGeneratorComplementData
    (q : QuadraticSpace K V) (L : Lattice K V)
    (scale A : Kˣ) where
  second : Kˣ
  second_isNormGeneratorValue :
    Lattice.IsNormGeneratorValue q L second
  diagonalIsometry :
    QuadraticSpace.Isometry
      (QuadraticSpace.finiteDiagonal
        (diagonalUnitCoefficients ![A, second])
        (QuadraticSpace.diagonalUnitCoefficients_ne_zero ![A, second])) q

set_option maxHeartbeats 0 in
noncomputable def BinaryNormGeneratorComplementData.ofQuadraticValue
    (scale A : Kˣ)
    (hmodular : Lattice.IsModular q L scale)
    (hrank : finrank K V = 2)
    (hA : Lattice.IsNormGeneratorValue q L A)
    (hvalue : (A : K) ∈ Lattice.quadraticValueSet q L) :
    BinaryNormGeneratorComplementData q L scale A := by
  let hexists := (Lattice.mem_quadraticValueSet_iff q L (A : K)).1 hvalue
  let x := Classical.choose hexists
  have hxmem : x ∈ L := (Classical.choose_spec hexists).1
  have hxvalue : q.quadratic x = (A : K) :=
    (Classical.choose_spec hexists).2
  have hxgenerator : Lattice.IsNormGenerator q L x := by
    refine ⟨hxmem, ?_⟩
    rw [hxvalue]
    exact hA.2
  have hxanisotropic : q.IsAnisotropic x := by
    unfold QuadraticSpace.IsAnisotropic
    rw [hxvalue]
    exact Units.ne_zero A
  let b : BONG V q L 2 :=
    BONG.ofNormGeneratorBinary q L x hxgenerator hxanisotropic hrank
  let second : Kˣ := b.modularTerminalNormValue scale
  have hsecondGenerator : Lattice.IsNormGeneratorValue q L second :=
    b.modularTerminalNormValue_isNormGeneratorValue scale hmodular
  have hzero : b.valueUnit 0 = A := by
    apply Units.ext
    change b.value 0 = (A : K)
    rw [b.value_zero_eq_quadratic_head,
      BONG.head_ofNormGeneratorBinary q L x hxgenerator hxanisotropic hrank,
      hxvalue]
  let c : Kˣ := uniformizerPowerUnit K (b.order 0 - ordUnit K scale)
  have hpower : uniformizerPowerUnit K
      (2 * b.order 0 - 2 * ordUnit K scale) = c ^ 2 := by
    change uniformizerUnit K ^ (2 * b.order 0 - 2 * ordUnit K scale) =
      (uniformizerUnit K ^ (b.order 0 - ordUnit K scale)) ^ 2
    rw [show 2 * b.order 0 - 2 * ordUnit K scale =
      (b.order 0 - ordUnit K scale) * (2 : Int) by omega,
      zpow_mul]
    norm_num
    rfl
  have hsecond : second = c ^ 2 * b.valueUnit 1 := by
    simp only [second, BONG.modularTerminalNormValue]
    rw [hpower]
  let desired : Fin 2 → Kˣ := ![A, second]
  let native : Fin 2 → Kˣ := b.valueUnit
  let multipliers : Fin 2 → Kˣ := ![1, c⁻¹]
  have hcoeff : ∀ i, (native i : K) =
      (multipliers i : K) ^ 2 * (desired i : K) := by
    intro i
    fin_cases i
    · change (b.valueUnit 0 : K) = (1 : K) ^ 2 * (A : K)
      rw [hzero]
      simp
    · change (b.valueUnit 1 : K) =
        (((c⁻¹ : Kˣ) : K)) ^ 2 * (second : K)
      rw [hsecond]
      simp only [Units.val_mul, Units.val_pow_eq_pow_val]
      rw [Units.val_inv_eq_inv_val]
      field_simp [Units.ne_zero c]
  have hsquare : (QuadraticSpace.finiteDiagonal
        (diagonalUnitCoefficients desired)
        (QuadraticSpace.diagonalUnitCoefficients_ne_zero desired)).IsIsometric
      (QuadraticSpace.finiteDiagonal
        (diagonalUnitCoefficients native)
        (QuadraticSpace.diagonalUnitCoefficients_ne_zero native)) := by
    apply QuadraticSpace.finiteDiagonal_isIsometric_of_eq_square_mul
      (diagonalUnitCoefficients desired)
      (diagonalUnitCoefficients native)
      (QuadraticSpace.diagonalUnitCoefficients_ne_zero desired)
      (QuadraticSpace.diagonalUnitCoefficients_ne_zero native)
      multipliers
    intro i
    exact hcoeff i
  refine {
    second := second
    second_isNormGeneratorValue := hsecondGenerator
    diagonalIsometry := ?_ }
  have hnative : QuadraticSpace.finiteDiagonal
      (diagonalUnitCoefficients native)
      (QuadraticSpace.diagonalUnitCoefficients_ne_zero native) =
      b.exactDiagonalSpace := rfl
  have hnativeIso : QuadraticSpace.Isometry
      (QuadraticSpace.finiteDiagonal
        (diagonalUnitCoefficients native)
        (QuadraticSpace.diagonalUnitCoefficients_ne_zero native)) q := by
    rw [hnative]
    exact b.exactDiagonalizationIsometry.symm
  simpa only [desired] using hsquare.some.trans hnativeIso

/-- The same binary complement, with the second coefficient transported to
the intrinsic fundamental lattice at the component scale. -/
structure JordanBinaryNormGeneratorComplementData {t : Nat}
    (J : Lattice.JordanDecomposition q L t) (p : Fin t) (A : Kˣ) where
  second : Kˣ
  second_isNormGeneratorValue :
    Lattice.IsNormGeneratorValue q (J.fundamentalLattice p) second
  componentDiagonalIsometry :
    QuadraticSpace.Isometry
      (QuadraticSpace.finiteDiagonal
        (diagonalUnitCoefficients ![A, second])
        (QuadraticSpace.diagonalUnitCoefficients_ne_zero ![A, second]))
      (J.component p).space

set_option maxHeartbeats 0 in
noncomputable def JordanBinaryNormGeneratorComplementData.ofQuadraticValue
    {t : Nat} (J : Lattice.JordanDecomposition q L t) (p : Fin t)
    (A : Kˣ) (hrank : J.componentRank p = 2)
    (heffective : BONG.jordanEffectiveNormOrder J p =
      ordUnit K (J.normGenerator p))
    (hA : Lattice.IsNormGeneratorValue q (J.fundamentalLattice p) A)
    (hvalue : (A : K) ∈ Lattice.quadraticValueSet
      (J.component p).space (J.component p).lattice) :
    JordanBinaryNormGeneratorComplementData J p A := by
  have hAOrderFund : ordUnit K A =
      ordUnit K (J.fundamentalNormGenerator p) := by
    apply (Lattice.principalIdeal_eq_iff_ordUnit_eq
      A (J.fundamentalNormGenerator p)).mp
    exact hA.2.symm.trans (J.fundamentalNormGenerator_spec p).2
  have hAOrderComponent : ordUnit K A =
      ordUnit K (J.normGenerator p) := by
    rw [hAOrderFund, J.fundamentalNormGenerator_order_eq_effective p,
      heffective]
  have hAComponent : Lattice.IsNormGeneratorValue
      (J.component p).space (J.component p).lattice A := by
    constructor
    · rcases (Lattice.mem_quadraticValueSet_iff
        (J.component p).space (J.component p).lattice (A : K)).1 hvalue with
        ⟨x, hxmem, hxvalue⟩
      exact ⟨x, hxmem, 0, Submodule.zero_mem _, by simpa using hxvalue.symm⟩
    · calc
        Lattice.normIdeal (J.component p).space (J.component p).lattice =
            Lattice.principalIdeal (K := K) (J.normGenerator p : K) :=
          J.normIdeal_eq p
        _ = Lattice.principalIdeal (K := K) (A : K) :=
          (Lattice.principalIdeal_eq_iff_ordUnit_eq
            (J.normGenerator p) A).2 hAOrderComponent.symm
  let D := BinaryNormGeneratorComplementData.ofQuadraticValue
    (q := (J.component p).space) (L := (J.component p).lattice)
    (J.scaleGenerator p) A (J.modular p) hrank hAComponent hvalue
  refine {
    second := D.second
    second_isNormGeneratorValue := ?_
    componentDiagonalIsometry := D.diagonalIsometry }
  exact J.isNormGeneratorValue_fundamentalLattice p
    D.second_isNormGeneratorValue heffective

end BONG

end Bong
