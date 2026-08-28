import Bong.Lattice.Omeara9328Necessity
import Bong.Lattice.Omeara9328PrefixTransport
import Bong.QuadraticSpace.Diagonalization

namespace Bong

open Dyadic Module

namespace Lattice.JordanDecomposition

universe u v w

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [DyadicDiscriminantClassLaws K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {L : Lattice K V} {M : Lattice K W} {n : Nat}

noncomputable def ProperPrefixIsometryFamily.mapIsometry
    (J : JordanDecomposition q L (n + 1))
    (f : Lattice.Isometry q r L M) :
    ProperPrefixIsometryFamily J (J.mapIsometry f) where
  isometry i := J.toOrthogonalDecomposition.prefixLatticeIsometry f
    (i.val + 1)

theorem isIsometric_iff_omeara9328Conditions_universe
    (J : JordanDecomposition q L (n + 2))
    (H : JordanDecomposition r M (n + 2))
    (ambient : q.IsIsometric r)
    (F : SameFundamentalType J H) :
    Lattice.IsIsometric q r L M ↔ J.Omeara9328Conditions H := by
  letI : FiniteDimensional K V :=
    L.ambientBasis.finiteDimensional_of_finite
  letI : FiniteDimensional K W :=
    M.ambientBasis.finiteDimensional_of_finite
  let fJ : Lattice.Isometry q q.diagonalModel L
      (Lattice.map q.diagonalizationIsometry.toLinearEquiv L) :=
    Lattice.Isometry.toMap q q.diagonalizationIsometry L
  let fH : Lattice.Isometry r r.diagonalModel M
      (Lattice.map r.diagonalizationIsometry.toLinearEquiv M) :=
    Lattice.Isometry.toMap r r.diagonalizationIsometry M
  let JD := J.mapIsometry fJ
  let HD := H.mapIsometry fH
  let FJ : SameFundamentalType J JD := SameFundamentalType.mapIsometry J fJ
  let FH : SameFundamentalType H HD := SameFundamentalType.mapIsometry H fH
  let FD : SameFundamentalType JD HD := FJ.symm.trans (F.trans FH)
  let ambientD : q.diagonalModel.IsIsometric r.diagonalModel := by
    rcases ambient with ⟨g⟩
    exact ⟨q.diagonalizationIsometry.symm.trans
      (g.trans r.diagonalizationIsometry)⟩
  let PJ : ProperPrefixIsometryFamily J JD :=
    ProperPrefixIsometryFamily.mapIsometry J fJ
  let PH : ProperPrefixIsometryFamily H HD :=
    ProperPrefixIsometryFamily.mapIsometry H fH
  let AJ : FundamentalNormGeneratorChoice J :=
    canonicalFundamentalNormGeneratorChoice J
  let AD : FundamentalNormGeneratorChoice JD := AJ.ofSameFundamentalType FJ
  have hIso : Lattice.IsIsometric q r L M ↔
      Lattice.IsIsometric q.diagonalModel r.diagonalModel
        (Lattice.map q.diagonalizationIsometry.toLinearEquiv L)
        (Lattice.map r.diagonalizationIsometry.toLinearEquiv M) := by
    constructor
    · rintro ⟨g⟩
      exact ⟨fJ.symm.trans (g.trans fH)⟩
    · rintro ⟨g⟩
      exact ⟨fJ.trans (g.trans fH.symm)⟩
  have hConditions : J.Omeara9328Conditions H ↔
      JD.Omeara9328ConditionsWith HD AD := by
    constructor
    · intro h
      have hWith : J.Omeara9328ConditionsWith H
          AJ :=
        (J.omeara9328ConditionsWith_canonical_iff H).2 h
      exact omeara9328ConditionsWith_transport FJ PJ.symm PH AJ hWith
    · intro h
      have hBack := omeara9328ConditionsWith_transport FJ.symm PJ PH.symm
        AD h
      apply (J.omeara9328ConditionsWith_canonical_iff H).1
      simpa only [AD, AJ, FundamentalNormGeneratorChoice.ofSameFundamentalType]
        using hBack
  rw [hIso, hConditions]
  exact isIsometric_iff_omeara9328ConditionsWith JD HD ambientD FD AD

end Lattice.JordanDecomposition

end Bong
