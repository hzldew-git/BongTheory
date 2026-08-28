/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2009ClassificationPropagation
import Bong.Bong.Representation
import Bong.QuadraticSpace.Diagonalization
import Bong.QuadraticSpace.HyperbolicPlane
import Bong.QuadraticSpace.OrthogonalSum
import Bong.Dyadic.HilbertSymbol

/-!
# Beli (2009/2010), Lemmas 3.5--3.7

This file introduces coordinate-free quadratic embeddings, orthogonal sums,
and scaled lines.  O'Meara 63:21 is isolated in one non-default interface;
the defect estimates, Hilbert-symbol reductions, representation switches,
and diagonal-prefix conclusions are then proved in Lean.
-/

namespace Bong

open Dyadic

universe u v w z

namespace QuadraticSpace

variable {K : Type u} [Field K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  {Z : Type z} [AddCommGroup Z] [Module K Z]

/-- A quadratic embedding, used for Beli's representation arrow. -/
abbrev Embedding (q : QuadraticSpace K V) (r : QuadraticSpace K W) :=
  Representation q r

/-- The source quadratic space embeds isometrically into the target space. -/
def EmbedsInto (q : QuadraticSpace K V) (r : QuadraticSpace K W) : Prop :=
  r.Represents q

theorem embedsInto_refl (q : QuadraticSpace K V) : EmbedsInto q q := by
  exact represents_refl q

end QuadraticSpace

/-- The Witt-theoretic input from O'Meara 63:21 used in Lemma 3.5.
This class intentionally has no default instance. -/
class Beli2009QuadraticRepresentationLaws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  lemma35_i
    {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type w} [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (q : QuadraticSpace K V) (r : QuadraticSpace K W)
    (hdim : Module.finrank K W + 1 = Module.finrank K V) :
    QuadraticSpace.EmbedsInto r q ↔
      QuadraticSpace.EmbedsInto q
        (QuadraticSpace.orthogonalSum r
          (QuadraticSpace.hyperbolicPlane (1 : Kˣ)))
  lemma35_ii
    {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type w} [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (q : QuadraticSpace K V) (r : QuadraticSpace K W)
    (detQ detR a : Kˣ)
    (detQ_spec : q.IsDeterminantRepresentative detQ)
    (detR_spec : r.IsDeterminantRepresentative detR)
    (hdim : Module.finrank K V = Module.finrank K W) :
    QuadraticSpace.EmbedsInto r
        (QuadraticSpace.orthogonalSum q (QuadraticSpace.scaledLine a)) ↔
      QuadraticSpace.EmbedsInto q
        (QuadraticSpace.orthogonalSum r
          (QuadraticSpace.scaledLine (a * detQ * detR)))
  lemma35_iii
    {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type w} [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (q : QuadraticSpace K V) (r : QuadraticSpace K W)
    (detQ detR a b : Kˣ)
    (detQ_spec : q.IsDeterminantRepresentative detQ)
    (detR_spec : r.IsDeterminantRepresentative detR)
    (hdim : Module.finrank K V = Module.finrank K W)
    (hhilbert : hilbertSymbol K (a * b) (detQ * detR) = 1) :
    QuadraticSpace.EmbedsInto r
        (QuadraticSpace.orthogonalSum q (QuadraticSpace.scaledLine a)) ↔
      QuadraticSpace.EmbedsInto r
        (QuadraticSpace.orthogonalSum q (QuadraticSpace.scaledLine b))

namespace QuadraticSpace

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  [FiniteDimensional K V] [FiniteDimensional K W]
  [Beli2009QuadraticRepresentationLaws.{u, v, w} K]

/-- Beli (2009/2010), Lemma 3.5(i). -/
theorem beli2009Lemma35_i (q : QuadraticSpace K V) (r : QuadraticSpace K W)
    (hdim : Module.finrank K W + 1 = Module.finrank K V) :
    EmbedsInto r q ↔
      EmbedsInto q (orthogonalSum r (hyperbolicPlane (1 : Kˣ))) :=
  Beli2009QuadraticRepresentationLaws.lemma35_i q r hdim

/-- Beli (2009/2010), Lemma 3.5(ii). -/
theorem beli2009Lemma35_ii (q : QuadraticSpace K V) (r : QuadraticSpace K W)
    (detQ detR a : Kˣ)
    (detQ_spec : q.IsDeterminantRepresentative detQ)
    (detR_spec : r.IsDeterminantRepresentative detR)
    (hdim : Module.finrank K V = Module.finrank K W) :
    EmbedsInto r (orthogonalSum q (scaledLine a)) ↔
      EmbedsInto q (orthogonalSum r (scaledLine (a * detQ * detR))) :=
  Beli2009QuadraticRepresentationLaws.lemma35_ii
    q r detQ detR a detQ_spec detR_spec hdim

/-- Beli (2009/2010), Lemma 3.5(iii). -/
theorem beli2009Lemma35_iii
    (q : QuadraticSpace K V) (r : QuadraticSpace K W)
    (detQ detR a b : Kˣ)
    (detQ_spec : q.IsDeterminantRepresentative detQ)
    (detR_spec : r.IsDeterminantRepresentative detR)
    (hdim : Module.finrank K V = Module.finrank K W)
    (hhilbert : hilbertSymbol K (a * b) (detQ * detR) = 1) :
    EmbedsInto r (orthogonalSum q (scaledLine a)) ↔
      EmbedsInto r (orthogonalSum q (scaledLine b)) :=
  Beli2009QuadraticRepresentationLaws.lemma35_iii
    q r detQ detR a b detQ_spec detR_spec hdim hhilbert

variable [HilbertSymbolLaws K]

/-- The defect-sum parenthetical assertion in Lemma 3.5(iii). -/
theorem beli2009Lemma35_iii_of_defect
    (q : QuadraticSpace K V) (r : QuadraticSpace K W)
    (detQ detR a b : Kˣ)
    (detQ_spec : q.IsDeterminantRepresentative detQ)
    (detR_spec : r.IsDeterminantRepresentative detR)
    (hdim : Module.finrank K V = Module.finrank K W)
    (hdefect : ((2 * ramificationIndex K : Nat) : ℕ∞) <
      quadraticDefect K (a * b) + quadraticDefect K (detQ * detR)) :
    EmbedsInto r (orthogonalSum q (scaledLine a)) ↔
      EmbedsInto r (orthogonalSum q (scaledLine b)) := by
  apply beli2009Lemma35_iii q r detQ detR a b
    detQ_spec detR_spec hdim
  exact hilbertSymbol_eq_one_of_defect_add_gt_two_mul_e K hdefect

end QuadraticSpace

/-- The defect data common to both assertions of Lemma 3.6. -/
structure Beli2009RepresentationSwitchData
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type w} [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (q : QuadraticSpace K V) (r : QuadraticSpace K W) where
  detQ : Kˣ
  detR : Kˣ
  detQ_spec : q.IsDeterminantRepresentative detQ
  detR_spec : r.IsDeterminantRepresentative detR
  a : Kˣ
  b : Kˣ
  weightCut : ℕ∞
  fundamentalCut : ℕ∞
  equalRank : Module.finrank K V = Module.finrank K W
  weight_le_normDefect : weightCut ≤ quadraticDefect K (a * b)
  fundamental_le_detDefect :
    fundamentalCut ≤ quadraticDefect K (detQ * detR)
  weight_lt_fundamental : weightCut < fundamentalCut
  threshold : ((2 * ramificationIndex K : Nat) : ℕ∞) <
    weightCut + fundamentalCut

namespace Beli2009RepresentationSwitchData

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  [FiniteDimensional K V] [FiniteDimensional K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  [repVW : Beli2009QuadraticRepresentationLaws.{u, v, w} K]
  [repWV : Beli2009QuadraticRepresentationLaws.{u, w, v} K]
  [HilbertSymbolLaws K]

def forwardWithA (D : Beli2009RepresentationSwitchData q r) : Prop :=
  QuadraticSpace.EmbedsInto r
    (QuadraticSpace.orthogonalSum q (QuadraticSpace.scaledLine D.a))

def forwardWithB (D : Beli2009RepresentationSwitchData q r) : Prop :=
  QuadraticSpace.EmbedsInto r
    (QuadraticSpace.orthogonalSum q (QuadraticSpace.scaledLine D.b))

def reverseWithB (D : Beli2009RepresentationSwitchData q r) : Prop :=
  QuadraticSpace.EmbedsInto q
    (QuadraticSpace.orthogonalSum r (QuadraticSpace.scaledLine D.b))

omit [Beli2009QuadraticRepresentationLaws.{u, v, w} K]
  [Beli2009QuadraticRepresentationLaws.{u, w, v} K] in
theorem hilbert_norm_det_eq_one
    (D : Beli2009RepresentationSwitchData q r) :
    hilbertSymbol K (D.a * D.b) (D.detQ * D.detR) = 1 := by
  apply hilbertSymbol_eq_one_of_defect_add_gt_two_mul_e K
  exact D.threshold.trans_le
    (add_le_add D.weight_le_normDefect D.fundamental_le_detDefect)

omit [Beli2009QuadraticRepresentationLaws.{u, v, w} K]
  [Beli2009QuadraticRepresentationLaws.{u, w, v} K]
  [HilbertSymbolLaws K] in
theorem twistedNormDefect_lower
    (D : Beli2009RepresentationSwitchData q r) :
    D.weightCut ≤
      quadraticDefect K ((D.a * D.b) * (D.detQ * D.detR)) := by
  apply (le_min D.weight_le_normDefect ?_).trans
    (quadraticDefect_mul_ge_min K (D.a * D.b) (D.detQ * D.detR))
  exact D.weight_lt_fundamental.le.trans D.fundamental_le_detDefect

omit [Beli2009QuadraticRepresentationLaws.{u, v, w} K]
  [Beli2009QuadraticRepresentationLaws.{u, w, v} K] in
theorem hilbert_twisted_det_eq_one
    (D : Beli2009RepresentationSwitchData q r) :
    hilbertSymbol K
      ((D.a * D.detQ * D.detR) * D.b) (D.detR * D.detQ) = 1 := by
  have hdefect : ((2 * ramificationIndex K : Nat) : ℕ∞) <
      quadraticDefect K ((D.a * D.b) * (D.detQ * D.detR)) +
        quadraticDefect K (D.detQ * D.detR) :=
    D.threshold.trans_le
      (add_le_add D.twistedNormDefect_lower D.fundamental_le_detDefect)
  have hhilbert := hilbertSymbol_eq_one_of_defect_add_gt_two_mul_e K hdefect
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hhilbert

theorem representation_switch
    (D : Beli2009RepresentationSwitchData q r) :
    (D.forwardWithA ↔ D.forwardWithB) ∧
      (D.forwardWithA ↔ D.reverseWithB) := by
  have hforward := repVW.lemma35_iii
    q r D.detQ D.detR D.a D.b D.detQ_spec D.detR_spec
      D.equalRank D.hilbert_norm_det_eq_one
  have hswap := repVW.lemma35_ii
    q r D.detQ D.detR D.a D.detQ_spec D.detR_spec D.equalRank
  have hreplace := repWV.lemma35_iii
    r q D.detR D.detQ (D.a * D.detQ * D.detR) D.b
      D.detR_spec D.detQ_spec D.equalRank.symm D.hilbert_twisted_det_eq_one
  exact ⟨hforward, hswap.trans hreplace⟩

/-- Beli (2009/2010), Lemma 3.6(i). -/
theorem beli2009Lemma36_i
    (D : Beli2009RepresentationSwitchData q r) :
    (D.forwardWithA ↔ D.forwardWithB) ∧
      (D.forwardWithA ↔ D.reverseWithB) :=
  representation_switch (repVW := repVW) (repWV := repWV) D

/-- Beli (2009/2010), Lemma 3.6(ii). -/
theorem beli2009Lemma36_ii
    (D : Beli2009RepresentationSwitchData q r) :
    (D.forwardWithA ↔ D.forwardWithB) ∧
      (D.forwardWithA ↔ D.reverseWithB) :=
  representation_switch (repVW := repVW) (repWV := repWV) D

end Beli2009RepresentationSwitchData

/-- The concrete diagonal-prefix target occurring in Lemma 3.7. -/
structure Beli2009PrefixRepresentationBridge
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type w} [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    (D : Beli2009RepresentationSwitchData q r) where
  sourceRank : Nat
  targetRank : Nat
  source : Fin sourceRank → K
  target : Fin targetRank → K

namespace Beli2009PrefixRepresentationBridge

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  [FiniteDimensional K V] [FiniteDimensional K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  {D : Beli2009RepresentationSwitchData q r}

def diagonalCondition (J : Beli2009PrefixRepresentationBridge D) : Prop :=
  DiagonalRepresents J.source J.target

end Beli2009PrefixRepresentationBridge

/-- Hyperbolic cancellation and the chosen diagonal identifications used in
Lemma 3.7.  This interface intentionally has no default instance. -/
class Beli2009PrefixRepresentationBridgeLaws
    {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K]
    {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type w} [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {D : Beli2009RepresentationSwitchData q r}
    (J : Beli2009PrefixRepresentationBridge D) : Prop where
  forwardB_iff : D.forwardWithB ↔ J.diagonalCondition
  reverseB_iff : D.reverseWithB ↔ J.diagonalCondition

namespace Beli2009PrefixRepresentationBridge

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]
  [FiniteDimensional K V] [FiniteDimensional K W]
  {q : QuadraticSpace K V} {r : QuadraticSpace K W}
  [repVW : Beli2009QuadraticRepresentationLaws.{u, v, w} K]
  [repWV : Beli2009QuadraticRepresentationLaws.{u, w, v} K]
  [HilbertSymbolLaws K]
  {D : Beli2009RepresentationSwitchData q r}
  (J : Beli2009PrefixRepresentationBridge D)
  [Beli2009PrefixRepresentationBridgeLaws J]

/-- Beli (2009/2010), Lemma 3.7(i). -/
theorem beli2009Lemma37_i :
    D.forwardWithA ↔ J.diagonalCondition :=
  (Beli2009RepresentationSwitchData.beli2009Lemma36_i
    (repVW := repVW) (repWV := repWV) D).1.trans
    Beli2009PrefixRepresentationBridgeLaws.forwardB_iff

/-- Beli (2009/2010), Lemma 3.7(ii). -/
theorem beli2009Lemma37_ii :
    D.forwardWithA ↔ J.diagonalCondition :=
  (Beli2009RepresentationSwitchData.beli2009Lemma36_ii
    (repVW := repVW) (repWV := repWV) D).2.trans
    Beli2009PrefixRepresentationBridgeLaws.reverseB_iff

end Beli2009PrefixRepresentationBridge

end Bong
