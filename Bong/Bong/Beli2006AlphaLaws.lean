/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2006AlphaP1Proof
import Bong.Bong.Beli2006AlphaP4P6Proof
import Bong.Bong.Beli2006AlphaP7Proof
import Bong.Bong.Beli2006SectionTwo

/-!
# Beli (2006) alpha-property interface

Properties P1 and P4--P7 are proved constructively.  The remaining local
dyadic calculations P2 and P3 are kept in one explicit interface until their
proof module is installed.  This low-level placement lets the 2009 arithmetic
lemmas use the seven properties without importing the 2006 classification
theorem.
-/

namespace Bong

open Dyadic

universe u v

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}

/-- The remaining local dyadic calculations establishing P2 and P3.
This class intentionally has no default instance. -/
class Beli2006AlphaLaws
    (K : Type u) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [DyadicContext K] : Prop where
  properties
    {V : Type v} [AddCommGroup V] [Module K V]
    {q : QuadraticSpace K V} {L : Lattice K V} {n : Nat}
    (b : BONG.GoodBONG q L (n + 1)) :
    b.Beli2006AlphaProperties

namespace BONG.GoodBONG

variable [Beli2006AlphaLaws.{u, v} K]

/-- The still-bundled Beli (2006) alpha properties. -/
theorem beli2006AlphaProperties (b : GoodBONG q L (n + 1)) :
    b.Beli2006AlphaProperties :=
  Beli2006AlphaLaws.properties b

omit [Beli2006AlphaLaws.{u, v} K] in
theorem alpha_p1 (b : GoodBONG q L (n + 1)) : b.SatisfiesAlphaP1 :=
  b.satisfiesAlphaP1_proved

theorem alpha_p2 (b : GoodBONG q L (n + 1)) : b.SatisfiesAlphaP2 :=
  b.beli2006AlphaProperties.p2

theorem alpha_p3 (b : GoodBONG q L (n + 1)) : b.SatisfiesAlphaP3 :=
  b.beli2006AlphaProperties.p3

omit [Beli2006AlphaLaws.{u, v} K] in
theorem alpha_p4 (b : GoodBONG q L (n + 1)) : b.SatisfiesAlphaP4 :=
  b.satisfiesAlphaP4_proved

omit [Beli2006AlphaLaws.{u, v} K] in
theorem alpha_p5 (b : GoodBONG q L (n + 1)) : b.SatisfiesAlphaP5 :=
  b.satisfiesAlphaP5_proved

omit [Beli2006AlphaLaws.{u, v} K] in
theorem alpha_p6 (b : GoodBONG q L (n + 1)) : b.SatisfiesAlphaP6 :=
  b.satisfiesAlphaP6_proved

omit [Beli2006AlphaLaws.{u, v} K] in
theorem alpha_p7 (b : GoodBONG q L (n + 1)) : b.SatisfiesAlphaP7 :=
  b.satisfiesAlphaP7_proved

end BONG.GoodBONG

end Bong
