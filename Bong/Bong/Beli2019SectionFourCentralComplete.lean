/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019SectionFourCentralEqual

/-!
# Beli (2019), Section 4: complete central certificates

This file assembles the four cases in the proof of Theorem 2.1(iii), split
according to whether the two adjacent representation alphas equal their
primed counterparts.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V}
  {L M N : Lattice K V} {n : Nat}

/-- The complete four-case central certificate at one active boundary. -/
theorem sectionFourCentralCertificate
    [Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hab : RepresentationConditions a b le_rfl)
    (hbc : RepresentationConditions b c le_rfl)
    (i : CentralRepresentationIndex (n + 1) (n + 1))
    (htrigger : a.centralAlphaTrigger c i) :
    CentralRepresentationCertificate a b c i := by
  by_cases hneAB : a.representationAlpha b (i.current i.lt_large.le) ≠
      a.representationAlphaPrime b (i.current i.lt_large.le)
  · by_cases hneBC : b.representationAlpha c i.previous ≠
        b.representationAlphaPrime c i.previous
    · exact a.sectionFourCentralCertificate_of_both_alpha_ne_prime
        b c hab hbc i htrigger hneAB hneBC
    · have heqBC : b.representationAlpha c i.previous =
          b.representationAlphaPrime c i.previous := not_ne_iff.mp hneBC
      exact a.sectionFourCentralCertificate_of_current_ne_previous_eq
        b c hab hbc i htrigger hneAB heqBC
  · have heqAB : a.representationAlpha b (i.current i.lt_large.le) =
        a.representationAlphaPrime b (i.current i.lt_large.le) :=
      not_ne_iff.mp hneAB
    by_cases hneBC : b.representationAlpha c i.previous ≠
        b.representationAlphaPrime c i.previous
    · exact a.sectionFourCentralCertificate_of_current_eq_previous_ne
        b c hab hbc i htrigger heqAB hneBC
    · have heqBC : b.representationAlpha c i.previous =
          b.representationAlphaPrime c i.previous := not_ne_iff.mp hneBC
      exact a.sectionFourCentralCertificate_of_both_eq
        b c hab hbc i htrigger heqAB heqBC

/-- All certificates for condition (iii) in Beli's Section 4 transitivity
proof. -/
theorem sectionFourCentralCertificates
    [Beli2006AlphaLaws.{u, v} K]
    [BONGStructuralLaws.{u, v} K]
    [HilbertSymbolLaws K]
    [DiagonalRepresentationParityLaws K]
    (a : GoodBONG q L (n + 1)) (b : GoodBONG q M (n + 1))
    (c : GoodBONG q N (n + 1))
    (hab : RepresentationConditions a b le_rfl)
    (hbc : RepresentationConditions b c le_rfl) :
    SectionFourCentralCertificates a b c where
  certificate i htrigger :=
    a.sectionFourCentralCertificate b c hab hbc i htrigger

end BONG.GoodBONG

end Bong
