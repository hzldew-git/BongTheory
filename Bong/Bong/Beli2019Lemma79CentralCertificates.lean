/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Beli2019RepresentationTransitivity
import Bong.Bong.Beli2019CanonicalApproximation
import Bong.Bong.Beli2019Lemma218
import Bong.Bong.DiagonalRepresentationParity

/-!
# Beli (2019), Lemma 7.9(iii): the two Lemma 1.5 certificates

The proof of condition 2.1(iii) in Lemma 7.9 starts by applying Lemma 1.5
in one of two ways.  In the first diagram both preceding prefixes are
represented by the same `a`-prefix.  In the second diagram the `b`-prefix is
represented by the next `a`-prefix.  A displayed Hilbert symbol closes the
remaining edge in either four-space cycle.

This file packages exactly those two geometric arguments.  It contains no
Section 7 arithmetic: the ten cases in the paper only have to construct one
of the two explicit certificates below.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.GoodBONG

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  [DiagonalRepresentationParityLaws K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L M N : Lattice K V} {n : Nat}

/-- The two four-space diagrams used at one boundary in the proof of
Lemma 7.9(iii).  Products are written with the same prefix convention as
the paper: `prefixProduct i` is `a_(1,i)`. -/
inductive Lemma79CentralCertificate
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (i : CentralRepresentationIndex (n + 2) (n + 2)) : Prop
  /-- Lemma 1.5(i): use the two representations into the `i`-th
  `a`-prefix and the Hilbert symbol
  `(a_(1,i)b_(1,i), b_(1,i-1)c_(1,i-1))`. -/
  | first
      (middlePrevious : DiagonalRepresents
        (b.prefixValues (i.val - 1) (by
          have := i.lt_large
          omega))
        (a.prefixValues i.val i.lt_large.le))
      (sourcePrevious : DiagonalRepresents
        (c.prefixValues (i.val - 1) (by
          have := i.lt_large
          omega))
        (a.prefixValues i.val i.lt_large.le))
      (hilbert : hilbertSymbol K
        (a.prefixProduct i.val * b.prefixProduct i.val)
        (b.prefixProduct (i.val - 1) * c.prefixProduct (i.val - 1)) = 1)
  /-- Lemma 1.5(ii): use the `i`-th `b`-prefix inside the next
  `a`-prefix, the preceding `c`-prefix inside the current `a`-prefix, and
  the Hilbert symbol
  `(a_(1,i)b_(1,i), -a_(1,i+1)c_(1,i-1))`. -/
  | second
      (middleCurrent : DiagonalRepresents
        (b.prefixValues i.val i.lt_large.le)
        (a.prefixValues (i.val + 1) (Nat.succ_le_of_lt i.lt_large)))
      (sourcePrevious : DiagonalRepresents
        (c.prefixValues (i.val - 1) (by
          have := i.lt_large
          omega))
        (a.prefixValues i.val i.lt_large.le))
      (hilbert : hilbertSymbol K
        (a.prefixProduct i.val * b.prefixProduct i.val)
        (-a.prefixProduct (i.val + 1) * c.prefixProduct (i.val - 1)) = 1)

namespace Lemma79CentralCertificate

/-- Construct the first Lemma 1.5 certificate from the two capped defects
used in the paper.  The uncapped defects dominate them, so the generic
dyadic defect-sum criterion supplies the displayed Hilbert symbol. -/
theorem first_of_truncatedDefects
    [HilbertSymbolLaws K]
    {a : GoodBONG q L (n + 2)} {b : GoodBONG q M (n + 2)}
    {c : GoodBONG q N (n + 2)}
    {i : CentralRepresentationIndex (n + 2) (n + 2)}
    (middlePrevious : DiagonalRepresents
      (b.prefixValues (i.val - 1) (by
        have := i.lt_large
        omega))
      (a.prefixValues i.val i.lt_large.le))
    (sourcePrevious : DiagonalRepresents
      (c.prefixValues (i.val - 1) (by
        have := i.lt_large
        omega))
      (a.prefixValues i.val i.lt_large.le))
    (hdefects :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        a.truncatedPrefixDefect b 1 i.val i.val +
          b.truncatedPrefixDefect c 1 (i.val - 1) (i.val - 1)) :
    Lemma79CentralCertificate a b c i := by
  refine Lemma79CentralCertificate.first middlePrevious sourcePrevious ?_
  apply hilbertSymbol_eq_one_of_defectOrder_add_gt_two_mul_e
  apply hdefects.trans_le
  apply add_le_add
  · simpa only [one_mul] using
      (a.truncatedPrefixDefect_le_defect b 1 i.val i.val)
  · simpa only [one_mul] using
      (b.truncatedPrefixDefect_le_defect c 1
        (i.val - 1) (i.val - 1))

/-- Construct the second Lemma 1.5 certificate from the capped equal-prefix
defect for `(a,b)` and the current v2 defect for `(a,c)`. -/
theorem second_of_truncatedDefects
    [HilbertSymbolLaws K]
    {a : GoodBONG q L (n + 2)} {b : GoodBONG q M (n + 2)}
    {c : GoodBONG q N (n + 2)}
    {i : CentralRepresentationIndex (n + 2) (n + 2)}
    (middleCurrent : DiagonalRepresents
      (b.prefixValues i.val i.lt_large.le)
      (a.prefixValues (i.val + 1) (Nat.succ_le_of_lt i.lt_large)))
    (sourcePrevious : DiagonalRepresents
      (c.prefixValues (i.val - 1) (by
        have := i.lt_large
        omega))
      (a.prefixValues i.val i.lt_large.le))
    (hdefects :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        a.truncatedPrefixDefect b 1 i.val i.val +
          a.centralCurrentDefect c i) :
    Lemma79CentralCertificate a b c i := by
  refine Lemma79CentralCertificate.second middleCurrent sourcePrevious ?_
  apply hilbertSymbol_eq_one_of_defectOrder_add_gt_two_mul_e
  apply hdefects.trans_le
  apply add_le_add
  · simpa only [one_mul] using
      (a.truncatedPrefixDefect_le_defect b 1 i.val i.val)
  · unfold centralCurrentDefect
    simpa only [neg_one_mul] using
      (a.truncatedPrefixDefect_le_defect c (-1)
        (i.val + 1) (i.val - 1))

/-- The first diagram when its two prefix representations are supplied by
condition (iii) for `(a,b)` and `(a,c)` at the same boundary. -/
theorem first_of_conditions
    [HilbertSymbolLaws K]
    {a : GoodBONG q L (n + 2)} {b : GoodBONG q M (n + 2)}
    {c : GoodBONG q N (n + 2)}
    {i : CentralRepresentationIndex (n + 2) (n + 2)}
    (hab : RepresentationConditions a b le_rfl)
    (hac : RepresentationConditions a c le_rfl)
    (htriggerAB : a.centralAlphaTrigger b i)
    (htriggerAC : a.centralAlphaTrigger c i)
    (hdefects :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        a.truncatedPrefixDefect b 1 i.val i.val +
          b.truncatedPrefixDefect c 1 (i.val - 1) (i.val - 1)) :
    Lemma79CentralCertificate a b c i :=
  first_of_truncatedDefects
    (hab.centralRepresentations i htriggerAB)
    (hac.centralRepresentations i htriggerAC) hdefects

/-- The second diagram when condition (iii) for `(a,b)` is activated at
the following boundary and condition (iii) for `(a,c)` at the current one. -/
theorem second_of_conditions
    [HilbertSymbolLaws K]
    {a : GoodBONG q L (n + 2)} {b : GoodBONG q M (n + 2)}
    {c : GoodBONG q N (n + 2)}
    {i : CentralRepresentationIndex (n + 2) (n + 2)}
    (hab : RepresentationConditions a b le_rfl)
    (hac : RepresentationConditions a c le_rfl)
    (j : CentralRepresentationIndex (n + 2) (n + 2))
    (hj : j.val = i.val + 1)
    (htriggerABNext : a.centralAlphaTrigger b j)
    (htriggerAC : a.centralAlphaTrigger c i)
    (hdefects :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
        a.truncatedPrefixDefect b 1 i.val i.val +
          a.centralCurrentDefect c i) :
    Lemma79CentralCertificate a b c i := by
  have hmiddle := hab.centralRepresentations j htriggerABNext
  have hjPrevious : j.val - 1 = i.val := by omega
  have hmiddle' : DiagonalRepresents
      (b.prefixValues i.val i.lt_large.le)
      (a.prefixValues (i.val + 1) (Nat.succ_le_of_lt i.lt_large)) := by
    exact prefixRepresents_cast b a hjPrevious hj hmiddle
  exact second_of_truncatedDefects hmiddle'
    (hac.centralRepresentations i htriggerAC) hdefects

/-- The common first step of the ten cases in Lemma 7.9(iii).  Lemma 2.18
splits the active `(b,c)` trigger into exactly the two Lemma 1.5 diagrams.
The remaining hypotheses are the profile-specific facts proved in the
numbered cases: the comparison cap `beta_i` is visible in the `(a,b)`
equal-prefix defect, and the required `(a,b)` and `(a,c)` central triggers
are active. -/
theorem of_lemma218_target
    [Beli2006AlphaLaws.{u, v} K]
    [HilbertSymbolLaws K]
    {a : GoodBONG q L (n + 2)} {b : GoodBONG q M (n + 2)}
    {c : GoodBONG q N (n + 2)}
    (hab : RepresentationConditions a b le_rfl)
    (hac : RepresentationConditions a c le_rfl)
    (hdefectBC : b.RepresentationDefectCondition c)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (htriggerBC : b.centralAlphaTrigger c i)
    (hbeta : b.prefixAlphaCap i.val ≤
      a.truncatedPrefixDefect b 1 i.val i.val)
    (hcurrentTransfer : b.centralCurrentDefect c i ≤
      a.centralCurrentDefect c i)
    (htriggerAB : a.centralAlphaTrigger b i)
    (htriggerAC : a.centralAlphaTrigger c i)
    (j : CentralRepresentationIndex (n + 2) (n + 2))
    (hj : j.val = i.val + 1)
    (htriggerABNext : a.centralAlphaTrigger b j) :
    Lemma79CentralCertificate a b c i := by
  rcases b.beli2019Lemma218_target c hdefectBC i htriggerBC with
    hprevious | hcurrent
  · apply first_of_conditions hab hac htriggerAB htriggerAC
    apply hprevious.trans_le
    apply add_le_add hbeta
    have hraw := hdefectBC i.previous
    rw [b.coe_representationAlphaValue c i.previous] at hraw
    exact hraw
  · apply second_of_conditions hab hac j hj htriggerABNext htriggerAC
    exact hcurrent.trans_le (add_le_add hbeta hcurrentTransfer)

/-- A logically sharp version of `of_lemma218_target`.  The two `(a,b)`
central triggers are requested only in the corresponding alternative of
Lemma 2.18, exactly as in cases 1--10 of the paper. -/
theorem of_lemma218_target_by_cases
    [Beli2006AlphaLaws.{u, v} K]
    [HilbertSymbolLaws K]
    {a : GoodBONG q L (n + 2)} {b : GoodBONG q M (n + 2)}
    {c : GoodBONG q N (n + 2)}
    (hab : RepresentationConditions a b le_rfl)
    (hac : RepresentationConditions a c le_rfl)
    (hdefectBC : b.RepresentationDefectCondition c)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (htriggerBC : b.centralAlphaTrigger c i)
    (hbeta : b.prefixAlphaCap i.val ≤
      a.truncatedPrefixDefect b 1 i.val i.val)
    (hcurrentTransfer : b.centralCurrentDefect c i ≤
      a.centralCurrentDefect c i)
    (htriggerAC : a.centralAlphaTrigger c i)
    (j : CentralRepresentationIndex (n + 2) (n + 2))
    (hj : j.val = i.val + 1)
    (htriggerAB :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
          b.prefixAlphaCap i.val + b.representationAlpha c i.previous →
        a.centralAlphaTrigger b i)
    (htriggerABNext :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
          b.prefixAlphaCap i.val + b.centralCurrentDefect c i →
        a.centralAlphaTrigger b j) :
    Lemma79CentralCertificate a b c i := by
  rcases b.beli2019Lemma218_target c hdefectBC i htriggerBC with
    hprevious | hcurrent
  · apply first_of_conditions hab hac (htriggerAB hprevious) htriggerAC
    apply hprevious.trans_le
    apply add_le_add hbeta
    have hraw := hdefectBC i.previous
    rw [b.coe_representationAlphaValue c i.previous] at hraw
    exact hraw
  · apply second_of_conditions hab hac j hj
      (htriggerABNext hcurrent) htriggerAC
    exact hcurrent.trans_le (add_le_add hbeta hcurrentTransfer)

/-- The terminal form of the Lemma 2.18 split.  In the second alternative
the `(i+1)`-st source prefix is the complete ambient BONG, so the middle
prefix representation follows from the concrete full-BONG coordinate
change instead of a nonexistent next central index. -/
theorem of_lemma218_target_endpoint
    [Beli2006AlphaLaws.{u, v} K]
    [HilbertSymbolLaws K]
    {a : GoodBONG q L (n + 2)} {b : GoodBONG q M (n + 2)}
    {c : GoodBONG q N (n + 2)}
    (hab : RepresentationConditions a b le_rfl)
    (hac : RepresentationConditions a c le_rfl)
    (hdefectBC : b.RepresentationDefectCondition c)
    (i : CentralRepresentationIndex (n + 2) (n + 2))
    (hfull : i.val + 1 = n + 2)
    (htriggerBC : b.centralAlphaTrigger c i)
    (hbeta : b.prefixAlphaCap i.val ≤
      a.truncatedPrefixDefect b 1 i.val i.val)
    (hcurrentTransfer : b.centralCurrentDefect c i ≤
      a.centralCurrentDefect c i)
    (htriggerAC : a.centralAlphaTrigger c i)
    (htriggerAB :
      (((2 * ramificationIndex K : Nat) : ℚ) : WithTop ℚ) <
          b.prefixAlphaCap i.val + b.representationAlpha c i.previous →
        a.centralAlphaTrigger b i) :
    Lemma79CentralCertificate a b c i := by
  rcases b.beli2019Lemma218_target c hdefectBC i htriggerBC with
    hprevious | hcurrent
  · apply first_of_conditions hab hac (htriggerAB hprevious) htriggerAC
    apply hprevious.trans_le
    apply add_le_add hbeta
    have hraw := hdefectBC i.previous
    rw [b.coe_representationAlphaValue c i.previous] at hraw
    exact hraw
  · have hprefix := b.prefixValues_represents_of_le
        i.val (n + 2) i.lt_large.le le_rfl
    have hfullRepresentation := hprefix.trans (b.fullPrefix_represents a)
    have hmiddle : DiagonalRepresents
        (b.prefixValues i.val i.lt_large.le)
        (a.prefixValues (i.val + 1) (Nat.succ_le_of_lt i.lt_large)) :=
      prefixRepresents_cast b a rfl hfull.symm hfullRepresentation
    apply second_of_truncatedDefects hmiddle
      (hac.centralRepresentations i htriggerAC)
    exact hcurrent.trans_le (add_le_add hbeta hcurrentTransfer)

/-- Either certificate produces the prefix representation required by
condition 2.1(iii) for the pair `(b,c)`. -/
theorem represents
    {a : GoodBONG q L (n + 2)} {b : GoodBONG q M (n + 2)}
    {c : GoodBONG q N (n + 2)}
    {i : CentralRepresentationIndex (n + 2) (n + 2)}
    (certificate : Lemma79CentralCertificate a b c i) :
    DiagonalRepresents
      (c.prefixValues (i.val - 1) (by
        have := i.lt_large
        omega))
      (b.prefixValues i.val i.lt_large.le) := by
  cases certificate with
  | first middlePrevious sourcePrevious hilbert =>
      let au := a.prefixValueUnits i.val i.lt_large.le
      let bu := b.prefixValueUnits i.val i.lt_large.le
      let cu := c.prefixValueUnits (i.val - 1) (by
        have := i.lt_large
        omega)
      have hmiddle : DiagonalRepresents
          (diagonalUnitCoefficients
            (diagonalUnitTake bu (i.val - 1) (by
              have := i.one_lt
              omega)))
          (diagonalUnitCoefficients au) := by
        simpa only [au, bu, diagonalUnitTake_prefixValueUnits,
          diagonalUnitCoefficients_prefixValueUnits] using middlePrevious
      have hsource : DiagonalRepresents
          (diagonalUnitCoefficients cu)
          (diagonalUnitCoefficients au) := by
        simpa only [au, cu, diagonalUnitCoefficients_prefixValueUnits] using
          sourcePrevious
      have hhilbert : hilbertSymbol K
          (diagonalUnitDeterminant au * diagonalUnitDeterminant bu)
          (diagonalUnitDeterminant
              (diagonalUnitTake bu (i.val - 1) (by
                have := i.one_lt
                omega)) *
            diagonalUnitDeterminant cu) = 1 := by
        simpa only [au, bu, cu, diagonalUnitTake_prefixValueUnits,
          diagonalUnitDeterminant_prefixValueUnits] using hilbert
      have hcycle := DiagonalRepresentationParityLaws.caseI
        au bu cu rfl (by
          have := i.one_lt
          omega)
      have hresult := hcycle.all_triple_consequences.2.2.1
        hmiddle hsource hhilbert
      simpa only [bu, cu, diagonalUnitCoefficients_prefixValueUnits] using
        hresult
  | second middleCurrent sourcePrevious hilbert =>
      let au := a.prefixValueUnits (i.val + 1)
        (Nat.succ_le_of_lt i.lt_large)
      let bu := b.prefixValueUnits i.val i.lt_large.le
      let cu := c.prefixValueUnits (i.val - 1) (by
        have := i.lt_large
        omega)
      have hmiddle : DiagonalRepresents
          (diagonalUnitCoefficients bu)
          (diagonalUnitCoefficients au) := by
        simpa only [au, bu, diagonalUnitCoefficients_prefixValueUnits] using
          middleCurrent
      have hsource : DiagonalRepresents
          (diagonalUnitCoefficients cu)
          (diagonalUnitCoefficients
            (diagonalUnitTake au i.val (by omega))) := by
        simpa only [au, cu, diagonalUnitTake_prefixValueUnits,
          diagonalUnitCoefficients_prefixValueUnits] using sourcePrevious
      have hhilbert : hilbertSymbol K
          (diagonalUnitDeterminant
              (diagonalUnitTake au i.val (by omega)) *
            diagonalUnitDeterminant bu)
          (-diagonalUnitDeterminant au * diagonalUnitDeterminant cu) = 1 := by
        simpa only [au, bu, cu, diagonalUnitTake_prefixValueUnits,
          diagonalUnitDeterminant_prefixValueUnits] using hilbert
      have hcycle := DiagonalRepresentationParityLaws.caseII
        au bu cu rfl (by
          have := i.one_lt
          omega)
      have hresult := hcycle.all_triple_consequences.2.2.1
        hmiddle hsource hhilbert
      simpa only [bu, cu, diagonalUnitCoefficients_prefixValueUnits] using
        hresult

end Lemma79CentralCertificate

/-- The paper closes an active condition-(iii) boundary in either of two
ways: most cases construct one of the Lemma 1.5 diagrams above, while the
exceptional endpoint-tower cases prove the required representation directly.
This sum type records both proof routes without adding a local-field law. -/
inductive Lemma79CentralWitness
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (i : CentralRepresentationIndex (n + 2) (n + 2)) : Prop
  | viaCertificate (certificate : Lemma79CentralCertificate a b c i)
  | direct (representation : DiagonalRepresents
      (c.prefixValues (i.val - 1) (by
        have := i.lt_large
        omega))
      (b.prefixValues i.val i.lt_large.le))

namespace Lemma79CentralWitness

/-- Either proof route supplies the prefix representation in
condition 2.1(iii). -/
theorem represents
    {a : GoodBONG q L (n + 2)} {b : GoodBONG q M (n + 2)}
    {c : GoodBONG q N (n + 2)}
    {i : CentralRepresentationIndex (n + 2) (n + 2)}
    (witness : Lemma79CentralWitness a b c i) :
    DiagonalRepresents
      (c.prefixValues (i.val - 1) (by
        have := i.lt_large
        omega))
      (b.prefixValues i.val i.lt_large.le) := by
  cases witness with
  | viaCertificate certificate => exact certificate.represents
  | direct representation => exact representation

end Lemma79CentralWitness

/-- Pointwise proof family allowing both of the proof routes actually used
in Lemma 7.9(iii). -/
structure Lemma79CentralWitnesses
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) : Prop where
  witness (i : CentralRepresentationIndex (n + 2) (n + 2)) :
    b.centralAlphaTrigger c i → Lemma79CentralWitness a b c i

/-- A complete family of certificate-or-direct witnesses proves
condition 2.1(iii). -/
theorem centralRepresentationConditions_of_lemma79Witnesses
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (witnesses : Lemma79CentralWitnesses a b c) :
    b.CentralRepresentationConditions c := by
  rw [b.centralRepresentationConditions_iff_forall_alphaTrigger c]
  intro i htrigger
  exact (witnesses.witness i htrigger).represents

/-- Pointwise certificate family for all active condition-(iii) triggers in
Lemma 7.9. -/
structure Lemma79CentralCertificates
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2)) : Prop where
  certificate (i : CentralRepresentationIndex (n + 2) (n + 2)) :
    b.centralAlphaTrigger c i → Lemma79CentralCertificate a b c i

/-- A complete family of the two explicit Lemma 1.5 certificates proves
condition 2.1(iii) for `(b,c)`. -/
theorem centralRepresentationConditions_of_lemma79Certificates
    (a : GoodBONG q L (n + 2)) (b : GoodBONG q M (n + 2))
    (c : GoodBONG q N (n + 2))
    (certificates : Lemma79CentralCertificates a b c) :
    b.CentralRepresentationConditions c := by
  rw [b.centralRepresentationConditions_iff_forall_alphaTrigger c]
  intro i htrigger
  exact (certificates.certificate i htrigger).represents

end BONG.GoodBONG

end Bong
