/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Bong.Prefix
import Bong.Lattice.Isometry

/-!
# Canonical isometry between prefix witnesses

Any two prefix witnesses for the same BONG block have the same coordinate
carrier and both realize exactly the intersection of the parent lattice with
that carrier.  The identity on ambient vectors therefore gives a canonical
lattice isometry between them.
-/

namespace Bong

open Dyadic

universe u v

namespace BONG.PrefixWitness

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]
  {V : Type v} [AddCommGroup V] [Module K V]
  {q : QuadraticSpace K V} {L : Lattice K V} {n length : Nat}
  {b : BONG V q L n} {bound : length ≤ n}

/-- The coordinate carriers of two witnesses for the same prefix agree. -/
theorem carrier_eq (P Q : PrefixWitness b length bound) :
    P.carrier = Q.carrier :=
  P.carrier_eq_segmentCarrier.trans Q.carrier_eq_segmentCarrier.symm

/-- The identity on ambient vectors is an isometry between any two
realizations of the same prefix lattice. -/
noncomputable def latticeIsometry
    (P Q : PrefixWitness b length bound) :
    Lattice.Isometry
      (q.restrict P.carrier P.nondegenerate)
      (q.restrict Q.carrier Q.nondegenerate)
      P.lattice Q.lattice where
  toLinearEquiv := LinearEquiv.ofEq P.carrier Q.carrier (P.carrier_eq Q)
  map_bilin := by
    intro x y
    change q.bilin
        ((LinearEquiv.ofEq P.carrier Q.carrier (P.carrier_eq Q) x :
          Q.carrier) : V)
        ((LinearEquiv.ofEq P.carrier Q.carrier (P.carrier_eq Q) y :
          Q.carrier) : V) =
      q.bilin (x : V) (y : V)
    simp
  map_mem := by
    intro x
    constructor
    · intro hx
      apply Q.contains_parent
      have hparent := P.contained x hx
      simpa using hparent
    · intro hx
      apply P.contains_parent
      have hparent := Q.contained
        (LinearEquiv.ofEq P.carrier Q.carrier (P.carrier_eq Q) x) hx
      simpa using hparent

@[simp]
theorem coe_latticeIsometry_apply
    (P Q : PrefixWitness b length bound) (x : P.carrier) :
    (((P.latticeIsometry Q).toLinearEquiv x : Q.carrier) : V) =
      (x : V) := by
  simp [latticeIsometry]

end BONG.PrefixWitness

end Bong
