/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/
import Bong.Lattice.OmearaSaturationComplement
import Bong.Lattice.OmearaHyperbolicCancellation

/-!
# Cancellation of componentwise paired hyperbolic stabilizations

This file supplies the finite rebracketing and cancellation argument used
in the rank-three part of O'Meara 93:21.  A family of blocks

`H_{s_i} ⊥ H_{s_i} ⊥ L_i`

is gathered into one nested tower over the coordinate product of the
`L_i`.  O'Meara 93:14 then cancels the two common planes at every scale.
-/

namespace Bong

open Dyadic Module

namespace Lattice

universe u v w x

/-- The carrier obtained by adjoining two outer hyperbolic planes at each
of `t` successive scales. -/
def PairedHyperbolicExtension (K : Type u) (W : Type v) : Nat → Type (max u v)
  | 0 => ULift.{u} W
  | t + 1 =>
      (Fin 2 → K) × ((Fin 2 → K) × PairedHyperbolicExtension K W t)

@[reducible, instance] def pairedHyperbolicExtensionAddCommGroup
    {K : Type u} [AddCommGroup K]
    {W : Type v} [AddCommGroup W] (t : Nat) :
    AddCommGroup (PairedHyperbolicExtension K W t) :=
  Nat.rec
    (motive := fun m ↦ AddCommGroup (PairedHyperbolicExtension K W m))
    (show AddCommGroup (ULift.{u} W) from inferInstance)
    (fun _ ih ↦ @Prod.instAddCommGroup _ _ inferInstance
      (@Prod.instAddCommGroup _ _ inferInstance ih)) t

@[reducible, instance] def pairedHyperbolicExtensionModule
    {K : Type u} [Field K]
    {W : Type v} [AddCommGroup W] [Module K W] (t : Nat) :
    Module K (PairedHyperbolicExtension K W t) :=
  Nat.rec
    (motive := fun m ↦
      @Module K (PairedHyperbolicExtension K W m) _
        (pairedHyperbolicExtensionAddCommGroup m).toAddCommMonoid)
    (show Module K (ULift.{u} W) from inferInstance)
    (fun _ ih ↦ @Prod.instModule K _ _ _ _ _ inferInstance
      (@Prod.instModule K _ _ _ _ _ inferInstance ih)) t

variable {K : Type u} [Field K] [CharZero K] [ValuativeRel K]
  [TopologicalSpace K] [DyadicContext K]

/-- Pull a quadratic form back along an equivalence whose source and target
may lie in different universes.  This local universe-polymorphic version is
needed only to pass through the `ULift` at the base of a finite tower. -/
private def pullbackQuadraticSpace
    {A : Type v} {B : Type w}
    [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B]
    (q : QuadraticSpace K B) (e : A ≃ₗ[K] B) :
    QuadraticSpace K A where
  bilin := LinearMap.mk₂ K (fun x y => q.bilin (e x) (e y))
    (by intros; simp)
    (by intros; simp)
    (by intros; simp)
    (by intros; simp)
  isSymm := ⟨by
    intro x y
    exact q.isSymm.eq (e x) (e y)⟩
  nondegenerate := by
    constructor
    · intro x hx
      apply e.injective
      rw [map_zero]
      apply q.nondegenerate.1
      intro y
      simpa using hx (e.symm y)
    · intro x hx
      apply e.injective
      rw [map_zero]
      apply q.nondegenerate.2
      intro y
      simpa using hx (e.symm y)

/-- The `ULift` copy of a quadratic space. -/
private noncomputable def uliftQuadraticSpace
    {W : Type v} [AddCommGroup W] [Module K W]
    (q : QuadraticSpace K W) : QuadraticSpace K (ULift.{u} W) :=
  pullbackQuadraticSpace q ULift.moduleEquiv

/-- The image of a lattice in the `ULift` copy of its ambient space. -/
private noncomputable def uliftLattice
    {W : Type v} [AddCommGroup W] [Module K W]
    (L : Lattice K W) : Lattice K (ULift.{u} W) :=
  map ULift.moduleEquiv.symm L

/-- The canonical integral isometry from an `ULift` copy back to its
original quadratic lattice. -/
private noncomputable def uliftLatticeIsometry
    {W : Type v} [AddCommGroup W] [Module K W]
    (q : QuadraticSpace K W) (L : Lattice K W) :
    Isometry (uliftQuadraticSpace q) q (uliftLattice L) L where
  toLinearEquiv := ULift.moduleEquiv
  map_bilin _ _ := rfl
  map_mem x := by
    change x ∈ map ULift.moduleEquiv.symm L ↔ ULift.moduleEquiv x ∈ L
    rw [mem_map_iff]
    rfl

/-- The quadratic form on a tower with two planes at every listed scale. -/
noncomputable def pairedHyperbolicExtensionForm
    {W : Type v} [AddCommGroup W] [Module K W]
    (q : QuadraticSpace K W) :
    (t : Nat) → (Fin t → Kˣ) →
      QuadraticSpace K (PairedHyperbolicExtension K W t)
  | 0, _ => uliftQuadraticSpace q
  | t + 1, scale =>
      (QuadraticSpace.hyperbolicPlane (scale 0)).orthogonalSum
        ((QuadraticSpace.hyperbolicPlane (scale 0)).orthogonalSum
          (pairedHyperbolicExtensionForm q t (Fin.tail scale)))

/-- The product lattice on a tower with two standard planes at every
listed scale. -/
noncomputable def pairedHyperbolicExtensionLattice
    {W : Type v} [AddCommGroup W] [Module K W]
    (L : Lattice K W) :
    (t : Nat) → Lattice K (PairedHyperbolicExtension K W t)
  | 0 => uliftLattice L
  | t + 1 =>
      product (hyperbolicPlaneLattice (K := K))
        (product (hyperbolicPlaneLattice (K := K))
          (pairedHyperbolicExtensionLattice L t))

/-- The zero-level paired extension is merely the `ULift` presentation of
the base lattice.  This public isometry lets invariant computations leave
the implementation-specific lift. -/
noncomputable def pairedHyperbolicExtensionBaseIsometry
    {W : Type v} [AddCommGroup W] [Module K W]
    (q : QuadraticSpace K W) (L : Lattice K W)
    (scale : Fin 0 → Kˣ) :
    Isometry
      (pairedHyperbolicExtensionForm q 0 scale) q
      (pairedHyperbolicExtensionLattice L 0) L :=
  uliftLatticeIsometry q L

/-- An integral isometry of the base lattices extends through the same
paired hyperbolic tower. -/
noncomputable def pairedHyperbolicExtensionIsometry
    {V : Type v} {W : Type w}
    [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W}
    (f : Isometry q r L M) :
    (t : Nat) → (scale : Fin t → Kˣ) →
      Isometry
        (pairedHyperbolicExtensionForm q t scale)
        (pairedHyperbolicExtensionForm r t scale)
        (pairedHyperbolicExtensionLattice L t)
        (pairedHyperbolicExtensionLattice M t)
  | 0, _ =>
      (uliftLatticeIsometry q L).trans <|
        f.trans (uliftLatticeIsometry r M).symm
  | t + 1, scale =>
      (Isometry.refl (QuadraticSpace.hyperbolicPlane (scale 0))
        (hyperbolicPlaneLattice (K := K))).orthogonalProductBasic
        ((Isometry.refl (QuadraticSpace.hyperbolicPlane (scale 0))
          (hyperbolicPlaneLattice (K := K))).orthogonalProductBasic
            (pairedHyperbolicExtensionIsometry f t (Fin.tail scale)))

/-- O'Meara 93:14 iterated twice at every scale in a paired tower. -/
noncomputable def cancelPairedHyperbolicExtension
    {V : Type v} {W : Type w}
    [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    {q : QuadraticSpace K V} {r : QuadraticSpace K W}
    {L : Lattice K V} {M : Lattice K W} :
    (t : Nat) → (scale : Fin t → Kˣ) →
      Isometry
        (pairedHyperbolicExtensionForm q t scale)
        (pairedHyperbolicExtensionForm r t scale)
        (pairedHyperbolicExtensionLattice L t)
        (pairedHyperbolicExtensionLattice M t) →
      Isometry q r L M
  | 0, _, f =>
      (uliftLatticeIsometry q L).symm.trans <|
        f.trans (uliftLatticeIsometry r M)
  | t + 1, scale, f => by
      let once := omeara9314_scaled (scale 0) f
      let twice := omeara9314_scaled (scale 0) once
      exact cancelPairedHyperbolicExtension t (Fin.tail scale) twice

/-- Move a left-hand base lattice through a paired hyperbolic tower, while
retaining it on the left of the tower's base. -/
noncomputable def moveBasePastPairedHyperbolicExtension
    {A : Type v} {B : Type w}
    [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B]
    (p : QuadraticSpace K A) (q : QuadraticSpace K B)
    (P : Lattice K A) (Q : Lattice K B) :
    (t : Nat) → (scale : Fin t → Kˣ) →
      Isometry
        (p.orthogonalSum (pairedHyperbolicExtensionForm q t scale))
        (pairedHyperbolicExtensionForm (p.orthogonalSum q) t scale)
        (product P (pairedHyperbolicExtensionLattice Q t))
        (pairedHyperbolicExtensionLattice (product P Q) t)
  | 0, _ =>
      ((Isometry.refl p P).orthogonalProductBasic
        (uliftLatticeIsometry q Q)).trans
        (uliftLatticeIsometry (p.orthogonalSum q) (product P Q)).symm
  | t + 1, scale => by
      let H := QuadraticSpace.hyperbolicPlane (scale 0)
      let HL := hyperbolicPlaneLattice (K := K)
      let tailForm := pairedHyperbolicExtensionForm q t (Fin.tail scale)
      let tailLattice := pairedHyperbolicExtensionLattice Q t
      let rotateOuter : Isometry
          (p.orthogonalSum (H.orthogonalSum (H.orthogonalSum tailForm)))
          ((H.orthogonalSum p).orthogonalSum (H.orthogonalSum tailForm))
          (product P (product HL (product HL tailLattice)))
          (product (product HL P) (product HL tailLattice)) :=
        orthogonalProductRotateLeft
      let associateOuter : Isometry
          ((H.orthogonalSum p).orthogonalSum (H.orthogonalSum tailForm))
          (H.orthogonalSum (p.orthogonalSum (H.orthogonalSum tailForm)))
          (product (product HL P) (product HL tailLattice))
          (product HL (product P (product HL tailLattice))) :=
        orthogonalProductAssoc
      let rotateInner : Isometry
          (p.orthogonalSum (H.orthogonalSum tailForm))
          ((H.orthogonalSum p).orthogonalSum tailForm)
          (product P (product HL tailLattice))
          (product (product HL P) tailLattice) :=
        orthogonalProductRotateLeft
      let associateInner : Isometry
          ((H.orthogonalSum p).orthogonalSum tailForm)
          (H.orthogonalSum (p.orthogonalSum tailForm))
          (product (product HL P) tailLattice)
          (product HL (product P tailLattice)) :=
        orthogonalProductAssoc
      let recursive := moveBasePastPairedHyperbolicExtension
        p q P Q t (Fin.tail scale)
      let inner : Isometry
          (p.orthogonalSum (H.orthogonalSum tailForm))
          (H.orthogonalSum
            (pairedHyperbolicExtensionForm (p.orthogonalSum q)
              t (Fin.tail scale)))
          (product P (product HL tailLattice))
          (product HL
            (pairedHyperbolicExtensionLattice (product P Q) t)) :=
        rotateInner.trans <| associateInner.trans <|
          (Isometry.refl H HL).orthogonalProductBasic recursive
      exact rotateOuter.trans <| associateOuter.trans <|
        (Isometry.refl H HL).orthogonalProductBasic inner

/-- The carrier of one block after adjoining two standard hyperbolic
planes. -/
abbrev TwiceHyperbolicCarrier
    (K : Type u) {n : Nat} (C : Fin (n + 1) → Type v)
    (i : Fin (n + 1)) :=
  (Fin 2 → K) × ((Fin 2 → K) × C i)

/-- The form on one twice-hyperbolically stabilized block. -/
noncomputable def twiceHyperbolicForm
    {n : Nat} (C : Fin (n + 1) → Type v)
    [∀ i, AddCommGroup (C i)] [∀ i, Module K (C i)]
    (qs : ∀ i, QuadraticSpace K (C i))
    (scale : Fin (n + 1) → Kˣ) (i : Fin (n + 1)) :
    QuadraticSpace K (TwiceHyperbolicCarrier K C i) :=
  (QuadraticSpace.hyperbolicPlane (scale i)).orthogonalSum
    ((QuadraticSpace.hyperbolicPlane (scale i)).orthogonalSum (qs i))

/-- The lattice on one twice-hyperbolically stabilized block. -/
noncomputable def twiceHyperbolicLattice
    {n : Nat} (C : Fin (n + 1) → Type v)
    [∀ i, AddCommGroup (C i)] [∀ i, Module K (C i)]
    (Ls : ∀ i, Lattice K (C i)) (i : Fin (n + 1)) :
    Lattice K (TwiceHyperbolicCarrier K C i) :=
  product (hyperbolicPlaneLattice (K := K))
    (product (hyperbolicPlaneLattice (K := K)) (Ls i))

/-- Gather a nonempty coordinate product of twice-stabilized blocks into a
single nested paired-hyperbolic tower over the coordinate product of the
unstabilized blocks. -/
noncomputable def gatherPairedHyperbolicBlockProduct :
    {n : Nat} →
    (C : Fin (n + 1) → Type v) →
    [(∀ i, AddCommGroup (C i))] → [(∀ i, Module K (C i))] →
    (qs : ∀ i, QuadraticSpace K (C i)) →
    (Ls : ∀ i, Lattice K (C i)) →
    (scale : Fin (n + 1) → Kˣ) →
    Isometry
      (BONG.blockOrthogonalForm n (TwiceHyperbolicCarrier K C)
        (twiceHyperbolicForm C qs scale))
      (pairedHyperbolicExtensionForm
        (BONG.blockOrthogonalForm n C qs) (n + 1) scale)
      (BONG.blockProductLattice n (TwiceHyperbolicCarrier K C)
        (twiceHyperbolicLattice C Ls))
      (pairedHyperbolicExtensionLattice
        (BONG.blockProductLattice n C Ls) (n + 1))
  | 0, C, _, _, qs, Ls, scale => by
      let stableSingleton := BONG.blockOrthogonalSingletonLatticeIsometry
        (TwiceHyperbolicCarrier K C)
        (twiceHyperbolicForm C qs scale)
        (twiceHyperbolicLattice C Ls)
      let liftBase : Isometry
          (twiceHyperbolicForm C qs scale 0)
          (pairedHyperbolicExtensionForm (qs 0) 1 scale)
          (twiceHyperbolicLattice C Ls 0)
          (pairedHyperbolicExtensionLattice (Ls 0) 1) :=
        (Isometry.refl (QuadraticSpace.hyperbolicPlane (scale 0))
          (hyperbolicPlaneLattice (K := K))).orthogonalProductBasic
          ((Isometry.refl (QuadraticSpace.hyperbolicPlane (scale 0))
            (hyperbolicPlaneLattice (K := K))).orthogonalProductBasic
              (uliftLatticeIsometry (qs 0) (Ls 0)).symm)
      let baseSingleton := BONG.blockOrthogonalSingletonLatticeIsometry
        C qs Ls
      exact stableSingleton.trans <| liftBase.trans <|
        pairedHyperbolicExtensionIsometry baseSingleton.symm 1 scale
  | n + 1, C, _, _, qs, Ls, scale => by
      let tailC : Fin (n + 1) → Type v := fun i ↦ C i.succ
      let tailQ : ∀ i, QuadraticSpace K (tailC i) := fun i ↦ qs i.succ
      let tailL : ∀ i, Lattice K (tailC i) := fun i ↦ Ls i.succ
      let tailScale : Fin (n + 1) → Kˣ := Fin.tail scale
      let H := QuadraticSpace.hyperbolicPlane (scale 0)
      let HL := hyperbolicPlaneLattice (K := K)
      let tailBaseForm := BONG.blockOrthogonalForm n tailC tailQ
      let tailBaseLattice := BONG.blockProductLattice n tailC tailL
      let tailTowerForm := pairedHyperbolicExtensionForm
        tailBaseForm (n + 1) tailScale
      let tailTowerLattice := pairedHyperbolicExtensionLattice
        tailBaseLattice (n + 1)
      let splitStable := BONG.blockOrthogonalSplitLatticeIsometry
        (K := K) n (TwiceHyperbolicCarrier K C)
        (twiceHyperbolicForm C qs scale)
        (twiceHyperbolicLattice C Ls)
      let recursive := gatherPairedHyperbolicBlockProduct
        tailC tailQ tailL tailScale
      let gatherTail :=
        (Isometry.refl (twiceHyperbolicForm C qs scale 0)
          (twiceHyperbolicLattice C Ls 0)).orthogonalProductBasic recursive
      let associateOuter : Isometry
          ((H.orthogonalSum (H.orthogonalSum (qs 0))).orthogonalSum
            tailTowerForm)
          (H.orthogonalSum
            ((H.orthogonalSum (qs 0)).orthogonalSum tailTowerForm))
          (product (product HL (product HL (Ls 0))) tailTowerLattice)
          (product HL (product (product HL (Ls 0)) tailTowerLattice)) :=
        orthogonalProductAssoc
      let associateInner : Isometry
          ((H.orthogonalSum (qs 0)).orthogonalSum tailTowerForm)
          (H.orthogonalSum ((qs 0).orthogonalSum tailTowerForm))
          (product (product HL (Ls 0)) tailTowerLattice)
          (product HL (product (Ls 0) tailTowerLattice)) :=
        orthogonalProductAssoc
      let reassociate := associateOuter.trans <|
        (Isometry.refl H HL).orthogonalProductBasic associateInner
      let moveBase := moveBasePastPairedHyperbolicExtension
        (qs 0) tailBaseForm (Ls 0) tailBaseLattice
        (n + 1) tailScale
      let liftMove :=
        (Isometry.refl H HL).orthogonalProductBasic
          ((Isometry.refl H HL).orthogonalProductBasic moveBase)
      let baseSplit := BONG.blockOrthogonalSplitLatticeIsometry
        (K := K) n C qs Ls
      exact splitStable.trans <| gatherTail.trans <|
        reassociate.trans <| liftMove.trans <|
          pairedHyperbolicExtensionIsometry baseSplit.symm (n + 2) scale

end Lattice
end Bong
