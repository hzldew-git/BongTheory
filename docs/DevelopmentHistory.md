# BongTheory

Lean 4 formalization of BONG theory for integral quadratic lattices over dyadic
local fields.

## M0 foundation

M0 fixes the ambient conventions used by later stages:

- Lean `v4.32.1` and mathlib `v4.32.1`;
- a characteristic-zero nonarchimedean local field;
- a compatible normalized additive valuation `ord : K → WithTop ℤ`;
- a selected uniformizer `π` satisfying `ord π = 1`;
- dyadicity expressed as `0 < ord 2`;
- a concrete `ℚ_[2]` instance and smoke tests.

The public M0 modules are `Bong.Dyadic.Basic` and
`Bong.Dyadic.Valuation`.  Concrete instances and tests live under `BongTest`.

## M1 scalar invariants

M1 adds the dyadic scalar invariants used by the later BONG classification:

- the square-class group `Kˣ / Kˣ²`;
- Beli's relative quadratic defect, including square invariance and the
  domination principle `min (d a) (d b) ≤ d (a * b)`;
- the quadratic norm group represented by `x² - a * y²`;
- the Hilbert symbol with its norm criterion, symmetry, and square-class
  invariance;
- explicit `QuadraticDefectLaws` and `HilbertSymbolLaws` interfaces for the
  deeper local-field theorems not presently supplied by mathlib.

The public M1 modules are `Bong.Dyadic.QuadraticDefect` and
`Bong.Dyadic.HilbertSymbol`.  The `ℚ_[2]` smoke test also checks that the
ramification index is one and that squares have infinite defect.

## M2 quadratic spaces and lattices

M2 fixes the geometric and integral objects on which BONGs are built:

- nondegenerate symmetric quadratic spaces in Beli's convention
  `Q(x) = B(x, x)`;
- finitely generated full modules over the dyadic valuation ring;
- the scale ideal `sL`, norm ideal `nL`, and norm-generator predicate;
- the proved relations `nL ⊆ sL` and `2sL ⊆ nL`;
- the explicit orthogonal projection onto `x⊥` and the projected full lattice
  `prₓ⊥ L` in that orthogonal complement.

The public M2 modules are `Bong.QuadraticSpace.Basic`, `Bong.Lattice.Basic`,
`Bong.Lattice.Ideals`, and `Bong.Lattice.Projection`.

## M3 bases of norm generators

M3 formalizes Beli's recursive basis-of-norm-generators construction:

- a dependent `BONG` certificate whose tail is a BONG of the projected lattice
  in the orthogonal complement of its head;
- nonzero scalar values `a_i`, integral orders `R_i`, and prefix products;
- the binary parameter `a₂ / a₁`, its square class, and the proved identity
  `ord(a₂ / a₁) = R₂ - R₁`;
- the improper-modular, proper-modular, and nonmodular order trichotomy;
- good BONGs, defined by `R_i ≤ R_{i+2}`, together with the proved equivalent
  adjacent-sum condition.

The public M3 modules are `Bong.Bong.Basic`, `Bong.Bong.Binary`, and
`Bong.Bong.Good`.

## M4 invariants and classification

M4 encodes Definition 1 and Theorem 3.1 of Beli's 2009 classification paper:

- the exact finite candidate set defining each `α_i`, valued in `WithTop ℚ`;
- a proof that every `α_i` is finite and hence has a rational value;
- quadratic-space and integral-lattice isometries;
- diagonal representation and the four explicit good-BONG classification
  conditions: orders, `α_i`, prefix defects, and conditional prefix
  representations;
- `GoodBONGClassificationLaws`, an explicit interface isolating the one deep
  equivalence that depends on O'Meara's local classification theorem 93:28.

No global axiom is introduced.  The public M4 modules are
`Bong.Bong.Invariants` and `Bong.Bong.Classification`.

## M5 representation

M5 formalizes the statement-level infrastructure of Beli's 2019 dyadic
representation theorem:

- injective representations of quadratic spaces and integral lattices, with
  identity, composition, quadratic-value preservation, and the forgetful map
  from integral to ambient representation;
- Definition 1's capped defects `d[εa₁,ᵢb₁,ⱼ]` and segment defects
  `d[εaᵢ,ⱼ]`, including their proved upper bounds by the raw defect and both
  boundary `α`-caps;
- Definition 4's full finite candidate set for `A_i(M,N)`, together with a
  proof that `A_i` is finite, and the exceptional boundary quantity
  `S_{N+1} + A_{N+1}`;
- all four conditions of Theorem 2.1, including the endpoint conventions in
  conditions (iii) and (iv);
- `GoodBONGRepresentationLaws`, an explicit interface isolating the deep
  equivalence with integral representability.

No global axiom is introduced.  The public M5 module is
`Bong.Bong.Representation`.

## M6 structural foundations

M6 supplies the structural language needed for Beli's 2003 spinor-norm paper,
especially Sections 1--4:

- the refined square-class group `Kˣ / (𝒚ˣ)²`, its map to ordinary field
  square classes, and exact defect domination for unequal defects;
- the principal-ideal-ring structure of the normalized valuation ring, chosen
  integral bases, and their extensions to ambient field bases;
- full integral dual lattices, antitonicity, exact biduality, rescaling,
  `(aL)♯ = a⁻¹L♯`, modularity, and unimodularity;
- nondegenerate quadratic sublattices, orthogonal decompositions, Jordan
  decompositions with scale and norm generators, and Jordan property A;
- the ambient orthogonal basis carried by a recursive BONG, its diagonal Gram
  matrix, determinant product, and BONG-independent ordinary square class;
- determinant representatives, refined determinant classes, volume ideals,
  and volume orders;
- normalized BONG units `ε_i`, properties A and B with endpoint conventions,
  reverse-dual vectors, and their reciprocal quadratic values;
- a dependent witness type for consecutive BONG segments.

At this stage the deeper integral existence and reconstruction results were
collected in the explicit `BONGStructuralLaws` interface.  Later stages M9--M25
prove determinant reconstruction, BONG existence, and consecutive-segment
realization unconditionally.  The interface now retains only good-BONG
existence, reverse-dual goodness, and the equivalence between Jordan property A
and the strict two-step order condition.  No global axiom is introduced.

The public M6 modules are `Bong.Dyadic.UnitSquareClass`,
`Bong.Lattice.Determinant`, `Bong.Lattice.Dual`, `Bong.Lattice.Modular`,
`Bong.Lattice.Jordan`, `Bong.Bong.Basis`, `Bong.Bong.Properties`, and
`Bong.Bong.Structural`.

## M7 Beli 2003, Section 2

M7 decomposes the integral content of Beli's Section 2 into its minimal local
inputs and formally derives the recursive consequences:

- BONG value products satisfy the head-tail product formula;
- determinant classes of zero-dimensional lattices are trivial;
- `BONGDeterminantProjectionLaws` isolates the one-step determinant identity
  used in Lemma 2.1;
- `BONGReconstructionLaws` isolates precisely the norm-and-projection
  containment criterion of Lemma 2.2;
- `BONGSectionTwoLaws` combines the two independent interfaces when both are
  needed;
- Lemma 2.1's refined determinant formula is proved by induction from only the
  determinant-projection interface;
- Corollary 2.6, uniqueness of a lattice determined by its BONG vectors, is
  proved by induction from only Lemma 2.2's interface;
- consecutive segment witnesses preserve their values, valuation orders,
  goodness, and property A, supplying the concrete part of Corollaries
  2.7--2.8.

The two local projection laws have no default instances.  Thus the remaining
unconditional work is explicit: prove the one-step integral determinant
identity and Lemma 2.2 from valuation-ring lattice theory.  No global axiom is
introduced.  The public M7 module is `Bong.Bong.SectionTwo`.

## M8 reconstruction reduction

M8 replaces the opaque part of Lemma 2.2 by concrete lattice operations and
two sharply localized arithmetic inputs:

- the sum of two full lattices is constructed as a full lattice, with its
  order and membership API;
- orthogonal projection is proved monotone and compatible with lattice sums;
- `normIdeal_sup_le` controls `n(L + M)` by `nL`, `nM`, and the mixed terms
  `2 B(L, M)`; in particular, `normIdeal_sup_eq_left` proves the equality used
  in Beli's proof;
- a norm generator is proved to remain a norm generator after adjoining a
  norm-controlled lattice;
- equality of refined determinant classes is proved to imply equality of
  volume ideals;
- `BONGMixedPairingLaws` isolates the dyadic coefficient estimate in Beli's
  argument, while `LatticeVolumeRigidityLaws` isolates the standard fact that
  equal-volume nested full lattices coincide;
- Lemma 2.2 is derived from these two inputs together with the one-step
  determinant law.  Consequently `BONGSectionTwoLocalLaws` automatically
  supplies `BONGReconstructionLaws`.

Thus reconstruction is no longer a single black-box local assumption.  The
remaining unconditional work consists of the one-step determinant identity,
the mixed-pairing estimate, and general volume rigidity.  No default instance
for any of these mathematical inputs and no global axiom is introduced.  The
public M8 modules are `Bong.Lattice.Sum` and `Bong.Bong.SectionTwo`.

## M9 volume rigidity

M9 proves the equal-volume rigidity input used in the reconstruction argument:

- every inclusion of full lattices is represented by a square matrix over the
  valuation ring in chosen integral bases;
- extending scalars sends this inclusion matrix to the corresponding ambient
  change-of-basis matrix;
- the Gram determinant obeys
  `det(L) = det(M) * det(inclusion) ^ 2` for `L ≤ M`;
- equality of the two volume ideals forces the inclusion determinant to be a
  unit, hence the inclusion is surjective and the two lattices are equal;
- `LatticeVolumeRigidityLaws` now has a theorem-backed default instance.

Consequently Beli's reconstruction law now follows from only the one-step
determinant identity and the mixed-pairing estimate.  These are the two
remaining local arithmetic inputs; no global axiom is introduced.  The public
M9 module is `Bong.Lattice.VolumeRigidity`.

## M10 determinant projection

M10 proves the remaining determinant input in Beli's 2003 Lemma 2.1:

- the kernel of projection from a lattice along a norm generator is exactly
  its integral generator line;
- the resulting short exact sequence splits and supplies an adapted integral
  basis;
- orthogonalizing the lifted tail is a determinant-one shear;
- the adapted Gram determinant is exactly
  `Q(x) * det(pr_(x⊥) L)`;
- an arbitrary integral change of basis contributes the square of a
  valuation-ring unit, so it vanishes in the refined determinant class;
- `BONGDeterminantProjectionLaws` now has a theorem-backed default instance.

Consequently Beli's refined BONG determinant formula is unconditional.  The
mixed-pairing estimate is now the sole remaining local arithmetic input in the
Section 2 reconstruction argument.  The public M10 module is
`Bong.Lattice.DeterminantProjection`.

## M11 mixed pairing and reconstruction

M11 proves the last local arithmetic input in Beli's 2003 Lemma 2.2:

- orthogonal projection gives an exact quadratic-value decomposition;
- twice every projection coefficient along a norm generator is integral;
- the valuation-ring implication
  `b² - g² ∈ 𝒪` and `2g ∈ 𝒪` implies `b - g ∈ 𝒪` is proved directly;
- these facts yield `2 B(M, N) ⊆ nM` under Beli's norm and projection
  hypotheses;
- `BONGMixedPairingLaws` and hence `BONGReconstructionLaws` now have
  theorem-backed default instances.

Thus Lemma 2.2 and Corollary 2.6 are unconditional, as is the refined
determinant formula from Lemma 2.1.  No global mathematical axiom is
introduced.  The public M11 module is `Bong.Lattice.MixedPairing`.

## M12 projected transporters

M12 proves the isometry-extension mechanism in Beli (2003), Sections
2.3--2.5:

- quadratic-space and lattice isometries are moved into reusable public
  modules, with identity, inverse, composition, and lattice-image APIs;
- an isometry of the orthogonal complement of an anisotropic vector is
  extended explicitly by fixing its line;
- the extension is proved to preserve the bilinear form and to commute with
  orthogonal projection;
- projection of an image lattice is identified with the image of its
  projected lattice;
- Lemma 2.2 upgrades a projected integral isometry to an integral isometry of
  the original lattices when they have a common norm generator;
- the automorphism specialization realizes the embedding
  `O(pr_(x⊥) L) → O(L)` from Section 2.5.

All proofs are unconditional.  The public M12 modules are
`Bong.QuadraticSpace.Isometry`, `Bong.QuadraticSpace.OrthogonalExtension`,
`Bong.Lattice.Isometry`, and `Bong.Lattice.Transporter`.

## M13 projection preimages

M13 formalizes the one-step inverse-image construction in Beli (2003),
Lemma 2.7(ii):

- for `N ≤ pr_(x⊥) L`, the vectors of `L` whose projection belongs to `N`
  form a full finitely generated lattice;
- its projection is exactly `N`, and it is a sublattice of `L`;
- if `x` is a norm generator of `L`, it remains a norm generator of the
  inverse-image lattice;
- consequently any BONG of `N` can be prepended by `x`, producing the BONG
  of the inverse image with exactly the requested ambient vectors.

All proofs are unconditional.  The public M13 modules are
`Bong.Lattice.ProjectionPreimage` and `Bong.Bong.SegmentConstruction`.

## M14 integral orthogonal-group embedding

M14 upgrades M12's extension operation to the exact group-theoretic statement
of Beli (2003), Section 2.5:

- integral lattice automorphisms are packaged as the group
  `IntegralOrthogonalGroup q L`;
- extension from the projected lattice preserves identity and composition;
- the resulting map `O(pr_(x⊥) L) →* O(L)` is a group homomorphism;
- commuting with projection proves that this homomorphism is injective.

All proofs are unconditional.  The public M14 module is
`Bong.Lattice.Automorphism`.

## M15 reflections and spinor generators

M15 builds the reflection layer required for the spinor norm in Beli (2003):

- reflection in an anisotropic vector is defined by the exact formula
  `y ↦ y - (2 B(x,y) / Q(x)) x`;
- it is proved involutive, fixes `x⊥`, negates `x`, and preserves the bilinear
  form;
- an explicit coefficient criterion guarantees that a reflection preserves a
  lattice, after which it is bundled in the integral orthogonal group;
- each reflection is assigned its canonical square class `[Q(x)]`;
- extending a tail reflection through a norm-generator projection is proved
  to be the same ambient reflection, preserving its square class.

All proofs are unconditional.  The public M15 modules are
`Bong.QuadraticSpace.Reflection` and `Bong.Lattice.Reflection`.

## M16 residual spaces and the Wall form

M16 begins a decomposition-free construction of the spinor norm:

- the residual space of an isometry is defined as `range (1 - f)`;
- the residual map is proved surjective and supplied with a chosen linear
  section;
- fixed vectors are proved orthogonal to the residual space;
- the pairing used in the Wall form is proved independent of the selected
  right inverse;
- the Wall form is constructed and shown to satisfy
  `χ_f((1-f)w, v) = 2 B(w,v)`.

All proofs are unconditional.  The public M16 module is
`Bong.QuadraticSpace.WallForm`.

## M17 Wall determinant and spinor norm

M17 completes the decomposition-free definition of the spinor norm:

- the Wall form is proved left-separating and hence nondegenerate;
- its determinant in a chosen finite basis is proved nonzero;
- the ambient spinor norm is defined as the square class of this Wall
  determinant;
- restricting the ambient invariant to the integral orthogonal group defines
  `theta(O(L))` as an explicit image set.

All proofs are unconditional.  The public M17 modules are
`Bong.QuadraticSpace.SpinorNorm` and `Bong.Lattice.SpinorNorm`.

## M18 reflection normalization and spinor transport

M18 connects the Wall definition to Beli's reflection convention and closes
the spinor-norm part of Beli (2003), Section 2.5:

- the residual space of reflection in `x` is proved to be exactly `K x`;
- its one-dimensional Wall determinant gives
  `theta(tau_x) = [Q(x)]`;
- the residual spaces of a tail isometry and its orthogonal extension are
  identified by an explicit linear equivalence preserving the Wall form;
- hence orthogonal extension preserves spinor norm;
- therefore `theta(O(pr_(x^perp) L))` is contained in `theta(O(L))`.

All proofs are unconditional.  The public M18 modules are
`Bong.QuadraticSpace.SpinorNormReflection`,
`Bong.QuadraticSpace.SpinorNormExtension`, and
`Bong.Lattice.SpinorNorm`.

## M19 unconditional Section 2 structural API

M19 removes two obsolete assumptions from the early structural interface:

- the refined determinant formula of Lemma 2.1 now uses the unconditional M10
  theorem directly;
- uniqueness from common ambient BONG vectors in Corollary 2.6 now uses the
  unconditional M11 reconstruction theorem directly;
- `BONGStructuralLaws` retains only the then-outstanding BONG-existence,
  segment, good-BONG, reverse-dual, and Jordan-coordinate assertions; M21 and
  M25 subsequently remove the first two.

The M19 smoke test deliberately has no `BONGStructuralLaws` instance, guarding
against accidental reintroduction of those assumptions.

## M20 recursive BONG-tail spinor embeddings

M20 specializes the M14 and M18 constructions to the recursive tail stored in
every nonempty BONG:

- the tail integral orthogonal group embeds injectively into the group of the
  original lattice;
- extension along the BONG head preserves the integral spinor norm;
- the tail spinor-norm image is contained in the original image.

This is the one-step recursive form of Beli (2003), Lemma 2.7(i).  The public
M20 module is `Bong.Bong.SpinorNorm`.

## M21 norm-generator and BONG existence

M21 proves the existence theorem built into Beli's recursive definition:

- the norm ideal is generated by the finite family consisting of quadratic
  values of a chosen integral basis and all pairwise sums;
- in positive dimension, nondegeneracy guarantees a nonzero candidate and a
  smallest valuation candidate generates the norm ideal;
- this gives an anisotropic norm generator in every positive-dimensional
  lattice;
- recursive projection then constructs a BONG for every lattice, terminating
  because the orthogonal complement has dimension one less.

Consequently BONG existence is removed from `BONGStructuralLaws` and is now
unconditional.  The public M21 modules are `Bong.Lattice.NormGenerator` and
`Bong.Bong.Existence`.

## M22 isometric transport of BONGs

M22 makes the recursive BONG construction functorial under isometries:

- an ambient quadratic isometry induces an isometry of successive orthogonal
  complements and commutes with orthogonal projection;
- projected lattices commute with mapping by an ambient isometry;
- every BONG therefore maps recursively to a BONG of the image lattice;
- its quadratic-value sequence and ambient vectors are preserved exactly;
- a lattice isometry specializes the construction directly to its target
  lattice.

All proofs are unconditional.  The public M22 modules are
`Bong.QuadraticSpace.OrthogonalMap`, `Bong.Lattice.OrthogonalMap`, and
`Bong.Bong.Map`.

## M23 recursive BONG suffixes

M23 proves the suffix-existence part of Beli (2003), Lemma 2.7(i):

- every recursive tail is transported into a concrete nondegenerate subspace
  of the original quadratic space;
- its BONG vectors are identified, index by index, with the corresponding
  suffix of the original ambient BONG basis;
- the construction works at every cut position, including the empty and full
  suffixes.

The result is unconditional and supplies a canonical `SegmentWitness` for a
full suffix.  The public M23 module is `Bong.Bong.Suffix`.

## M24 coordinate segments and restricted lattices

M24 supplies the linear and integral infrastructure needed to cut a BONG at
both ends:

- consecutive ambient BONG vectors are linearly independent and form a basis
  of their coordinate span;
- that span is nondegenerate and has dimension exactly the segment length;
- the inverse image of a full lattice in an integrally spanning subspace is
  bundled as a full lattice;
- norm generators remain norm generators after this restriction.

All proofs are unconditional.  The public M24 modules are
`Bong.Bong.CoordinateSegment` and `Bong.Lattice.Restriction`.

## M25 unconditional consecutive BONG segments

M25 completes Beli (2003), Lemma 2.7 and Corollary 2.8:

- every initial block is built recursively as a BONG of its coordinate
  subspace, with its integral lattice contained in the parent lattice;
- an arbitrary block is obtained by taking a suffix and then such a prefix;
- the resulting carrier is definition-independently identified with the
  canonical span of the selected ambient vectors;
- `BONG.exists_segmentWitness` no longer requires `BONGStructuralLaws`.

The construction and its public API have only Lean's standard quotient and
choice axioms.  The public M25 modules are `Bong.Bong.Segment` and
`Bong.Bong.Prefix`.

## M26 exact initial-block restriction

M26 strengthens the initial-block construction to the equality asserted in
Beli (2003), Lemma 2.7(iii):

- a vector of the prefix carrier belongs to the constructed prefix lattice if
  and only if its ambient vector belongs to the parent lattice;
- consequently the prefix lattice is exactly the pullback of the parent
  lattice to the coordinate carrier, not merely a contained sublattice;
- the equivalence is maintained recursively through projection preimages.

All proofs are unconditional and use only Lean's standard quotient and choice
axioms.  The public M26 module is `Bong.Bong.Prefix`.

## M27 the binary determinant invariant

M27 begins Beli (2003), Section 3 by defining the refined binary invariant
`a(L) = det(L) * a₁⁻²`.  Using the unconditional determinant product
formula, it proves Lemma 3.1: this invariant is exactly the class represented
by the binary BONG parameter `a₂ / a₁`.

The proof is unconditional.  The public M27 module is
`Bong.Bong.BinaryInvariant`.

## M28 independence of the binary invariant

M28 proves that the refined class `a₂ / a₁` is independent of the chosen
binary BONG of a fixed lattice.  The key integral lemma shows that two nonzero
generators of the same principal fractional ideal differ by a unit of the
valuation ring.  Its square disappears in `Kˣ / (𝒰ˣ)²`, so both BONGs
give the same determinant-normalized invariant.

All proofs are unconditional.  The public API is in
`Bong.Lattice.Ideals` and `Bong.Bong.BinaryInvariant`.

## M29 the binary relative order

M29 formalizes the second invariant in Beli (2003), Definition 3:

- additive valuation descends through equality in the refined square-class
  quotient;
- the determinant formula gives
  `ord(vol L) = ord(a₁) + ord(a₂)`;
- therefore `R(L) = ord(vol L) - 2 ord(nL) = R₂ - R₁`;
- this order gap is independent of the chosen binary BONG.

All proofs are unconditional.  The public API is in
`Bong.Dyadic.Valuation`, `Bong.Dyadic.UnitSquareClass`, and
`Bong.Bong.BinaryInvariant`.

## M30 reverse-dual order theory

M30 starts the constructive proof of Beli (2003), Lemma 4.8:

- the reverse-dual vector is defined as
  `Q(x_{n-1-i})⁻¹ x_{n-1-i}`;
- its quadratic value is the reciprocal BONG value and is nonzero;
- its additive order is `-R_{n-1-i}`;
- reversing and negating a good BONG order sequence preserves the good
  two-step inequalities.

The scalar and order-theoretic half of Lemma 4.8 is therefore unconditional.
The remaining integral step is to realize these vectors recursively as a BONG
of the dual lattice.  The public M30 module is `Bong.Bong.Dual`.

## M31 reverse-dual basis lattices

M31 identifies the ambient basis in the reverse-dual construction with the
ordinary bilinear dual basis.  It proves that:

- the integral lattice generated by any field basis has the expected bundled
  full-lattice structure;
- reindexing a field basis does not alter that basis lattice;
- the dual of a basis lattice is generated by the bilinear dual basis;
- consequently, the reverse-dual BONG basis generates the dual of the original
  BONG basis lattice.

This is the field-basis lattice bridge required by Beli (2003), Lemma 4.8.  The
next integral step is to compare the actual recursively generated BONG lattice
with its basis lattice.  The public M31 API is in `Bong.Lattice.Basic`,
`Bong.Lattice.Dual`, and `Bong.Bong.Dual`.

## M32 orthogonal basis lattices and binary diagonalization

M32 computes both the scale and norm ideals of the integral lattice generated
by an orthogonal field basis.  Specializing this calculation to BONGs gives:

- orthogonal projection of a BONG basis lattice deletes its first basis vector;
- every unary BONG lattice equals its integral basis lattice;
- if a binary BONG satisfies `R₁ ≤ R₂`, its head is also a norm generator of
  the basis lattice;
- reconstruction then proves that the original lattice equals the orthogonal
  basis lattice.

The last statement is Beli (2003), Corollary 3.4(ii).  All results are
unconditional and use only Lean's standard quotient and choice axioms.  The
public M32 API is in `Bong.Lattice.OrthogonalBasis`,
`Bong.Bong.BasisLattice`, and `Bong.Bong.BinaryDiagonal`.

## M33 unary reverse duality

M33 proves the rank-one case of Beli (2003), Lemma 4.8 constructively:

- the reverse-dual basis remains orthogonal;
- its unique vector is a norm generator of its basis lattice;
- the unary BONG lattice equals its basis lattice, so the generated dual basis
  lattice is the actual integral dual `L♯`;
- `Q(x)⁻¹x` is therefore a good BONG of `L♯`, with reciprocal quadratic value;
- applying the reverse normalization twice recovers the original vector.

No `BONGStructuralLaws` assumption is used.  The public M33 API is in
`Bong.Bong.Dual` and `Bong.Bong.UnaryDual`.

## M34 diagonal binary reverse duality

M34 proves the `R₁ ≤ R₂` branch of the binary case of Beli (2003), Lemma 4.8:

- a finite orthogonal basis lattice can be projected by deleting its head;
- the reverse-dual tail is constructed as a basis of the head orthogonal
  complement;
- the order inequality makes the first reverse-dual vector a norm generator;
- the tail is the unconditional unary construction from M33;
- the resulting binary BONG is a good BONG of the actual integral dual lattice,
  with values `a₂⁻¹, a₁⁻¹`.

All assertions are constructive and independent of `BONGStructuralLaws`.  The
public M34 API is in `Bong.Lattice.OrthogonalBasis`,
`Bong.Bong.BasisLattice`, and `Bong.Bong.BinaryDual`.

## M35 unary rigidity and binary uniqueness

M35 proves the rigidity input behind Beli (2003), Lemma 3.2:

- inclusion of nonzero principal coefficient ideals is characterized exactly
  by reverse valuation order;
- two unary BONG lattices with equal quadratic-value order are equal—their
  basis vectors differ by a valuation unit;
- two binary BONGs with the same head norm generator and the same relative
  order have equal projected unary lattices;
- reconstruction therefore proves equality of the original binary lattices.

The last assertion is Beli (2003), Lemma 3.2(ii).  It is unconditional and
uses only Lean's standard quotient and choice axioms.  The public M35 API is in
`Bong.Lattice.NormGenerator`, `Bong.Bong.BasisLattice`, and
`Bong.Bong.BinaryUniqueness`.

## M36 binary inclusion by relative order

M36 completes the lattice-inclusion assertion of Beli (2003), Lemma 3.2(i):

- for unary BONGs, `L ≤ M` is equivalent to reverse comparison of their
  quadratic-value orders;
- for binary BONGs sharing their head norm generator, projection reduces
  inclusion to that unary criterion;
- the converse is lifted from the projected lattices by the unconditional
  reconstruction theorem;
- hence `L ≤ M` if and only if `R(M) ≤ R(L)`.

The result is unconditional and has only Lean's standard quotient and choice
axioms.  The public M36 API is in `Bong.Bong.BasisLattice` and
`Bong.Bong.BinaryUniqueness`.

## M37 binary orthogonal-group inclusion

M37 completes the remaining assertion of Beli (2003), Lemma 3.2(i):

- a binary BONG can be constructed from any prescribed anisotropic norm
  generator;
- an automorphism of the smaller lattice maps the common generator to a norm
  generator of the larger lattice;
- binary uniqueness forces the automorphism to stabilize the larger lattice;
- retaining the same ambient linear map gives an injective group homomorphism
  `O(L) → O(M)`.

Thus all parts of Beli's Lemma 3.2 are now unconditional.  The public M37 API
is in `Bong.Bong.Existence`, `Bong.Bong.BinaryAutomorphism`, and
`Bong.Lattice.Automorphism`.

## M38 ordered orthogonal binary bases

M38 proves the constructive content of Beli (2003), Lemma 3.3(ii):

- start with an anisotropic orthogonal basis of a binary quadratic space;
- assume that the first diagonal value has no larger valuation than the
  second;
- identify the projected lattice with the basis lattice of the orthogonal
  tail;
- recursively construct the unary tail and cons the first norm generator;
- recover exactly the supplied ambient vectors and diagonal values.

Consequently every ordered anisotropic orthogonal binary basis is a BONG of
its integral basis lattice.  The theorem is unconditional and has only Lean's
standard quotient and choice axioms.  The public M38 API is in
`Bong.Bong.OrthogonalBasis`.

## M39 binary orthogonal invariants

M39 completes the invariant formulas in Beli (2003), Lemma 3.3(ii), and hence
the corresponding content of Corollary 3.4(i):

- the value units are exactly those attached to the two diagonal quadratic
  values;
- the binary parameter is their quotient;
- the relative order is the second diagonal order minus the first;
- the determinant-normalized invariant is the refined unit-square class of
  that quotient.

These formulas apply directly to the BONG constructed in M38 and introduce no
new assumptions.  The public M39 API is in `Bong.Bong.OrthogonalBasis`.

## M40 diagonal modularity

M40 proves the exact modularity criterion for anisotropic orthogonal basis
lattices and specializes it to rank two:

- globally rescaling a field basis rescales its integral basis lattice;
- coordinatewise multiplication by valuation units leaves the lattice fixed;
- membership in a basis lattice is characterized by integral coordinates;
- the dual of an orthogonal basis divides each vector by its quadratic value;
- such a basis lattice is `a`-modular exactly when every diagonal value has
  the same order as `a`;
- in rank two, modularity at the first value is therefore equivalent to
  equality of the two diagonal orders.

This establishes both directions of the diagonal boundary case of Beli
(2003), Lemma 3.3(i), without extra assumptions.  The public M40 API is in
`Bong.Lattice.BasisUnits`, `Bong.Lattice.DiagonalModular`, and
`Bong.Bong.BinaryModular`.

## M41 modular volume and binary parity

M41 proves the determinant and volume identities needed for Beli (2003),
Lemma 3.3(iii):

- a lattice volume may be computed in any ambient basis whose integral span
  is that lattice;
- rescaling a rank-`n` lattice by `a` adds `2n ord(a)` to its volume order;
- taking the integral dual negates the volume order;
- an `a`-modular rank-`n` lattice therefore has volume order `n ord(a)`;
- for a binary BONG on such a lattice,
  `R(L) = 2 ord(a) - 2 R₁`, so `R(L)` is even;
- in the nonnegative diagonal branch, modularity at the first BONG value is
  equivalent to zero relative order.

All determinant changes are proved from integral transition matrices and use
only standard Lean axioms.  The public M41 API is in
`Bong.Lattice.DeterminantBasis`, `Bong.Lattice.ModularVolume`, and
`Bong.Bong.BinaryModularInvariant`.

## M42 norm ideals of modular duals

M42 completes the norm-ideal calculation used in Beli (2003), Lemma 3.3(iii)
and Corollary 3.4(iii):

- a norm generator `x` of `L` rescales to the norm generator `c x` of `cL`;
- if `L` is `a`-modular, then `a⁻¹x` is a norm generator of `L♯`;
- for a binary BONG, `2 ord(a) = R₁ + R₂`;
- the quadratic value of the displayed dual norm generator has order `-R₂`;
- hence `n(L♯)` is the principal ideal generated by a value of order `-R₂`.

Together with the head norm-generator identity `nL = (a₁)`, this proves the
three order formulas `ord(sL) = (R₁+R₂)/2`, `ord(nL) = R₁`, and
`ord(nL♯) = -R₂` whenever the modular parameter is supplied.  The public M42
API is in `Bong.Lattice.NormRescale` and
`Bong.Bong.BinaryModularInvariant`.

## M43 the modular direction of the binary criterion

M43 proves the unconditional modular-to-order direction of Beli (2003),
Lemma 3.3(i), and packages the remaining numerical assertions of
Lemma 3.3(iii) and Corollary 3.4(iii):

- the first BONG value generates the norm ideal exactly;
- the second value is the determinant divided by the first value in the
  refined unit-square-class group;
- modularity gives `R₂ = 2 ord(a) - R₁` and `R₁ ≡ R₂ (mod 2)`;
- the scaled head lies in the dual lattice, so integrality of its pairing
  with the head proves `ord(a) ≤ R₁`;
- consequently every modular binary BONG satisfies `R(L) ≤ 0`, equivalently
  `R₂ ≤ R₁`.

This direction uses only the definition `L♯ = a⁻¹L`; no scale-generator
axiom is assumed.  The converse `R(L) ≤ 0 → L modular` remains the next
binary structure theorem.  The public M43 API is in
`Bong.Bong.BinaryInvariant` and `Bong.Bong.BinaryModularInvariant`.

## M44 scale-and-volume criterion for modularity

M44 isolates the basis-free mechanism needed for the converse direction of
Beli (2003), Lemma 3.3(i):

- equality of lattice volume orders implies equality of their principal
  volume ideals;
- a nested pair of full lattices with equal volume order is equal;
- if every pairing in `L` is divisible by `a`, then `a⁻¹L ⊆ L♯`;
- if additionally `ord(vol L) = rank(L) ord(a)`, volume rigidity upgrades
  that inclusion to `L♯ = a⁻¹L`.

Thus the remaining strict-negative binary case is reduced to an explicit
two-by-two calculation: find one mixed pairing `c` that divides the whole
Gram matrix and prove `ord(vol L) = 2 ord(c)`.  The public M44 API is in
`Bong.Lattice.VolumeRigidity` and `Bong.Lattice.ModularCriterion`.

## M45 a binary BONG-adapted integral basis

M45 supplies the exact integral basis needed for the strict-negative branch:

- the norm-generator projection sequence is exposed as an integral linear
  equivalence `L ≃ 𝒦 × pr(L)`;
- any chosen integral basis of the projected lattice lifts to an adapted
  integral basis of `L`;
- a unary BONG vector is bundled as an integral basis of its actual lattice;
- specializing the lift to the unary tail gives a binary basis whose first
  vector is the BONG head and whose second vector projects to the tail head;
- consequently the quadratic value of that projection is exactly `a₂`.

The construction is unconditional.  It turns the remaining proof into the
literal two-by-two Gram calculation in Beli's argument.  The public M45 API is
in `Bong.Lattice.DeterminantProjection`, `Bong.Lattice.AdaptedBasis`,
`Bong.Bong.BasisLattice`, and `Bong.Bong.BinaryAdaptedBasis`.

## M46 complete binary modularity criterion

M46 completes Beli (2003), Lemma 3.3(i), including its strict-negative
branch:

- in the BONG-adapted integral basis, let `c` be the mixed Gram entry;
- if `R₂ < R₁`, the projected norm containment and the ultrametric
  equality give `2 ord(c) = R₁ + R₂`, in particular `c ≠ 0`;
- this order identity shows that `c` divides all four adapted Gram entries;
- the determinant has order `2 ord(c)`, so the scale-and-volume criterion
  proves that the lattice is `c`-modular;
- the equality branch `R₂ = R₁` is the diagonal modular case from M40;
- combining both branches with M43 yields
  `L modular ⇔ R(L) ≤ 0 ⇔ R₂ ≤ R₁`.

The result is unconditional and uses only Lean's standard quotient and
choice axioms.  The public M46 API is in `Bong.Lattice.ScaleBasis` and
`Bong.Bong.BinaryStrictModular`.

## M47 modular binary normal forms

M47 completes the remaining ideal-theoretic content of Beli (2003),
Lemma 3.3(iii), and Corollary 3.4(iii):

- a positive-rank `a`-modular lattice has scale ideal exactly `(a)`;
- the reverse scale inclusion is witnessed constructively by an integral
  basis vector and its bilinear dual vector;
- any prescribed anisotropic norm generator extends to a binary BONG;
- its second order is `2 ord(a) - R₁`, while its unit-square class is the
  determinant class divided by the first value class;
- the scale, norm, and dual norm ideals have generators of orders
  `(R₁+R₂)/2`, `R₁`, and `-R₂`, respectively;
- the two BONG orders are congruent modulo two.

All formulas are unconditional and use only standard Lean axioms.  The
public M47 API is in `Bong.Lattice.ModularScale` and
`Bong.Bong.BinaryNormalForm`.

## M48 explicit realization of binary invariants

M48 supplies the constructive core of Beli (2003), Lemmas 3.5--3.6:

- the symmetric Gram model `[[1,c],[c,c²+a]]` is constructed and proved
  nondegenerate with determinant `a`;
- the conditions `2c ∈ 𝒪` and `c²+a ∈ 𝒪` make its first standard
  vector a norm generator of the standard integral lattice;
- the resulting concrete binary BONG has first value one and refined binary
  invariant represented by `a`;
- conversely, every binary BONG supplies such a witness
  `c = B(x₁,y)/Q(x₁)` from its adapted integral basis;
- hence the operational admissibility condition is exactly the set of
  refined classes realized by binary BONGs.

The construction is unconditional.  The public M48 API is in
`Bong.QuadraticSpace.BinaryModel`, `Bong.Lattice.DeterminantBasis`, and
`Bong.Bong.BinaryRealization`.

## M49 Beli's binary quadratic-defect criterion

M49 completes the criterion in Beli (2003), Lemma 3.5:

- an absolute defect is integral exactly when a square approximation has
  integral error;
- every operationally admissible parameter satisfies
  `ord(a) ≥ -2e`;
- in the nonsquare case, an integral error forces the missing condition
  `2c ∈ 𝒦`; this follows by contradiction from the local `2e` defect
  bound;
- in the square case, `ord(a) ≥ -2e` is sufficient by choosing an actual
  square root of `-a`;
- consequently the operational parameter and refined-class predicates are
  equivalent to Beli's two-case formulation.

The equivalence is parameterized by `QuadraticDefectLaws`, which records the
local square theorem and the sharp nonsquare `2e` bound.  Its proofs use only
Lean's standard quotient and choice axioms.  The public M49 API is in
`Bong.Bong.BinaryDefectCriterion`.

## M50 exact normalized binary realization

M50 completes the normalized constructive content of Beli (2003),
Lemma 3.6:

- the orthogonalized vector `e₁ - c e₀` is bundled as an explicit basis
  of the complement of `e₀`;
- the projection of the standard integral model lattice is proved equal to
  the lattice generated by this vector;
- the resulting recursively constructed BONG has values exactly `1` and
  `a`, rather than values agreeing only modulo valuation-unit squares;
- its scalar binary parameter is therefore definitionally realized as `a`;
- operational admissibility is equivalent to existence of this exact model.

The construction is unconditional and uses only Lean's standard quotient and
choice axioms.  The public M50 API is in
`Bong.Bong.BinaryExactRealization`.

## M51 stability of the binary admissible set

M51 formalizes the admissibility part of Beli (2003), Lemma 3.8:

- multiplying an admissible parameter by the square of an integral nonzero
  scalar preserves admissibility;
- multiplying by a valuation-unit square is an equivalence, since its inverse
  is integral as well;
- the operational predicate therefore depends only on the refined class in
  `Kˣ / (𝒦ˣ)²`;
- the existential class predicate can consequently be checked on any chosen
  representative.

All results are unconditional and use only Lean's standard quotient and choice
axioms.  The public M51 API is in `Bong.Bong.BinaryAdmissibility`.

## M52 uniform order-and-defect form of the binary criterion

M52 reconciles the formulation of the admissible set in Beli 2003 with the
one recalled in Beli 2006 and Beli 2009/2010:

- `absoluteDefectThreshold(a) = max(0, -ord(a))` is the relative
  approximation depth needed for an integral absolute error;
- satisfying that threshold is equivalent to the existence of `x` with
  `a - x² ∈ 𝒦`;
- it is also equivalent to the extended-order inequality encoded by
  `ord(a) + d(a) ≥ 0`;
- consequently `a` is a binary BONG parameter exactly when
  `ord(a) + 2e ≥ 0` and `ord(a) + d(-a) ≥ 0`.

The last equivalence uses `QuadraticDefectLaws`; the threshold equivalence is
unconditional.  The public M52 API is in
`Bong.Dyadic.AbsoluteQuadraticDefect` and
`Bong.Bong.BinaryDefectCriterion`.

## M53 spinor-image inclusion for binary lattices

M53 completes the spinor-norm consequence of Beli (2003), Lemma 3.2(i), used
in the proof of Lemma 3.8:

- a nested pair of binary lattices with a common BONG head has the canonical
  injective homomorphism between its integral orthogonal groups;
- this homomorphism retains the same ambient isometry;
- its Wall spinor norm is therefore unchanged;
- hence the integral spinor-norm image of the smaller lattice is contained in
  that of the larger lattice.

The result is unconditional and uses only Lean's standard quotient and choice
axioms.  The public M53 API is in
`Bong.Bong.BinarySpinorInclusion`.

## M54 integral-square shifts and Beli 2003, Lemma 3.8

M54 completes the geometric and spinor-norm part of Beli (2003), Lemma 3.8:

- rescaling any lattice by a nonzero integral scalar produces a sublattice;
- the unary tail of a binary BONG can be rescaled explicitly by such a scalar;
- the projection-preimage construction keeps the original first norm
  generator and replaces only the projected tail;
- the resulting binary BONG has parameter exactly `a * s ^ 2` when the
  original parameter is `a`;
- the new lattice is contained in the original lattice, so its integral
  spinor-norm image is contained in the original image.

Together with M51, this gives both conclusions of the lemma: admissibility of
the shifted parameter and monotonicity of its realized spinor-norm image.  The
construction is unconditional and uses only Lean's standard quotient and
choice axioms.  The public M54 API is in
`Bong.Bong.BinaryIntegralSquare`.

## M55 quadratic value sets and Corollary 3.10(a)

M55 begins the value-set analysis following Beli (2003), Lemma 3.8:

- `quadraticValueSet q L` is the formal set `Q(L)`;
- `integralSquareResidueSet I` is the basis-free form of `𝓞² + I`;
- the quadratic value of any vector is expanded explicitly in the two BONG
  coordinates;
- when the first value is `1` and the binary order is positive, the lattice
  is the integral span of its orthogonal BONG basis;
- every value of the lattice is therefore an integral square modulo the
  principal ideal generated by the second BONG value.

This is Corollary 3.10(a), with the ideal `(a₂)` replacing the choice-dependent
notation `𝔭ᴿ`.  All results are unconditional and use only Lean's standard
quotient and choice axioms.  The public M55 API is in
`Bong.Lattice.QuadraticValues` and `Bong.Bong.BinaryValueSet`.

## M56 norm-generator values and Lemma 3.11 reduction

M56 formalizes the ideal-theoretic first step of Beli (2003), Lemma 3.11:

- two nonzero scalars generate the same coefficient ideal exactly when their
  quotient is a valuation unit;
- relative to any fixed anisotropic norm generator, another lattice vector is
  a norm generator exactly when the quotient of their quadratic values is a
  valuation unit;
- after normalizing the fixed generator to value `1`, this simply says that
  the other quadratic value is a valuation unit;
- consequently the norm-generator value set is exactly
  `Q(L) ∩ {valuation units}`;
- in the positive binary-order branch this set inherits the M55 containment
  modulo the second-value ideal.

The results are unconditional and use only Lean's standard quotient and choice
axioms.  The public M56 API is in
`Bong.Lattice.NormGeneratorValues` and `Bong.Bong.BinaryValueSet`.

## M57 adapted binary values and the modular core of Corollary 3.10

M57 establishes the common algebraic calculation behind Corollary 3.10(b,c):

- every vector of a binary BONG lattice has two coefficients in the valuation
  ring with respect to the projection-adapted integral basis;
- its quadratic value is expanded into the head square, the adapted second
  diagonal term, and the mixed term;
- `binaryValueErrorIdeal` is generated by `2B(x,y)` and `Q(y)`;
- if the head value is normalized to `1`, every lattice value is an integral
  square modulo this error ideal;
- the same containment holds for the norm-generator value set.

The remaining distinction between parts (b) and (c) is now reduced to bounding
this error ideal by the appropriate defect-dependent principal ideal.  M57 is
unconditional and uses only Lean's standard quotient and choice axioms.  Its
public API is in `Bong.Bong.BinaryAdaptedValues`.

## M58 valuation criterion for the binary error ideal

M58 converts the adapted calculation of M57 into the exact interface needed
for the two modular branches of Corollary 3.10:

- if a principal ideal contains both `2B(x,y)` and `Q(y)`, it contains the
  complete binary error ideal;
- it suffices to compare the valuations of those two coefficients with the
  valuation of a chosen nonzero generator `t`;
- under these two inequalities, every value in `Q(L)` is an integral square
  modulo `(t)`.

Thus Corollary 3.10(b,c) is reduced to the normal-form valuation estimates
`ord(t) ≤ ord(2B(x,y))` and `ord(t) ≤ ord(Q(y))`.  The result is
unconditional and uses only Lean's standard quotient and choice axioms.  The
public M58 API is in `Bong.Bong.BinaryAdaptedValues`.

## M59 maximal-ideal powers and the original form of Corollary 3.10(a)

M59 restores the paper's uniformizer-power notation in a choice-controlled
way:

- `uniformizerPowerUnit K r` is the selected uniformizer to an integral power;
- `powerIdeal r` formalizes the fractional ideal `𝔭ʳ`;
- membership is exactly `(r : WithTop Int) ≤ ord(a)`;
- inclusion of power ideals reverses the order of their exponents;
- every nonzero principal ideal equals the power ideal indexed by its
  generator's valuation;
- M55's positive-order containment is consequently restated verbatim as
  `Q(L) ⊆ 𝓞² + 𝔭ᴿ`, with `R = binaryOrderGap`.

All results are unconditional and use only Lean's standard quotient and choice
axioms.  The public M59 API is in `Bong.Lattice.PowerIdeal` and
`Bong.Bong.BinaryValueSet`.

## M60 congruence and norm subgroups in the square-class group

M60 supplies the group language required by Beli (2003), Definitions 4 and 6:

- `principalUnitSubgroup K n` is the group of valuation units congruent to
  `1` modulo `𝔭ⁿ`;
- these groups form a decreasing filtration;
- their images in `Kˣ / Kˣ²` formalize `(1 + 𝔭ⁿ)Kˣ² / Kˣ²`;
- the image of all valuation units formalizes `𝓞ˣKˣ² / Kˣ²`;
- the image of `quadraticNormGroup K a` formalizes Beli's `N(a)` inside the
  square-class group;
- the filtration and its inclusion into the valuation-unit square classes are
  proved at the subgroup level.

The constructions and filtration proofs are unconditional and use only Lean's
standard quotient and choice axioms.  The public M60 API is in
`Bong.Dyadic.CongruenceSubgroup`.

## M61 valuation-unit square classes for Beli's function `g`

M61 distinguishes the codomain of Definition 6 from the coarser field
square-class group used by Definition 4:

- `ValuationUnitClass K` is exactly `𝓞ˣ / 𝓞ˣ²`;
- the principal-unit filtration is restricted to valuation units and mapped
  to this quotient;
- the valuation-unit part of each quadratic norm group is mapped to the same
  quotient;
- the decreasing principal-unit filtration is proved again in the correct
  codomain.

This supplies the exact subgroup types needed for the piecewise definition of
`g(a)` and Lemma 3.11.  The constructions are unconditional and use only
Lean's standard quotient and choice axioms.  The public M61 API remains in
`Bong.Dyadic.CongruenceSubgroup`.

## M62 Beli 2003, Definition 6

M62 formalizes the piecewise norm-generator group `g(a)`:

- every parameter is decomposed canonically as `a = πᴿ ε`, with `ε` proved to
  be a valuation unit;
- `beliParameterDefect a` is the paper's `d(-a)` (hence zero at odd order);
- the low-defect exponent `R + d`, high-defect exponent `R/2 + e`, and doubled
  cutoff `2e - R` are encoded without half-integer rounding in comparisons;
- the three branches of Definition 6 are defined in
  `𝓞ˣ / 𝓞ˣ²`: the trivial group, a principal-unit/norm-group intersection, and a
  principal-unit subgroup;
- branch reduction theorems expose each original formula directly.

The integer-to-natural conversions make the function total outside the
admissible set; M52 supplies the inequalities that make all exponents exact on
admissible binary parameters.  The definition is unconditional and uses only
Lean's standard quotient and choice axioms.  The public M62 API is in
`Bong.Dyadic.BeliGroups`.

## M63 Beli 2003, Lemma 3.11

M63 connects actual binary norm generators to Definition 6:

- every norm generator of a binary lattice is proved anisotropic;
- its quotient `Q(y) / Q(x₁)` is bundled as a nonzero field element and proved
  to be a valuation unit;
- the quotient is mapped to the exact group `𝓞ˣ / 𝓞ˣ²`;
- the complete set of such classes is defined without choosing representatives;
- Lemma 3.11 identifies this set with `beliNormGeneratorGroup`.

The ideal-theoretic direction is unconditional.  The final equality is exposed
through `BinaryNormGeneratorLocalLaws`: this isolates precisely the reverse
value-set argument whose high-defect branch uses the Hensel/Newton-polygon
calculation on page 139.  No opaque Lean axiom is introduced; downstream
theorems carry this local-law assumption explicitly.  The public M63 API is in
`Bong.Bong.BinaryNormGeneratorGroup`.

## M64 Beli 2003, paragraph 3.12

M64 upgrades the quotient-class statement of Lemma 3.11 to an exact
representative statement:

- multiplying a norm generator by a valuation unit preserves the norm-generator
  property;
- its value ratio is multiplied by the square of that unit;
- equality in `𝓞ˣ / 𝓞ˣ²` is unpacked into an actual valuation-unit square;
- that square is absorbed by rescaling the norm generator, producing an exact
  value ratio equal to any prescribed representative of a class in `g(a)`.

Only the invocation of Lemma 3.11 carries `BinaryNormGeneratorLocalLaws`; the
rescaling and representative argument are unconditional.  The public M64 API
is in `Bong.Lattice.NormGeneratorValues` and
`Bong.Bong.BinaryNormGeneratorGroup`.

## M65 Beli 2003, Definitions 4 and 5

M65 formalizes the complete binary spinor-group formula on a representative
`a : Kˣ`:

- the inadmissible and exceptional hyperbolic cases are explicit;
- all six numbered branches of `G(a)` are encoded with doubled or fourfold
  comparisons, so no fractional inequalities are rounded;
- the final exponent is exactly
  `e - floor((2e - R) / 4)`;
- `G'(a)` retains its stated domain `R > 2e` as a proof parameter;
- the identity `G(a) = ⟨a⟩ G'(a)` is proved in that domain.

The representative-level name records that Definition 4 still has to be
descended from `Kˣ` to `Kˣ / 𝓞ˣ²`.  Every branch theorem is unconditional and
uses only standard Lean axioms.  The public M65 API is in
`Bong.Bong.BinarySpinorGroupFormula`.

## M66 Definition 4 on its quotient domain

M66 proves that every ingredient in the representative formula is invariant
under multiplication by a valuation-unit square:

- admissibility and additive order;
- the parameter defect `d(-a)` and all cutoff exponents;
- the cyclic square-class subgroup and quadratic norm subgroup;
- the exceptional class represented by `-1/4`.

Consequently `beliSpinorGroup` is a well-defined function on the exact domain
`Kˣ / 𝓞ˣ²` of Beli's Definition 4.  Additive order is also descended to that
quotient for later use with Definition 5.  The proof is unconditional and uses
only standard Lean axioms.  The public M66 API is in
`Bong.Bong.BinarySpinorGroupInvariant`.

## M67 Definition 5 on its quotient domain

M67 proves valuation-unit-square invariance for the representative formula of
`G'(a)` and descends it to `Kˣ / 𝓞ˣ²`.  The paper-facing definition retains the
hypothesis `R > 2e`, expressed intrinsically through the descended class order.
The cyclic factor is likewise defined directly from a refined square class.

For every admissible nonexceptional class in that domain, the quotient-level
identity `G(A) = ⟨A⟩ G'(A)` is proved.  The construction is unconditional and
uses only standard Lean axioms.  The public M67 API is in
`Bong.Bong.BinaryAuxiliarySpinorGroup`.

## M68 Beli 2003, Lemma 3.7

M68 connects the integral spinor-norm image of a binary lattice to Definition
4.  The cited local calculations of Hsia and Xu are exposed through the
explicit assumption `BinarySpinorLocalLaws`; no theorem is postulated as an
opaque Lean axiom.

From that input the file proves both forms used by Beli:

- `θ(O(L)) = G(a₂/a₁)` for a binary BONG;
- `θ(O(L)) = G(a(L))` for the determinant-normalized lattice invariant.

The conversion between the two forms, including quotient descent and BONG
independence of `a(L)`, is fully formalized.  The public M68 API is in
`Bong.Bong.BinarySpinorGroup`.

## M69 Beli 2003, Lemma 3.8

M69 upgrades the earlier sublattice construction to the formula-level
monotonicity theorem for `G`:

- an integral-square change of a binary parameter is realized by a concrete
  binary sublattice with the same norm generator;
- inclusion of integral orthogonal groups gives inclusion of spinor-norm
  images, and Lemma 3.7 converts this into inclusion of the `G` subgroups;
- from `R ≤ R'` and `R' ≡ R (mod 2)` Lean constructs `k : ℕ` with
  `R' = R + 2k`;
- the identities for `πᵏ`, its integrality, both parameter orders, shifted
  admissibility, and `G(πᴿ'ε) ≤ G(πᴿε)` are all proved.

The only specialized input is the same explicit `BinarySpinorLocalLaws`
assumption used by Lemma 3.7.  The public M69 API is in
`Bong.Bong.BinarySpinorMonotonicity`.

## M70 Beli 2003, Corollary 3.10(b,c)

M70 completes the two even-order branches of Corollary 3.10.  The exact local
normal-form input from paragraph 3.9 is isolated at coefficient level in
`BinaryDefectAdaptedLocalLaws`: it records the orders of the mixed and second
diagonal entries, including the zero entry in the square case.

From those coefficient identities and the unconditional M57–M58 value
formula, Lean proves:

- in the high-defect branch, `Q(L) ⊆ 𝓞² + 𝔭^(R/2+e)`;
- in the low-defect branch, `Q(L) ⊆ 𝓞² + 𝔭^(R+d)`.

All half-integer expressions are justified by the evenness hypothesis, and
nonnegativity of the exponents is proved rather than assumed.  No opaque axiom
is introduced.  The public M70 API is in
`Bong.Bong.BinaryDefectAdaptedValues`.

## M71 Canonical unit-square-class image

M71 makes explicit the quotient change used in Beli 2003, Lemma 3.16.  It
constructs the canonical homomorphism
`𝓞ˣ / 𝓞ˣ² → Kˣ / Kˣ²`, proves its value on representatives, and
maps the norm-generator group `g(a)` into the field square-class group as
`beliNormGeneratorSquareClassGroup`.

Thus later inclusions between `g(a)` and `G(a)` are typed between subgroups of
the same ambient group, without silently identifying distinct quotients.  The
construction is unconditional and uses only standard Lean axioms.  The public
M71 API is in `Bong.Bong.BinaryNormGeneratorSquareClass`.

## M72 Integral reflections and multiplicative spinor norms

M72 proves directly that reflection in every anisotropic norm generator is
integral.  The proof uses `2sL ⊆ nL` and the defining equality
`nL = Q(x)𝓞`, so the reflection coefficient is exhibited as an element of
the valuation ring.

It also exposes Wall-spinor multiplicativity through the explicit
`SpinorNormMultiplicativeLaws` interface, and from it bundles the integral
spinor norm as a group homomorphism.  Its range subgroup has exactly the
carrier of the previously defined `θ(O(L))`.  The public M72 APIs are in
`Bong.Lattice.Reflection` and `Bong.Lattice.SpinorNormMultiplicative`.

## M73 Beli 2003, paragraph 3.16: `g(a) ⊆ G(a)`

M73 follows Beli's geometric proof.  Every class in `g(a)` is first realized
by an actual norm generator using Lemma 3.11 and paragraph 3.12.  Reflections
in that vector and in the BONG head are integral by M72; multiplicativity of
the spinor norm identifies the spinor class of their product with the given
unit class.  Lemma 3.7 then converts membership in `θ(O(L))` to membership in
`G(a)`.

The theorem is stated using M71's canonical map
`𝓞ˣ / 𝓞ˣ² → Kˣ / Kˣ²`, so the inclusion is type-correct.  The public M73 API is
in `Bong.Bong.BinaryNormGeneratorSpinorInclusion`.

## M74 Beli 2003, paragraph 3.16: `a ∈ G(a)`

M74 constructs `-id` both as an ambient isometry and as an integral lattice
automorphism.  On the two vectors of a binary orthogonal BONG basis, Lean
proves that the composite of the two coordinate reflections is exactly
`-id`.  Reflection normalization and spinor-norm multiplicativity then give
`θ(-id) = [a₁a₂] = [a₂/a₁]`, the square class of the binary
parameter.

Together with M73, `beliParagraph316` now contains both statements from
paragraph 3.16: the canonical image of `g(a)` lies in `G(a)`, and `a` itself
belongs to `G(a)`.  The public M74 API is in
`Bong.Bong.BinaryParameterSpinorMembership`.

## M75 Definition 6 source correction and quotient embedding

During the Lemma 3.13 audit, M75 corrected Definition 6(I) against the printed
paper: for `R > 2e`, `g(a)=𝓞ˣ²`, so its subgroup in
`𝓞ˣ/𝓞ˣ²` is bottom, not top.  It also restores the printed strict
boundary `R > 2e` and the low-defect condition `d ≤ e-R/2` (encoded as
`2d ≤ 2e-R`).

The canonical map `𝓞ˣ/𝓞ˣ² → Kˣ/Kˣ²` is now proved injective, and Lean
computes the exact field-square-class images of the principal-unit and norm
branches.  This supplies source-correct branch theorems for Lemmas 3.13–3.15.
The public M75 APIs are in `Bong.Dyadic.CongruenceSubgroup` and
`Bong.Bong.BinaryNormGeneratorSquareClass`.

## M76 Beli 2003, Lemma 3.13(i)

M76 proves the exact identity
`G'(πᴿε) = g(πᴿ⁻²ᵉε)Kˣ²` for `R > 2e`.  Lean verifies the
normalization of the unit factor, equality of defects, both filtration
exponent shifts, the cutoff shift, and invariance of the quadratic norm group
under the square `(πᵉ)²`.  The proof then matches all three branches of the
corrected Definition 6 with Definition 5.

No new local-field assumption is needed for this equality.  The public M76
API is in `Bong.Bong.BeliLemma313`.

## M77 Beli 2003, Lemma 3.13(i), congruence inclusion

M77 adds the second assertion of Lemma 3.13(i):
`G'(πᴿε) ⊇ (1+𝓅ᴿ⁻²ᵉ)Kˣ²`.  It is derived from M76's exact
group identity and the principal-unit inclusion recorded in the remark after
Lemma 3.11.

The remaining Hensel/value-set content of that remark is exposed as the
explicit field-level interface `BeliNormGeneratorCongruenceLaws`; the group
shift and inclusion proof introduce no opaque axiom.  The public M77 API is in
`Bong.Bong.BeliLemma313`.

## M78 Beli 2003, Lemma 3.13(ii), even-order comparison

M78 proves the exact identity
`G(πᴿε) = g(πᵀε)Kˣ²`, where
`T = -2⌊e/2-R/4⌋`, under the printed hypotheses that `R ≤ 2e` is even and
`d(-ε) > e-R/2`.  Lean verifies the floor arithmetic, the middle/high branch
correspondence, the square change of norm parameter, and every filtration
exponent.

The proof also handles the exceptional refined class `-1/4`: Lean computes
its order as `-2e`, its parameter defect as infinite, and both sides as the
full valuation-unit square-class subgroup.

The only new local-field inputs are exposed as the precise interfaces
`UnitQuadraticDefectParityLaws` and
`PrincipalUnitSquareClassFiltrationLaws`.  They record respectively the
oddness of unit defects below `2e` and the equality of adjacent square-class
filtration layers at positive even depth.  The public M78 API is in
`Bong.Bong.BeliLemma313II`.

## M79 Beli 2003, Hilbert duality lemmas

M79 formalizes the character algebra used by Lemma 3.14.  The Hilbert
character is descended to `Kˣ/Kˣ²`, and its kernel is proved to be exactly the
quadratic norm square-class subgroup.  From the fact that an integer unit is
`1` or `-1`, Lean proves both subgroup identities of Beli's Lemma 1.3 and the
index-two coset argument used later in Section 3.

The concrete principal-unit containment criterion of Lemma 1.2(iii) is the
single local-field input in `BeliHilbertCongruenceLaws`; the duality identities
themselves are derived rather than assumed.  The public M79 API is in
`Bong.Dyadic.HilbertDuality`.

## M80 Beli 2003, Lemma 3.14

M80 proves the printed product formula
`g(πᴿε)g(πᴿη) = (1+𝔭ᴿ⁺ᵈ⁽ᵋᶯ⁾)Kˣ² g(πᴿε)` for `R ≤ 2e`.
The formal proof follows all three cases in Beli's argument: unequal defects,
equal low defects, and two high defects.  The first two cases use the derived
Hilbert-kernel identities from M79; the last uses the quadratic-defect
domination theorem.

The source audit also corrects Definitions 4--6 uniformly: their parameter is
the actual relative defect `d(-a)`, not the defect of a normalized unit part.
Thus odd-order parameters have defect zero, while the familiar `d(-ε)`
formula is used only for even `R`.  Admissibility supplies
`ord(a)+d(-a) ≥ 0` directly from Lemma 3.5, so Lemma 3.14 needs no additional
admissibility axiom.  The only local congruence input remains
`BeliHilbertCongruenceLaws`.  The public M80 API is in
`Bong.Bong.BeliLemma314`.

## M81 Beli 2003, Corollary 3.15

M81 proves both product formulas of Corollary 3.15.  For `2e < R ≤ 4e`,
Lean transports Lemma 3.14 through `G'(πᴿε)=g(πᴿ⁻²ᵉε)` and performs the
cyclic square-class change of generators.  For even `R ≤ 2e`, it transports
through Lemma 3.13(ii) and obtains the printed layer
`(1+𝔭ᴿ⁄²⁺ᵈ⁽ᵋᶯ⁾⁻ᵉ)Kˣ²`.

The floor-parity exception in the paper is proved explicitly.  Below the
maximal finite defect, adjacent layers agree by the even-step filtration law.
At defect `2e`, Lean derives
`(1+𝔭ᴿ⁄²⁺ᵉ)Kˣ² ≤ G(πᴿε)` directly from Definition 4 and Lemma 1.2(iii), so
the extra layer is absorbed.  The public M81 API is in
`Bong.Bong.BeliCorollary315`.

## M82 Beli 2003, Lemma 3.17, normalized binary models

M82 formalizes assertions (1) and (2) of Lemma 3.17 in the canonical Gram
model `[[1,c],[c,c²+a]]`.  It proves that a coordinate solution with integral
first coefficient and unit second coefficient is equivalent to an actual
second norm generator of the same value which, together with the first,
spans the complete model lattice.

Lean also proves directly that two admissible shears `c,c'` for the same
parameter differ by an integer.  The explicit coordinate change transports
the equal-value basis witness between them, yielding the normalized
equivalence `(1) ↔ (2)` without a new local-field axiom.  The public M82 API
is in `Bong.Bong.BeliLemma317`.

## M83 Beli 2003, Lemma 3.17, four-case classification

M83 completes Lemma 3.17 by proving that the universal equal-norm-generator
assertion is equivalent to Beli's four parameter alternatives.  The Lean
statement includes the infinite-defect part of case (iii): when
`d(-ε)=∞`, its strict defect-boundary condition is automatic.

Necessity is proved through the four coordinate obstructions in Beli's
argument: odd parameter order, unequal defect-adapted correction orders, the
exceptional `-1/4` class, and the endpoint `R=2e`.  The finite and infinite
defect branches share a formal square-difference parity interface; the
two-element residue-field endpoint uses the corresponding discriminant
interface.  These are generic dyadic local-field laws rather than assumptions
of Lemma 3.17 itself.

The public theorem `Bong.BONG.beliLemma317` records `(1) ↔ (2)` and
`(2) ↔ (3)`, while the two projections
`hasSomeEqualNormGeneratorBasis_iff_parameterCases` and
`hasEveryEqualNormGeneratorBasis_iff_parameterCases` expose the direct
equivalences.  The public M83 API is in `Bong.Bong.BeliLemma317`.

## M84 Beli 2003, Lemma 3.18, equal-value norm generators

M84 completes all three assertions of Lemma 3.18.  If two binary norm
generators have equal quadratic value and anisotropic difference, Lean proves
that reflection in their difference preserves the lattice.  The proof maps a
BONG by the reflection and invokes binary uniqueness from Lemma 3.2(ii), so
the integrality assertion is derived rather than postulated.  Multiplying this
reflection by reflection in the first generator places
`Q(x) Q(x - x')` in `G(a(L))`.

For `R(L) > 2e`, integral orthogonal coordinates give
`1 - α² = β² a(L)`.  A valuation factorization proves that exactly one of
`1 - α` and `1 + α` has order `e`; consequently both signed differences have
order at least `ord Q(x) + 2e`, with exactly one equality.  In the equality
case, M84 constructs the head-scaled lattice generated by `π^e x` and the
orthogonal companion.  Its parameter is `a(L) / π^(2e)`, and `x - x'` is a
norm generator of this lattice.  The representative-free form of Lemma
3.13(i) then gives membership in `G'(a(L))`.

The public theorem `Bong.BONG.beliLemma318` collects parts (i)--(iii); the
individual integrality, order-dichotomy, `G`, and `G'` theorems remain
available in `Bong.Bong.BeliLemma318`.

## M85 Beli 2003, Lemma 3.19, the scaled hyperbolic plane

M85 proves that vectors `x,y` satisfying
`ord Q(x), ord Q(y) > R` and `ord Q(x+y) = R` generate a lattice isometric
to `π^(R-e) A(0,0)`.  Lean first derives the exact polarization identity
`ord B(x,y) = R-e`.  The normalized discriminant differs from one at depth
strictly above `2e`, so the quadratic-defect square theorem supplies a square
root; its sign is chosen so that its sum with one has order exactly `e`.

Two explicit integral shears then produce an isotropic basis.  Lean checks
that both the shear matrix and its inverse have valuation-ring entries,
proves that the pair span is nondegenerate, and constructs an actual lattice
isometry to the standard scaled hyperbolic model.  The public intrinsic
statement is `Bong.BONG.beliLemma319`, with conclusion
`Bong.BONG.IsScaledHyperbolicPair`.

## M86 Beli 2003, Definitions 7--9, Lemma 4.1, and Corollary 4.2

M86 begins Section 4 with source-faithful decomposition data:

- property A now requires every Jordan component to have rank exactly one or
  two, excluding vacuous zero-rank components;
- a maximal norm splitting consists of unary or modular-binary components,
  ordered scales, and the exact weak norm-gap inequalities from the remark
  after Definition 8;
- every property-A Jordan splitting is constructed as a maximal norm
  splitting;
- putting together component BONGs is encoded by an order-preserving
  equivalence between global indices and the dependent sum of component
  indices, with equality of the actual ambient vectors;
- Definition 9 is identified definitionally with `BONG.IsGood`;
- `BeliSectionFourLaws` isolates the remaining integral induction in Lemma
  4.1 and the endpoint comparison of Corollary 4.2(ii), with no default
  instance.  Corollary 4.2(i) is obtained from the existing explicit
  Jordan-coordinate interface.

The public M86 APIs are in `Bong.Lattice.MaximalNormSplitting` and
`Bong.Bong.BeliLemma41`.

## M87 Beli 2003, Lemma 4.3

M87 formalizes the characterization of orthogonal bases which occur as good
or property-A BONGs:

- an orthogonal field basis carries intrinsic nonzero values and integral
  valuation orders;
- realization by a BONG means equality of the actual ambient vectors, and
  therefore equality of value and order sequences;
- existence of every adjacent binary lattice is represented by a concrete
  binary carrier, restricted quadratic space, lattice, and two-vector BONG;
- consecutive-segment realization proves the adjacent-pair condition for
  every global BONG;
- the only-if direction of Lemma 4.3(ii) is unconditional, while the only-if
  direction of (i) uses the explicit Jordan-coordinate interface from M6;
- `BeliLemma43ConstructionLaws` isolates the inductive converse construction
  and part (iii)'s maximal norm splitting with improper binary components.  It
  has no default instance.

The public M87 API is in `Bong.Bong.BeliLemma43`.

## M88 Beli 2003, Corollary 4.4

M88 encodes all five parts of Corollary 4.4 with explicit geometric data:

- a BONG segment is promoted to a quadratic sublattice of the ambient space;
- two-block and three-block splitting witnesses contain actual orthogonal
  decompositions and identify every component with the corresponding
  consecutive segment lattice;
- part (iii) means that the adjacent indices map to the same component under
  the exact order-preserving concatenation equivalence from M86;
- part (iv) is expressed as
  `2 ord(sL) = min(2 R₁, R₁ + R₂)`, avoiding any rounded integer division;
- the three cross-boundary inequalities in part (v) are encoded with verified
  zero-based indices and combined with good prefix and suffix segments.

`BeliCorollary44Laws` isolates the remaining integral splitting arguments and
has no default instance.  The public M88 API is in
`Bong.Bong.BeliCorollary44`.

## M89 Beli 2003, Lemmas 4.5--4.7

M89 formalizes the modular replacement and order-profile layer of Section 4:

- a binary-first two-component modular splitting records exact scale and norm
  ideals, component ranks, and the modularity witnesses;
- Lemma 4.5 preserves exact scale ideals and ranks while equalizing either
  norm ideals or the dual norm orders;
- Lemma 4.6's maximal norm splitting existence is isolated in the terminating
  replacement interface `BeliLemma46Laws`;
- from such a splitting, M86's concatenation theorem constructs a good BONG,
  so the second assertion of Lemma 4.6 is formally derived rather than added
  as another assumption;
- Lemma 4.7 is encoded by a lexicographically ordered Jordan profile: at scale
  order `r` and norm order `u`, entries are constantly `r` when `r=u`, and
  otherwise alternate `u, 2r-u`; good-BONG order independence is exposed as
  the stated consequence.

The remaining replacement and profile inductions are carried by the explicit,
non-default interfaces `BeliLemma45Laws`, `BeliLemma46Laws`, and
`BeliLemma47Laws`.  The public M89 API is in
`Bong.Bong.BeliLemmas45To47`.

## M90 Beli 2003, Lemmas 4.8--4.9 and Corollary 4.10

M90 closes Section 4:

- Lemma 4.8's reverse dual good BONG is identified vector-by-vector with
  `Q(x)⁻¹x`, and its values and orders are proved to be the reversed
  reciprocals and reversed negatives;
- Lemma 4.9(i)'s good and property-A segment assertions use the unconditional
  segment construction; its orthogonal-group inclusion and part (ii)'s
  segment replacement are isolated in `BeliLemma49Laws`;
- Corollary 4.10(i) is proved by reflecting in the norm generator of a unary
  segment and transporting its spinor class to the full lattice;
- Corollary 4.10(ii) is proved from the exact binary spinor formula and the
  segment inclusion, with a verified equality between the local binary
  parameter and `a_(i+1)/a_i`;
- the ternary replacement in part (iii) is stated using an actual valuation
  unit representative, its class in `g(a)`, and the resulting twisted `G`
  subgroup.

The public M90 API is in `Bong.Bong.BeliLemmas48To410`.

## M91 Beli 2003, Definition 10, Lemma 4.11, and Remark 4.12

M91 completes the property-B layer at the end of Section 4:

- Definition 10 is exposed with its exact endpoint convention;
- consecutive BONG segments preserve property B, including the normalized
  adjacent defects rather than only their order sequences;
- every adjacent BONG gap is at least `-2e`, and an odd adjacent gap is
  positive; the latter is proved directly from binary admissibility;
- Remark 4.12 is then unconditional: property B implies
  `R_i + 2 ≤ R_(i+2)`;
- Lemma 4.11 is exposed through the explicit non-default
  `BeliLemma411Laws` interface for its remaining integral spinor argument.

The public M91 API is in `Bong.Bong.BeliLemma411`.

## M92 Beli 2003, Theorem 1 forward inclusion

M92 begins Section 5 and gives a literal subgroup formulation of the main
formula in rank at least three:

- `theoremOneTwoStepDepth` is the floored half-gap
  `floor((R_(i+2) - R_i) / 2)`;
- `theoremOneAlpha` is the minimum of the finite nonempty set of all such
  depths, with attainment and comparison lemmas;
- the product of the adjacent `G(a_(i+1)/a_i)` groups is encoded as their
  subgroup supremum, and the principal-unit factor is joined to it to form
  `theoremOneRHS`;
- Corollary 4.10(ii) proves that every adjacent factor lies in the integral
  spinor image;
- an alpha-attaining consecutive ternary segment is constructed, so the
  global principal-unit inclusion follows from the one rank-three
  calculation and Lemma 4.9's exact segment inclusion;
- the long four-case ternary calculation from Section 5 is isolated in the
  explicit non-default `BeliTheoremOneTernaryLaws` interface.

Thus `theoremOneRHS_le_spinorNormImage` is the paper's forward inclusion.
The public M92 API is in `Bong.Bong.BeliTheoremOneForward`.

## M93 Beli 2003, Lemma 6.1

M93 begins the reverse inclusion in Section 6:

- `HeadRescaleWitness` records an actual lattice and BONG obtained by scaling
  only the first BONG vector by a prescribed uniformizer power;
- `HeadDepthWitness` strengthens this with the exact order-threshold carrier
  and preservation of goodness;
- norm generators are proved unconditionally to be exactly the lattice
  vectors whose quadratic value has the minimal BONG order;
- consequently, the first threshold lattice is proved to consist exactly of
  the non-norm-generators, deriving Lemma 6.1(i) from part (ii);
- the two numerical alternatives in part (iii) are encoded literally, and
  property B supplies the required third-vector inequality through M91's
  unconditional two-step estimate.

The remaining integral head-rescaling construction is isolated in the
explicit non-default `BeliLemma61Laws` interface.  The public M93 API is in
`Bong.Bong.BeliLemma61`.

## M94 Beli 2003, Lemma 6.2

M94 formalizes the inverse-rescaling and value-set lemma used throughout the
reverse inclusion:

- `HeadInverseRescaleWitness` records the actual enlarged lattice and BONG
  with first vector `π⁻¹x₁` and every later vector unchanged;
- its first value and order are proved to become `π⁻²a₁` and
  `R₁ - 2`, while all later values and orders are unchanged;
- `scaledIntegralSquareResidueSet a I` gives the literal basis-free meaning
  of the paper's set `a · 𝒪² + I`;
- the cutoff and low/high exponents encode respectively
  `e - (R₂-R₁)/2`, `R₂+d(-ε₁ε₂)`, and
  `(R₁+R₂)/2+e`, including a proof that the natural cutoff has the
  displayed integer value in the even branch;
- if either the original or inverse-rescaled BONG has property B, the
  original BONG is proved good using M91's two-step estimate;
- parts (ii)(a--c) are exposed as exact containments of `Q(L)` in the three
  scaled square-residue sets.

The inverse-rescaling construction and the induction proving the three value
estimates are isolated in the explicit non-default `BeliLemma62Laws`
interface.  The public M94 API is in `Bong.Bong.BeliLemma62`.

## M95 Beli 2003, Definition 11 and Lemma 6.3

M95 formalizes the norm-generator ratio sandwich:

- the binary value-ratio definitions from M56 are generalized from rank two
  to every nonempty BONG, without changing the binary API;
- Definition 11's `beliNormGeneratorUpperGroup` is the exact piecewise group
  `g'(a)`: the full valuation-unit square-class group above `2e`, and the
  appropriate principal-unit subgroup in the two lower branches;
- `g(a) ≤ g'(a)` is proved directly from their piecewise definitions;
- the initial binary prefix is constructed unconditionally, and every one of
  its norm generators is proved to remain a norm generator of the full
  lattice;
- binary Lemma 3.11 therefore proves the lower inclusion
  `g(a₂/a₁) ⊆ {Q(v)/Q(x₁)}` for the full lattice;
- the higher-rank estimates give the upper inclusion into `g'(a₂/a₁)`,
  while property B sharpens it to `g(a₂/a₁)` and hence yields the
  equality in Lemma 6.3(ii).

Only the two higher-rank value estimates are isolated in the explicit
non-default `BeliLemma63Laws` interface; the lower inclusion and final equality
argument are derived.  The public M95 API is in `Bong.Bong.BeliLemma63`.

## M96 Beli 2003, Lemma 6.4

M96 formalizes the hyperbolic-plane containment criterion used in Section 6:

- `ContainsScaledHyperbolicPlane` gives a basis-free meaning to containment
  of the scaled hyperbolic plane appearing in the paper;
- containment is proved to pass unconditionally from an orthogonal component
  or a BONG prefix to the parent lattice;
- unary-first and binary-modular-first orthogonal splittings record the exact
  rank, scale, modularity, and norm hypotheses of parts (i) and (ii);
- part (ii)'s reverse implication and part (iii)'s prefix-to-parent implication
  are derived from the containment-transfer lemmas.

The three difficult exclusion and descent implications are isolated in the
explicit non-default `BeliLemma64Laws` interface.  The public M96 API is in
`Bong.Bong.BeliLemma64`.

## M97 Beli 2003, Lemma 6.5

M97 formalizes the projection-and-reflection lemma following the hyperbolic
plane criterion:

- `headSecondRescaledParameter` is the exact parameter obtained after
  replacing `x₂` by `πᵏ x₂`, and its order is proved to be
  `R₂ + 2k - R₁`;
- `Lemma65Setup` records the least nonnegative admissible `k`, the concrete
  rescaled tail BONG, and non-hyperbolicity of the initial binary lattice;
- the normal projection conclusion and the exceptional residue-two case are
  stated separately, including `k = 2` and failure to be a norm generator in
  the once-rescaled tail;
- parts (ii) and (iii) use a single witness carrying both anisotropy of
  `x₁-x` and integrality of its reflection, while part (iv) derives
  anisotropy unconditionally from the prescribed finite order;
- the reflection is proved unconditionally to carry `x₁` to `x` whenever
  their quadratic values agree.

The remaining valuation estimates and integral-reflection arguments are
isolated in the explicit non-default `BeliLemma65Laws` interface.  The public
M97 API is in `Bong.Bong.BeliLemma65`.

## M98 Beli 2003, Lemma 6.6 and the following remark

M98 formalizes the proper-rotation transport lemma:

- `IntegralRotation` represents `O⁺(L)` as integral orthogonal maps with
  determinant one and exposes their action and spinor norm;
- the unrounded exponent `(R₃-R₁)/2` in Lemma 6.6 is encoded by its
  discrete-valuation ceiling, while the following remark is encoded by the
  floor already used in Theorem 1;
- the sharp head factor `H` and tail obstruction `H'` are literal joins of
  the corresponding adjacent `G` group with the principal-unit factor;
- property B proves floor `≤` ceiling, hence the sharp congruence, head, and
  tail groups are contained in their floored counterparts;
- the floored version of Lemma 6.6 is consequently derived from the sharp
  version, including the non-full obstruction implication;
- an equal-value lattice vector is proved unconditionally to be a norm
  generator before the transport theorem is applied.

The long reflection/Eichler-transformation construction is isolated in the
explicit non-default `BeliLemma66Laws` interface.  The public M98 API is in
`Bong.Bong.BeliLemma66`.

## M99 Beli 2003, Lemma 6.7

M99 formalizes the non-property-B branch of the reverse inclusion:

- property A together with failure of property B is proved unconditionally
  to yield a concrete exceptional adjacent pair and a neighboring gap smaller
  than `2e + 1`;
- `lemma67LocalFactor` is the literal product of that pair's binary `G` group
  and Theorem 1's principal-unit factor;
- every such local factor is proved to lie in the global right-hand side of
  Theorem 1;
- the local valuation/norm-group calculation in Lemma 6.7 is isolated in the
  explicit non-default `BeliLemma67Laws` interface;
- consequently one local factor, and hence the entire right-hand side of
  Theorem 1, is proved to be the full square-class group whenever property B
  fails.

The public M99 API is in `Bong.Bong.BeliLemma67`.

## M100 Beli 2003, Theorem 1 reverse inclusion

M100 completes the reverse inclusion and the equality in Theorem 1:

- Beli's Lemma 2.3 is constructed directly: an integral orthogonal map fixing
  a norm generator restricts to the projected tail lattice, its extension is
  the original map, and its integral spinor norm is unchanged;
- property B is proved to pass to the recursive BONG tail;
- `sectionSixRHS` expands the right-hand side into all adjacent binary factors
  and all two-step principal-unit factors, including a direct rank-two
  reduction to Lemma 3.7;
- the expanded presentation is proved equal to Theorem 1's minimum-`alpha`
  presentation, using antitonicity of principal-unit subgroups and attainment
  of the finite minimum;
- the property-B branch is proved by induction on the rank using M98's
  transported rotation, the concrete Lemma 2.3 restriction, multiplicativity
  of spinor norms, and the binary base case;
- the non-property-B branch combines M99 with Lemma 4.11;
- the two branches give `spinorNormImageSubgroup_le_theoremOneRHS`, which is
  combined with M92's forward inclusion to obtain `beliTheoremOne` and its
  original set-valued form.

The public M100 API is in `Bong.Bong.BeliTheoremOneReverse`.

## M101 Beli 2003, Lemma 7.1

M101 begins the treatment of lattices not satisfying property A:

- `SpinorNormIsUnitBounded` is the literal condition
  `θ(L) ⊆ 𝒪ˣFˣ²`;
- membership of a field square class in the valuation-unit subgroup is proved
  equivalent to even valuation order;
- `NormOrderDatum` records the order of a lattice norm through an actual
  generator of its norm ideal;
- `HyperbolicPlaneSplitting` records an exact two-component orthogonal
  decomposition whose first component is isometric to `πʳ A(0,0)`;
- Lemma 7.1(i) is exposed as equality modulo two of all component norm orders;
- Lemma 7.1(ii) gives the valuation-unit group in the equal-parity branch and
  the full square-class group in the unequal-parity branch.

The reflection and Eichler-transformation arguments are isolated in the
explicit non-default `BeliLemma71Laws` interface.  The public M101 API is in
`Bong.Bong.BeliLemma71`.

## M102 Beli 2003, Theorem 2

M102 formalizes the classification after splitting all hyperbolic planes:

- `HyperbolicTowerSplitting` is an exact orthogonal decomposition into `t`
  components isometric to `πʳ A(0,0)` followed by a residual component;
- the residual component carries a nonempty BONG and explicitly contains no
  further scaled hyperbolic plane;
- the two conditions in the paper are stated literally: property A and a
  unit-bounded spinor group for the residual lattice, together with parity
  agreement between every hyperbolic norm order and the residual norm order;
- `beliTheoremTwo` proves the iff with the full lattice's unit-square-class
  bound;
- when at least one hyperbolic plane occurs, the inclusion is strengthened to
  equality with the valuation-unit square-class subgroup, as noted in the
  paper.

The residual-extraction and tower-induction steps are isolated in the
explicit non-default `BeliTheoremTwoLaws` interface.  The public M102 API is in
`Bong.Bong.BeliTheoremTwo`.

## M103 Beli 2003, Lemma 7.2

M103 formalizes the binary group criterion used in the final classification:

- `beliParameterDefectOrderQ` embeds `d(-a)` in `WithTop ℚ`, retaining both
  infinite defects and genuinely half-integral cutoffs;
- the exceptional `-1/4` refined square class is proved to have infinite
  parameter defect;
- `SatisfiesLemma72UnitCriterion` states exactly that the parameter order is
  even and either the exceptional class occurs or the defect exceeds
  `e - R/2`;
- the criterion implies the weak defect lower bound stated at the end of part
  (i);
- `lemma72CombinedParameter` is the literal parameter
  `(-1)^(k-1) π^R ε₁⋯εₖ`, and its order is proved unconditionally to be `R`;
- part (ii) exposes admissibility and the unit bound for this combined
  parameter.

The local binary norm-group equivalence and domination step are isolated in
the explicit non-default `BeliLemma72Laws` interface.  The public M103 API is
in `Bong.Bong.BeliLemma72`.

## M104 Beli 2003, Lemma 7.3

M104 formalizes the three-entry replacement and hyperbolic splitting:

- `Lemma73Hypotheses` records equality of the endpoint orders and the two
  valuation-unit bounds on the adjacent binary spinor groups;
- `Lemma73SplittingWitness` gives an exact global orthogonal decomposition,
  identifies its first component with the scaled hyperbolic plane, and equips
  the complementary component with a good BONG of rank two less;
- the residual BONG agrees with the original before and after the replaced
  block, while its replacement entry has the exact value
  `-π^Rᵢ εᵢ εᵢ₊₁ εᵢ₊₂`;
- the valuation of that replacement value is proved directly to be `Rᵢ`.

The ternary modular calculation and global reconstruction are isolated in the
explicit non-default `BeliLemma73Laws` interface.  The public M104 API is in
`Bong.Bong.BeliLemma73`.

## M105 Beli 2003, Theorem 3

M105 completes the 2003 paper's unit-bounded spinor-norm classification:

- `SatisfiesTheoremThreeConditions` states the paper's two conditions for all
  adjacent pairs and all equal-order three-entry blocks;
- Lemma 7.2 is used to prove that condition (i) makes every adjacent order gap
  even, hence all BONG orders have the same parity;
- the necessary direction embeds every adjacent binary group by Corollary
  4.10 and combines the exact Lemma 7.3 splitting with Lemma 7.1(i) to derive
  condition (ii);
- the property-A branch follows from Theorem 1, since both its adjacent and
  principal-unit factors lie in the valuation-unit square classes;
- the remaining branch is a genuine strong induction on rank: Lemma 7.3
  removes a hyperbolic plane, the conditions pass to the residual good BONG,
  and Lemma 7.1(ii) reattaches the plane using the proved parity identity.

The low-rank base case and the Lemma 7.2(ii) replacement calculation are
isolated in the explicit non-default `BeliTheoremThreeLaws` interface.  The
public M105 API is in `Bong.Bong.BeliTheoremThree`.

## M106 Beli 2006, Section 2

M106 begins the 2006 representation paper:

- the binary similarity invariant `a(L)` is identified with the refined
  binary parameter class, and its order is proved to be `R₂ - R₁`;
- `SatisfiesGoodBONGCriteria` states the weak two-step inequalities and the
  admissibility of every adjacent binary parameter;
- the only-if direction of adjacent admissibility is proved from actual
  binary segment witnesses;
- the numerical criterion is shown equivalent to realizing the prescribed
  orthogonal basis as a good BONG;
- a BONG is good exactly when it is put together from a maximal norm
  splitting, with improper binary components available in the forward
  direction.

The local construction of adjacent binary lattices is isolated in the
non-default `Beli2006SectionTwoLaws` interface.  The public M106 API is in
`Bong.Bong.Beli2006SectionTwo`.

## M107 Beli 2006, Section 3

M107 formalizes the classification invariants and their basic properties:

- `orderGap`, `halfGapValue`, `alphaLeftEndpoint`, and
  `alphaRightEndpoint` give exact finite coordinates for the formulas in the
  paper;
- `SatisfiesAlphaP1` through `SatisfiesAlphaP7` state all seven announced
  properties, including every equality case and the reverse-duality index;
- `exists_reverseDual_with_alpha` combines P7 with an actual reverse-dual
  good BONG and proves the vector, scalar-value, order, and alpha formulas in
  one witness;
- `order_alpha_invariant` proves that the complete `R_i` and `alpha_i`
  sequences are independent of the chosen good BONG of a fixed lattice;
- `beli2006Theorem32` is the exact four-condition good-BONG translation of
  O'Meara's classification theorem.

The local proofs of P1--P7 are isolated in the non-default
`Beli2006AlphaLaws` interface.  O'Meara's quoted Theorem 93:28 remains isolated
in `GoodBONGClassificationLaws`.  The public M107 API is in
`Bong.Bong.Beli2006SectionThree`.

## M108 Beli 2009/2010, Lemmas 2.1--2.3

M108 begins the classification paper in its published order:

- `AlphaLocalizationIndex` records the exact consecutive block surrounding
  the alpha index, with checked global and local finite indices;
- `localizedReplacementCandidates` replaces precisely the candidates internal
  to that block by the alpha of the corresponding segment;
- Lemma 2.1 exposes the exact finite-minimum replacement and derives the
  segment upper bound;
- Lemma 2.2 proves monotonicity of `R_i + alpha_i` and antitonicity of
  `-R_(i+1) + alpha_i` from property P1;
- Corollary 2.3 proves endpoint constancy, the parity-two-step formulas for
  orders and alphas, and synchronized attainment of the half-gap candidate.

Only the local finite-minimum identification in Lemma 2.1 is isolated in the
non-default `Beli2009AlphaLocalizationLaws` interface.  The monotonicity and
all Corollary 2.3 consequences are derived in Lean.  The public M108 API is in
`Bong.Bong.Beli2009AlphaMonotonicity`.

## M109 Beli 2009/2010, Lemma 2.4--Remark 2.6

M109 formalizes both compression formulas and their first consequences:

- Lemma 2.4 replaces an entire left or right family of defect candidates by
  the alpha of the corresponding consecutive segment and proves equality of
  the finite minima;
- Corollary 2.5(i) reduces the defining minimum to the half-gap, local defect,
  and valid predecessor/successor alpha terms;
- Corollary 2.5(ii) uses canonical prefix and suffix BONG realizations, with
  empty optional finite sets encoding the endpoint terms that the paper says
  to ignore;
- Remark 2.6 constructs the reverse-dual BONG with reversed alphas and proves
  scaling invariance directly from common coefficient scaling, valuation
  additivity, and invariance of quadratic defect under squares.

No new law interface is introduced in M109.  Its only hypotheses are the
previously isolated localization and alpha-property interfaces, plus the
structural reverse-duality interface for the duality assertion.  The public
API is in `Bong.Bong.Beli2009AlphaCompression`.

## M110 Beli 2009/2010, Lemma 2.7--Corollary 2.9

M110 formalizes the arithmetic shape of the alpha invariants:

- Lemma 2.7 identifies nonnegativity, the two sides of the ramification
  threshold, every equality case, and the odd-integral alternative to the
  half-gap value;
- Corollary 2.8 proves the exact exceptional case for integrality, the three
  threshold equivalences, and the integral/half-integral interval
  decomposition;
- Corollary 2.9 proves the half-gap formula at all four specified gap cases
  and the minimum formula for odd gaps.

Only Lemma 2.7(iv)'s local defect-parity input is isolated in the non-default
`Beli2009AlphaParityLaws` interface.  Lemma 2.7(i)--(iii) are the already
formalized P2--P4, while all Corollary 2.8--2.9 statements are derived in
Lean.  The public M110 API is in `Bong.Bong.Beli2009AlphaArithmetic`.

## M111 Beli 2009/2010, Lemmas 2.10--2.12

M111 introduces the ideal language needed for the Jordan-theoretic part:

- `normGroupSet` is the concrete set `gL = Q(L) + 2sL`;
- `OrderedFractionalIdeal`, `scalarIdeal`, `twoScaleIdeal`, and
  `quadraticDefectIdeal` encode every ideal and order occurring in the three
  formulas;
- Lemma 2.10 gives the exact characterization of the weight ideal;
- Lemma 2.11 gives both finite orthogonal-sum formulas for `gJ` and `wJ`;
- Lemma 2.12 records the four-term fundamental-ideal formula, including its
  evenness hypothesis and the two norm-stability hypotheses.

O'Meara 93A, the orthogonal-sum weight calculation, and formula 93:26 are
isolated respectively in the non-default `Beli2009WeightIdealData`,
`Beli2009OrthogonalIdealLaws`, and `Beli2009FundamentalIdealLaws` interfaces.
All sets and ideal expressions on either side are concrete Lean definitions.
The public M111 API is in `Bong.Bong.Beli2009JordanIdeals`.

## M112 Beli 2009/2010, Lemmas 2.13--2.16 and Corollary 2.17

M112 connects good-BONG coordinates with Jordan components:

- a checked half-open interval represents each Jordan block and proves the
  alternating order formulas from either endpoint in Lemma 2.13(i),(ii);
- consecutive orders in a block sum to twice its scale order, while the four
  norm-generator assertions of Lemma 2.13(iii) are exposed exactly;
- Lemma 2.14 gives the weight order in rank one and higher rank, including
  the equality forced by a non-unary first Jordan component;
- optional neighboring ideals implement the endpoint convention in Lemma
  2.15 without sentinel values;
- Lemma 2.16 proves the two internal weight identities and separates the
  regular and exceptional boundary cases;
- Corollary 2.17 derives the normalized internal order and the
  endpoint-aware minimum formula.

Only the genuinely external Jordan-decomposition inputs are isolated in the
non-default `Beli2009JordanBlockLaws`, `Beli2009JordanWeightOrderLaws`,
`Beli2009UnaryJordanIdealLaws`, and `Beli2009JordanAlphaLaws` interfaces.
All parity transport, adjacent-order algebra, exceptional-case arithmetic,
and capped-minimum reductions are proved in Lean.  The public M112 API is in
`Bong.Bong.Beli2009JordanCoordinates`.

## M113 Beli 2009/2010, Lemmas 3.2--3.4

M113 begins the classification proof:

- prefix products satisfy an exact one-step recurrence, and comparison
  products satisfy the two-coordinate factorization used in Lemma 3.2;
- quadratic-defect domination and square invariance prove both forward and
  backward propagation of condition 3.1(iii), including both endpoints;
- `JordanClassificationReduction` records checked component, boundary,
  weight, and fundamental-ideal data, and Lemma 3.3 derives the global
  equivalence from its local Jordan-chain reductions;
- Lemma 3.4 is a direct consequence of the already formalized property P6.

The only new field-theoretic interface is the non-default
`Beli2009AmbientDeterminantLaws`, expressing preservation of the full
determinant square class under ambient isometry.  The non-default
`Beli2009JordanReductionLaws` isolates the local O'Meara/Jordan-chain
identifications and the block-coverage induction.  All finite-product,
defect-domination, endpoint, and alpha arithmetic is proved in Lean.  The
public M113 API is in `Bong.Bong.Beli2009ClassificationPropagation`.

## M114 Beli 2009/2010, Lemmas 3.5--3.7

M114 formalizes the quadratic-space representation steps used in the
classification proof:

- quadratic embeddings, orthogonal sums, and the one-dimensional form
  `[a]` are concrete coordinate-free definitions;
- Lemma 3.5 exposes the three consequences of O'Meara 63:21, while its
  defect-sum parenthetical assertion follows from the Hilbert-symbol laws;
- Lemma 3.6 derives both representation switches from the weight and
  fundamental-ideal defect bounds;
- Lemma 3.7 transfers those switches to the diagonal-prefix condition.

The genuinely Witt-theoretic input is isolated in the non-default
`Beli2009QuadraticRepresentationLaws` interface.  The chosen diagonal
identifications and hyperbolic cancellation used for Lemma 3.7 are isolated
in `Beli2009PrefixRepresentationBridgeLaws`.  All intervening defect-order,
Hilbert-symbol, and logical equivalence calculations are proved in Lean.
The public M114 API is in
`Bong.Bong.Beli2009QuadraticRepresentation`.

## M115 Beli 2009/2010, Lemmas 3.8--3.9 and Theorem 3.1

M115 completes the main classification theorem:

- a general threshold-substitution lemma proves the regular boundary cases
  of Lemma 3.8 from Lemma 2.16(ii);
- a fully proved capped-minimum identity handles the internal unary case,
  including the disjunction of its two neighboring ideal containments;
- Lemma 3.9 is assembled from finite local representation sites and their
  incident O'Meara clauses, so unary and non-unary cases share one checked
  logical reduction;
- conditions 3.1(i)--(iii) are converted by Lemma 3.3 into the fundamental
  type and condition 93:28(i), and Lemma 3.9 supplies 93:28(ii)--(iii);
- Theorem 3.1 is then derived from O'Meara 93:28.

The only final classification input is the non-default
`Beli2009Omeara9328Laws` interface.  It states O'Meara 93:28 and preservation
of fundamental type under lattice isometry; it does not assume Beli's four
good-BONG conditions.  The public M115 API is in
`Bong.Bong.Beli2009MainTheorem`.

## M116 Beli 2009/2010, Section 4

M116 proves the 2-adic specialization:

- adjacent binary admissibility gives the lower bound and negative-gap
  parity needed in Lemma 4.1;
- Lemma 4.1 is derived from Corollary 2.9, yielding the exact piecewise
  formula for every alpha invariant when `e = 1`;
- the sum of two piecewise alpha formulas is proved equivalent to the order
  inequality and the three exceptional pairs in Theorem 4.2(iii);
- equal order sequences force equal alpha sequences, making condition
  3.1(ii) redundant;
- even comparison-product orders reduce condition 3.1(iii) to the square
  and distinguished-square alternatives of Theorem 4.2(ii);
- Theorem 4.2 follows by rewriting all four conditions of Theorem 3.1.

The unique endpoint square-class input is isolated in the non-default
`Beli2009TwoAdicDefectClassLaws`, which supplies the distinguished class and
the defect-depth-two equivalence.  The public M116 API is in
`Bong.Bong.Beli2009TwoAdic`.

## M117 Beli 2009/2010, Lemma 5.1 and Remark 5.2

M117 proves the binary norm-group formula at the beginning of Section 5:

- the compact cut is identified with the exact minimum
  `min (R / 2 + e) (R + d(-a))` in all three numerical branches;
- odd parameter order is proved to force relative quadratic defect zero;
- the principal-unit factor is normalized branch by branch, including the
  bottom subgroup when the cut is greater than `2e`;
- Lemma 5.1 follows from the norm-generator formula and the containment
  cited from Beli (2003), paragraph 3.16;
- Remark 5.2 identifies the binary parameter with the adjacent determinant
  parameter up to a square and transfers the quadratic norm subgroup.

The cited paragraph-3.16 containment is isolated in the non-default
`Beli2009BinaryNormContainmentLaws` interface.  The valuation arithmetic,
square invariance, alpha identification, and group rewrites are proved in
Lean.  The public M117 API is in `Bong.Bong.Beli2009BinaryRemarks`.

## M118 Beli 2009/2010, final Section 5 remarks

M118 completes the formal statement of the paper's final discussion:

- the recursive alpha formula is identified exactly with Corollary 2.5(ii);
- a binary transformation acts on two adjacent coordinates, and finite
  successions are represented by the reflexive-transitive closure;
- the assertion that such a succession implies all four conditions of the
  main theorem is exposed explicitly;
- the large-residue-field conclusion and the residue-two obstruction are
  packaged as a precise dichotomy;
- the parameterized residue-two rank-four obstruction records the displayed
  value sequences with `R = 2e - 2d`;
- the explicit rank-four `Q_2` example is bundled as two good BONGs of one
  lattice, with values `(1,1,1,1)` and `(7,7,7,7)` and non-reachability.

The paper only sketches these final transformation and existence assertions.
They therefore form the non-default `Beli2009BinaryTransformationLaws`
interface;
the transformation operation, reachability relation, coordinate formulas,
and logical assembly are concrete Lean definitions and proofs.  The public
M118 API is in `Bong.Bong.Beli2009FinalRemarks`.

## M119 Beli 2006, Lemma 4.2 and Definition 4.3

M119 starts the proof layer shared by the 2006 announcement and the complete
2019 representation paper:

- multiplicative domination for embedded quadratic-defect orders is factored
  into `Bong.Bong.DefectArithmetic` and reused by both papers;
- the capped defect satisfies Beli's three-lattice domination principle;
- Lemma 4.2 is formalized as invariance of both prefix and segment truncated
  defects under a change of good BONG;
- every candidate in Definition 4.3 has the expected lower-bound theorem;
- `A_i(M, N)`, its rational value, and the exceptional terminal quantity are
  proved independent of the chosen good BONGs.

The one remaining input at this stage is the explicitly named, non-default
`Beli2006PrefixChangeLaws` interface, including the determinant endpoint. It
will be discharged in the 2019 Section 1 proof layer rather than treated as a
global axiom. The public M119 API is in
`Bong.Bong.Beli2006SectionFourInvariants`.

## M120 Beli 2019, Definitions 2--3 and Lemmas 1.6--1.8

M120 formalizes the pure order theory used by condition 2.1(i):

- `BeliOrderSequence n` is the set `B_n` of two-step-monotone integer
  sequences;
- `BeliOrderLE` is Beli's rank-changing comparison relation;
- the adjacent-pair estimate and both implications of Lemma 1.6 are proved;
- reflexivity, antisymmetry, and transitivity give a partial order on the
  disjoint union `BeliOrderFamily`;
- `IsKappaBounded` and both parts of Lemma 1.8 are proved;
- the existing `RepresentationOrderCondition` is proved equivalent to this
  abstract sequence order for good BONG valuation sequences.

No new local-field law interface is introduced. The public M120 API is in
`Bong.Bong.Beli2019OrderSequence`.

## M121 Beli 2019, sequence reversal and lattice duality

M121 formalizes the involution
`(x₁, ..., xₙ) ↦ (-xₙ, ..., -x₁)` from the end of Section 1:

- reversal preserves `Bₙ(kappa)`;
- it reverses Beli's order on every fixed-rank stratum;
- every good BONG order sequence belongs to `Bₙ(2e)`;
- a reverse-dual good BONG realizes the combinatorial involution.

The public M121 API is in `Bong.Bong.Beli2019SequenceDual`.

## M122 Beli 2019, the W-sequence

M122 defines the rational sequence
`W(L) = (R₁ + alpha₁, R₂ - alpha₁, ..., Rₙ - alphaₙ₋₁)` by a
generic alternating interleaving construction.  Its even and odd coordinate
formulas are proved, as is the duality identity `W(L*) = W(L)*`.  The public
M122 API is in `Bong.Bong.Beli2019WeightSequence`.

## M123 Beli 2019, prefix-change endpoint discharge

M123 removes the temporary determinant-endpoint assumption from M119.  The
internal prefix bound follows from classification condition (iii), the empty
prefix from `d(1) = infinity`, and the complete prefix from the square of the
change-of-basis determinant.  Consequently `Beli2006PrefixChangeLaws` is now
derived automatically from `GoodBONGClassificationLaws`; no additional law
interface is required.  The public M123 API is in
`Bong.Bong.Beli2019PrefixChange`.

## M124 Beli 2019, Lemmas 1.3 and 1.5 and revised condition (iii')

M124 completes the reusable logical layer of Sections 1-2:

- exact defect domination is lifted to the rational `WithTop` order;
- all three alternatives of Lemma 1.3 are proved, including square factors;
- the two-class four-cycle parity argument of Lemma 1.5 is formalized;
- the two truncated defects in arXiv v2 condition (iii') are defined with
  their endpoint conventions;
- original condition (iii), condition (iii'), and their four-condition
  packages are proved equivalent from the pointwise trigger equivalence that
  is precisely the conclusion required from Lemma 2.16.

The public APIs are in `Bong.Bong.Beli2019DefectMin`,
`Bong.Bong.Beli2019MainConditions`, and
`Bong.Bong.Beli2019RepresentationParity`.

## M125 Beli 2019, Section 3 approximations

M125 introduces Definitions 9-10 in a form aligned with the existing BONG
API:

- `IsPrefixApproximation` handles internal and endpoint square classes
  uniformly through `prefixAlphaCap`;
- scalar approximation is proved independent of the chosen good BONG;
- capped defects computed from arbitrary approximations are proved equal to
  the original prefix-product defects;
- diagonal left, right, and two-sided space approximations are defined;
- the vacuous-alpha-sum case of Remark 3.1 is proved;
- the exact two-step prefix recurrence and the sign-changing propagation step
  in Lemma 3.2 are proved from defect domination.

The public M125 API is in `Bong.Bong.Beli2019Approximation`.

## M126 Beli 2019, Lemma 3.2 inside a Jordan block

M126 connects the scalar recurrence to the Jordan coordinates developed for
the 2009/2010 paper:

- orders two places apart are proved equal inside a single Jordan block;
- the determinant seed propagates through every even-parity boundary;
- the norm-generator seed propagates through every odd-parity boundary;
- the `i = 0` endpoint is included, and the alternating sign remains explicit
  until it is absorbed by the two-sided choice of norm generator.

The public M126 API is in `Bong.Bong.Beli2019JordanApproximation`.

## M127 Beli 2019, Corollary 3.3 by reverse duality

M127 proves the dual transport used for the right-hand Jordan formulas:

- reciprocal reversed BONG values satisfy the exact complementary-prefix
  product identity;
- alpha caps reverse at every boundary, including both endpoints;
- an approximation at boundary `n + 1 - i` transports to boundary `i` after
  multiplication by the full BONG determinant;
- the structural reverse-dual existence theorem packages this as the
  existence form of Corollary 3.3.

The public M127 API is in `Bong.Bong.Beli2019ApproximationDual`.

## M128 Beli 2019, Lemma 3.8 for space approximations

M128 separates the change-of-BONG proof into its invariant and local parts:

- both alpha-sum triggers are proved invariant from the classification
  invariance of the alpha sequence;
- the two representation equivalences required at a boundary are bundled as
  explicit data, rather than installed as a new global law;
- scalar, left-space, right-space, and two-sided approximation invariance are
  then composed into the exact statement of Lemma 3.8.

The public M128 API is in `Bong.Bong.Beli2019SpaceApproximation`.

## M129 Beli 2019, approximation formulas for Definition 4

M129 performs the concrete substitution used before Lemma 3.10:

- the primary and secondary defect candidates for `A_i` are expressed using
  arbitrary scalar approximations `X_i,Y_i`;
- the resulting candidate set and its minimum are proved equal to the
  original `A_i`;
- both candidates of the exceptional terminal adjustment are treated in the
  same way;
- condition (ii) is proved equivalent to the paper's condition (ii').

The public M129 API is in `Bong.Bong.Beli2019ApproximationInvariants`.

## M130 Beli 2019, Section 4 transitivity skeleton

M130 isolates the short, reusable part of the transitivity proof:

- condition (i) is transitive for arbitrary compatible ranks through
  `BeliOrderLE.trans`;
- at equal rank, the key-lemma bounds `C_i ≤ A_i` and `C_i ≤ B_i` combine
  with the two source defect conditions;
- the three-lattice capped-defect domination theorem then proves the target
  instance of condition (ii), pointwise and globally.

The public M130 API is in `Bong.Bong.Beli2019Transitivity`.

## M131 Beli 2019, Definition 7 and dual essential indices

M131 formalizes essential indices with the paper's endpoint convention:

- each inequality is required only when all of its neighboring indices
  exist, so no artificial boundary value is introduced;
- the first and last indices are proved essential unconditionally;
- reversing and negating two order sequences, while exchanging their roles,
  carries an essential index to the reflected essential index.

The public M131 API is in `Bong.Bong.Beli2019EssentialIndex`.

## M132 Beli 2019, Section 4 key lemma and condition (ii)

M132 gives the key lemma a boundary-indexed formal interface and completes
the logical assembly of condition 2.1(ii):

- the two direct-branch inequalities encode the exceptional endpoint cases
  by vacuous quantification;
- the direct and shifted conclusions of both parts of Lemma 4.2 are recorded
  at the exact ordinary boundary they control;
- source condition (ii) is proved to bound every `A_i` by both adjacent
  intrinsic alpha invariants;
- Lemmas 2.11 and 2.12 remain as an explicit local reduction structure, and
  all direct, shifted, current-essential, next-essential, and nonessential
  cases are assembled into target condition (ii).

No global transitivity law is introduced. The public M132 API is in
`Bong.Bong.Beli2019KeyLemma`.

## M133 Beli 2019, completion of the Section 4 composition layer

M133 gives the representation-valued parts of transitivity explicit proof
objects:

- diagonal representations are proved to compose;
- condition (iii) is certified either by a literal factorization through a
  neighboring prefix of the middle BONG or by a checked Lemma 1.5 parity
  diagram;
- condition (iv) is certified by a literal factorization through one of the
  three neighboring middle prefixes;
- these certificates, together with M130-M132, assemble all four fields of
  `RepresentationConditions` at equal rank.

The public M133 API is in
`Bong.Bong.Beli2019RepresentationTransitivity`.

## M134 Beli 2019, Lemma 5.5(i)

M134 begins the pure order-theoretic part of the index-`p` reduction:

- valuation sequences receive a zero-extended prefix-sum operation;
- one-step and two-step recursion formulas are proved;
- the first-coordinate and adjacent-pair estimates give every cumulative
  inequality by two-step induction;
- condition 2.1(i) is connected directly to cumulative order sums for good
  BONGs of arbitrary compatible ranks.

The public M134 API is in `Bong.Bong.Beli2019OrderSums`.

## M135--M137 Beli 2019, Lemmas 5.5(ii)--(iv) and pair propagation

These milestones complete the finite-sum rigidity used by Section 5:

- suffix sums satisfy the dual inequalities and equality propagation;
- equality of total volume forces the required prefix and suffix rigidity;
- interval gaps give the equality case in Lemma 5.5(iv);
- equality of an adjacent pair sum propagates across the relevant parity
  class in Lemma 5.6.

The public APIs are in `Bong.Bong.Beli2019OrderSumRigidity` and
`Bong.Bong.Beli2019EqualityPropagation`.

## M138--M140 Beli 2019, Lemma 5.6 extremal formulas

M138 and M139 prove the minimum and maximum formulas for the last differing
coordinate. M140 packages them as the extremal difference profile used by
Lemma 5.7. The public APIs are in `Bong.Bong.Beli2019PrefixMinimum`,
`Bong.Bong.Beli2019SuffixMaximum`, and
`Bong.Bong.Beli2019ExtremalDifference`.

## M141--M144 Beli 2019, Lemma 5.7 and Corollary 5.8

This block formalizes the order theory after choosing a norm generator:

- the maximal initial odd plateau and the complete Lemma 5.7 order profile;
- the exact reconstruction formula of Corollary 5.8;
- the second-coordinate equality criterion used in Corollary 5.9(i);
- canonical finite maxima replacing the paper's informal choices of `k`
  and `l`.

The public APIs are in `Bong.Bong.Beli2019NormGeneratorOrders`,
`Bong.Bong.Beli2019OrderReconstruction`,
`Bong.Bong.Beli2019SecondOrderCriterion`, and
`Bong.Bong.Beli2019MaximalIndices`.

## M145--M146 Beli 2019, Corollary 5.9

M145 translates the second-order criterion into the norm-ideal inclusion and
equality statement of Corollary 5.9(i). M146 proves all three sufficient
conditions in Corollary 5.9(ii): `S₁ < S₃`, `S₂ - S₁ = 2e`, and rank at most
two. The proof of the middle case uses the concrete lower bound `-2e` for an
adjacent BONG order gap.

The public APIs are in `Bong.Bong.Beli2019ProjectionNormIdeal` and
`Bong.Bong.Beli2019NormGeneratorGoodness`.

## M147--M167 Beli 2019, Lemma 5.7 and Corollary 5.10

This block completes the geometric prefix-extension construction:

- tails of order sequences and the four Corollary 5.10 triggers are stable
  under deletion of a common first vector;
- adjoining and projecting a norm generator gives the enlarged lattice used
  in Lemma 5.7, including its volume-order and order-shift formulas;
- projected lattices and good BONGs are transported across nonzero rescaling;
- the enlarged candidate has the prescribed first vector, unchanged tail,
  and the required good-BONG inequalities;
- the comparison data are constructed automatically, with the paper's
  auxiliary exponent chosen from the third order when the rank is at least
  three;
- induction over the prefix length yields a good BONG with any admissible
  ambient prefix, which is the full conclusion of Corollary 5.10.

The public APIs are in `Bong.Bong.Beli2019EnlargedLattice`,
`Bong.Bong.Beli2019EnlargedComparison`,
`Bong.Bong.Beli2019ComparisonExistence`, and
`Bong.Bong.Beli2019PrefixExtensionFull`.

## M168--M171 Beli 2019, proof architecture for 2.1(ii)

These milestones translate the first part of the post-Corollary 5.10 case
analysis into scalar statements:

- an ambient-prefix replacement preserves all selected values and their
  prefix products;
- a one-step difference of cumulative orders makes the relevant product have
  odd valuation, hence quadratic-defect order zero;
- Lemma 5.13's two recurring branches are assembled pointwise into
  `RepresentationDefectCondition`: either the two prefix approximations are
  equal, or the cumulative orders differ by one and the target alpha bound is
  nonpositive.

The public APIs are in `Bong.Bong.Beli2019PrefixConsequences`,
`Bong.Bong.Beli2019OddPrefixDefect`, and
`Bong.Bong.Beli2019DefectConditionBranches`. M171 records Lemma 5.13's exact
two outputs and derives the global defect condition from its subsequent
alpha bounds.

## M172--M176 Beli 2019, Theorem 2.1

This block closes the main theorem at the project's explicit local-law
boundary:

- M172 formalizes Lemma 5.17 and its Corollary 5.10 consequence;
- M173 assembles the index-`p` result of Sections 5--6, including conditions
  (ii)--(iv) and v2 condition (iii');
- M174 builds finite prime chains and composes them with the Section 4
  transitivity certificates;
- M175 formalizes the well-founded rank/volume descent of Sections 7--9 and
  separates the Lemmas 9.3, 9.6, and 9.12 outcomes;
- M176 first assembled `beli2019Theorem21` and
  `beli2019Theorem21_prime`; M650--M660 below replace its remaining
  final-step boundary by the concrete Sections 7--9 proof.

The final proofs do not assume `GoodBONGRepresentationLaws`. Deep
Jordan/local-field inputs remain visible as non-default proof-producing
interfaces, listed precisely in `docs/Beli2019V2FormalizationMap.md`.

The complete theorem-by-theorem map and the explicit trust boundary are in
`docs/Beli2009Coverage.md` and `docs/Beli2019V2FormalizationMap.md`.
`BongTest.Beli2009Audit` and `BongTest.Beli2019Audit` centrally check the
public theorem layer and its current explicit trust boundary. The complete
current status, including the distinction between the finished conditional
assembly and the still-uninstantiated local-law boundary, is recorded in the
formalization map and in `docs/audit/Beli2019V2`.

## M630--M640 Beli 2019, Lemmas 8.12--8.14

This block completes the noncircular Section 8 input needed by the final
descent:

- Lemmas 8.12 and 8.13 are proved directly from the representation
  conditions, without invoking Theorem 2.1;
- all three exceptional alternatives in Lemma 8.14, including the
  complement-space condition in (c), are invariant under the required good
  BONG changes;
- necessity and sufficiency of Lemma 8.14 are proved for ranks three, four,
  and at least five, including the unequal-outer half-gap boundary and its
  final binary exception;
- `beli2019Lemma814Explicit` is the completed, noncircular theorem for every
  target rank at least three.

The implementation is assembled in
`Bong.Bong.Beli2019Lemma814Complete`; the detailed proof-to-paper map and the
remaining Section 7/9 trust boundary are recorded in
`docs/Beli2019V2FormalizationMap.md`.

## M641 Beli 2019, Lemma 9.1 immediate branches

Four of the five direct branches of Lemma 9.1 are now kernel checked:

- `R₁ < R₃` excludes every Lemma 8.14 exception immediately;
- `R₂ = R₄` excludes the exceptions using Remark 8.7;
- `R₂ - R₁ = 2e` reaches the binary branch by proving the required
  Hilbert symbol from the exact first alpha and positive adjacent defect.
- `d[-a₁,3b₁] = α₁ < β₁` removes the full-source alpha cap,
  reduces to the canonical unary first segment, and excludes all three
  Lemma 8.14 exceptions.

These results are in `Bong.Bong.Beli2019Lemma91OrderBranches`.  The remaining
`R₂ = S₂` alternative, together with the wrapper deriving the unary
Lemma 8.13 hypotheses from the full representation assumptions, belongs to
the explicit Section 9 worklist.

## M642 Beli 2019, Lemma 9.1 equal-second-order rigidity

The common arithmetic entrance to the remaining `R₂ = S₂` branch is now
kernel checked.  Condition 2.1(ii) at the first boundary gives
`α₁ ≤ β₁`.  If `R₁ = R₃` and the full first-three defect is capped by
`β₁`, Lemma 8.12(ii), the second defect condition, and Remark 8.7 squeeze
the invariants to `A₂ = α₂` and `β₁ = α₁`.  The proof is in
`Bong.Bong.Beli2019Lemma91SecondOrder` and introduces no new local law.

For exceptions (b) and (c), the source cap is now forced rather than assumed:
selecting the unary defect would make both candidates defining `A₂` strictly
larger than `α₂`, contradicting condition 2.1(ii).  Thus these two exceptions
automatically enter the rigid `A₂ = α₂`, `β₁ = α₁` subcase.

The three ensuing contradictions for Lemma 8.14(a), (b), and (c), including
their binary and ternary prefix-representation arguments, remain the active
part of the `R₂ = S₂` worklist.

## M643 Beli 2019, Lemma 9.1 exception-(a) geometry

The local contradiction for exception (a) is now kernel checked once the
paper's smaller binary-prefix representation
`[b₁,b₂] rep [a₁,a₂,a₃]` is supplied.  The source first-adjacent defect is
bounded below by `α₂`, the other defect is bounded by
`d[-a₁,₃b₁]`, and exception (a) puts their sum above `2e`.  The resulting
Hilbert symbol is one; determinant completion therefore makes the represented
ternary prefix isotropic, contradicting exception (a).

## M644 Beli 2019 v2, condition (iii') at the first central index

The binary-prefix representation in Lemma 9.1 is now derived from the
current problem, not postulated and not obtained through a circular appeal
to the main theorem.  At `i = 3`, the completed Lemma 2.16 converts condition
(iii) to the revised-v2 condition (iii').  Its two hypotheses are exactly
`R₄ > S₂` and
`d[-a₁,₃b₁] + d[-a₁,₄b₁,₂] > 2e + S₂ - R₄`.

## M645 Beli 2019, Lemma 9.1 exception (a)

The full exception-(a) contradiction is kernel checked.  The long strict
defect estimate is proved in both exhaustive subcases: the full first-three
defect is either the unary defect or the source alpha cap.  Condition (ii),
P1, Remark 8.7, and capped-defect domination prove condition (iii'), which
supplies `[b₁,b₂] rep [a₁,a₂,a₃]`; M643 then gives the Hilbert/isotropy
contradiction.  In target rank three the same binary-prefix representation
comes directly from the ambient representation restricted to the first
source segment.  The rank-three and high-rank cases are combined in
`not_lemma814ExceptionA_of_equalSecondOrder_allRanks`.

## M646 Beli 2019, Lemma 9.1 exception (b)

Exception (b) is now completely excluded in the `R₂ = S₂` branch.  The
third representation alpha is estimated from its half-gap, primary-defect,
and Lemma 2.7 previous-defect candidates.  Condition (ii) then gives both
the full determinant-defect bound and the source third-alpha cap.  A
determinant product identity, P1, and the finite candidate formula force the
first source alpha to be attained on its initial binary segment.  Its
adjacent defect is therefore exactly `α₂`; the residue-two Hilbert-symbol
criterion contradicts the isotropy clause of exception (b).

Target rank three is treated separately: when the source also has rank
three, equal-rank ambient representation makes the full determinant ratio a
square, replacing the unavailable `A₃` estimate.  The all-rank result is
`not_lemma814ExceptionB_of_equalSecondOrder`.  Its focused axiom audit
reports only `propext`, `Classical.choice`, and `Quot.sound`.

The remaining equal-second-order work is exception (c).

## M647 Beli 2019, Lemma 9.1

Exception (c) is excluded in all source ranks, and the unary Lemma 8.13
input is constructed from the actual first source segment.  Its ambient
quadratic-space representation follows by composing the segment inclusion
with the theorem's ambient representation, and the required unary conditions
then follow from the independently proved necessity direction.  Together
with M641--M646 this gives the complete, noncircular theorem
`BONG.GoodBONG.beli2019Lemma91`.  Its focused axiom audit uses only `propext`,
`Classical.choice`, and `Quot.sound`.

## M648 Beli 2019, Lemma 9.2

Lemma 9.2 is now kernel checked for every rank at least four.  The rank-four
and rank-five failure branches derive the paper's endpoint recursions,
strict defect inequalities, odd unit depths, and the bound
`alpha_3 + alpha_4 < 2e`.  Corollary 8.10 supplies the first-binary
normalization in rank five.  The resulting explicit coefficient changes are
realized by good BONGs, inserted into the first four or five coefficients,
and propagated through arbitrary rank.  The public theorem is
`BONG.GoodBONG.beli2019Lemma92`; its focused audit again uses only Lean's
three standard logical axioms.

## M649 Beli 2019, Lemma 9.3 Case 1 (large-defect branch)

The source-first selection order in Case 1 is now formalized: Corollary 8.11
first selects the source BONG with alpha/tail-alpha equality at every shifted
boundary, Lemma 9.1 then prescribes the matching target head, and Lemma 9.2
normalizes the target.  Mixed capped-defect transport proves exact comparison-
alpha equality after the first two tail boundaries.

For the displayed subcase
`d[-a_(1,3)b_1] >= (S_2-R_3)/2 + e`, the paper's separate `A_2` and `A_3`
estimates are kernel checked.  The `A_3` proof treats the terminal rank and
the current-/next-essential alternatives through the two forms of Lemma 2.7.
The two low estimates are promoted to the uniform reverse certificate and
then to the concrete `Lemma93Input`.  The public endpoint is
`Beli2019Lemma93CaseOneNormalizedPair.toLemma93Input_of_largeDefect`; its axiom
audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

This does not yet complete Lemma 9.3: the two remaining Case 1 subcases and
Case 2 (including its final exceptional configuration) remain.

## M650--M660 Beli 2019 v2 completion

These milestones supersede the unfinished-state sentence above.

- M650 completes Lemma 9.3 in Case 1, Case 2, rank three, rank four, and
  arbitrary higher rank.
- M651 completes the exceptional Lemma 9.6 head reduction.
- M652 completes the residual Lemma 9.12 index-`\mathfrak p` descent,
  including rank-three and rank-four endpoints.
- M653 assembles Section 9 for every rank at least three.
- M654 completes the Section 7 equal-norm-or-smaller-counterexample
  reduction.
- M655 supplies the unary and binary base cases.
- M656 completes the equal-rank well-founded rank-volume induction.
- M657--M658 prove strict-rank completion and arbitrary-rank sufficiency.
- M659 proves both the original and revised-v2 forms of Theorem 2.1.
- M660 removes `Beli2019FinalStepLaws`, refreshes the audit tests, and adds
  the semantic fidelity and reproducibility reports in
  `docs/audit/Beli2019V2`.

The public endpoints are:

- `Bong.beli2019_sufficiency_complete`;
- `Bong.beli2019Theorem21`;
- `Bong.beli2019Theorem21_prime`.

These theorems are kernel checked and do not assume
`GoodBONGRepresentationLaws` or a theorem-level final-step oracle. They
remain conditional on the explicit non-default local arithmetic, Jordan,
classification, Section 4/5, scaling, and deep-complement law classes in the
main theorem signature. The accurate completion claim is therefore:
complete at the explicit modular local-law boundary, not yet an
unconditional theorem for every dyadic local field.

## M661 Henselian closure of the quadratic-defect laws

M661 starts the foundational law-closure phase. The normalized valuation
ring is proved Henselian from compactness and adic completeness. Applying
Hensel's lemma to `X^2 + X - c` proves that every principal unit of depth
strictly greater than `2e` is a square. Consequently:

- relative quadratic defect greater than `2e` forces a square;
- infinite relative defect is equivalent to being a square;
- every nonsquare has relative defect at most `2e`;
- `QuadraticDefectLaws` now has a concrete default instance for every
  `DyadicContext`;
- the public Beli 2019 Theorem 2.1 signature no longer accepts a
  `QuadraticDefectLaws` parameter, reducing its project-specific law/data
  slots from 49 to 48.

The public module is `Bong.Dyadic.QuadraticDefectHensel`. Its focused axiom
audit, including both Beli 2019 main endpoints, reports only `propext`,
`Classical.choice`, and `Quot.sound`.

## Build

```text
lake build
```

## M662--M663 further local-law closure

- M662 proves the dyadic unit square-difference, principal-unit filtration,
  quadratic-defect parity, and unit-defect spectrum interfaces from
  `DyadicContext` and the Henselian square theorem.  The two corresponding
  parameters disappear from the Beli 2019 main endpoints.
- M663 proves codimension-one diagonal cancellation directly from
  finite-dimensional nondegenerate quadratic-space linear algebra.  The
  proof constructs the one-dimensional orthogonal complement, identifies
  its coefficient through the determinant square class, rescales that line,
  and applies common-tail cancellation.  The
  `DiagonalCodimensionOneCancellationLaws` parameter consequently disappears.

Together with the removal of two duplicate Lemma 3.10 instances that are
constructed inside the main theorem, the revised-v2 endpoint now has 43
project-specific law/data slots.  Focused audits still report only
`propext`, `Classical.choice`, and `Quot.sound`.

## Unconditional completion update (28 August 2026)

The local-law closure phase is complete.  Every project-specific law or data
package used by the four-paper proof chain now has a concrete construction,
and the public endpoints instantiate those packages internally.  In
particular, the elaborated signatures of the Beli 2003 main theorems, Beli
2006 Theorems 3.2 and 4.5, Beli 2009/2010 Theorem 3.1 and its final Section 5
conclusions, and both versions of Beli 2019 Theorem 2.1 contain no
project-specific law/data parameters.

The final closure also proves the path-refined forms of Beli 2009 Lemmas 9.2
and 9.3 needed for all-rank adjacent-binary connectivity.  The public results
are:

- `Bong.beli2009Section5_largeResidueConnectivity_proved`;
- `Bong.Beli2009FinalRemarksProof.beli2009Section5_residueTwoParametricCounterexample_proved`;
- `Bong.Beli2009FinalRemarksProof.beli2009Section5_q2Counterexample_proved`;
- `Bong.beli2009Section5_binaryTransformationDichotomy_proved`.

`BongTest.FinalPublicTheoremAudit` prints the signatures and axiom sets of
all core public endpoints.  `BongTest.Beli2009Audit` checks 65 listed
declarations, while `BongTest.Beli2019Audit` checks 555 declarations covering
the 138-item v2 paper inventory.  Every reported axiom set is a subset of
`{propext, Classical.choice, Quot.sound}`.  A lexical source scan finds no
`sorry`, `admit`, `sorryAx`, or project `axiom` command.  The three project
`opaque` declarations are definitions with explicit, kernel-checked bodies;
their own axiom reports contain only the same three standard logical axioms.

The ambient hypothesis remains `[DyadicContext K]`.  This is the project's
definition-level packaging of a characteristic-zero nonarchimedean local
field with a compatible normalized additive valuation, a chosen uniformizer,
and positive valuation of `2`; it does not contain a Beli theorem or a local
classification law.  `BongTest.Q2` constructs a concrete instance for
`ℚ_[2]`.

The current semantic status is `PROVISIONAL_MATCH`, project grade B.  The
earlier `FORMALIZATION_WEAKER` / grade-C reports describe historical
conditional snapshots and are superseded by
`docs/audit/Beli2019V2/15_unconditional_completion_audit.md`.  Grade A is not
claimed because an independent mathematical correspondence review and a
clean-clone build from a committed repository have not yet been completed.
The current reproducibility classification is therefore
`PARTIALLY_REPRODUCIBLE`.

The final verification command `lake --log-level=error build` completed
successfully with all 5,555 jobs after the transient high-concurrency Windows
failures were rebuilt sequentially.
