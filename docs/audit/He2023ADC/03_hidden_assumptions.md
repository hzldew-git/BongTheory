# Hidden assumptions

The formal predicate explicitly requires source integrality, target rank `n`,
target integrality, and representation of the target ambient quadratic space by
the source ambient space. The paper-facing Lemma 2.1 specialization also records
the standing assumption `n > 0`. Current field assumptions are dyadic local, stronger
than the paper's general local-field wording in Lemma 2.1.

The global predicates now exist, but `GlobalLocalLatticeSystem.Theorem13Laws`
still supplies the arithmetic inputs. A clean transitive axiom report does
not discharge a theorem parameter. The stable-rank global reductions likewise
retain ambient representation premises. These interfaces do not establish
the corresponding concrete algebraic-number-field theorems.

The profile criterion quantifies over every good BONG of an integral lattice
on the specified space. It assumes ambient isometry, not lattice isometry.
Maximality of the reference table rows is proved internally. The ten profile
endpoints and the odd second-column endpoint of Lemma 4.9 now have no
undischarged `GoodBONGClassificationLaws` parameter: they use the checked
Beli classification proof. Ordinary field, integrality, unit, defect, and
rank hypotheses remain part of the mathematical statements.

The unary table is indexed by a finite complete and irredundant unit
square-class representative system. Completeness and irredundancy are used
as mathematical hypotheses, not hidden axioms. The exact count `2 * |U|` is
unconditional once that index is chosen. The conversion to the printed
`4 * (N p)^e` now uses the proved theorem
`HeADC2025Corollary721CountingLaw.card_unit_representatives`; the namespace
name is retained for compatibility, but there is no counting-law typeclass or
theorem parameter. See reports 50 and 57.

The publisher's standing convention on page 986 assumes integrality for
all subsequent lattices. Thus the explicit integrality premise of the new
published-family criteria does not narrow Lemmas 4.11--4.12. Nonexceptional
unit rows use the square-class domain excluding squares and the discriminant
class. Their finite defect, oddness and upper bound are derived. The final
odd second-column criterion has no auxiliary `kappa` parameter: its existence
at defect `2e-1` is proved. See checkpoint `976883e` and report 14.

Proposition 4.13 at checkpoint `9c432a6` assumes only the source's dyadic
context, good BONG, and norm maximality. It derives the unit normalization,
ambient row, actual maximal-lattice isometry, and order profile internally.
There is no additional representative-system or profile premise; see report 15.

The Proposition 4.16 endpoint at `5fff597` assumes only the dyadic field
context, a nondegenerate space, a full norm-maximal lattice, and rank four.
No good BONG, order profile, anisotropy, or project-law premise is added.
The extra field restriction is substantive: the published proposition also
includes non-dyadic local fields. Its exception is an integral isometry class,
not equality of arbitrarily chosen representatives. The factor pi scales
the form, not the lattice vectors. See report 16.

Lemma 6.4 assumes actual integral representations of its named maximal
tests. Their good BONGs, profiles, determinant separation and completion data
are constructed internally. The rank inequality is derived. In part (i),
the positive next-order statement is conditional on the existence of its
index, while the unconditional order statement includes equal rank. In
parts (ii) and (iv), the two different determinant classes imply strictly
larger source rank. Part (iii)'s named-space domain excludes exactly the
undefined binary square row. Part (iv)'s unit kappa and defect `2e-1` are
the parameters explicitly specified by the paper; sharp-domain membership
and both last-order formulas are not added hypotheses. See report 17.

Lemma 6.5 assumes no representation or ambient representation. Its public
endpoints derive target orders on arbitrary good BONGs from isometries with
the two actual unit-uniformizer maximal classes. Part (ii) adds no next-order
bound; the required bound follows from good-BONG monotonicity. Its defect
bridge retains both alpha caps. The empty head at n=2 is not an additional
positive-rank assumption. See report 18.

Theorem 6.1 quantifies over arbitrary full lattices with even n >= 2 and
rank n+1. It constructs the BONG and derives all testing and profile facts.
Integrality belongs to both `IsNADC` and `IsOMaximal`; no extra field,
profile, representative-system or classification-law premise is hidden.
The universe parameters of ADC testing are explicitly `{u,u,u}`. Report 19
records the independently expanded public statement.

Lemma 6.6's target orders are derived for arbitrary isometric good BONGs,
not supplied. The parity branch requires only even next order; the raw
defect branch derives its square class. Neither branch assumes ambient
or integral representation. Clause (ii)'s positive k condition is exactly
n >= 4, where the second square-class model is defined. See report 21.

Lemma 6.7 assumes actual representation of its named lattice, as printed,
not a testing law or ambient-only representation. Its target BONG and
integrality are constructed internally. The preceding alpha bound and the
strict uncapping inequality are derived; next-order zero and raw/capped
equality are not assumed. See report 22.

Lemma 6.8(i)--(ii) constructs the good BONG, actual tests and all order
data. Rank is derived from the stated ambient isometry and integrality
from n-ADC. Clause (i) includes n=2 by a proved uniform embedding argument;
clause (ii) retains n>=4. No undefined binary square second model or
full-determinant assumption is introduced. See report 23.

Lemma 6.8(v),(vi) derives the three actual tests, finite full defect and
entire profile. Its class-domain core has no representative normalization
premise. The printed-domain wrappers explicitly require the fixed Delta
to belong to U; page 983's normalization alone does not imply this.
This is a disclosed representative convention, not a classification law.
See report 24 and `SOURCE_DELTA.md`; author confirmation remains pending.

Report 25's second-column endpoints construct all complementary tests and
kappa internally. The internal central-alpha implication is discharged
before either public theorem; rank and norm integrality follow from the
ambient and ADC hypotheses. The positive k assumption in (iv) is visible
and genuinely restricts it to n>=4. It is not a paper-wide convention and
is not counted as a complete proof of the published (iv).

The boundary counterexample uses `IsNADC.{u,u,u}`. Thus its target carriers
share the universe of the field and source carrier. Every finite-dimensional
binary space has a coordinate model there, so this does not omit a binary
isometry class; an arbitrary-universe strengthening is not separately exported.
The abstract `DyadicContext` is inhabited by the checked `Q_2` instance.
Square normalization permits a scalar of negative valuation, but integral
transport is obtained through maximal-lattice uniqueness rather than by
assuming that the coordinate scaling is an integral map.

Theorem 7.2 exposes the finite representative system `U`, its completeness,
and the occurrence of the distinguished discriminant class. The latter is
needed only to translate the printed deletion `U \ {1, Delta}` into the
intrinsic sharp square-class domain. The product hypotheses, defect bound,
line order, selected column, ADC property, and maximal-overlap profile are
all derived in the public theorem chain; no product-classification law or
maximal-overlap law is supplied by the caller. See report 44.

Remark 7.3 uses the same explicit finite representative-system interface as
Theorem 7.2 for its first two formulas. The integer `l`, its nonnegativity,
and `2l <= 2e-2` are derived from the quadratic defect. The binary shear,
integrality conditions, maximal-lattice comparison, discriminant endpoint,
and auxiliary defect-`2e-1` unit used for the third formula are all
constructed internally. The exact third representative wrapper needs only
that `U` is complete and normalized. See report 45.

Corollary 7.21's finite catalogue, isometry completeness, irredundancy,
maximality partition, and counts in terms of `|U|` add no counting premise.
The printed residue-norm formulas use the internally proved O'Meara 63:9
identity `|U|=2(N p)^e`. The proof passes through an actual equivalence between
the representative system and `ValuationUnitClass K`, so completeness and
irredundancy do not conceal a cardinality premise. See reports 46 and 57.

Section 5 is proved over `HeADC2025NonDyadicSystem.SectionFiveLaws`. The
package explicitly contains the non-dyadic Jordan-rank identities, ambient
representation separations, target integrality/ranks, and maximal-lattice
facts used by the published proof. Supplying such a structure is a genuine
mathematical assumption until a concrete non-dyadic instance is built; it is
not discharged by the theorem bodies or by their standard-only axiom reports.
None of the numbered Section 5 conclusions occurs as a structure field. See
report 47.

Report 61 removes a narrower part of this boundary. The 16 block expressions
printed in Lemma 4.7(i), their parity-dependent hyperbolic multiplicities,
their `J_0`/`J_1` ranks, `J_{0,1}=N` table arithmetic, and the missing binary
row are now concrete finite data. This does not construct the corresponding
local lattices. Their maximality, isometry classification, exhaustive and
minimal testing properties, and the concrete non-dyadic instance of the
generic O'Meara representation theorem remain genuine mathematical inputs to
`SectionFiveLaws` and `CatalogueLaws`. Report 66 derives He's complete Lemma
4.8 conclusion from that lower-level cited-theorem interface.

Section 8 is proved over `HeADC2025GlobalData.SectionEightLaws` together with
the existing Theorem 1.3 law package. Concrete localization, genus transport,
class-number-one regularity, the distinguishing-lattice theorem, and scaling
stability are all visible structure fields. In particular, Theorem 8.2's
Meyer--Xu--O'Meara content is not reconstructed by returning its field.
The remaining theorems do prove the source deductions from those inputs. See
report 47.

The corrected quaternary catalogue does not assume completeness or
irredundancy. Those properties are proved using the corrected three-way
classification, maximal-lattice uniqueness, and nonisometric ambient spaces.
The final residue-norm conversion now uses the proved O'Meara 63:9 theorem;
both `4|U|+2` and `8(N p)^e+2` are unconditional in the dyadic interface.
See reports 48 and 57.

The dyadic Theorem 1.10 endpoint does not infer an isometry-class count from
the cardinality of an arbitrary parameter list. Each maximal-table branch is
proved complete and irredundant for integral isometry by using the relevant
maximality classification and maximal-lattice uniqueness. The final
residue-norm formulas now use the unconditional theorem in the compatibility
namespace `HeADC2025Corollary721CountingLaw`; the endpoint does not include
the non-dyadic branch. See reports 51 and 57.

The non-dyadic Theorem 1.10 endpoint separately proves the seven- and
eight-row finite counts and all catalogue deductions. Its
`CatalogueLaws` parameter still assumes maximality, exhaustion, and
irredundancy of the published non-dyadic rows, plus the equal-rank
ADC-implies-maximal implication. Those are genuine undisclosed mathematical
obligations until a concrete local-field instance is constructed. No count
or Theorem 1.10 conclusion is a law field. The common row-definedness
predicate is now shared with the concrete symbolic table certificate, so the
unary and seven-row binary combinatorics are not duplicated. Report 63 also
removes the rank-four finite case split from the boundary. Its remaining
`QuaternaryTableRealizationLaws` fields state the actual block-to-lattice
representation, exceptional isometry, and transport facts. See reports 52
and 61--63.

Report 64 isolates the additional inputs behind Lemma 4.7(ii). The finite
defined-row family and its cardinalities are internal, as is the proof that
maximal classification, representation transport/composition, maximal
overlattices, and row deletion witnesses imply literal minimal testing.

Report 65 removes the final Proposition 4.15 necessity conclusion from the
catalogue law package. The remaining assumptions are the lower-level
existence of a maximal lattice on the represented ambient space, same-rank
maximality transfer, and the maximal-lattice representation fact used in
Lemma 4.14. None of these fields states Proposition 4.15 or the `n`-ADC
conclusion of Lemma 4.14.

Report 66 replaces the missing final Lemma 4.8 statement by a derived public
biconditional. Its external field is the cited O'Meara 1958 Theorem 1 for an
arbitrary `J_{0,1}=N` target, not He's Table 4.7 conclusion. A concrete
non-dyadic implementation of that general theorem remains an explicit
assumption boundary.
Concrete maximal-overlattice and deletion-witness instances remain external.

Report 67 introduces no proposition-valued law package for the dyadic Lemma
4.6 endpoints. The source ambient-isometry conditions are exposed as
equal-rank diagonal representation, and the target nonexception condition is
its negation against the opposite published row. Their interpretation relies
on the exact BONG diagonalization bridge already proved in the repository.
The corank-two determinant condition uses the ordinary-determinant square-class
translation from Lemma 4.5(i); reviewers must not read it as literal equality
of chosen determinant representatives. The remaining restriction is the
dyadic context itself.

The two final enumeration results have distinct visible boundaries. For
Corollary 1.8, the Hanke and Kirschmer class types, their partition, and the
cardinalities 115 and 471 are supplied; only the total 586 is derived. For
Theorem 1.11, `HeADC2025Theorem111Laws` supplies Oh-catalogue exhaustion,
the local row checks, and table metadata. The final 21-row classification is
not a law field: its source-row list, nonrepetition, count, global `2`-ADC
deduction, completeness, and maximality conclusion are proved. The 48
concrete matrix rows, their printed discriminants, positive definiteness, and
literal last-column pattern are closed in Report 59. Oh-catalogue exhaustion,
the global-lattice interpretation, and the actual local computations remain
open.

Lemma 2.2 is not overgeneralized to an arbitrary abstract field extension.
`HasOneDimensionalSubspaceDescent` still exposes the arithmetic base case in
the reusable algebraic theorem, but Report 56 proves its concrete instance
for every number-field finite completion. Density is supplied by mathlib's
completion theorem, while square-class openness is proved from the inverse
function theorem. The final
`heADC2025Lemma22_numberFieldFiniteCompletion` has no proposition-valued law
premise. See reports 55--56.
