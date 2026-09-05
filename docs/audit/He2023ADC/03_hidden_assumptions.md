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
