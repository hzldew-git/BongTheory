# Unconditional Completion Audit

## Audit identity

- Audit date: 28 August 2026.
- Formal scope: the BONG dependency chain used for Beli 2003, Beli 2006,
  Beli 2009/2010, and Beli 2019 v2.
- Primary 2019 source: Constantin N. Beli, *Representations of quadratic
  lattices over dyadic local fields*, arXiv v2.
- Paper PDF SHA-256:
  `1669C626A6D01AF297E07C2CB9584C5BD34F4CEE0F2B188EE0B351BD091C387C`.
- Paper TeX SHA-256:
  `00D58B232A331E559D175C2DF383DE82A49BC7B044E035092B7AC96015858292`.
- Formal Lean/build-input snapshot SHA-256:
  `7F388DB9F8175ECC9589C4C63583DF3D982D17CC098937AC1F9D8CFBE1819397`.
  This is a path-delimited SHA-256 over all `Bong` and `BongTest` Lean files
  plus the two root modules, Lake files, manifest, and toolchain file.
- Lean: 4.32.1, commit
  `f054605aea4b840552cca2e725580bffd1e1b704`.
- mathlib:
  `520045ab14e26149ee970e2e617ca04b09bde5d6`.

This report supersedes the conditional semantic status recorded in reports
`03`, `05`--`09`, and `12`--`14`.  Those files remain historical evidence for
the sequence in which the local-law boundary was closed.

## Outcome

The earlier explicit local-law boundary has been closed.  The elaborated
signatures of the public main endpoints contain no project-specific law or
data parameters.  Internal `...Laws` and `...Data` structures remain useful
modular proof APIs, but their fields are constructed by checked Lean terms on
the public proof paths; they are not assumptions of the final declarations.

Current semantic verdict: **`PROVISIONAL_MATCH`**.

Current project grade: **B**.

The grade is not A because no independent mathematical reviewer has yet
confirmed every source-to-Lean quantifier, endpoint convention, and
normalization.  A committed clean-clone build has now been demonstrated, but
technical reproducibility cannot replace that human semantic decision.  The
former `FORMALIZATION_WEAKER`, grade-C verdict no longer describes the current
theorem signatures.

## Meaning of the field boundary

The public results assume `Field K`, `CharZero K`, `ValuativeRel K`,
`TopologicalSpace K`, and `DyadicContext K`.  `DyadicContext` extends
`IsNonarchimedeanLocalField` and contains only:

1. a normalized additive valuation with values in `WithTop Int`;
2. compatibility of that valuation with the existing valuative relation;
3. a chosen uniformizer of valuation one; and
4. positivity of the valuation of `2`.

It contains no Beli conclusion, Jordan classification, scaling theorem,
Hilbert-symbol theorem, or representation theorem.  Thus it is the project's
definition-level packaging of a dyadic local field with chosen normalized
data, not a residual mathematical law boundary.  `BongTest.Q2` constructs an
actual `DyadicContext` instance for `ℚ_[2]`, which also rules out a vacuous
empty-class interpretation of the development.

The theorem APIs use chosen good BONGs and lengths `m + 1` and `n + 1`.
Accordingly, the public statements cover positive-rank lattices equipped with
the good BONGs used to state the criteria.  No rank-zero claim is added beyond
the paper's BONG formulation.

## Public theorem endpoints

| Paper | Public Lean endpoint | Remaining project law/data parameters |
|---|---|---:|
| Beli 2003, Theorem 1 | `BONG.beliTheoremOne_proved` | 0 |
| Beli 2003, Theorem 2 | `Lattice.beliTheoremTwo_proved` | 0 |
| Beli 2003, Theorem 3 | `BONG.beliTheoremThree_proved` | 0 |
| Beli 2006, Theorem 3.2 | `beli2006Theorem32_proved` | 0 |
| Beli 2006, Theorem 4.5 | `beli2006Theorem45_proved` | 0 |
| Beli 2009/2010, Theorem 3.1 | `BONG.GoodBONG.beli2009Theorem31_concrete` | 0 |
| Beli 2009/2010, final positive remark | `beli2009Section5_largeResidueConnectivity_proved` | 0 |
| Beli 2009/2010, final dichotomy | `beli2009Section5_binaryTransformationDichotomy_proved` | 0 |
| Beli 2019, Theorem 2.1 | `beli2019Theorem21` | 0 |
| Beli 2019 v2, Theorem 2.1 with (iii') | `beli2019Theorem21_prime` | 0 |

The parameterized residue-two family and the explicit two-adic example are
also unconditional:

- `Beli2009FinalRemarksProof.beli2009Section5_residueTwoParametricCounterexample_proved`;
- `Beli2009FinalRemarksProof.beli2009Section5_residueTwoCounterexample_proved`;
- `Beli2009FinalRemarksProof.beli2009Section5_q2Counterexample_proved`.

## Source correspondence for Beli 2019 v2

The v2 TeX source at lines 791--827 was compared with the current formal
definitions and theorem signatures.

| Source feature | Formal counterpart | Audit result |
|---|---|---|
| Ambient representation `FN` by `FM` | `q.Represents r` | `PROVISIONAL_MATCH` |
| Integral representation `N` by `M` | `Lattice.Represents q r L M` | `PROVISIONAL_MATCH` |
| Rank condition `n <= m` | `hRank : n ≤ m`, with lengths `n+1`, `m+1` | `PROVISIONAL_MATCH` |
| Condition (i) | `RepresentationOrderCondition` | `PROVISIONAL_MATCH` |
| Condition (ii) | `RepresentationDefectCondition` | `PROVISIONAL_MATCH` |
| Condition (iii) | `CentralRepresentationConditions` | `PROVISIONAL_MATCH` |
| Condition (iv), including `i = n+1` convention | `LongRepresentationConditions` and typed terminal indices | `PROVISIONAL_MATCH` |
| Revised condition (iii') | `CentralRepresentationConditionsPrime` | `PROVISIONAL_MATCH` |
| Equivalence of (iii) and (iii') under (i)--(ii) | `BONG.GoodBONG.beli2019Lemma216` | `PROVISIONAL_MATCH` |

The source/target orientation was checked from the representation
definitions: `target.Represents source` is an injective form-preserving map
from the smaller source into the larger target.  The strict inequalities,
prefix lengths, zero-based/one-based index translation, and terminal branch
were reviewed explicitly.  No direction reversal or off-by-one change was
found.

## Coverage evidence

- Beli 2003 is connected through its Section 2--7 development to the three
  public main theorems and their focused milestone tests.
- Beli 2006 has unconditional public forms of its two announced main
  criteria.  The classification announcement is discharged by the complete
  2009 proof; the representation announcement is discharged by the complete
  2019 proof.
- `BongTest.Beli2009Audit` checks 65 declarations covering every numbered
  result in the project inventory and all formalized final remarks.
- The Beli 2019 v2 inventory contains 138 numbered objects: 11 definitions,
  96 theorem-like results, and 31 numbered notes.  All 138 have section-level
  formal mappings.  `BongTest.Beli2019Audit` prints axiom reports for 555
  declarations in the decomposed proof families.

The inventory counts are coverage evidence, not a claim that 138 separate
human reviewers have independently certified 138 exact statement matches.
That distinction is the reason for `PROVISIONAL_MATCH` rather than
`VERIFIED_MATCH`.

## Adversarial and circularity review

The following failure modes were tested:

1. **Conclusion hidden in a law class.** The final signatures expose no
   project law/data class.  Internal classes are instantiated by concrete
   proof modules before the endpoints are assembled.
2. **Theorem assumed by itself.** The 2019 main module does not import either
   2006 public wrapper.  It imports the independently proved 2009
   classification theorem.  The 2006 wrappers are downstream corollaries.
3. **2009/2019 import cycle.** The 2009 classification proof is upstream of
   2019.  Only the later, independent 2009 final binary-connectivity module
   uses the completed 2019 representation result; it is not imported by the
   2019 main theorem.
4. **Vacuous ambient structure.** A concrete `ℚ_[2]` context is built and
   compiled in `BongTest.Q2`.
5. **Wrong representation notion.** Both ambient and lattice
   representations require injective form-preserving maps, and the lattice
   conclusion additionally preserves membership in the target lattice.
6. **Lost strict-rank source.** The deep-complement construction returns from
   the equal-rank envelope to the original represented lattice by an explicit
   composition theorem.
7. **Dropped endpoint conditions.** Dedicated typed index structures and
   terminal lemmas cover the paper's “ignore meaningless conditions”
   conventions.

No critical mismatch was found in this review.

## Kernel and placeholder audit

`BongTest.FinalPublicTheoremAudit` prints every public signature above and
its transitive axiom set.  Every endpoint reports only:

- `propext`;
- `Classical.choice`;
- `Quot.sound`.

The 65 Beli 2009 reports have exactly this set.  The 555 Beli 2019 reports
have this set or the subset omitting `Classical.choice`.

A source scan found no Lean use of `sorry`, `admit`, `sorryAx`, a project
`axiom`, `unsafe`, `extern`, `implemented_by`, `native_decide`, or `run_tac`.
There are three `noncomputable opaque` definitions:

- `Lattice.JordanDecomposition.saturationStepResult`;
- `Lattice.omearaTwoPlaneAddLatticeIsometry`;
- `Lattice.omearaTwoPlaneSquareAddLatticeIsometry`.

Each declaration has an explicit `by` body built from preceding proved
geometry.  Opacity prevents reduction by clients but does not create an
axiom.  Their own `#print axioms` reports contain only the same three standard
logical axioms.

## Build and reproducibility

The release-candidate verification commands are:

```powershell
lake --log-level=error build
lake env lean BongTest\FinalPublicTheoremAudit.lean
lake env lean BongTest\Beli2006Audit.lean
lake env lean BongTest\Beli2009Audit.lean
lake env lean BongTest\Beli2019Audit.lean
```

All five commands completed successfully in a separate clone of committed
revision `ee826e7a8e67dda053563c01e027b2379bd68e6f`.  The clone initially had
no `.lake` directory.  The official binary cache was unavailable, so the
dependency and project artifacts used by the successful run were generated
from the pinned sources.  The final default run reported:

```text
Build completed successfully (5555 jobs).
```

The default build includes both the `Bong` and `BongTest` targets.  An initial
source-build attempt used effectively unbounded Lake runtime concurrency and
eventually produced Windows file-read, access-violation, and `std::bad_alloc`
failures.  It was stopped without deleting the artifacts already generated in
that clean clone.  A retry with process-local `LEAN_NUM_THREADS=4` rebuilt the
failed modules and completed all 5,555 jobs without a Lean error.  In
particular, the three modules that failed during the first attempt have
explicit successful build records in the retry log.  No Lean source change
was needed.

The four focused audit modules then exited zero.  They contain 18 final-public,
2 Beli 2006, 65 Beli 2009, and 555 Beli 2019 axiom reports respectively, with
no forbidden placeholder or unknown-declaration marker.  The final
`git status --porcelain` output was empty.

Local reproducibility status:
**`REPRODUCIBLE_WITH_DOCUMENTED_EXTERNAL_DEPENDENCIES`**.

The dependency sources remain external network inputs pinned by
`lake-manifest.json`.  Public exact-tag evidence subsequently passed on
Ubuntu and Windows: Ubuntu built the complete default target without a GitHub
project cache; Windows separately completed a 5,555-job no-project-cache full
build and a corrected 4,935-job public-audit dependency closure whose four
audit logs match the local Windows receipt byte for byte.  The complete local
and hosted receipts and log hashes are recorded in
`docs/reproducibility/clean-clone-ee826e7.md` and
`docs/reproducibility/github-actions-v0.1.0-rc.1.md`.

## Precise completion claim

The justified claim is:

> Lean accepts an unconditional, project-law-free formal proof of the listed
> Beli 2003, 2006, 2009/2010, and 2019 v2 public results for positive-rank
> quadratic lattices over the project's `DyadicContext`, with the paper's
> good-BONG data and endpoint conventions.  Source correspondence is
> provisional pending independent mathematical sign-off.

This audit does not claim that Lean has independently validated the prose of
the papers or that every source item has received independent human review.
The public hosted technical evidence does not replace the independent human
semantic sign-off required for `VERIFIED_MATCH` or Grade A.
