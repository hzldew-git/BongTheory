# Theorem 1.10 dyadic catalogue checkpoint

Status: `DYADIC_BRANCHES_FORMALIZED_WITH_BINARY_SOURCE_CORRECTION`.

Code checkpoint:
`125dcf24f39f0b22a5f69fb33241885169314c06` on
`feat/he-formalization`.

## Source authority and scope

The sole semantic authority is the publisher version of record, Theorem 1.10
on p. 986 and its proof on p. 1017. The theorem counts integral-isometry
classes of rank-`m`, `n`-ADC lattices for `m` in `{n,n+1,n+2}`. This
checkpoint closes every dyadic rank and parity branch. The non-dyadic branch
and a repository proof of the cited O'Meara 63:9 cardinality remain outside
this checkpoint.

The publisher's binary corank-two value `8(N p)^e+1` is false. Report 48
proves the exact corrected value `8(N p)^e+2`; this report preserves that
source mismatch and never substitutes the correction silently.

## Exact catalogues, not parameter counts

`HeADC2025IsExactNADCIsometryCatalogue n m family` records four obligations:

- every member of `family` has rank `m`;
- every member is `n`-ADC;
- every rank-`m`, `n`-ADC lattice is integrally isometric to a member; and
- integrally isometric members have equal indices.

The generic even and odd constructors prove these obligations from the
published finite maximal tables and a classification theorem saying that the
relevant `n`-ADC lattices are maximal. Completeness uses ambient-space table
exhaustion followed by uniqueness of maximal lattices in an isometry class.
Irredundancy transports an integral isometry to an ambient isometry and then
uses the already proved irredundancy of the normalized square-class table.

The following endpoints instantiate the generic construction:

| Rank branch | Classification input | Exact endpoint |
|---|---|---|
| `m=n=2k+2` | Proposition 4.15 | `heADC2025Theorem110EqualRankEven` |
| `m=n=2k+3` | Proposition 4.15 | `heADC2025Theorem110EqualRankOdd` |
| `n=2k+2`, `m=n+1` | Theorem 6.1 | `heADC2025Theorem110EvenCorankOne` |
| `n=2k+3`, `m=n+1` | Theorem 7.1 | `heADC2025Theorem110OddCorankOne` |
| `n=2k+2>=4`, `m=n+2` | corrected stable Theorem 6.2 | `heADC2025Theorem110EvenCorankTwo` |
| `n=2`, `m=4` | corrected six-family catalogue | `HeADC2025QuaternaryCatalogue.isExactIsometryCatalogue` |
| `n=2k+3`, `m=n+2` | Corollary 7.21 | `HeADC2025Corollary721Index.heADC2025Corollary721` |

The single endpoint `heADC2025Theorem110DyadicCorrected` packages this
exhaustive list. Its binary field contains the corrected six-family
catalogue and `+2` count, while a separate field contains the formal
negation of the publisher's `+1` statement.

## Counts and visible premise

Before the cited substitution, the maximal tables have cardinalities
`4|U|-1` in binary rank and `4|U|` in every higher rank. Corollary 7.21 has
total `(4e+3)|U|` and nonmaximal part `(4e-1)|U|`. The corrected binary
corank-two catalogue has `4|U|+2` entries.

After the explicit premise `|U|=2(N p)^e`, the formal endpoints give:

- `8(N p)^e-1` for `m=n=2`;
- `8(N p)^e` for every maximal-table branch;
- `(8e+6)(N p)^e`, with `(8e-2)(N p)^e` nonmaximal classes, for odd
  dyadic corank two; and
- `8(N p)^e+2` for binary dyadic corank two, refuting the printed `+1`.

`HeADC2025Corollary721CountingLaw` remains an ordinary theorem parameter.
It is neither a Lean axiom nor a proved generic instance in this repository.

## Mechanical evidence

At the code checkpoint, the new module compiles directly with Lean 4.32.1.
Its dependency build completes 5,025 jobs, the canonical paper entry
completes 5,033 jobs, and the expanded paper audit passes. Selected
dependency reports for all catalogue constructors and all rank-branch
endpoints contain exactly `propext`, `Classical.choice`, and `Quot.sound`.
The new source has no `sorry`, project `axiom`, `opaque`, or `unsafe`
declaration, has no line over 100 columns, and passes `git diff --check`.

A new exact-revision clean Review Kit, GitHub-hosted CI, and independent
human semantic sign-off remain separate gates.

## Audit verdict

Every dyadic branch of Theorem 1.10 is `FULLY_FORMALIZED` as an exact
integral-isometry catalogue, with semantic status `PROVISIONAL_MATCH` except
for the binary corank-two branch, whose printed count is
`SEMANTIC_MISMATCH` and whose corrected count is proved. Numerical formulas
remain `FORMALIZED_RELATIVE_TO_CITED_COUNTING_LAW`. The unrestricted theorem
over all local fields remains `NOT_COMPLETE` because the concrete
non-dyadic counting construction is pending.
