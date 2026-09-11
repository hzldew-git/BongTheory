# Non-dyadic Lemma 4.5 invariant derivation

## Status

Checkpoint: `b2dba36476d6dea37762bc6b1b00b7d952aafa62`.

Classification: `CONDITIONAL_FORMALIZATION` / `SOURCE_LOGIC_MATCH`. Both
directions of the published quadratic-space lemma are proved from an explicit
local invariant interface. The remaining condition is construction of that
interface for the repository's eventual concrete non-dyadic local-field
model; no exactly-one conclusion is assumed.

## Authoritative source

The sole statement authority is Zilong He, *On n-ADC integral quadratic
lattices over algebraic number fields*, *Documenta Mathematica* 30 (2025),
no. 4, 981--1022, p. 993, DOI 10.4171/DM/1003. Publisher-PDF SHA-256:

`E26190C88B16624DCCB7F269C6C3FFDA02BC6830677A5BC0C8E0AD48A36E72D6`.

The formal statements retain every source restriction:

- part (i) has `n >= 2`, two non-isometric `n`-spaces with the same
  determinant class, and a source of dimension `n+1`, or dimension `n+2`
  with the same determinant;
- part (ii) has `n >= 3`, the same pair, and a target of dimension `n-1`, or
  dimension `n-2` with the same determinant;
- the direction of representation is reversed in part (ii); and
- both positive and negative alternatives are present, so "precisely one"
  is not weakened to mere existence.

The two table-specific "in particular" clauses retain the standing
definedness convention from Definition 4.1, including the omitted low-rank
second-column rows.

## Formal construction

`Bong.Bong.He2023ADCNonDyadicLemma45` introduces:

- `SpaceRepresentsExactlyOne` and `SpaceIsRepresentedByExactlyOne`, with the
  two opposite representation directions separated;
- `Lemma45InvariantData`, containing a determinant class, a Boolean encoding
  of the two-valued Hasse invariant, and the four expected signs for the two
  codimensions and two directions; and
- `Lemma45Laws`, containing only the determinant--Hasse classification
  implication and the four codimension-one/two representation criteria.

The public theorems
`Lemma45Laws.heADC2025Lemma45iNonDyadic` and
`Lemma45Laws.heADC2025Lemma45iiNonDyadic` first prove that the two spaces have
different Hasse bits. A finite Boolean exhaustion then shows that exactly one
bit equals the relevant representation sign, and each criterion transports
that alternative back to the corresponding representation statement.

`Bong.Bong.He2023ADCNonDyadicLemma46` supplies the two defined table rows'
rank, determinant equality, and non-isometry facts. Its new
`heADC2025Lemma45iNonDyadicTargets` and
`heADC2025Lemma45iiNonDyadicTargets` prove both publisher "in particular"
sentences. Lemma 4.6(i) now invokes the former theorem. The former
`lemma45i_corankOne` and `lemma45i_corankTwo` exactly-one fields have been
removed from `Lemma46Laws`.

Thus the exposed trust boundary has moved downward from He's Lemma 4.5
conclusion to the standard local classification and codimension criteria used
to prove it. These proposition-valued law fields are visible mathematical
inputs, not Lean axioms and not a concrete non-dyadic implementation.

## Mechanical evidence

With Lean 4.32.1:

- the new focused audit completes 2,999 jobs;
- the refactored Lemma 4.6 focused audit completes 3,002 jobs;
- the canonical paper entry, canonical audit, and both focused audits
  complete 5,563 jobs;
- all six new public Lemma 4.5 endpoints report only `propext` and
  `Quot.sound`; the pre-existing Lemma 4.6(ii) transport endpoints additionally
  report `Classical.choice`;
- the comment-aware source scanner checks 2,784 tracked Lean files;
- all 27 CI policy tests pass; and
- changed Lean lines are at most 100 columns, the manifest parses, and
  `git diff --check` passes.

This is local exact-checkpoint evidence, not a fresh-extraction Review Kit.
Report 69 records the clean kit for the immediately preceding `9350ca3`
checkpoint. A later clean kit must include this report and code before the
new invariant derivation is considered deployment evidence.
