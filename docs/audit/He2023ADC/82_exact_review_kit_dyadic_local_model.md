# Exact Review Kit receipt for the concrete dyadic local model

Status: `FRESH_EXTRACTION_RESUMED_LOCAL_PASS` / `SEMANTIC_GRADE_D`.

This receipt fixes the independently extracted local proof-closure evidence
for clean commit `f358750b10f41f03066d2b3acb31552bad58c15e`. That
checkpoint contains the concrete one-place dyadic local-maximality model from
Report 81. It is not yet a GitHub-hosted checkpoint.

## Archive identity

- archive: `BongTheory-He2023ADC-v0.4.1-rc.1-review-kit.zip`;
- size: 6,358,627 bytes;
- SHA-256:
  `CD0DD5C6E3CD187F1318438653EE8F2871B03C44032EA4279731AF06E3F841C0`;
- recorded source commit:
  `f358750b10f41f03066d2b3acb31552bad58c15e`;
- recorded source-tree state: `clean`;
- recorded local Lean sources: 2,009;
- recorded packaged files: 2,114;
- verified payload hashes after extraction: 2,113.

The strict structure verifier confirmed that the archive contains exactly one
paper manifest, paper directory, audit directory, and paper-specific theorem
index. It contains no `.git` directory, cached `.lake` directory, compiled
Lean artifact, publisher PDF, or manuscript TeX source.

## Controlled fresh extraction and Lean verification

The archive was extracted into a previously nonexistent directory. No project
`.lake` tree or compiled artifact was copied into that extraction. The build
was deliberately resumed inside the same extraction while tuning worker count:

- two workers reached job 763;
- four workers reached job 1,370;
- eight workers reached job 3,062;
- a short twelve-worker probe reached job 3,116 but was stopped when free
  memory fell to about 1 GB;
- eight workers then completed the remaining build.

Each resume reused only artifacts produced by the preceding stage in this same
fresh extraction. The final `lake build` completed all 5,595 jobs. This is a
controlled fresh-extraction result, not an uninterrupted single-process run.

The verifier then reran all 21 paper-specific audit modules from the generated
manifest and the enforcing `BongTest.PaperAxiomGate`; all 22 commands exited
successfully. The independently rerun gate reported:

```text
AXIOM_GATE_PASS: 61167 declarations checked
```

The comment-aware scanner separately checked all 2,740 tracked Lean sources
and found no forbidden proof token outside comments. All 30 scanner,
deployment-policy, and shard-planning tests passed.

## Independent exact-arithmetic verification

Both checked-in Mathematica programs were rerun from the extraction. The
Table 1 verifier returned `True` for all 48 determinants, symmetry, positive
definiteness, the literal source selection, and its 21-row count. The
non-dyadic Table 4.7 verifier returned `True` for all 12 symbolic profile,
definedness, count, and quaternary-case checks.

## Locked dependencies

All nine downloaded dependency repositories were clean, and their actual
heads exactly matched `lake-manifest.json`:

```text
mathlib           520045ab14e26149ee970e2e617ca04b09bde5d6
plausible         e12c1910fe855cbfc38803cd4e55543906d5fa62
LeanSearchClient  c5d5b8fe6e5158def25cd28eb94e4141ad97c843
importGraph       7e9612bf0b9ee66db3cb5b9988a35afc706f5a12
proofwidgets      6e311e2a844da9b2cc3971187df2fe0066947b93
aesop             a7dbf0c63b694e47f425f3dcddbc0e178bb432d3
Qq                38d591e778f100aec9762bb582f9c7f55f50e9dc
batteries         023ce7d62a0531e22a5331e20b587817a80d49ff
Cli               88679d088c9720c27ebdf2ba4dafe17341747f94
```

## Scope of this receipt

This supersedes the older local Review Kit receipt for proof closure through
Report 81. It certifies this exact archive and commit only. It does not turn
the one-place adapter into a concrete all-finite-place number-field model,
instantiate the remaining non-dyadic or external-catalogue law packages,
repair the published binary and Lemma 7.13 mismatches, provide independent
human semantic sign-off, or certify a later GitHub branch, merge commit, tag,
or release. The whole-paper verdict remains `NOT_COMPLETE`, Grade D.
