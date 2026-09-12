# Current v5 Review Kit and Windows verifier receipt

Status: `FRESH_EXTRACTION_RESUMED_LOCAL_PASS` /
`NOT_WHOLE_PAPER_COMPLETE` / `NOT_DEPLOYED`.

This receipt records source-package integrity and Lean-kernel verification for
the current v5 code-and-audit checkpoint. It is not GitHub CI, a tagged release
receipt, independent human semantic approval, or evidence that every assertion
in the manuscript is correct.

## Frozen inputs

- Semantic authority: author-corrected `classic_dyadic-n-uni-v5.tex`,
  139,941 bytes.
- Authoritative-source SHA-256:
  `C334676733163C7A521824E1F00C782A7BF0FD1ABE5366BF76D838238EDCA049`.
- Lean code checkpoint:
  `e3b18be95c813885a421b83fe0a0148d6b561ae0`.
- Packaged source-and-audit commit:
  `ab1901ac9df3e659a40a8cd4e1c0590997622217`.
- Source branch: `release/heclassic-v0.5.0-rc.1-prep`.
- Source tree state at packaging: `clean`.

The author-held TeX source is identified by its hash but is not copied into
the repository or Review Kit.

## Archive and structural verification

- Archive:
  `BongTheory-He2022Classic-v0.5.0-rc.1-ab1901a-review-kit.zip`.
- Archive size: 6,246,336 bytes.
- Archive SHA-256:
  `92AD5F18A70386948D970C627BC7C94835B3B380ADBF1FE9265949BFF09A336A`.
- Local Lean sources recorded by the manifest: 1,961.
- Lean files in the archive, including generated package entry and gate:
  1,964.
- Checksummed payload files: 2,023; packaged files including
  `FILES.sha256`: 2,024.
- Exact payload-hash coverage: `PASS`.
- Paper-directory, root-document, and theorem-index isolation: `PASS`.
- Forbidden manuscript, Git, cache, or compiled content: none.

In particular, the archive contains no `.tex`, `.pdf`, `.git`, `.lake`,
`.olean`, or `.ilean` entry.

## Kernel and audit verification

The archive was expanded into a new directory. Its dependency directory was
connected to a local cache whose nine Git checkouts were separately checked
against the packaged manifest and found exact and clean. No project
`.lake/build` directory was imported from the archive. After a memory-pressure
failure at higher concurrency, verification resumed in that same new
extraction with locally generated build outputs and two Lean workers. The
result was:

```text
Build completed successfully (5682 jobs).
```

All nine manifest-selected checks were then run separately and returned exit
code zero:

1. `BongTest.He2022ClassicAudit`;
2. `BongTest.He2022ClassicDiscriminantRamificationAudit`;
3. `BongTest.He2022ClassicNumberFieldGlobalDataAudit`;
4. `BongTest.He2022ClassicNumberFieldLocalExtensionAudit`;
5. `BongTest.He2022ClassicEvenExtensionAudit`;
6. `BongTest.He2022ClassicLocalUniversalityAudit`;
7. `BongTest.He2022ClassicProposition82Audit`;
8. `BongTest.He2022ClassicStrongApproximationAudit`; and
9. the enforcing gate `BongTest.PaperAxiomGate`.

The enforcing gate reports:

```text
AXIOM_GATE_PASS: 62917 declarations checked
```

It permits only `propext`, `Classical.choice`, and `Quot.sound`. Nonfatal
linter and deprecation warnings do not change kernel acceptance or the
semantic status.

## Dependency closure

Every dependency head equals the revision pinned by the packaged
`lake-manifest.json`, and every dependency worktree is clean:

| Dependency | Exact revision |
|---|---|
| mathlib | `520045ab14e26149ee970e2e617ca04b09bde5d6` |
| plausible | `e12c1910fe855cbfc38803cd4e55543906d5fa62` |
| LeanSearchClient | `c5d5b8fe6e5158def25cd28eb94e4141ad97c843` |
| importGraph | `7e9612bf0b9ee66db3cb5b9988a35afc706f5a12` |
| proofwidgets | `6e311e2a844da9b2cc3971187df2fe0066947b93` |
| aesop | `a7dbf0c63b694e47f425f3dcddbc0e178bb432d3` |
| Qq | `38d591e778f100aec9762bb582f9c7f55f50e9dc` |
| batteries | `023ce7d62a0531e22a5331e20b587817a80d49ff` |
| Cli | `88679d088c9720c27ebdf2ba4dafe17341747f94` |

## Windows verifier correction

The first scripted verification stopped before the build because Windows
PowerShell converted ordinary native stderr progress from Git/Lake into a
terminating error under `ErrorActionPreference = Stop`. The verifier now
captures both native streams while treating the native exit code as the sole
success criterion. PowerShell parsing, all 30 policy tests, the 2,802-source
forbidden-token scan, and a structure-only run of the corrected verifier pass.

The archive above predates that script correction. Any Review Kit generated
from a later commit containing this report also contains the corrected
verifier. The correction changes orchestration only; it does not alter any
Lean declaration or proof.

## Semantic and deployment boundary

This receipt establishes archive integrity, exact dependency recovery, Lean
kernel acceptance, and the declared transitive-axiom boundary for the stated
checkpoint. It does not resolve either source-level defect in v5:

1. Corollary 6.3 is unrestricted in odd rank, but its proof says "without loss
   of generality, assume that n is even". A kernel-checked `e = 2`, `n = 3`
   counterexample refutes the odd statement. A source repair must restrict the
   result to even `n >= 2` or replace the odd conclusion, and propagate that
   change to Lemma 8.3 and Theorems 1.7--1.8.
2. Lemma 8.1(iii) names the preassigned localized scalar-extension lattice
   `L_P`, whereas the cited He--Hu coefficient criterion gives a good BONG for
   some lattice. V5 supplies no carrier-identification argument. A source
   repair must either weaken the conclusion to the proved existence statement
   or add a theorem identifying the constructed lattice with `L_P`.

Concrete number-field lattice/localization, place-equivalence, local
sum-of-squares, and strong-approximation instances also remain open. Therefore
the project grade stays D, the completion verdict stays `NOT_COMPLETE`, and
GitHub deployment stays disabled pending a corrected source and separate
release authorization.
