# Current v5 source-only Review Kit receipt

Status: `FRESH_EXTRACTION_RESUMED_LOCAL_PASS` / `NOT_WHOLE_PAPER_COMPLETE` /
`NOT_DEPLOYED`.

This receipt records local package integrity and Lean-kernel verification for
the exact source commit below. It is not GitHub CI, a tagged release receipt,
or independent human semantic approval.

## Frozen inputs

- Semantic authority: author-corrected
  `classic_dyadic-n-uni-v5.tex`, 139,941 bytes.
- Authoritative-source SHA-256:
  `C334676733163C7A521824E1F00C782A7BF0FD1ABE5366BF76D838238EDCA049`.
- Repository source commit:
  `c1ee018dd9eb6c788165a51fe08bdfe8f9ff7b2e`.
- Source branch: `release/heclassic-v0.5.0-rc.1-prep`.
- Source tree state at packaging: `clean`.

The author-held TeX source is identified by its hash but is not copied into
the repository or Review Kit.

## Archive and structural verification

- Archive:
  `BongTheory-He2022Classic-v0.5.0-rc.1-review-kit.zip`.
- Archive size: 6,204,941 bytes.
- SHA-256:
  `270EDD600F51B2F28821F8BD52C135D0D8C9EFB3831A05224C79A6D556410485`.
- Local Lean source count recorded by the manifest: 1,955.
- Checksummed payload files: 2,010; packaged files including
  `FILES.sha256`: 2,011.
- Exact payload-hash coverage: `PASS`.
- Single `papers/he2022classic` directory and single
  `docs/audit/He2022Classic` directory: `PASS`.
- Paper-specific root review documents and theorem-index isolation: `PASS`.
- Forbidden manuscript or compiled content in the source archive: none.

In particular, no `.tex`, `.pdf`, `.git`, `.lake`, `.olean`, or `.ilean`
artifact is present in the source archive.

## Kernel and audit verification

The archive was expanded into a new directory and verified with Lean 4.32.1
and four Lean workers. The first full build process was externally interrupted
after 5,438 of 5,679 then-known tasks. Verification resumed in the same fresh
extraction, retaining only Lean-generated build cache, and completed
successfully. The resumed `lake build` reports:

```text
Build completed successfully (5671 jobs).
```

All seven manifest-selected checks then completed with exit code zero:

1. `BongTest.He2022ClassicAudit`;
2. `BongTest.He2022ClassicDiscriminantRamificationAudit`;
3. `BongTest.He2022ClassicEvenExtensionAudit`;
4. `BongTest.He2022ClassicLocalUniversalityAudit`;
5. `BongTest.He2022ClassicProposition82Audit`;
6. `BongTest.He2022ClassicStrongApproximationAudit`; and
7. the generated enforcing gate `BongTest.PaperAxiomGate`.

The enforcing gate reports:

```text
AXIOM_GATE_PASS: 62746 declarations checked
```

It admits only `propext`, `Classical.choice`, and `Quot.sound`. The complete
build and all seven direct audit logs contain no Lean error line. Nonfatal
linter warnings about unused arguments, tactic suggestions, and the generated
gate's unlimited-heartbeat setting do not change kernel acceptance or the
semantic status.

## Dependency closure

Every checked-out dependency commit equals the revision pinned by the
packaged `lake-manifest.json`, and each dependency worktree was clean:

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

## Semantic and deployment boundary

This receipt establishes archive integrity, exact dependency recovery, Lean
kernel acceptance, and the declared transitive-axiom boundary for commit
`c1ee018`. It does not make the v5 manuscript true or complete the remaining
global arithmetic interfaces.

The kernel-checked `e = 2`, `n = 3` counterexample in Report 26 still refutes
the unrestricted odd clause of v5 Corollary 6.3. Lemma 8.3 and Theorems
1.7--1.8 therefore remain exported only in their proof-supported even scope,
and the concrete number-field lattice, localization, scalar-extension, local
sum-of-squares, and strong-approximation instances remain open. The project
grade remains D and the completion verdict remains `NOT_COMPLETE`.

In accordance with the paper manifest and the user's deployment boundary,
the Classic branch, archive, and formalization remain local. Nothing in this
receipt authorizes or claims a GitHub upload or release.
