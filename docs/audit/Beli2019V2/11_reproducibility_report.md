# Reproducibility Report

> Historical snapshot notice (28 August 2026): this report records the M660
> build.  The current build and snapshot identifiers are in
> `15_unconditional_completion_audit.md`; reproducibility remains partial.

## Result

Status: `PARTIALLY_REPRODUCIBLE`.

The complete default Lake target built successfully in the audited working
tree:

```text
Build completed successfully (4544 jobs).
```

The focused deep-extension and main-theorem targets also built successfully:

```text
Build completed successfully (3768 jobs).
```

## Toolchain

- Operating environment: Windows, PowerShell.
- Lean: 4.32.1, x86_64-w64-windows-gnu.
- Lean commit: `f054605aea4b840552cca2e725580bffd1e1b704`.
- Lake: 5.0.0-src+f054605.
- Toolchain file: `leanprover/lean4:v4.32.1`.
- Project default targets: `Bong` and `BongTest`.

The verification command was:

```powershell
lake build -Kjobs=2
lake build Bong.Bong.GoodBONGDeepIntegralExtensionProof Bong.Bong.Beli2019MainTheorem -Kjobs=4
```

An initial full run at four-way concurrency ended with a Windows process
exception while compiling `BongTest.M32`.  That module and `BongTest.M24`
both succeeded when rerun serially.  The rerun also exposed a stale smoke-test
qualification in `BongTest.M171`; it was updated from the former global data
namespace to `Beli2019Lemma513LocalData`.  The complete two-way-concurrency
build above then succeeded.

## Dependency lock

The checked `lake-manifest.json` pins:

| Package | Revision |
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

## Source snapshot identity

The root Git branch is unborn:

```text
## No commits yet on master
HEAD=UNBORN
```

Therefore no repository commit identifies the audited project. A deterministic
source snapshot hash was computed over 1,942 files: all Lean files under
`Bong` and `BongTest`, the two root import files, toolchain and Lake files,
README, the v2 formalization map, and GitHub workflows. Audit reports were
excluded to avoid a self-referential certificate hash.

- Total hashed bytes: 14,970,727.
- Aggregate SHA-256:
  `A7CDDE532BD6C0614414F9524740A7B4B46C9EC4C7352BB40AE93D67A7C31260`.

The aggregate is the SHA-256 of sorted UTF-8 rows
`relative/path|file-sha256`, each terminated by LF.

## Paper identity

- PDF SHA-256:
  `1669C626A6D01AF297E07C2CB9584C5BD34F4CEE0F2B188EE0B351BD091C387C`.
- TeX SHA-256:
  `00D58B232A331E559D175C2DF383DE82A49BC7B044E035092B7AC96015858292`.

## Reproducibility limitations

1. The project has no commit and all root files are untracked.
2. No clean clone can be tested from an unborn branch.
3. Lake reports local changes in the cached mathlib, aesop, and batteries
   repositories.
4. The mathlib differences are predominantly Windows script/symlink
   normalization: 42 script paths show metadata-only changes and two Python
   symlink targets appear deleted.
5. The aesop and batteries worktrees report broken/missing `HEAD` tree
   objects to direct Git diff inspection, even though the pinned revisions
   are present in the manifest and the Lean build succeeds.
6. The successful build is therefore evidence for this local source and
   cache, not yet for a clean external checkout.
7. GitHub CI workflow files exist, but no CI run is identified because no
   commit exists.

## Steps required for full reproducibility

1. create an initial repository commit containing the audited source;
2. restore clean dependency checkouts from `lake-manifest.json`;
3. run `lake clean` followed by `lake --old build` in a fresh clone;
4. archive the complete build log and successful CI run;
5. recompute and publish the snapshot/commit identifier.
