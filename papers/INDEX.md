# Paper-specific Lean 4 review kits

Each row provides a canonical paper entry point, a kernel/axiom audit, and a
standalone source-only Review Kit. The kits contain the paper's complete local
import closure and pinned Lake metadata, but no `.lake`, `.olean`, publisher
PDF, unrelated milestone test, or Git history.

| Paper | Formalization entry | Audit | Fidelity materials | v0.3.0-rc.1 kit |
|---|---|---|---|---|
| Beli 2003 | [`Bong.Papers.Beli2003`](../Bong/Papers/Beli2003.lean) | [`BongTest.Beli2003Audit`](../BongTest/Beli2003Audit.lean) | [`Beli2003`](../docs/audit/Beli2003) | [`Beli2003 review kit`](https://github.com/hzldew-git/BongTheory/releases/download/v0.3.0-rc.1/BongTheory-Beli2003-v0.3.0-rc.1-review-kit.zip) |
| Beli 2006 | [`Bong.Papers.Beli2006`](../Bong/Papers/Beli2006.lean) | [`BongTest.Beli2006Audit`](../BongTest/Beli2006Audit.lean) | [`Beli2006`](../docs/audit/Beli2006) | [`Beli2006 review kit`](https://github.com/hzldew-git/BongTheory/releases/download/v0.3.0-rc.1/BongTheory-Beli2006-v0.3.0-rc.1-review-kit.zip) |
| Beli 2009/2010 | [`Bong.Papers.Beli2009`](../Bong/Papers/Beli2009.lean) | [`BongTest.Beli2009Audit`](../BongTest/Beli2009Audit.lean) | [`Beli2009`](../docs/audit/Beli2009) | [`Beli2009 review kit`](https://github.com/hzldew-git/BongTheory/releases/download/v0.3.0-rc.1/BongTheory-Beli2009-v0.3.0-rc.1-review-kit.zip) |
| Beli 2019 v2 | [`Bong.Papers.Beli2019`](../Bong/Papers/Beli2019.lean) | [`BongTest.Beli2019Audit`](../BongTest/Beli2019Audit.lean) | [`Beli2019V2`](../docs/audit/Beli2019V2) | [`Beli2019 review kit`](https://github.com/hzldew-git/BongTheory/releases/download/v0.3.0-rc.1/BongTheory-Beli2019-v0.3.0-rc.1-review-kit.zip) |
| Beli 2020 | [`Bong.Papers.Beli2020`](../Bong/Papers/Beli2020.lean) | [`BongTest.Beli2020Audit`](../BongTest/Beli2020Audit.lean) | [`Beli2020`](../docs/audit/Beli2020) | [`Beli2020 review kit`](https://github.com/hzldew-git/BongTheory/releases/download/v0.3.0-rc.1/BongTheory-Beli2020-v0.3.0-rc.1-review-kit.zip) |

The Beli 2020 row denotes the paper first submitted in 2020. Its frozen source
is arXiv:2008.10113v2, revised in 2022. The paper year and revision year are
recorded separately throughout the repository.

## Verification inside any kit

```text
lake exe cache get
lake build
lake env lean <audit-path-from-paper-manifest.json>
```

The Mathlib cache is an optimization. A fresh extraction may instead run
`lake --no-cache build` to compile the pinned dependency closure locally.
