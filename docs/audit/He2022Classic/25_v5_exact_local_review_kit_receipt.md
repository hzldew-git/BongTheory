# Author-corrected v5 exact local Review Kit receipt

This receipt records a local clean-extraction reproducibility check. It is not
GitHub CI, an exact-tag release receipt, or independent human semantic
approval.

## Frozen inputs

- Authoritative source: `classic_dyadic-n-uni-v5.tex`.
- Authoritative source SHA-256:
  `C334676733163C7A521824E1F00C782A7BF0FD1ABE5366BF76D838238EDCA049`.
- Repository source commit:
  `b8c379ad5bebb3f25e57be8c30fd9f01bd7dc78b`.
- Source tree state recorded by the verifier: `clean`.

The author-held TeX source was not copied into the Review Kit or repository
history.

## Archive and extraction

- Archive:
  `BongTheory-He2022Classic-v5-local-b8c379a-review-kit.zip`.
- Archive size: `6,152,725` bytes.
- SHA-256:
  `57D6FF66332CDEE48F8D9A19A0FE5E3A5815E3003D91C5455C68D6BD5BB56FFB`.
- Payload files verified after extraction: `1,993`.
- Structural verification: `PASS`.

## Kernel and trust checks

The archive was extracted into a new directory and built there with four Lean
workers. The complete build finished successfully with `5,028` jobs. The
paper audit `BongTest.He2022ClassicAudit` passed. The generated enforcing gate
`BongTest.PaperAxiomGate` also passed and checked `62,622` declarations against
the allowed foundational set `propext`, `Classical.choice`, and `Quot.sound`.

Final verifier result: `CLASSIC_FRESH_KIT_EXIT=0`.

## Scope boundary

This result establishes source-package integrity, kernel acceptance, and the
declared transitive-axiom boundary for the exact commit above. That commit
predates the kernel-checked counterexample to the author-corrected v5 odd
Corollary 6.3. It does not instantiate the remaining number-field arithmetic
packages or supply an independent semantic sign-off. Reports 24 and 26 and
the current manifest supersede its old gap-only assessment; the current
whole-paper grade is D.

Because this receipt predates integration into a release branch, the final
GitHub Review Kit must be regenerated and checked again at its exact release
commit.
