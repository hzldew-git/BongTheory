# Changelog

## 0.2.0-rc.1 — 2026-09-01

- Add the complete Lean formalization of Beli's *Universal integral quadratic
  forms over dyadic local fields*.
- Publish project-law-free endpoints for Theorems 2.1 and 3.1, Lemmas
  4.1--4.9, Corollary 4.5(i)--(iv), and Corollary 4.10.
- Record rather than silently repair the Theorem 3.1 exponent discrepancy:
  direct substitution gives coefficient `2r_1`, while the frozen paper prints
  `r_1`.
- Add the paper-specific kernel, axiom, fidelity, and reproducibility audits.
- Retain semantic status `PROVISIONAL_MATCH`, Grade B, pending independent
  mathematical and Lean-expert sign-off.

## 0.1.0-rc.1 — 2026-08-29

- Freeze the Lean 4.32.1 and mathlib dependency inputs.
- Publish project-law-free public endpoints for the selected Beli 2003, 2006,
  2009/2010, and 2019 v2 results.
- Add 604 test and audit modules, including elaborated-signature and transitive
  axiom reports.
- Add source hashes, theorem maps, independent-review packets, reproducibility
  instructions, and pinned CI workflows.
- Retain semantic status `PROVISIONAL_MATCH`, Grade B, pending independent
  mathematical and Lean-expert sign-off.
