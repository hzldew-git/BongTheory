# Formalization certificate draft

This is a partial-scope draft, not a certificate for the whole paper.

Source: the publisher version of Zilong He, *On n-ADC integral quadratic
lattices over algebraic number fields*, Doc. Math. 30 (2025), 981--1022,
DOI 10.4171/DM/1003. The exact SHA-256 is recorded in `00_audit_scope.md`
and the paper manifest. The arXiv version is comparison-only.

Checked code checkpoint: `976883e6cda7c17402c4c1f0bc768db555460eae`.
Toolchain: Lean 4.32.1; dependency revisions are in `lake-manifest.json`.
The listed concrete dyadic endpoints pass incremental kernel checks. The
new maximal-profile criteria, thirteen published-family endpoints and volume criterion depend only on `propext`,
`Classical.choice`, and `Quot.sound`.

The audited declaration groups and scope limitations are in
`05_theorem_correspondence.md`. Semantic matches remain provisional. In
particular, explicit arithmetic premises in the global reductions are not
proved by their axiom reports. No statement here certifies the unformalized
classifications, enumeration, or omitted boundary cases.

Independent author approval: pending. Independent domain-expert approval:
pending. Independent formalization-expert approval: pending. Reproducibility:
incremental checks passed; the new revision still requires clean-kit CI
validation. Overall coverage grade: C. Whole-paper completion: not achieved.
