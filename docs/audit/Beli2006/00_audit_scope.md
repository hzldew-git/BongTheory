# Audit scope: Beli 2006

- Paper: Constantin N. Beli, “Representations of integral quadratic forms over dyadic local fields.”
- Version: 13-page publisher PDF, SHA-256 `DB1B681B186F1688FB1C2CF4B03CAB7E78896144D680471F67D6893C82DF2371`.
- Formal baseline: commit `10e8c666bfda81dcac44332cd38f481d8d02e31a`, branch `main`.
- Proof assistant: Lean 4.32.1; dependencies pinned by `lake-manifest.json`.
- Audit date: 29 August 2026.

The paper is an announcement: Theorems 3.2 and 4.5 state the new
classification and representation criteria, while the later Beli 2009/2010
and 2019 v2 papers supply complete proofs. This audit therefore checks both the
2006 statement correspondence and the provenance of the downstream proofs.
Bibliographic and priority claims are excluded.
