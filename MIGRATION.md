# Three-repository migration

This repository is the lowest layer of the split.

- Public baseline: `a81fa2edf7d79c7740ea58539b809ce93f1612c0`.
- Extraction tree: clean He Classic integration commit
  `1f3d92e7419db481c0e1ac229c5b7c0b1fdc5dd7`.
- Included Lean modules: every module whose transitive local imports contain
  neither a `Beli*` nor a `He*` paper module.
- Downstream direction: `BeliPapers -> BongTheory` and
  `HePapers -> BeliPapers -> BongTheory`.

`MIGRATION_MODULES.tsv` is the exact source-path inventory. Module names,
theorem statements, signatures, docstrings, namespaces, and proof bodies were
preserved during the mechanical extraction. The generated aggregate entry
files and package metadata are new.
