# Contributing

Contributions should preserve the separation between proof completion,
semantic correspondence, and reproducibility.

1. Create a focused branch and state the paper result or infrastructure issue.
2. Add or update a theorem correspondence entry when public semantics change.
3. Run `lake build` and the focused `#print axioms` audit.
4. Do not introduce `sorry`, project axioms, native trusted computation, or an
   imported equivalent of a target theorem without explicit review and
   disclosure.
5. Keep source references versioned and include exact section/result locators.
6. Report changes to typeclass assumptions, endpoint conventions, coercions,
   representation orientation, or valuation normalization prominently.
7. For every new BONG-related paper, add a `papers/<paper-id>/paper.json`, a
   canonical `Bong.Papers.<PaperName>` entry, a paper audit module, and a
   dedicated fidelity package as required by `papers/SCHEMA.md`.
8. Build the generated paper Review Kit after clean extraction; do not treat a
   successful build of only the complete monorepo as sufficient packaging
   evidence.

Pure style cleanup should not be mixed with mathematical changes. New public
results require an English author review card and an update to
`THEOREM_INDEX.md`.
