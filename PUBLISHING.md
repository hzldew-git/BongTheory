# Publication checklist

This is the first repository in the publication order. Publish its reviewed commit and immutable tag before changing either downstream repository.

The required order is `BongTheory`, then `BeliPapers`, then `HePapers`. For `BongTheory`:

1. start from a clean committed tree and record the commit hash;
2. use only exact upstream commit revisions and the checked-in Lean toolchain;
3. clone into an empty directory, fetch the Mathlib cache, and run `lake build`;
4. run the repository enforcing axiom gate and every paper audit named in `papers/*/paper.json`;
5. keep source comparison, semantic-fidelity status, conditional inputs, and incomplete scope visible;
6. run the manuscript/privacy scan before push; do not publish paper TeX, PDFs, local snapshots, build products, or opaque archives;
7. tag only the exact commit validated from the fresh clone, and attach any Review Kit with its SHA-256 and exact source commit.

Each downstream repository must pin the exact reviewed Git commit of its
upstream dependency and pass a fresh-clone build before tagging. `BongTheory`
itself has no dependency on either paper repository.
