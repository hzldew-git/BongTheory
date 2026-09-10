# Odd testing theorem: terminal-reduction checkpoint

Historical checkpoint: the “remaining mathematical obligation” below was
closed after the author supplied corrected v5. Report 22 records the
unconditional theorem. This file preserves the earlier factored reduction.

At this historical checkpoint the publisher version was the working source.
It and the post-publication arXiv v3 copy are now comparison-only; the current
authority is the author-corrected v5 identified in Report 22.

## Kernel-checked reduction

The following new declarations avoid the false literal Lemma 7.1(ii).

- `he2022ClassicLemma45_j2_of_terminalUpper` proves the full lower-even
  `J2_E` condition from its terminal upper inequality, lower `J1'_E`, source
  classic integrality, and lower-even ambient universality.  Its proof also
  includes the binary-rank clause.
- `he2022ClassicLemma45_j2_of_j2Prime_of_ramification_gt_one` specializes
  this result: when `e > 1`, `J2'_E` supplies the required upper inequality.
- `all_publishedOdd_implies_classicUniversal_of_lowerTerminalUpper` proves
  odd-rank classic universality from the complete literal odd table and that
  single lower-even terminal inequality, for every dyadic ramification index.
- `all_publishedOdd_implies_classicUniversal_of_lowerJ2Prime` weakens the
  additional premise to lower `J2'_E` in the branch `e > 1`.

The proof chain is:

1. the literal odd table gives odd ambient universality and hence the source
   rank bound;
2. its `C1(omega)` row gives lower `J1'_E`;
3. the terminal inequality gives lower `J2_E` by the new Lemma 4.5 reduction;
4. the already checked literal rows supply the source-dependent tests in
   Lemmas 5.4, 5.7, and 5.8;
5. Theorem 5.1 yields the odd classic-universality conclusion.

Both edited modules were checked directly with Lean 4.32.1.  No `sorry`, new
axiom, `opaque`, `unsafe`, or native-evaluation escape was introduced.

## Remaining mathematical obligation

This checkpoint does not derive the terminal inequality, or `J2'_E`, from
the literal odd table alone.  That implication is now the exact remaining
local obligation for unconditional odd testing sufficiency.  The refuted
Lemma 7.1(ii) is neither assumed nor hidden behind a renamed interface.

This obligation is no longer current: v5 Lemma 7.1 yields
`all_publishedOdd_implies_all_publishedEven_v5`, and Theorem 1.3(ii) plus odd
literal minimality are now proved. The overall project grade remains C for
unrelated global and human-review gaps.
