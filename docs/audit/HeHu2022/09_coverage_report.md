# Coverage report

Coverage status: `SECTIONS_2_3_CORE_AND_THEOREM_4_1_COMPLETE`.

- Publisher inventory: 47/47 directly numbered items identified.
- Accounted publisher-result endpoints: 27/47, comprising every numbered
  item in Section 2 (Definition 2.4, Lemma 2.2, Corollary 2.3,
  Propositions 2.5--2.7, Theorem 2.8, and Lemmas 2.9--2.11).
- Section 3 coverage additionally includes Definitions 3.1, 3.4, and 3.6 and
  Propositions 3.2--3.5. Definition 3.1 uses a canonical equivalent
  representative and is explicitly marked for human semantic review.
  Proposition 3.5 includes all Table 1 branches, full space exhaustion, and
  the unique excluding-space statement with its binary exceptional case.
  Definition 3.6 supplies intrinsic canonical maximal representatives on
  every defined Table 1 space. Proposition 3.7 now proves all ten Table 2
  maximality rows, including the three critical endpoint exclusions.
  Lemma 3.9 supplies all three literal endpoint models, including the
  canonical `kappa#` construction and the exact ternary coefficient list.
  Lemma 3.10 supplies the exact recursive coefficient list for every
  prepended half-hyperbolic block and proves that the original tail is
  unchanged.
  Lemma 3.11 computes every published even- and odd-rank `R_i` profile from
  exact Table 2 good-BONG tails; no row is represented merely by an assumed
  order vector.
  Lemmas 3.13--3.14 additionally cover the two higher-rank exactly-one
  representation alternatives and all first-column comparisons used later.
- Statement encoding: the complete right-hand side of Theorem 1.1 is encoded,
  but its equivalence with `IsNUniversal` is not yet proved.
- Supporting proof: the abstract maximal-lattice testing reduction underlying
  Theorem 1.2 is proved, but the explicit family and minimality assertion are
  not yet formalized and therefore do not count as Theorem 1.2 coverage.
- Section 4 now includes the complete checked Lemma 4.2 equivalence.  Its
  necessity direction uses the literal `N_1^n(1)` and `N_1^n(Delta)`
  models and a proved nonsquare determinant-prefix product; its sufficiency
  direction uses a deep same-rank integral completion.  Lemma 4.3 is also
  complete: the literal `N_2^n(Delta)` target satisfies both strict defect
  conclusions and is proved not represented by the relevant source prefix
  through the exact Table 1 normal forms. Lemma 4.4 now proves the universal
  central-condition equivalence with `I2^E`: necessity uses that literal
  target, and sufficiency treats all integral even-rank targets, including
  both terminal-order branches. Infrastructure also
  includes exact `I1^E`--`I3^E` definitions, a
  proved Theorem 2.8 universality factorization, the checked logical assembly
  of Theorem 4.1, and the complete invariant conversion used in Theorem 4.7.
  Lemma 4.5 now discharges the final long-representation component, including
  the exceptional binary defect branch.  These three component equivalences
  are instantiated in `heHu2022Theorem41Even`, so Theorem 4.1 is now counted.
  Corollary 4.6 and Theorem 4.7 still require direct theorem endpoints.

The accounted coverage ratio is therefore **27/47**: 26 direct checked
publisher items plus the Definition 3.1 equivalent-construction endpoint
that remains explicitly flagged for independent semantic review. This is a bookkeeping
statement, not a judgment about how
much reusable Beli infrastructure is already available.  Coverage increases
only when a source-numbered endpoint has a checked proof and a completed
correspondence entry.
