# Coverage report

Coverage status: `SECTION_2_COMPLETE_SECTION_3_IN_PROGRESS`.

- Publisher inventory: 47/47 directly numbered items identified.
- Direct checked publisher-result endpoints: 17/47, comprising every numbered
  item in Section 2 (Definition 2.4, Lemma 2.2, Corollary 2.3,
  Propositions 2.5--2.7, Theorem 2.8, and Lemmas 2.9--2.11).
- Section 3 coverage additionally includes Definitions 3.1 and 3.4 and
  Propositions 3.2--3.5. Definition 3.1 uses a canonical equivalent
  representative and is explicitly marked for human semantic review.
  Proposition 3.5 includes all Table 1 branches, full space exhaustion, and
  the unique excluding-space statement with its binary exceptional case.
  Lemmas 3.13--3.14 additionally cover the two higher-rank exactly-one
  representation alternatives and all first-column comparisons used later.
- Statement encoding: the complete right-hand side of Theorem 1.1 is encoded,
  but its equivalence with `IsNUniversal` is not yet proved.
- Supporting proof: the abstract maximal-lattice testing reduction underlying
  Theorem 1.2 is proved, but the explicit family and minimality assertion are
  not yet formalized and therefore do not count as Theorem 1.2 coverage.

The strict direct proof ratio is therefore **17/47**. This is a bookkeeping
statement, not a judgment about how
much reusable Beli infrastructure is already available.  Coverage increases
only when a source-numbered endpoint has a checked proof and a completed
correspondence entry.
