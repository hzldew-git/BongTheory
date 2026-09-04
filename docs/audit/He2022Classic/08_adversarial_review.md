# Adversarial review

Primary risks are confusing norm integrality with scale integrality, reversing
the over-lattice inclusion in maximality, omitting source integrality from
universality, and calling an abstract test family minimal. The BONG criteria
must separately check parity, the theorem's exclusion of ranks `m=n+1` and
`m=n+2`, and residue characteristic two. In the statement transcription,
paper adjacent index `j` is Lean index `j-1`; the lower bound `j >= n+2` in the
odd upper branch is therefore Lean bound `n+1 <= j.val`.

The current code supplies both directions of Theorem 1.1 and explicitly
eliminates low source ranks. This is no longer a statement-only project.
Conversely, the n >= 2 hypothesis in the local Theorem 1.5 endpoint excludes
the unary boundary allowed by the paper and must be reported.

The literal Lemma 7.1(ii) disjunction fails when e > 1. The repository exports
its checked refutation and does not promote the qualified odd testing result
to unconditional sufficiency. This is an unresolved source obstruction, not
an admitted proof. See `SOURCE_DELTA.md` for the exact witnesses and scope.

Constructed testing rows, their integrality, cardinalities of an index type,
testing sufficiency, and proper-subset minimality are distinct claims. The
even Lemma 7.4 proof must not be used as a certificate for all of Theorem 1.3.
