# Adversarial Review

> Historical snapshot notice (28 August 2026): the high-risk uninstantiated
> law boundary identified below has since been closed.  See the renewed
> adversarial review in `15_unconditional_completion_audit.md`.

## Review question 1: Is the representation direction reversed?

The API uses `target.Represents source`. Thus
`Lattice.Represents q r L M` is an embedding of the `r,M` lattice into the
`q,L` lattice. In the main theorem, `a` belongs to the larger rank `m+1`
target and `b` belongs to the smaller rank `n+1` source. This agrees with the
paper's statement that the smaller lattice is represented by the larger one.

Result: no reversal found.

## Review question 2: Is the rank inequality off by one?

The theorem quantifies over `hRank : n ≤ m` but the actual BONG lengths are
`n + 1` and `m + 1`. The inequality therefore translates to
`n+1 ≤ m+1` exactly. The cost is exclusion of rank zero.

Result: correct for positive ranks; rank-zero scope requires author decision.

## Review question 3: Does the v2 theorem silently replace more than one condition?

`RepresentationConditionsPrime` retains the original order, defect, and long
representation fields. Only the central representation field uses the new
defect trigger. `representationConditions_iff_prime` performs exactly that
replacement using `beli2019Lemma216`.

Result: no extra replacement found.

## Review question 4: Is the final theorem proved by assuming itself?

The public theorem does not accept `GoodBONGRepresentationLaws`. The former
`Beli2019FinalStepLaws` theorem-level oracle is absent. The equal-rank proof
constructs concrete counterexample nodes and applies a well-founded
rank-volume induction.

Result: no direct theorem-level circularity found.

## Review question 5: Can a remaining class encode the whole theorem indirectly?

`Beli2019SectionFiveLaws` still returns complete one-step data. The 2019
Section 4 package and the deep-extension package are now constructed, but
their lower inputs include substantial structural, classification, and legacy
Section 4 interfaces. These are narrower than the full representation
equivalence, but they still cover substantial chunks of the printed proof.

Result: no literal restatement of Theorem 2.1 was found, but the conditional
boundary remains mathematically substantial. High-risk review item.

## Review question 6: Are “no axioms” claims misleading?

Yes, if read as “unconditional theorem.” The axiom printer sees only kernel
constants used after all theorem parameters are introduced. It does not list
the law parameters as axioms. The project must state both facts:

1. no project axiom or admitted proof occurs;
2. strong explicit mathematical assumptions remain.

Result: documentation now states both.

## Review question 7: Are endpoint conditions dropped?

The paper's “ignore meaningless conditions” convention is replaced by typed
index domains and terminal constructors. Dedicated terminal lemmas occur in
the Lemma 2.16 and rank-completion developments. No obvious ordinary or
terminal branch is missing from the public packages.

Result: `MATCH_CANDIDATE`, not independently verified.

## Review question 8: Does a compiled helper theorem prove the wrong notion?

The review checked the definitions of ambient and lattice representation.
Both require injectivity and preservation of the bilinear form; the lattice
version additionally maps source-lattice members into the target lattice.
The final conclusion therefore expresses integral representation rather than
only a scalar or diagonal surrogate.

Result: intended conclusion found.

## Review question 9: Does the strict-rank completion lose the original source?

The construction now explicitly splits the represented image from its
nondegenerate orthogonal complement, chooses a good BONG on the complement,
rescales it deeply into the target lattice, and adjoins it to the source.
After equal-rank representation, `completed_represents_original` composes the
result back to the original smaller lattice.

Result: no loss of the original source found.

## Review question 10: Can the artifact be independently reproduced?

Not yet from a repository commit. The root branch is unborn and every project
file is untracked. The cached mathlib checkout also has Windows-side local
script/symlink changes. A source snapshot hash and exact dependency revisions
can identify this audit, but a clean clone has not been demonstrated.

Result: `PARTIALLY_REPRODUCIBLE`.

## Adversarial verdict

The main logical assembly survived the direction, rank, endpoint, circularity,
and conclusion-kind checks. The decisive unresolved objection is the large
uninstantiated law boundary. Final status remains
`FORMALIZATION_WEAKER`.
