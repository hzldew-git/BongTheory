# Independent review protocol

The review is intentionally divided between roles. A reviewer may fill more
than one role only if that overlap is disclosed.

## Mathematical reviewer

Read the frozen paper independently, then use the paper inventory and author
review cards. Confirm the mathematical objects, normalization of valuation
and quadratic defect, source/target orientation, quantifier order, strict
inequalities, rank conventions, exceptional cases, and one-based to zero-based
index translation. Record disagreements rather than silently repairing them.
For Beli 2020, explicitly decide whether the `r_1` coefficient printed in
Theorem 3.1(3.2.1--2) agrees with the `2r_1` coefficient obtained by direct
substitution into Theorem 2.1, or should be recorded as a source correction.

## Formalization reviewer

Build a clean clone, inspect the actual declaration signatures rather than
their names or comments, expand `DyadicContext` and the representation
definitions, run the axiom audits, and check the import graph for circularity
or an imported equivalent of a target theorem.

## Required evidence

Each signed review must identify:

- paper version and SHA-256;
- repository full commit and tag, if any;
- reviewer name, affiliation or public profile, role, and date;
- exact files or theorem cards reviewed;
- build platform and command results for a reproducibility review;
- one decision for every core review card;
- all reservations, exclusions, and conflicts of interest.

Signatures belong in `docs/audit/IndependentReviewSignoff.md` or in an
immutable linked issue/review. A name added by the project author or an AI
agent is not independent sign-off.

The project may be promoted from Grade B to Grade A only after every core
result is `VERIFIED_MATCH`, the clean-clone build is independently repeated,
and no unresolved core semantic issue remains.
