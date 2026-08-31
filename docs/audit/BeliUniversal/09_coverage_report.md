# Coverage report

| Region | Checked proof coverage | Qualification |
| --- | --- | --- |
| Definitions and preliminary reductions | Complete | Exact integrality, universality, scalar representation, and unary reduction |
| Alpha/order/endpoint arithmetic | Complete | Some paper packaging is distributed across reusable declarations |
| Unary case analysis | Complete | Both Case I and Case II, including II(a') conversion |
| Theorem 2.1 | Complete | `PROVISIONAL_MATCH` pending independent review |
| Jordan definitions | Complete | Literal and direct predicates both recorded |
| Theorem 3.1 derivation | Complete for the direct substitution | Literal predicate proved under `r_1=0`; frozen source has a documented coefficient discrepancy |
| Lemmas 4.1--4.4 | Complete | Maximal-lattice and splitting infrastructure is proved transitively |
| Corollary 4.5 | Complete | All four clauses |
| Lemmas 4.6--4.9 | Complete | Full good-BONG and residual invariant packages |
| Corollary 4.10 | Complete | Includes the minimal-tail boundary |

Safe claim:

> The complete mathematical scope of Beli's universal-forms paper is
> formalized over the project's audited dyadic context, with standard kernel
> axioms only; Theorem 3.1(3.2.1--2) is represented both literally and in the
> form obtained by direct derivation, and their source discrepancy is explicit.

Unsafe claims:

- that the paper's printed `r_1` exponent is unconditionally equivalent to
  the derived `2r_1` exponent;
- that independent reviewers have certified every source-to-Lean mapping;
- that an uncommitted working-tree overlay is an archival reproducibility
  release.
