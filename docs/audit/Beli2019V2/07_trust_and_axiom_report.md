# Trust and Axiom Report

> Historical snapshot notice (28 August 2026): the remaining-boundary table
> below is obsolete.  The current trust and opacity audit is in
> `15_unconditional_completion_audit.md`.

## Kernel-level result

The focused audit module reports these dependencies for
`beli2019_sufficiency_complete`, `beli2019Theorem21`, and
`beli2019Theorem21_prime`:

- `propext`;
- `Classical.choice`;
- `Quot.sound`.

These are standard Lean/mathlib logical foundations. No project-defined axiom
appears in the reported axiom set.

## Placeholder scan

A source scan of `Bong` and `BongTest` found no declaration or proof using:

- `sorry`;
- `admit`;
- `sorryAx`;
- a project `axiom` declaration;
- a project `opaque` declaration used to hide a proof.

The only lexical `opaque` hit was English prose in a comment.

## Why the axiom report is not sufficient

Lean's `#print axioms` does not list theorem parameters as axioms. The public
main theorem has many typeclass parameters whose fields are mathematical
propositions or proof-producing constructions. A theorem can therefore have
only standard kernel axioms while still being conditional on strong,
uninstantiated mathematical interfaces.

## Remaining trust boundary

| Boundary | What it supplies | Default instance for arbitrary dyadic field |
|---|---|---|
| Defect/Hilbert field laws | spectra, partners, products, discriminant classes | Not established |
| BONG structural/existence laws | bases, good BONGs, structural identities | Not established as one closed dyadic-field instance chain |
| Earlier Beli law classes | alpha, Jordan, classification, prefix change | Partly decomposed; final theorem still accepts them as parameters |
| `Beli2019SectionFiveLaws` | complete data for one index-\(\mathfrak p\) step | None found |
| Legacy Section 4 inputs | earlier transitivity and Corollary 4.4 data used by the concrete 2019 construction | Not established as one closed dyadic-field instance chain |
| Scaling laws | binary/quaternary ambient basis changes | None found |
| `Beli2019UnaryBinaryJordanLaws` | local order and weight calculations | None found |

## Trusted computing base

The checked artifact relies on:

- Lean 4.32.1 kernel, commit
  `f054605aea4b840552cca2e725580bffd1e1b704`;
- mathlib revision
  `520045ab14e26149ee970e2e617ca04b09bde5d6`;
- generated `.olean` files matching the current working source;
- the correctness of the local executable and operating system.

## Audit grade

Grade C.

Rationale: the formal development is extensive, has no admitted proofs, and
the final rank-volume descent, 2019 Section 4 package, and deep-completion
construction are concrete. Nevertheless, core local mathematical interfaces
remain assumptions of the main theorem, including Section 5, lower-level
legacy Section 4 inputs, scaling, Jordan computations, and field-level local
arithmetic. Compilation validates the conditional theorem, not the
unconditional paper theorem.
