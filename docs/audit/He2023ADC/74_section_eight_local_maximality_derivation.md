# Section 8 local maximality derivation

Status: `CONDITIONAL_FORMALIZATION` / `SOURCE_LOGIC_MATCH`.

Code checkpoint:
`c204de5e938b6dbfc01b9c7483b8ab8ede0a13ba` on
`feat/he2023adc-local-maximality`.

## Source authority and locators

The semantic authority is Zilong He, *On n-ADC integral quadratic lattices
over algebraic number fields*, *Documenta Mathematica* 30 (2025), no. 4,
981--1022, DOI 10.4171/DM/1003. The audited publisher PDF has SHA-256
`E26190C88B16624DCCB7F269C6C3FFDA02BC6830677A5BC0C8E0AD48A36E72D6`.

Theorem 1.5 is stated on publisher page 984. Its proof on page 1016 derives
part (i) by combining Proposition 4.15 with Theorems 5.1, 6.1, and 7.1, and
derives part (ii) from part (i) and O'Meara section 82K. Lemma 8.1(ii), on
page 1017, uses section 82K and Lemma 4.14 to pass from global maximality to
local `n`-ADC-ness.

## Formal change

The earlier `SectionEightLaws` interface directly stored both

```text
localMaximal(localize p M) -> IsNADCAt M p n
```

and the complete local Theorem 1.5 equivalence. Those final-conclusion fields
have been removed.

The new `LocalMaximalityLaws` interface records the lower ingredients of the
standard maximal-lattice argument:

1. a locally maximal lattice is integral;
2. every integral local target has a maximal extension with the same ambient
   representation behaviour;
3. a maximal source represents a maximal target whenever the ambient source
   represents the ambient target;
4. integral representation is transitive;
5. the classification-dependent necessity direction in the two ranks of
   Theorem 1.5(i).

`LocalMaximalityLaws.localMaximal_isNADCAt` now proves Lemma 4.14's local
maximal-implies-ADC implication by extending an arbitrary integral target,
representing the maximal extension, and composing representations.
`LocalMaximalityLaws.local_theorem15` combines that theorem with the remaining
necessity input. The compatibility endpoints under `SectionEightLaws` are
derived, and Lemma 8.1(ii), Theorem 1.5(i), and Theorem 1.5(ii) consume them.

Thus no `SectionEightLaws` field now states either local maximal-implies-ADC
or the complete local Theorem 1.5 equivalence.

## Mechanical evidence

With Lean 4.32.1, the following focused build succeeds:

```text
lake build Bong.Lattice.He2023ADCSectionEight \
  BongTest.He2023ADCLocalMaximalityAudit
```

It completes four jobs. The focused audit then runs directly. Its seven
explicit axiom reports show no axioms for the two lower derived theorems, the
two compatibility endpoints, Lemma 8.1(ii), or Theorem 1.5(i); Theorem
1.5(ii) uses only `propext`.

An incremental whole-paper compatibility build completes all 5,562 planned
jobs for `Bong.Papers.He2023ADC` and `BongTest.He2023ADCAudit`. The canonical
audit exits successfully. The focused transitive gate reports
`AXIOM_GATE_PASS: 61070 declarations checked`. The comment-aware scanner
checks 2,733 tracked Lean sources, the 23 scanner tests, five deployment tests,
and two shard-planner tests pass, and `git diff --check` is clean.

The incremental build reused locally copied project artifacts from the clean
release-preparation worktree. It is compatibility evidence, not a fresh
extraction or independent Review Kit receipt.

## Fidelity boundary

The classification-dependent necessity field still represents the concrete
combination of Proposition 4.15 and Theorems 5.1, 6.1, and 7.1 at every
finite completion. The maximal-extension and maximal-representation laws also
still require construction in an actual local-lattice instance. Moreover,
the global-local maximality equivalence from O'Meara section 82K remains an
explicit `SectionEightLaws` input.

Consequently this checkpoint lowers two final-conclusion boundaries but does
not instantiate the number-field system, resolve the published statement
mismatches elsewhere in the paper, change the whole-paper Grade-D verdict,
provide human semantic approval, or constitute an exact clean Review Kit.
