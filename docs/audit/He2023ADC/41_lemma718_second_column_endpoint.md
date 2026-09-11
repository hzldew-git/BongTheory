# Lemma 7.18 second-column endpoint exclusion

Status: `FULLY_FORMALIZED` / `PROVISIONAL_MATCH`.

Code checkpoint: `7b21fe0e07e97ba082dd9e78a79e3ec8091630af`.

## Source authority

The sole semantic authority is the publisher version of record:

- Zilong He, *On n-ADC integral quadratic lattices over algebraic number
  fields*, *Documenta Mathematica* 30 (2025), no. 4, 981--1022;
- DOI: <https://doi.org/10.4171/DM/1003>;
- publisher PDF SHA-256:
  `E26190C88B16624DCCB7F269C6C3FFDA02BC6830677A5BC0C8E0AD48A36E72D6`.

Lemma 7.18 and its proof occur on p. 1015. The post-publication arXiv
revision remains comparison-only.

## Formal statement

For odd `n=2k+3`, `heADC2025Lemma718` assumes a rank-`n+2` good BONG on an
`n`-ADC lattice whose ambient space is `W_2^(n+2)(epsilon)`, with
`epsilon` a valuation unit. It proves

```text
R_(n+1) != -2e.
```

The Lean index `2k+3` is zero-based and denotes the paper's one-based
`R_(n+1)`. The wrapper `heADC2025Lemma718_not_definition716` proves the
equivalent assertion that `M_(2,e)^(n+2)(epsilon)` is not defined.

## Proof route

Assuming the forbidden endpoint, the already proved maximal branch of Lemma
7.15 makes the source lattice `O`-maximal. Maximal-lattice uniqueness then
identifies it integrally with the chosen maximal lattice in the same
published second-column ambient space. The actual Lemma 4.12(ii) order
profile of that named lattice gives the incompatible penultimate order.

This is a different but equivalent formal route to the paper's use of Lemma
7.14(i) and Proposition 3.5(v). It concludes on actual integral lattices and
does not assume the desired column distinction or a profile law for the
source lattice.

## Statement-strength conclusion

The public theorem retains the source's `n`-ADC, unit-parameter, and ambient
second-column hypotheses and proves its exact endpoint exclusion. The
undefinedness formulation is derived from the formal Definition 7.16.
The result is therefore `LOGICALLY_EQUIVALENT` to Lemma 7.18.

## Mechanical trust checks

The module, canonical paper entry, and focused audit compile directly with
Lean 4.32.1. The transitive report for the public endpoint contains exactly
`propext`, `Classical.choice`, and `Quot.sound`. The focused enforcing gate
reports `AXIOM_GATE_PASS: 59555 declarations checked`; the source scanner
checks 2,735 tracked Lean files, and the scoped line-width and diff checks
pass.

These are local checks at the stated code commit. Exact-revision Review Kit
CI, release promotion, and independent human sign-off remain separate gates.

Author decision: unsigned. Domain-expert decision: unsigned.
Formalization-expert decision: unsigned.
