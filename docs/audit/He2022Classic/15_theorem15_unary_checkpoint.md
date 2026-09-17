# Theorem 1.5 unary and all-ranks local checkpoint

Date: 2026-09-06. Code checkpoint:
`66b408163590da57edcd0325fc20266369fb70c2`. Lean: 4.32.1. The sole
semantic authority is the 37-page publisher version of record with SHA-256
`51F3626A15692E2FF0BAAE62F0EBCC4B8BEE02052C4D3CB1EA579B02E17480C1`.

## Published statement and proof boundary

Theorem 1.5 on journal p. 562 starts with a classic integral number-field
lattice of rank `m >= n + 3 >= 4`. At a dyadic prime, it assumes that the
localization is classic `n`-universal and that every unsigned adjacent defect
is greater than one, and concludes that the local ramification index is one.
It then draws an all-dyadic-primes conclusion: two is unramified in the number
field, equivalently the discriminant is odd.

The proof on journal p. 586 separates `n = 1`. Under the contrary assumption
`e > 1`, it shows that the initial alpha invariant is greater than one by
bounding its half-gap and defect candidates, contradicting the universal
criterion cited there as Beli [6, Theorem 2.1]. The proof then treats odd
`n >= 3` and even `n >= 2` through the classic universality classification.

## Formal endpoints

- `he2022ClassicTheorem15_unary` proves the local implication at `n = 1`.
- `he2022ClassicTheorem15` is the existing local branch for `n >= 2`.
- `he2022ClassicTheorem15_allRanks` dispatches between them and covers every
  positive `n` satisfying the published local rank inequality.

The unary proof does not assume the cited criterion as a paper-specific axiom.
It proves that every integral unary target is classic integral, converts
classic 1-universality to scalar universality, and invokes the already proved
Beli universal theorem. It then proves every member of the actual finite set
`alphaCandidates 0` is strictly greater than one. This yields
`alphaValue 0 > 1`, contrary to either branch of Beli's necessary conditions.

The formal rank is `tail + 2`, the adjacent indices are `Fin (tail + 1)`, and
the source condition is retained as `n + 3 <= tail + 2`. Paper indices are
one-based; formal indices are zero-based. The unsigned-to-signed defect bridge
uses `d(-1) >= e > 1` and the domination law, matching the source proof.

## Scope assessment

The local-field mathematical implication is `FULLY_FORMALIZED` over the
published range `n >= 1`, with correspondence status `PROVISIONAL_MATCH`.
The complete printed theorem remains `PARTIAL_FORMALIZATION` because the
repository does not yet encode the number-field lattice, localization at all
dyadic primes, or the equivalence between unramifiedness of two and odd global
discriminant. No global claim is inferred from the local endpoint name.

## Mechanical evidence

At the fixed checkpoint:

- `Bong/Bong/He2022ClassicTheorem15.lean` compiles;
- `Bong/Papers/He2022Classic.lean` compiles;
- `BongTest/He2022ClassicAudit.lean` compiles and prints the unary and
  all-ranks endpoints;
- both new public endpoints depend only on `propext`, `Classical.choice`, and
  `Quot.sound`;
- the focused transitive axiom gate passes on 61,546 declarations;
- the repository proof-token scanner checks 2,742 tracked Lean sources with no
  forbidden unfinished-proof token, and all 24 CI helper tests pass.

These cached local checks do not substitute for an exact-commit clean Review
Kit run, GitHub CI, permanent release, or independent human semantic approval.
