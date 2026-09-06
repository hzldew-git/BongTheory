# Lemma 7.19 named-product construction

Status: `FULLY_FORMALIZED` / `PROVISIONAL_MATCH`.

Code checkpoint: `7b21fe0e07e97ba082dd9e78a79e3ec8091630af`.

## Source authority

The sole semantic authority is the publisher version of record:

- Zilong He, *On n-ADC integral quadratic lattices over algebraic number
  fields*, *Documenta Mathematica* 30 (2025), no. 4, 981--1022;
- DOI: <https://doi.org/10.4171/DM/1003>;
- publisher PDF SHA-256:
  `E26190C88B16624DCCB7F269C6C3FFDA02BC6830677A5BC0C8E0AD48A36E72D6`.

Lemma 7.19 and its proof occur on p. 1015. The post-publication arXiv
revision remains comparison-only.

## Published hypotheses and endpoints

For odd `n=2k+3`, a valuation unit `delta` with `d(delta)<2e`, a normalized
parameter `c` with order zero or one, and each `nu` in `{1,2}`, the two
public endpoints

- `heADC2025Lemma719FirstNamedPublished`, and
- `heADC2025Lemma719SecondNamedPublished`

prove the complete conclusion on the literal named products
`N_nu^(n+1)(delta) orthogonal-sum <c>`: the product is `n`-ADC, admits the
constructed good BONG, and has
`R_(n+1)=1-d(delta)`.

`heADC2025Lemma719_unitDefectData` derives, rather than assumes, that the
finite defect is odd, nonnegative, and strictly below `2e`. It also proves
that `delta` lies in the sharp domain needed to define the second column by
excluding both the square and discriminant square classes from the strict
defect bound.

## Good-BONG construction

The binary tail has orders `0,1-d` and adjacent defect `d`. Lemma 3.10
adjoins `k+1` standard half-hyperbolic planes while retaining that tail and
the alternating initial profile. The unary good BONG for `<c>` is appended
using proved endpoint inequalities; its last order is exactly `ord(c)`.

The core theorem checks every clause of Theorem 7.4. In particular, the
boundary alpha has upper bound one from the actual adjacent defect `d` and
gap `1-d`. It is nonzero because that gap is not `-2e`, and every nonzero
alpha is at least one. Hence `alpha_n=1`, with no caller-supplied alpha law.
Theorem 7.4 then gives `n`-ADC and the retained tail gives
`R_(n+1)=1-d`, an even value in `[2-2e,0]`.

## Identification with `N_1` and `N_2`

The explicit construction is not treated as definitionally equal to the
paper's named maximal lattice. For each column, the binary diagonal
representation is lifted through the hyperbolic tower to the corresponding
published `W` space. Proposition 3.7 proves the explicit base maximal, while
the chosen `N` model is maximal by construction; maximal-lattice uniqueness
therefore supplies an actual integral isometry.

That isometry is combined with the identity on `<c>`. The constructed good
BONG, its penultimate order, and the `n`-ADC property are then transported
to the literal named product. This closes the model correspondence rather
than merely comparing coefficient orders.

## Statement-strength conclusion

The named endpoints expose exactly the paper's unit, strict-defect, and
normalized-parameter hypotheses. All parity, defect-domain, integrality,
good-BONG, alpha, maximality, ambient-representation, and isometry facts are
proved internally. They are therefore `LOGICALLY_EQUIVALENT` to Lemma 7.19
under the paper's standing good-BONG convention.

## Mechanical trust checks

The four Lemma 7.19 modules, canonical paper entry, and expanded audit
compile directly with Lean 4.32.1. The selected transitive reports, including
both named-product endpoints, contain exactly `propext`,
`Classical.choice`, and `Quot.sound`. The focused enforcing gate reports
`AXIOM_GATE_PASS: 59555 declarations checked`. The comment-aware scanner
checks 2,735 tracked Lean files without a forbidden proof token outside
comments. The scoped 100-column check and `git diff --check` pass.

These are local checks at the stated code commit. Exact-revision Review Kit
CI, release promotion, and independent human sign-off remain separate gates.

## Coverage consequence

Section 7 now has sixteen fully formalized numbered items: Theorems 7.1 and
7.4; Lemmas 7.5--7.12 and 7.14--7.15; Definition 7.16; Remark 7.17; and
Lemmas 7.18--7.19. Lemma 7.13 remains a documented quantifier mismatch.
Theorem 7.2, Remark 7.3, Lemma 7.20, and Corollary 7.21 remain pending.

Author decision: unsigned. Domain-expert decision: unsigned.
Formalization-expert decision: unsigned.
