# Theorem 7.4 and the Lemma 7.5 proof chain

Status at code checkpoint `2417a4f`: Theorem 7.4 and Lemmas 7.5--7.10 and 7.12 are
`FULLY_FORMALIZED` / `PROVISIONAL_MATCH`. Lemma 7.11 is
`SPECIAL_CASE_ONLY`. Lemma 7.13 has a documented source-quantifier
`SEMANTIC_MISMATCH`.

Code checkpoint: `2417a4f31e4a9f96e22c4da6d2276e2e94210fdd`.

Historical note: the partial Lemma 7.11 status in this checkpoint is
superseded by the complete two-row proof at `832d10c` and report 37. Theorem
7.4, Lemma 7.5, and the Lemma 7.13 mismatch recorded here remain current.

## Source authority

The sole semantic authority is the publisher version of record:

- Zilong He, *On n-ADC integral quadratic lattices over algebraic number
  fields*, *Documenta Mathematica* 30 (2025), no. 4, 981--1022;
- DOI: <https://doi.org/10.4171/DM/1003>;
- publisher PDF SHA-256:
  `E26190C88B16624DCCB7F269C6C3FFDA02BC6830677A5BC0C8E0AD48A36E72D6`.

Theorem 7.4 and Lemma 7.5 occur on p. 1007. Lemmas 7.6--7.8 occupy
pp. 1007--1010; Lemmas 7.9--7.13 and the necessity proof occupy
pp. 1011--1013. The post-publication arXiv revision remains comparison-only.

## Complete Lemma 7.5 equivalence

`GoodBONG.HeADCLemma75Conditions` records the four published conditions:

1. the alternating initial orders through index `n`;
2. the alternative `alpha_n=0` or the exact alpha/defect identity;
3. the large terminal-gap implication;
4. the even penultimate interval and final `{0,1}` restriction when
   `alpha_n=1`.

`heADC2025Lemma75Necessity` and `heADC2025Lemma75Sufficiency` prove the two
directions. `heADC2025Lemma75` exports the exact biconditional for
`n=2k+3` and a rank-`n+2` good BONG. The sufficient direction handles both
the bounded-gap representation criterion and the large-gap maximal-lattice
branch. The necessary direction derives all four conditions rather than
accepting any as auxiliary laws.

The supporting public endpoints are:

- `heADC2025Lemma76i`--`heADC2025Lemma76v`;
- `heADC2025Lemma77i`--`heADC2025Lemma77iii`;
- `heADC2025Lemma78`, `Lattice.heADC2025Lemma79`,
  `heADC2025Lemma710`, and `heADC2025Lemma712`.

Together they formalize the complete numbered statements of Lemmas
7.6--7.10 and 7.12, including the raw/capped defect distinctions and the
central and long representation conditions required by Theorem 3.6.

## Lemma 7.11 scope and rank boundary

The source's Lemma 7.11 quantifies over every nonzero parameter `c`, splitting
it in the proof into unit and unit-times-uniformizer cases. The current
`heADC2025Lemma711Odd` proves the full pointwise failure for the
unit-times-uniformizer tests `N_2^3(delta*pi)`. The separate theorem
`heADC2025Lemma711_exists_represented_oddTarget` constructs one of two such
ambiently represented targets, and `heADC2025Lemma711_badBranch_impossible`
uses 3-ADC lifting to eliminate exactly the bad rank-five branch required in
the proof of Lemma 7.5(iii).

This required correcting the existing He--Hu Lemma 5.7 interface from
`m>=4` to its actual minimal `m>=3`: the paper index `4` only needs the
source rank `m+2` to be at least five. All six affected endpoints now admit
the rank-five instance and compile. No theorem conclusion was strengthened.

The even-valuation part of the published all-parameter Lemma 7.11 has not yet
been formalized. Therefore Lemma 7.11 is not counted as a fully covered
numbered result, even though the proved odd-valuation consequence suffices for
the current Lemma 7.5 route.

## Lemma 7.13 quantifier mismatch

The printed Lemma 7.13(ii) states the prefix non-representation conclusion
after introducing either of two targets. On pp. 1011--1012, however, the
proof assumes that the prefix represents both targets and derives a Hilbert
symbol contradiction. That argument proves

`not represents first OR not represents second`,

not the stronger conjunction saying that both individual representations
fail. The necessity proof on p. 1013 explicitly needs only that Theorem
3.6(iii) fails for either target.

`heADC2025Lemma713` therefore records the disjunction justified by the proof,
separately in both target columns, and `heADC2025Lemma713_trigger_impossible`
uses it to exclude the bad alpha branch. The stronger printed per-target
claim is not silently assumed. The downstream proof of Lemma 7.5(iv) and
Theorem 7.4 remains complete under the corrected quantifier.

## Theorem 7.4

`GoodBONG.HeADCTheorem74Conditions` records the published normal form:

- alternating initial orders;
- an even penultimate order in `[2-2e,0]`;
- final order and `alpha_n` in `{0,1}`.

`heADC2025Theorem74Necessity`, `heADC2025Theorem74Sufficiency`, and
`heADC2025Theorem74` prove the two directions and the exact equivalence.
The delicate endpoint `R_(n+1)=2-2e` is not discharged by an unchecked
arithmetic shortcut: the proof uses the next adjacent-alpha upper bound to
show that the truncated defect is exactly `2e-1`, matching the publisher's
argument on pp. 1007--1008.

## Mechanical trust checks

The corrected He--Hu modules, all twelve new Section 7 modules, canonical
paper entry, and focused audit compile directly with Lean 4.32.1. Nine
selected transitive axiom reports contain exactly `propext`,
`Classical.choice`, and `Quot.sound`. The focused enforcing gate reports
`AXIOM_GATE_PASS: 59190 declarations checked`. The comment-aware scanner
checks 2,715 tracked Lean sources and finds no forbidden proof token outside
comments. All scoped new Lean source lines satisfy the 100-column limit, and
`git diff --check` passes.

These are local checks at the stated commit. Exact-revision Review Kit CI,
release promotion, and human sign-off remain separate gates.

## Historical coverage consequence at `2417a4f`

Section 7 now has nine fully formalized numbered items: Theorems 7.1 and 7.4,
and Lemmas 7.5--7.10 and 7.12. Lemma 7.11 remains partial; Lemma 7.13 is
formally covered only in the weaker quantifier form proved by the paper.
Theorem 7.2, Remark 7.3, Lemmas 7.14--7.15, Definition 7.16, Remark 7.17,
Lemmas 7.18--7.20, and Corollary 7.21 remain pending.

Author decision: unsigned. Domain-expert decision: unsigned.
Formalization-expert decision: unsigned.
