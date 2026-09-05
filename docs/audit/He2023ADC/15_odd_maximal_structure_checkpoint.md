# Proposition 4.13 checkpoint and independent review

Date: 2026-09-05. Code:
`9c432a685c96c134b12664800464ae4b1d0d6eec`.
Source: Zilong He, *On n-ADC integral quadratic lattices over algebraic number
fields*, Doc. Math. 30 (2025), Proposition 4.13, p. 995, in the dyadic case.
Publisher PDF SHA-256:
`E26190C88B16624DCCB7F269C6C3FFDA02BC6830677A5BC0C8E0AD48A36E72D6`.
Lean: 4.32.1. Dependencies: the committed Lake manifest.

## Independent extraction and correspondence

A separate read-only AI reviewer extracted the proposition and the capped
defect convention from the publisher text before inspecting the code. The
reviewer independently checked the publisher hash, the complete elaborated
types, and the existing audit module. No blocking semantic issue was found.
This does not constitute human sign-off.

The main endpoint is `Bong.BONG.GoodBONG.heADC2025Proposition413` in
`Bong/Bong/He2023ADCOddMaximalStructure.lean`. It proves the structure
`HeADCProposition413Conclusions`. Supporting endpoints are
`exists_heADCOddNormalizedAmbient` and `heADCOddMaximal_orders` in the same
namespace and file.

Put n = 2k + 3 and D = d[-b_(n-2)b_(n-1)], with the paper's alpha caps.

| Source clause | Formal conclusion | Assessment |
|---|---|---|
| (i), initial orders through n-2 | `initialOrders`: zero at paper odd indices, -2e at paper even indices | Match |
| (i), penultimate order | `penultimate`: -2e or 2-2e | Match |
| (ii), penultimate order -2e | `standardTail`: last order 0 or 1, beta_(n-2)=0, beta_(n-1) >= D >= 2e | Match |
| (iii), penultimate order 2-2e | `raisedTail`: last order 0, beta_(n-2)=1, D=beta_(n-1)=2e-1 | Match |

Coverage: `FULLY_FORMALIZED`. Logical strength: `LOGICALLY_EQUIVALENT` under
the standing dyadic and good-BONG conventions. Semantic assessment:
`PROVISIONAL_MATCH`, pending human confirmation.

## Expanded assumptions and boundary cases

The main inputs are the dyadic field context, a nondegenerate quadratic space,
a full lattice, an arbitrary good BONG of odd length, and norm maximality.
Maximality includes norm integrality; this is not classic/scale maximality.

The valuation-unit parameter is constructed by square-class normalization.
Ambient exhaustion selects one of the four valuation-parity rows. Maximality
of the comparison model and uniqueness of maximal lattices then produce an
actual integral isometry. Lemma 4.12 supplies the orders. No representative
system, auxiliary unit, kappa, order profile, or separate project-law premise
is assumed by the main theorem.

The last three order indices are 2k, 2k+1, and 2k+2; the last two alpha
indices are 2k and 2k+1. Thus every odd rank n >= 3 is included, including
k = 0. At this ternary boundary, `prefixAlphaCap_zero` is top, correctly
omitting the nonexistent beta_0. The defect is the capped minimum, not the
raw binary defect. No infinity-to-natural conversion occurs. The finite
quantity 2e-1 is explicitly formed in the rationals before embedding into
`WithTop`. The unramified case e = 1 is included.

The alpha equalities and defect bounds follow from the previously proved
Section 3 alpha arithmetic and the right prefix-cap inequality. The review
found no dependency cycle or imported assumption equivalent to the target.

## Author review card

Paper statement in mathematical English: an odd-rank norm-maximal lattice
has the alternating initial order pattern and exactly the terminal orders,
alpha values, and capped-defect bounds in the table above.

Formal statement translated into mathematical English: the same assertions
hold for every good BONG of every such lattice, with rank parameterized as
2k+3. Neither terminal profile is a hypothesis; only the source's conditional
branch assumptions appear within their corresponding conclusions.

Definitions requiring confirmation: norm maximality, good-BONG order and
alpha invariants, the bracketed defect, normalized valuation, and integral
isometry. No extra mathematical assumption or omitted conclusion was found.
The only indexing difference is one-based paper indices versus zero-based
formal indices. The n=3 and e=1 boundaries were checked explicitly.

Questions for the author and domain expert: Confirm the bracketed-defect
interpretation and the omission of the absent alpha cap in rank three.
Question for the formalization expert: Confirm that normalization and
maximal-lattice uniqueness discharge all auxiliary proof data.

Author decision, name, date, and signature: not provided. Domain-expert and
human formalization-expert approval: not provided.

## Trust and reproducibility

The new module, canonical paper entry, and expanded audit compiled locally.
The independent reviewer also ran the audit successfully. The three new
endpoints report exactly `propext`, `Classical.choice`, and `Quot.sound`.
No admitted proof, new axiom, or native-evaluation mechanism was used.

These were cached local checks with the previously existing mathlib, aesop,
and batteries worktree warnings. This checkpoint was created after the
successful remote profile-kit build, so that older artifact cannot certify
the new proposition. Exact-commit clean-kit CI remains pending.

This result closes the Proposition 4.13 gap recorded at the earlier report 14
checkpoint. Proposition 4.16, unary testing, non-dyadic results, ADC
classifications, concrete global arithmetic, and human review remain outside
this completed sub-result. The whole ADC project remains Grade C and
`NOT_COMPLETE`.
