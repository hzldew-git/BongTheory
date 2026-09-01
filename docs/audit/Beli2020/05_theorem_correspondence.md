# Theorem correspondence

| Paper item | Formal endpoint or proof family | Fidelity decision |
| --- | --- | --- |
| Theorem 1.1 | Earlier Beli 2009/2010 classification endpoints | `PROVISIONAL_MATCH` in its own audit |
| Theorem 1.2 | Revised Beli 2019-v2 representation endpoint | `PROVISIONAL_MATCH` in its own audit |
| Lemmas 2.2--2.7 | Individually named reductions | `PROVISIONAL_MATCH` |
| Lemma 2.8 and Corollary 2.9 | Reusable all-index alpha theorems and first-index specializations | `PROVISIONAL_MATCH`; packaging is distributed |
| Lemmas 2.10--2.14 | Defect, endpoint, central, and long equivalences | `PROVISIONAL_MATCH` |
| Theorem 2.1 | `beliUniversalTheorem21`; direct iff endpoint | `PROVISIONAL_MATCH` |
| Theorem 3.1, all cases other than (3.2.1--2) | Arbitrary-Jordan translation proof | `PROVISIONAL_MATCH` |
| Theorem 3.1(3.2.1--2), literal text | `UniversalTheorem31Conditions` plus the zero-scale theorem | `SOURCE_DISCREPANCY` outside `r_1=0` |
| Theorem 3.1, direct consequence of Theorem 2.1 | `isUniversal_iff_universalTheorem31DirectConditions` | `PROVISIONAL_MATCH_TO_DERIVATION` |
| Lemmas 4.1--4.4 | `Lattice.beliUniversalLemma41`--`44` | `PROVISIONAL_MATCH` |
| Corollary 4.5 | Four public clauses | `PROVISIONAL_MATCH` |
| Lemmas 4.6--4.9 | Good-BONG splitting and residual-invariant endpoints | `PROVISIONAL_MATCH` |
| Corollary 4.10 | `BONG.GoodBONG.beliUniversalCorollary410` | `PROVISIONAL_MATCH` |

## Theorem 3.1 derivation boundary

The paper says that Theorem 3.1 is a translation of Theorem 2.1 and omits a
proof.  The Lean proof does not copy the claimed conclusion.  It:

1. chooses a good BONG of the given lattice;
2. aligns its order profile with the prescribed Jordan decomposition;
3. transports prefix isotropy using the 2019 approximation lemma and proved
   codimension-one cancellation;
4. translates every arithmetic branch;
5. discharges the chosen BONG and alignment witness.

For first component rank two, the dictionary gives `R_2=2r_1`.
Consequently the II(b) substitution gives `2r_1` in (3.2.1--2).  The frozen
text prints `r_1`.  This is the only known statement-level discrepancy in
the completed paper scope.

`PROVISIONAL_MATCH` means that source and formal statements have been
compared but independent domain and Lean reviewers have not signed the review
cards.  Kernel acceptance alone does not upgrade it to `VERIFIED_MATCH`.
