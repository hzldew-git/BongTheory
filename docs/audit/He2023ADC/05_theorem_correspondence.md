# Theorem correspondence

| Source | Formal endpoint | Correspondence |
|---|---|---|
| Definition 1.1(ii), local `n`-ADC | `IsNADC` | Dyadic specialization; review pending |
| Lemma 2.1 | `heADCLemma21LocalDyadic` | Dyadic specialization proved |
| Definition 1.2 and regularity | `GlobalLocalLatticeSystem.IsGloballyNADC`, `IsGloballyNUniversal`, `IsNRegular` | Abstract predicates; concrete number-field realization pending |
| Theorem 1.3 | `GlobalLocalLatticeSystem.heADCTheorem13` | Conditional on `Theorem13Laws`; not a completed global theorem |
| Theorem 1.4(i) | `heADCTheorem14iLocalDyadic` | Proved dyadic stable-rank specialization |
| Theorem 1.4(ii)(iii) | `GlobalLocalLatticeSystem.heADCTheorem14ii`, `heADCTheorem14iii` | Logical reductions with ambient arithmetic premises |
| Lemma 3.1--Theorem 3.6 | `heADC2025Lemma31`, `heADC2025Corollary32*`, `heADC2025Proposition3*`, `heADC2025Theorem36` | Direct reuse of proved Beli/He--Hu results; transcription review provisional |
| Theorem 3.6, literal published package | `GoodBONG.heADC2025Theorem36Published`, `heADC2025Theorem36PublishedFull` | `PROVISIONAL_MATCH` after independent AI review at `218cfb9`; exact capped-defect trigger and terminal index; report 20; two adapters, not two new paper results |
| Definition 4.1, Proposition 4.2, Remark 4.3 | `heADCW*`, `heADCN*`, including `heADCW1Unary` and `heADCN1Unary`, `heADC2025Proposition42*`, `heADC2025Remark43*` | Unary definitions now included; complete unary classification/counting and unrestricted field scope remain pending |
| Lemma 4.4 | `heADC2025Lemma44*` | Table-index uniqueness and determinant/Hasse forms of the two representation criteria; parameter-form correspondence remains reviewable |
| Lemma 4.5 | `heADC2025Lemma45i*`, `heADC2025Lemma45ii*` | Dyadic exactly-one representation results in both directions |
| Lemma 4.6 | `IsNADC.representsExactlyOne_of_ambient`, `represents_every_of_ambient`, `GoodBONG.heADC2025Lemma46iEvenCorankOne` | Generic lifting and the actual even corank-one exactly-one test are proved; `SPECIAL_CASE_ONLY` for the whole lemma; other table specializations remain |
| Lemmas 4.7--4.8 | none | Non-dyadic scope pending |
| Lemma 4.9(i) | `heADC2025Lemma49*` table-row endpoints | Maximality of the explicit dyadic models; Beli classification premise internally discharged |
| Lemma 4.9(ii) | `heADC2025Lemma49iiEven`, `heADC2025Lemma49iiOdd` | Literal finite deletion-minimal testing sets for rank at least two; unary case pending |
| Remark 4.10 | `GoodBONG.heADC2025Remark410` | Full coordinate formula for a supplied integral tail; the named-lattice decomposition is assembled through the table and transport results |
| Lemma 4.11(i) | `GoodBONG.heADC2025Lemma411iOnePublished`, `heADC2025Lemma411iDeltaPublished` | Both first-column `W/N` endpoints, with both directions proved |
| Lemma 4.11(ii) | `GoodBONG.heADC2025Lemma411iiOnePublished`, `heADC2025Lemma411iiDeltaPublished` | Both second-column `W/N` endpoints; square row starts at rank four |
| Lemma 4.11(iii) | `GoodBONG.heADC2025Lemma411iiiUnitFirstPublished`, `UnitSecondPublished`, `UniformizerFirstPublished`, `UniformizerSecondPublished` with the same prefix | All four `W/N` branches; finite-defect and sharp-unit arithmetic are proved internally |
| Lemma 4.12(i)(ii) | `GoodBONG.heADC2025Lemma412iPublished`, `heADC2025Lemma412iiPublished`, `heADC2025Lemma412UnaryPublished` | Both `W/N` columns; rank one included; final second-column theorem has no `kappa` premise |
| Lemma 4.12(iii) | `GoodBONG.heADC2025Lemma412iiiFirstPublished`, `heADC2025Lemma412iiiSecondPublished`, `heADC2025Lemma412UnaryPublished` | Both `W/N` unit-uniformizer columns, including rank one |
| Proposition 4.13 | `Bong.BONG.GoodBONG.heADC2025Proposition413` | `FULLY_FORMALIZED`, semantic `PROVISIONAL_MATCH`: all three clauses for every odd rank at least three; exact capped-defect bounds and equality retained |
| Lemma 4.14, Proposition 4.15 | `heADCLemma414LocalDyadic`, `heADCProposition415LocalDyadic` | Proved dyadic specializations |
| Proposition 4.16 | `Bong.Lattice.heADC2025Proposition416Dyadic` and `Bong.heADCN2QuaternaryOne_isIsometric_A_product_scaledA` | `SPECIAL_CASE_ONLY` for the published proposition; dyadic restriction `FULLY_FORMALIZED` / `PROVISIONAL_MATCH` after independent AI review, with integral representations and the exact half-scaled Gram normalization |
| Lemma 6.4(i)--(iv) | `Bong.BONG.GoodBONG.heADC2025Lemma64i`, `heADC2025Lemma64ii`, `heADC2025Lemma64iii`, `heADC2025Lemma64iv` | `FULLY_FORMALIZED` / `PROVISIONAL_MATCH`; all four clauses independently reviewed; report 17; included in clean-kit f6f7485/c82668b; human approval pending |
| Lemma 6.5(i)--(ii) | `Bong.BONG.GoodBONG.heADC2025Lemma65i`, `heADC2025Lemma65ii` | `FULLY_FORMALIZED` / `PROVISIONAL_MATCH`; exact failing indices, both actual classes and n=2 independently checked; report 18; included in clean-kit f6f7485/c82668b; human approval pending |
| Theorem 6.1 | `Bong.Lattice.heADC2025Theorem61` | `FULLY_FORMALIZED` / `PROVISIONAL_MATCH`: arbitrary full lattice, even n >= 2, rank n+1, ADC iff maximal; no supplied BONG/profile/law; independent review at `272d810`; report 19; included in clean-kit f6f7485/c82668b; human approval pending |
| Lemma 6.6(i)--(ii) | `Bong.BONG.GoodBONG.heADC2025Lemma66i`, `heADC2025Lemma66ii` | `FULLY_FORMALIZED` / `PROVISIONAL_MATCH` at `cd8ecbd`; literal central failure, actual targets, raw/capped distinction and short-rank boundaries reviewed; report 21; included in clean-kit f6f7485/c82668b; human approval pending |
| Lemma 6.7(i)--(ii) | `Bong.BONG.GoodBONG.heADC2025Lemma67i`, `heADC2025Lemma67ii` | `FULLY_FORMALIZED` / `PROVISIONAL_MATCH` at `b0f832e`; actual tests, exact alpha alternatives and raw/capped equalities, both rank boundaries and e=1 reviewed; report 22; included in clean-kit f6f7485/c82668b; human approval pending |
| Lemma 6.8(i)--(ii) | `Bong.Lattice.heADC2025Lemma68i`, `heADC2025Lemma68ii` | Each clause `FULLY_FORMALIZED` / `PROVISIONAL_MATCH` at `b624d40`; exact n=2/n>=4 boundaries; report 23; own clean CI and human approval pending |
| Lemma 6.8(iii) | `Bong.Lattice.heADC2025Lemma68iii` | `FULLY_FORMALIZED` / `PROVISIONAL_MATCH` at `074f2cd`, including n=2; report 25; own clean CI and human approval pending |
| Lemma 6.8(iv) | `Bong.Lattice.heADC2025Lemma68iv_of_pos`; `Bong.BONG.GoodBONG.not_heADC2025Lemma68ivBinaryStatement` | `PROVISIONAL_MATCH` for n>=4 at `074f2cd`; `SEMANTIC_MISMATCH` at n=2. The latter declaration proves the negation of the printed binary implication using an actual nonmaximal 2-ADC lattice; independently audited in reports 30--31 |
| Lemma 6.8(v)--(vi) | `Bong.Lattice.heADC2025Lemma68v`, `heADC2025Lemma68vi` and their `Published` wrappers | `FULLY_FORMALIZED` / `PROVISIONAL_MATCH` at `b728bce`; actual original-parameter lattice isometry, n=2 included; printed V domain explicitly requires compatible Delta in U; report 24; with report 25 whole lemma 5/6, own clean CI and human approval pending |
| Section 5, remaining Sections 6--8 and Section 1 results | none | Pending; the proof of Theorem 6.2 cannot be certified through Lemma 6.8(iv) as printed |

The field restriction prevents claiming the full generality of Lemma 2.1.
At checkpoint `976883e6cda7c17402c4c1f0bc768db555460eae`, all thirteen
published-family branches have checked model-to-`W/N` transport. This closes
the earlier correspondence gap for Lemmas 4.11--4.12. Report 14 lists the
full declaration names and remaining audit boundaries. Human approval is
still pending; these are not `VERIFIED_MATCH` declarations.
