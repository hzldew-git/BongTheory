# Formalization fidelity audits

Every audit artifact in this directory is written in English and distinguishes
kernel acceptance, proof completeness, semantic fidelity, coverage, and
reproducibility.

- `Beli2003`: the three integral spinor-norm main theorems.
- `Beli2006`: the announced classification and representation criteria.
- `Beli2009`: the classification proof and final binary-transformation results.
- `Beli2019V2`: the complete representation proof, including revised condition
  `(iii')`.

The paper statements and formal statements were extracted independently before
comparison. Current theorem cards are `PROVISIONAL_MATCH`; none is
`VERIFIED_MATCH` until the required human decisions are recorded.

Local committed-source reproducibility is recorded separately in
[`../reproducibility/clean-clone-ee826e7.md`](../reproducibility/clean-clone-ee826e7.md).
It does not replace the independent mathematical and Lean-review signatures.
