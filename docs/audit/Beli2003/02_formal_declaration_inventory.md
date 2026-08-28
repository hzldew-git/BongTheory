# Formal declaration inventory

| Declaration | Location | Expanded mathematical role |
| --- | --- | --- |
| `Bong.BONG.beliTheoremOne_proved` | `Bong/Bong/BeliTheoremOneProof.lean:33` | For a BONG of length at least three with property A, identifies the lattice spinor-norm image subgroup with the explicitly defined paper right-hand side. |
| `Bong.BONG.beliTheoremOne_set_proved` | same file | Set-equality form of Theorem 1. |
| `Bong.Lattice.beliTheoremTwo_proved` | `Bong/Bong/BeliTheoremTwoProof.lean:799` | Equates unit-bounded spinor norm with the conditions attached to a concrete hyperbolic-tower splitting. |
| `Bong.Lattice.beliTheoremTwo_eq_unit_proved` | same file | Identifies the group with the valuation-unit square-class subgroup in the positive-tower case. |
| `Bong.BONG.beliTheoremThree_proved` | `Bong/Bong/BeliTheoremThreeUnconditional.lean:32` | For any displayed good BONG, equates unit-bounded spinor norm with the paper's good-BONG conditions. |

The supporting declarations are grouped by paper numbering, including
`BeliLemma313*`, `BeliLemma317`, `BeliLemma318`, `BeliLemma319`,
`BeliLemma41`, `BeliCorollary44`, `BeliLemma45*`, `BeliLemma47*`,
`BeliLemma61`–`BeliLemma67`, and `BeliLemma71`–`BeliLemma73`.

Every public main endpoint quantifies over the field, valuation/topology
context, quadratic space, lattice, and displayed decomposition or BONG. No
project-specific law/data class occurs in these endpoint signatures.
