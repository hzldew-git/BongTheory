# Proposition 4.16: dyadic quaternary checkpoint

Date: 2026-09-05. Code: `5fff59784a0a3dd4442405f204519c36e0a8e468`.
Source: Zilong He, *On n-ADC integral quadratic lattices over algebraic
number fields*, Doc. Math. 30 (2025), Proposition 4.16, p. 996; definitions
of H and A on p. 983. Publisher PDF SHA-256:
`E26190C88B16624DCCB7F269C6C3FFDA02BC6830677A5BC0C8E0AD48A36E72D6`.
Lean: 4.32.1. Dependencies: the committed Lake manifest.

## Exact scope and author-facing statement

The paper states the proposition for general non-archimedean local fields
of characteristic different from two. The text preceding Lemma 4.14
explicitly returns to general local fields, and the proof cites both the
non-dyadic and dyadic maximal-lattice tables. The present code is dyadic.

Paper statement in mathematical English: a quaternary norm-maximal lattice
represents H unless it is in the class N_2^4(1). That exceptional class does
not represent H and is isometric to A orthogonal sum A scaled by pi.

Formal statement translated into mathematical English: exactly the same
two assertions hold for every quaternary norm-maximal lattice over a field
in the dyadic context. Equality with the chosen N representative means
integral isometry, not literal equality of carriers or representatives.

Coverage relative to the entire published proposition: `SPECIAL_CASE_ONLY`.
Coverage of the dyadic restriction: both clauses proved. The completed
restriction does not complete the non-dyadic proposition or the whole paper.
For that restriction, coverage is `FULLY_FORMALIZED`, logical strength is
`LOGICALLY_EQUIVALENT`, and the semantic verdict is `PROVISIONAL_MATCH`.

## Definition and normalization dictionary

- H is `(1/2) A(0,0)`, with off-diagonal Gram entries 1/2.
- A is `(1/2) A(2,2rho)`, with Gram matrix `[[1,1/2],[1/2,rho]]`.
- The discriminant data satisfy Delta = 1 - 4 rho and are constructed by
  the proved dyadic discriminant-class instance.
- `heADCAForm_bilin_apply` proves that exact Gram formula; it is not an
  informal interpretation of diagonal BONG coefficients.
- A scaled by pi uses `QuadraticSpace.rescaleUnit`. The underlying standard
  integral coordinate lattice is unchanged; its vectors are not multiplied
  by pi, which would instead multiply norms by pi squared.
- Maximality is norm-integral maximality. Neither classical scale integrality
  nor maximality only in a selected list is substituted.

## Source-to-code correspondence

All new declarations are in `Bong/Bong/He2023ADCQuaternaryMaximal.lean`.

| Mathematical assertion | Public declaration |
|---|---|
| A maximal lattice represents H iff its space is isotropic | `Bong.Lattice.IsOMaximal.represents_halfHyperbolic_iff` |
| The square quaternary W_2 row is the fixed anisotropic space | `Bong.heADCW2QuaternaryOne_eq_anisotropic` |
| Exact A Gram matrix | `Bong.heADCAForm_bilin_apply` |
| Endpoint block corresponds to pi^R-scaled A as a lattice | `Bong.heADCDiscriminantEndpoint_isIsometric_scaledA` |
| N_2^4(1) is integrally isometric to A orthogonal sum A^(pi) | `Bong.heADCN2QuaternaryOne_isIsometric_A_product_scaledA` |
| Anisotropy iff the exceptional integral class | `Bong.Lattice.IsOMaximal.isAnisotropic_iff_heADCN2QuaternaryOne` |
| Both source clauses over dyadic fields | `Bong.Lattice.heADC2025Proposition416Dyadic` |

## Proof completeness and expanded assumptions

The public proposition requires only the dyadic field context, a
nondegenerate quadratic space, a full lattice, norm maximality, and rank
four. It has no good-BONG, order-profile, representative-system, anisotropy,
maximal-table or project-law premise.

A nonzero isotropic vector in the original maximal lattice's ambient space
gives an integral half-hyperbolic splitting by the proved O'Meara machinery.
The head inclusion is an actual integral representation. Conversely, an
embedding of H carries a nonzero isotropic vector to a nonzero isotropic
vector, excluding an anisotropic target.

Uniqueness of the anisotropic quaternary space identifies it with W_2^4(1).
Uniqueness of maximal lattices then gives the integral N_2 class. The
exceptional concrete two-block model is independently maximal by the
He--Hu table proof. Its BONG diagonalization identifies the ambient space;
the endpoint-to-standard isometries at R=0 and R=1 identify its integral
model with A orthogonal sum A^(pi). Thus no assumed representation or
assumed exceptional-class identification is used to prove itself.

## Review card and independent review

A separate read-only AI reviewer checked the publisher scope and proof
route before implementation. The reviewer confirmed the two Gram matrices,
the meaning of form scaling, the isometry-class exception, and the required
non-representation direction. The same independent reviewer then inspected
the frozen implementation and complete elaborated signatures, reran the new
module, canonical entry and whole audit, and found no semantic blocker.
The reviewer confirmed the absence of additional good-BONG, prescribed-row,
representative-witness or project-law premises; both representation
directions; actual integral product isometry; and the six standard-axiom
reports. This is independent AI review, not human sign-off or clean CI.

Author/domain-expert questions: confirm the local-field restriction,
isometry-class interpretation, and half-integral Gram convention.
Formalization-expert question: confirm that maximal-lattice uniqueness and
the endpoint isometries discharge every auxiliary proof input.
Author decision, name, date and signature: not supplied. Domain-expert and
human formalization-expert approval: not supplied.

## Trust and reproducibility

The new module, canonical paper entry and complete expanded audit compiled
locally. All six newly queried transitive axiom sets are exactly `propext`,
`Classical.choice`, and `Quot.sound`. No admitted proof, new axiom or
native-evaluation mechanism appears in the new module.

These are cached local checks; the existing mathlib, aesop and batteries
worktree warnings were preserved. The older remote profile-kit artifact
does not contain this module. Its successful CI must not be attributed to
the new proposition. Exact-revision clean-kit CI is still required.

This closes only the dyadic Proposition 4.16 gap recorded at report 15's
earlier checkpoint. Non-dyadic results, unary testing, ADC classifications,
concrete global arithmetic, enumeration, and human review remain outside
this sub-result. Whole-paper grade: C. Whole-paper verdict: `NOT_COMPLETE`.
