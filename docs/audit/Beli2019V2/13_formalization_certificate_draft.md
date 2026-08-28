# Formalization Certificate Draft

> Superseded draft notice (28 August 2026): the 49-slot semantic qualification
> below is historical.  The current uncountersigned completion certificate is
> contained in `15_unconditional_completion_audit.md`.

## Certificate identity

- Certificate: `BONG-BELI2019V2-2026-08-15-DRAFT`.
- Status: draft; not independently countersigned.
- Audit date: 15 August 2026.
- Paper: Constantin N. Beli, *Representations of quadratic lattices over
  dyadic local fields*, arXiv v2.

## Artifact identifiers

- Paper PDF SHA-256:
  `1669C626A6D01AF297E07C2CB9584C5BD34F4CEE0F2B188EE0B351BD091C387C`.
- Paper TeX SHA-256:
  `00D58B232A331E559D175C2DF383DE82A49BC7B044E035092B7AC96015858292`.
- Formal source snapshot SHA-256:
  `A7CDDE532BD6C0614414F9524740A7B4B46C9EC4C7352BB40AE93D67A7C31260`.
- Lean: 4.32.1, commit
  `f054605aea4b840552cca2e725580bffd1e1b704`.
- mathlib:
  `520045ab14e26149ee970e2e617ca04b09bde5d6`.
- Repository commit: none; unborn `master` branch.

## Certified technical facts

For the identified local working-tree snapshot:

1. `Bong.beli2019Theorem21` elaborates and is accepted by Lean.
2. `Bong.beli2019Theorem21_prime` elaborates and is accepted by Lean.
3. `Bong.beli2019_sufficiency_complete` elaborates and is accepted by Lean.
4. the complete default Lake build succeeds with 4,544 jobs;
5. the main endpoints report only `propext`, `Classical.choice`, and
   `Quot.sound` through `#print axioms`;
6. no `sorry`, `admit`, `sorryAx`, project `axiom`, or hidden project
   `opaque` proof declaration was found;
7. the public main theorem does not assume
   `GoodBONGRepresentationLaws`;
8. the theorem-level `Beli2019FinalStepLaws` class and obsolete sufficiency
   placeholder are absent;
9. the Sections 7--9 and rank-completion route is connected to the public
   theorem by concrete Lean declarations;
10. `Beli2019SectionFourLaws` is constructed from lower-level inputs rather
    than accepted as a public main-theorem parameter;
11. `GoodBONGDeepIntegralExtensionLaws` is constructed from good-BONG
    existence and the lattice API, and its checked proof term uses only the
    same three standard Lean axioms listed above.

## Semantic qualification

This draft does **not** certify that the Lean theorem is the unconditional
paper theorem over every dyadic local field. The formal declaration has 49
additional project-specific law/data-instance slots, several of which are not
instantiated from the paper's base-field hypothesis.

Final semantic classification: **`FORMALIZATION_WEAKER`**.

Project grade: **C**.

## Reproducibility qualification

The result was checked in the identified local source/cache state. Because
the root repository has no commit and dependency worktrees are not clean,
this certificate is not a clean-clone reproducibility certificate.

Reproducibility classification: **`PARTIALLY_REPRODUCIBLE`**.

## Required independent sign-off

The following reviews remain open:

- mathematical author review of source/target, quantifiers, endpoints, and
  all four conditions;
- confirmation that each local law interface follows from the intended
  dyadic-local-field setting;
- fresh-clone build and CI confirmation;
- repository commit identification.

Formalization auditor: ____________________  Date: __________

Mathematical reviewer: ____________________  Date: __________

Reproducibility reviewer: _________________  Date: __________
