# Audited mathematical sources

The source versions below are frozen by bibliographic metadata and SHA-256.
Publisher PDFs are not redistributed by this repository. The hashes identify
the exact local copies used for statement extraction and semantic audit.

| Key | Bibliographic record | Audited artifact | SHA-256 |
| --- | --- | --- | --- |
| Beli 2003 | Constantin N. Beli, “Integral spinor norm groups over dyadic local fields,” *Journal of Number Theory* 102(1), 125–182 (2003), DOI [10.1016/S0022-314X(03)00057-X](https://doi.org/10.1016/S0022-314X(03)00057-X) | 58-page publisher PDF | `BB2C45F06EB2888D75D7030F7E893B5048588B1CA092180A816DA0C2A9F4A055` |
| Beli 2006 | Constantin N. Beli, “Representations of integral quadratic forms over dyadic local fields,” *Electronic Research Announcements of the AMS* 12, 100–112 (2006), DOI [10.1090/S1079-6762-06-00165-X](https://doi.org/10.1090/S1079-6762-06-00165-X) | 13-page publisher PDF | `DB1B681B186F1688FB1C2CF4B03CAB7E78896144D680471F67D6893C82DF2371` |
| Beli 2009/2010 | Constantin N. Beli, “A new approach to classification of integral quadratic forms over dyadic local fields,” electronically published 2009, *Transactions of the AMS* 362(3), 1599–1617 (2010), DOI [10.1090/S0002-9947-09-04802-8](https://doi.org/10.1090/S0002-9947-09-04802-8) | 19-page publisher PDF | `09ADCDCDD698F96D232C3F46D3901719321FE08FEF5259488D0E3B482F702120` |
| Beli 2019 v2 | Constantin N. Beli, “Representations of quadratic lattices over dyadic local fields,” [arXiv:1905.04552v2](https://arxiv.org/abs/1905.04552v2), revised 30 May 2022 | 139-page arXiv v2 PDF | `1669C626A6D01AF297E07C2CB9584C5BD34F4CEE0F2B188EE0B351BD091C387C` |
| Beli 2019 v2 source | Same work and version | arXiv v2 TeX source | `00D58B232A331E559D175C2DF383DE82A49BC7B044E035092B7AC96015858292` |
| Beli 2020 | Constantin N. Beli, “Universal integral quadratic forms over dyadic local fields,” [arXiv:2008.10113v2](https://arxiv.org/abs/2008.10113v2), first submitted 23 August 2020 and revised 26 June 2022 | 19-page arXiv v2 PDF | `35ECB7CB20A42768A6F55D80E69D4699837419854FAB021515020CCC7488986C` |
| He--Hu 2022 / published 2024 | Zilong He and Yong Hu, “On n-universal quadratic forms over dyadic local fields,” *Sci. China Math.* 67 (2024), 1481--1506, DOI [10.1007/s11425-022-2133-0](https://doi.org/10.1007/s11425-022-2133-0) | 26-page publisher version of record | `32CBF87286B6580B91DCF051CABF3C31C62D65098B7C75177B00C5FBCF1E24E6` |
| He 2022 Classic / published 2024 | Zilong He, “On classic n-universal quadratic forms over dyadic local fields,” *manuscripta math.* 174 (2024), 559--595, DOI [10.1007/s00229-023-01516-0](https://doi.org/10.1007/s00229-023-01516-0) | 37-page publisher version of record | `51F3626A15692E2FF0BAAE62F0EBCC4B8BEE02052C4D3CB1EA579B02E17480C1` |
| He 2023 ADC / published 2025 | Zilong He, “On n-ADC integral quadratic lattices over algebraic number fields,” *Doc. Math.* 30 (2025), no. 4, 981--1022, DOI [10.4171/DM/1003](https://doi.org/10.4171/DM/1003) | 42-page publisher version of record | `E26190C88B16624DCCB7F269C6C3FFDA02BC6830677A5BC0C8E0AD48A36E72D6` |

The revised condition `(iii')` following Theorem 2.1 occurs in the audited
2019 v2 source. It is represented by the separate public endpoint
`Bong.beli2019Theorem21_prime` and must not be inferred from an earlier draft.

For Beli 2020, direct substitution into Theorem 2.1 gives coefficient
`2r_1` in the ideal exponents of Theorem 3.1(3.2.1--2), while the frozen PDF
prints `r_1`.  Both predicates and their zero-scale comparison are formalized;
the discrepancy is not silently repaired.  See
`docs/audit/Beli2020/13_completion_audit.md`.

The formal development also uses results from O'Meara's *Introduction to
Quadratic Forms* where Beli invokes them. Only the results used by the proof
chain are formalized; their locations and roles are documented in source
comments and the audit reports.

For the three He papers, publisher versions of record are the sole semantic
authority. The comparison copies arXiv:2204.01997v2, arXiv:2206.04885v3, and
arXiv:2306.00334v3 have separate hashes in the schema-2 paper manifests. The
latter two were revised after publication and cannot override publisher text.
