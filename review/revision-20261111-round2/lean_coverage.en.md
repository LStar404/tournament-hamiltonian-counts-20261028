# Manuscript–Lean coverage: English reviewer summary (2026-11-11, round 2)

This is an English reading index, not a new formalization or a Lean build report. An existing endpoint for a conclusion does **not** certify every step of the current manuscript proof. The two added degree-variance observations below are manuscript arguments only.

## Fixed evidence and version boundaries

- [Detailed historical correspondence (Chinese; canonical statement/quantifier table)](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/1b66d66cd287310c3a85dc3c64816fa319d55af2/review/revision-20261111/lean_correspondence.md).
- [Machine-readable historical correspondence](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/1b66d66cd287310c3a85dc3c64816fa319d55af2/review/revision-20261111/lean_correspondence.json).
- [Historical 2026-11-11 source/index checks](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/1b66d66cd287310c3a85dc3c64816fa319d55af2/review/revision-20261111/lean_checks.json).
- [Historical run input manifest](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/1b66d66cd287310c3a85dc3c64816fa319d55af2/review/lean-rerun-20261107/input_manifest.json).
- [Historical 2026-11-07 build summary](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/1b66d66cd287310c3a85dc3c64816fa319d55af2/review/lean-rerun-20261107/summary.json).
- [Historical run report](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/1b66d66cd287310c3a85dc3c64816fa319d55af2/review/lean-rerun-20261107/README.zh.md).
- [Historical verification logs](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/1b66d66cd287310c3a85dc3c64816fa319d55af2/review/lean-rerun-20261107/verification_logs.zip).
- [Exact endpoint catalog and printed types](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/1b66d66cd287310c3a85dc3c64816fa319d55af2/formal/coverage.json).
- [Pinned Lean toolchain](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/1b66d66cd287310c3a85dc3c64816fa319d55af2/formal/lean-toolchain).
- [Pinned dependency manifest](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/1b66d66cd287310c3a85dc3c64816fa319d55af2/formal/lake-manifest.json).

All links above are pinned to repository commit `1b66d66cd287310c3a85dc3c64816fa319d55af2`, so they do not depend on publication of this new index. The historical production source identity is `c678e9ee24fb304cad755a27c99f511c8640f75e`, corroborated by the manifest and per-file hashes. These are different roles for different commits, not competing claims about a new build.

The recorded run is **2026-11-07 16:40:36–17:04:14 UTC**, not this revision: 609 production modules, 3067 registered endpoints, 223 key endpoint type/definition checks, and 318 commands with exit code zero. The report records Lean 4.35.0 and mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`; upstream caches were reused, so this was not a cold rebuild of mathlib. The recorded recursive axiom audit allows only `propext`, `Classical.choice`, and `Quot.sound`.

This revision adds no Lean endpoint and performs no Lean compilation, new recursive axiom audit, or new type printing. The accompanying checker only verifies index consistency, hashes, pinned Git objects, and existing source checks. It cannot certify the new mathematics. Historical records remain unchanged.

## How to read the statuses

- **Existing conclusion:** historical endpoints cover the stated conclusion under their exact hypotheses. This is not a line-by-line correspondence for a revised proof.
- **Same conclusion; different proof:** the conclusion follows from existing endpoints, but the current manuscript proof chain has not been mapped.
- **Partial coverage:** only the old part has an endpoint.
- **Composition not mapped:** relevant components exist, but their current combination has no mapped endpoint.
- **No new endpoint:** no endpoint or build evidence is claimed for this manuscript statement.
- **Historical only:** an old statement must not be identified with a new statement merely because their numbers match.

The summaries below are deliberately shorter than the canonical table. For precise quantifiers and types, consult that table and `actual_full_printed_type` in the linked endpoint catalog. Full declaration names and unchanged source hashes are also retained in [lean_coverage.json](lean_coverage.json).

## Current correspondence

| Current manuscript location | Status | Scope |
|---|---|---|
| Theorem 1.1 | **Existing conclusion** | Sharp asymptotic for the actual maximum Hamilton path count, with absolute uniform constants. |
| Theorem 1.3 (formerly 1.2) | **Existing conclusion** | Original-angle Hessian identity, positivity and determinant formula. The present short Schur-complement proof is not mapped step by step. |
| Corollary 1.4 (formerly 1.3) | **Existing conclusion** | Eventual unique carousel extremizers in all four blow-up models, with a common threshold for all base tournaments of each fixed odd order. |
| Corollary 1.5 (formerly 1.4) | **Existing conclusion** | Strict monotonicity and limit of the regular-carousel constants. |
| Theorem 3.1 | **Existing conclusion** | Uniform permanent approximation for bounded doubly centred perturbations with a fixed operator-norm gap. |
| Technical appendix, Lemma 3.2 | **Existing conclusion** | Summable weighted core-excess coefficients and first-excess estimate. |
| Technical appendix, Lemma 3.3 | **Existing conclusion** | Complex permanent polarization and nonnegativity for positive semidefinite matrices. |
| Technical appendix, Lemma 3.4 | **Existing conclusion** | Complete-homogeneous and geometric permanent bounds, retaining spectral multiplicities. |
| Technical appendix, Proposition 3.5 | **Existing conclusion** | Gaussian recovery with the stated error budget and factorial second moment. |
| Lemma 4.1 | **Existing conclusion** | Local matrix scaling, including signed-input estimates and separate support/nonnegativity conclusions. |
| Lemma 4.2 | **Existing conclusion** | Displacement, capacity and mass-restored normalization bounds. |
| Lemma 4.3 | **Existing conclusion** | Gram-determinant deletion, centering and Lipschitz estimates. |
| Lemma 4.4 | **Existing conclusion** | Uniform paired Gaussian estimates for independent row and column deletion sets of equal size. |
| Lemma 4.5 | **Existing conclusion** | Small-score relative permanent approximation with uniform constants. |
| Lemma 5.1 | **Existing conclusion** | Positive determinant–permanent convolution for actual Hamilton path counts, including empty and singleton cases. |
| Lemma 6.1 | **Partial coverage** | The cotangent operator bound and old C_* spectral bound have endpoints. The added bound rho <= (3n-1)/(n+1) < 3 has no new endpoint. |
| Theorem 6.2 | **Existing conclusion** | Tournament-matrix product comparison and suffix equality propagation. |
| Lemma 6.3 | **Existing conclusion** | Truncated-prefix comparison and equality rigidity. |
| Lemma 6.4 | **Existing conclusion** | Spectral extremality and signed-permutation classification, with a separate regular-carousel isomorphism bridge. |
| Lemma 6.5 | **Existing conclusion** | Integral sixth-moment deficit and quantitative spectral gap for regular non-carousel tournaments. |
| Historical Proposition 7.1 only | **Historical only** | The old C_* auxiliary bound, NOT the current sharp-L Proposition 7.1. |
| Lemma 7.2 | **Existing conclusion** | Permanent variance bound, with the correct factor between degree variance and score variance. |
| Theorem 8.1 | **Existing conclusion** | Uniform small-score Hamilton path asymptotics for score bounds o(sqrt(n)). |
| Corollary 8.2 | **Existing conclusion** | Explicit odd carousel and even one-vertex-deletion path counts attain L + O(1/n). |
| Theorem 9.2 | **Existing conclusion** | Analytic original-coordinate branch and its Hessian. The current short alternative derivation is not mapped step by step. |
| Corollary 10.2 | **Existing conclusion** | Actual path/cycle expectation limits in uniform and regular models, and their ratios. |
| Proposition 10.3 | **Existing conclusion** | Determinant, spectral-ratio and regular-carousel constant closed forms. |
| Corollary 10.5 | **Existing conclusion** | The same discrete odd-order monotonicity and limit as Corollary 1.5. |
| Corollary 11.2 | **Existing conclusion** | The same four-model eventual extremizer conclusion as Corollary 1.4. |
| Section 11.1 (companion Lemma 11.5) | **Existing conclusion** | Fair random augmentation identities and normalized expectation bridges; the order-one exception is retained. |
| Proposition 7.1 (current sharp-L bound) | **Same conclusion; different proof** | The sharp maximum endpoints imply the same uniform upper bound; the present 5.2 -> 6.6 -> 7.3 -> 7.1 proof chain is not mapped. |
| Lemma 5.2 | **No new endpoint** | Weighted convolution moments and the uniform long-deletion tail have no new endpoint. |
| Proposition 6.6 | **Composition not mapped** | Existing spectral and closed-form components do not constitute a mapped endpoint for this all-order composition. |
| Proposition 7.3 | **No new endpoint** | The score-sensitive upper bound retaining exp(-tau/2 + K_1/n) has no new endpoint; a global sharp bound does not substitute for it. |
| Theorem 1.2 / Corollary 8.3 | **No new endpoint** | Degree stability V_deg <= C(epsilon*n^2+n), and O(n) variance for exact maximizers, have no new endpoint. This does not assert regularity, edit-distance stability or carousel isomorphism. |
| Section 1.2, remark after Theorem 1.2 | **No new endpoint** | For even n, every tournament has V_deg >= n/4 by integrality of outdegrees. Together with Corollary 8.3 this gives V_deg = Theta(n) for exact maximizers. No new Lean endpoint. |
| Corollary 8.4 | **No new endpoint** | With delta=(P(n)-H(T))/mu_n, absolute C,N work uniformly for n>=N and 0<=delta<=(L-1)/4: V_deg(T)<=C(delta*n^2+n). In particular an O(mu_n/n) count gap gives O(n) variance. No new Lean endpoint. |

## Key named endpoints

### Theorem 1.1

- [`TournamentHamiltonian.sharp_path_asymptotic`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/1b66d66cd287310c3a85dc3c64816fa319d55af2/formal/TournamentHamiltonian/SharpMain.lean#L26).
- [`TournamentHamiltonian.sharp_path_normalized_error`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/1b66d66cd287310c3a85dc3c64816fa319d55af2/formal/TournamentHamiltonian/SharpMain.lean#L34).
- [`TournamentPaths.maxPathCountFinite_eq_legacy`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/1b66d66cd287310c3a85dc3c64816fa319d55af2/formal/Tournament/SharpBound.lean#L47).
- [`PaperCarouselPath.corollary8_2`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/1b66d66cd287310c3a85dc3c64816fa319d55af2/formal/TournamentHamiltonian/PaperCarouselPath/Endpoint.lean#L56).

### Theorem 1.3 (formerly 1.2)

- [`Tournament.wormald_original_angle_hessian`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/1b66d66cd287310c3a85dc3c64816fa319d55af2/formal/Tournament/HessianTheorem.lean#L29).

### Proposition 7.1 (current sharp-L bound)

- [`TournamentHamiltonian.sharp_path_asymptotic`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/1b66d66cd287310c3a85dc3c64816fa319d55af2/formal/TournamentHamiltonian/SharpMain.lean#L26).
- [`TournamentHamiltonian.sharp_path_normalized_error`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/1b66d66cd287310c3a85dc3c64816fa319d55af2/formal/TournamentHamiltonian/SharpMain.lean#L34).
- [`TournamentPaths.maxPathCountFinite_eq_legacy`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/1b66d66cd287310c3a85dc3c64816fa319d55af2/formal/Tournament/SharpBound.lean#L47).

### Historical Proposition 7.1 only

- [`PaperEndpointWrappersB.mainBound`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/1b66d66cd287310c3a85dc3c64816fa319d55af2/formal/TournamentHamiltonian/PaperEndpointWrappersB/MainBound.lean#L37).
- [`PaperEndpointWrappersB.proposition7_1`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/1b66d66cd287310c3a85dc3c64816fa319d55af2/formal/TournamentHamiltonian/PaperEndpointWrappersB/MainBound.lean#L55).

Neither Proposition 7.3, Theorem 1.2 / Corollary 8.3, the even-order variance remark, nor Corollary 8.4 has a new endpoint. In particular, the old Hessian Theorem 1.2 is now Theorem 1.3; it must not be presented as formal evidence for the new degree-stability Theorem 1.2.

## Rechecking this index

Run `python3 review/revision-20261111-round2/check_lean_coverage.py` from the repository root. A passing result concerns metadata and source identity only, not Lean compilation or mathematical proof verification.
