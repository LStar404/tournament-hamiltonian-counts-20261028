# Formal evidence and source anchors (Gemini revision, 2026-11-11)

This is a reading index, not a new Lean build or formal proof of the revised manuscript. All source/evidence links below use the already published base `6d960c34a7827d8e4c8409b967dc403c468388f2`. The historical build input remains `c678e9ee24fb304cad755a27c99f511c8640f75e`. Existing endpoints certify their exact conclusions and hypotheses, not every revised proof.

## Scope and trust boundary

The formal development includes continuous analysis as well as discrete and algebraic arguments: complex analyticity of the original determinant branch and logarithm, real Fréchet second derivatives, Gaussian/series estimates, and asymptotic expectation limits. In particular, the uniform and regular expectation endpoints take a genuine regular base tournament and positive order as hypotheses; they do not take a Wormald limit or Hessian identity as an unproved premise. This does not claim to formalize every theorem or proof in Wormald's papers. The manuscript's cited model-limit route and the existing Lean internal proof route must be distinguished.

The pinned dependency is upstream `leanprover-community/mathlib4`, revision `56a005855ea17e0b0958f73ec801ae140b0a1679`, with Lean 4.35.0. The manifest and lakefile do not select a fork. The historical run records tracked-clean dependency checkouts; this reading audit does not inspect a fresh dependency checkout or claim a fresh upstream rebuild.

The historical run on 2026-11-07 (16:40:36–17:04:14 UTC) records 609 freshly compiled production modules, 3067 registered endpoints, 223 key endpoint checks, and only `propext`, `Classical.choice`, `Quot.sound` in the recursive registered-endpoint axiom audit. Upstream caches were reused. No claim of “axiom-free” foundations is made. The source scanner rejects `sorry`, `admit`, `axiom`, `unsafe`, and `native_decide` in production code after removing comments and strings. That scanner and the existing metadata checker passed in this revision; neither constitutes Lean compilation or a fresh recursive axiom audit.

- [Historical run and limitations](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/review/lean-rerun-20261107/summary.json)
- [Historical input hashes](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/review/lean-rerun-20261107/input_manifest.json)
- [Historical verification logs](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/review/lean-rerun-20261107/verification_logs.zip)
- [Dependency declaration](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/lakefile.toml)
- [Dependency lock](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/lake-manifest.json)
- [Source scanner](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/scripts/check_sources.py)
- [Recursive axiom-audit implementation](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/scripts/audit_axioms.py)
- [Exact historical printed types](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/coverage.json)
- [Detailed historical correspondence](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/review/revision-20261111/lean_correspondence.md)
- [Previous English mapping](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/review/revision-20261111-round2/lean_coverage.en.md)

## Direct analytic anchors

- [Original angle and actual iterated real derivative](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/Tournament/HessianMain.lean#L30)
- [Original-coordinate branch analyticity](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/Tournament/OriginalCoordinates.lean#L202)
- [Original logarithm analyticity](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/Tournament/OriginalCoordinates.lean#L225)
- [Original exponential-coordinate analyticity](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/Tournament/OriginalCoordinates.lean#L235)
- [Hessian identity, positivity, determinant and positive rational square root](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/Tournament/HessianTheorem.lean#L29)
- [Uniform actual cycle and path expectation limits](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/UniformFinal/UniformExpectationLimit.lean#L22)
- [Regular actual expectation limits and regular/uniform ratios](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/RegularExpectation/Endpoint.lean#L22)

## Existing manuscript mapping, with exact declaration anchors

All 37 rows of the previous English mapping are retained below. “Existing conclusion” never means that a new Schur-complement proof or explanatory estimate has been checked. The new Hessian conditioning/explanatory bounds in this revision have no new mapped endpoint. Proposition 7.3 and the degree-stability statements likewise have no new endpoint. Historical Proposition 7.1 is not current Proposition 7.1; historical Theorem 1.2 is current Hessian Theorem 1.3, not degree-stability Theorem 1.2.

### Theorem 1.1

conclusion with existing endpoint. Sharp asymptotic for the actual maximum Hamilton path count, with absolute uniform constants.

- [`TournamentHamiltonian.sharp_path_asymptotic`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/SharpMain.lean#L26)
- [`TournamentHamiltonian.sharp_path_normalized_error`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/SharpMain.lean#L34)
- [`TournamentPaths.maxPathCountFinite_eq_legacy`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/Tournament/SharpBound.lean#L47)
- [`PaperCarouselPath.corollary8_2`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/PaperCarouselPath/Endpoint.lean#L56)

### Theorem 1.3 (formerly 1.2)

conclusion with existing endpoint. Original-angle Hessian identity, positivity and determinant formula. The present short Schur-complement proof is not mapped step by step.

- [`Tournament.wormald_original_angle_hessian`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/Tournament/HessianTheorem.lean#L29)

### Corollary 1.4 (formerly 1.3)

conclusion with existing endpoint. Eventual unique carousel extremizers in all four blow-up models, with a common threshold for all base tournaments of each fixed odd order.

- [`FiniteExtremum.eventual_four_models_of_odd`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/FiniteExtremum/Endpoint.lean#L45)
- [`FiniteExtremum.UniformMaximumAt`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/FiniteExtremum/Comparison.lean#L64)
- [`FiniteExtremum.RegularMaximumAt`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/FiniteExtremum/Comparison.lean#L70)
- [`FiniteFamilyGap.CarouselClass`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/FiniteFamilyGap/Scores.lean#L15)
- [`FiniteExtremum.eventual_four_strict_outside`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/FiniteExtremum/Endpoint.lean#L54)

### Corollary 1.5 (formerly 1.4)

conclusion with existing endpoint. Strict monotonicity and limit of the regular-carousel constants.

- [`TournamentHamiltonian.regularCarouselConstant_monotone_convergent`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/Carousel/Monotonicity.lean#L39)
- [`TournamentHamiltonian.regularCarouselConstant_closed_form`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/Carousel/CarouselConstants.lean#L18)

### Theorem 3.1

conclusion with existing endpoint. Uniform permanent approximation for bounded doubly centred perturbations with a fixed operator-norm gap.

- [`PaperEndpointsA.paper_3_1_uniform_constant`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/PaperEndpointsA/Permanent31.lean#L59)
- [`PaperEndpointsA.paper_3_1_determinant`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/PaperEndpointsA/Permanent31.lean#L47)
- [`PaperEndpointsA.paper_3_1_relative`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/PaperEndpointsA/Permanent31.lean#L70)

### Technical appendix, Lemma 3.2

conclusion with existing endpoint. Summable weighted core-excess coefficients and first-excess estimate.

- [`PaperEndpointsA.paper_3_2`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/PaperEndpointsA/Activity32.lean#L50)
- [`PaperEndpointsA.paper_3_2_first`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/PaperEndpointsA/Activity32.lean#L59)

### Technical appendix, Lemma 3.3

conclusion with existing endpoint. Complex permanent polarization and nonnegativity for positive semidefinite matrices.

- [`TournamentHamiltonian.permanent_polarization`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/PermanentPolarization.lean#L191)
- [`TournamentHamiltonian.complex_posSemidef_permanent_nonnegative`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/PermanentPolarization.lean#L154)

### Technical appendix, Lemma 3.4

conclusion with existing endpoint. Complete-homogeneous and geometric permanent bounds, retaining spectral multiplicities.

- [`TournamentHamiltonian.complex_posSemidef_permanent_le_homogeneous`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/CircularPSDComparison.lean#L140)
- [`TournamentHamiltonian.complex_posSemidef_permanent_le_geometric`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/HomogeneousGeometricBound.lean#L90)
- [`TournamentHamiltonian.complex_posSemidef_permanent_nonnegative`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/PermanentPolarization.lean#L154)

### Technical appendix, Proposition 3.5

conclusion with existing endpoint. Gaussian recovery with the stated error budget and factorial second moment.

- [`PaperGaussianRecovery.paper_3_5`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/PaperGaussianRecovery/Endpoint.lean#L101)
- [`PaperGaussianRecovery.paper_3_5_normalized`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/PaperGaussianRecovery/Endpoint.lean#L56)
- [`PaperGaussianRecovery.factorial_second_hasSum`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/PaperGaussianRecovery/Series.lean#L106)

### Lemma 4.1

conclusion with existing endpoint. Local matrix scaling, including signed-input estimates and separate support/nonnegativity conclusions.

- [`TournamentHamiltonian.exists_local_scaling`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/LocalScalingEstimates.lean#L158)
- [`TournamentHamiltonian.localScaledMatrix_nonnegative`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/LocalScalingExistence.lean#L436)
- [`TournamentHamiltonian.localScaledMatrix_zero_support`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/LocalScalingExistence.lean#L441)

### Lemma 4.2

conclusion with existing endpoint. Displacement, capacity and mass-restored normalization bounds.

- [`TournamentHamiltonian.exists_local_scaling_displacement_capacity`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/LocalScalingCapacity.lean#L144)
- [`TournamentHamiltonian.exists_normalized_local_scaling_witness`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/LocalScalingComplete.lean#L69)
- [`TournamentHamiltonian.massRestoredLocalPotentials_capacity`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/LocalScalingNormalization.lean#L22)

### Lemma 4.3

conclusion with existing endpoint. Gram-determinant deletion, centering and Lipschitz estimates.

- [`TournamentHamiltonian.gramGaussian_deletion_bound`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/GramDeletion.lean#L310)
- [`TournamentHamiltonian.gramGaussian_centering_bound`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/GramCentering.lean#L196)
- [`TournamentHamiltonian.gramGaussian_log_lipschitz`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/GramLipschitz.lean#L214)

### Lemma 4.4

conclusion with existing endpoint. Uniform paired Gaussian estimates for independent row and column deletion sets of equal size.

- [`TournamentHamiltonian.adjacency_nonprincipal_gaussian_uniform_log`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/UniformPairedPermanentGaussian.lean#L18)

### Lemma 4.5

conclusion with existing endpoint. Small-score relative permanent approximation with uniform constants.

- [`PaperEndpointWrappersB.lemma4_5`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/PaperEndpointWrappersB/SmallScore.lean#L30)
- [`PaperEndpointWrappersB.lemma4_5_actual_score`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/PaperEndpointWrappersB/SmallScore.lean#L66)
- [`PaperEndpointWrappersB.lemma4_5_relative_actual_score`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/PaperEndpointWrappersB/Relative.lean#L26)

### Lemma 5.1

conclusion with existing endpoint. Positive determinant–permanent convolution for actual Hamilton path counts, including empty and singleton cases.

- [`TournamentPaths.pathCountFinite_eq_pathConvolutionSum`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/Tournament/PathConvolution.lean#L87)
- [`TournamentPaths.pathCount_eq_positive_convolution`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/Tournament/PathConvolution.lean#L99)
- [`TournamentPaths.empty_path_convolution`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/Tournament/PathConvolution.lean#L112)
- [`TournamentPaths.singleton_path_convolution`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/Tournament/PathConvolution.lean#L116)

### Lemma 6.1

partial conclusion. The cotangent operator bound and old C_* spectral bound have endpoints. The added bound rho <= (3n-1)/(n+1) < 3 has no new endpoint.

- [`TournamentHamiltonian.signMatrix_complex_opNorm_le_cot`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/TransitiveCotSpectrum.lean#L342)
- [`TournamentHamiltonian.transitive_cot_lt_two_mul_div_pi`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/TransitiveCotSpectrum.lean#L347)
- [`TournamentHamiltonian.spectralRatio_le_upperConstant`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/OperatorCap.lean#L365)

### Theorem 6.2

conclusion with existing endpoint. Tournament-matrix product comparison and suffix equality propagation.

- [`TournamentHamiltonian.Equality.tournament_list_product_comparison_and_suffixes`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/SpectralSupplement/ProductComparison.lean#L160)

### Lemma 6.3

conclusion with existing endpoint. Truncated-prefix comparison and equality rigidity.

- [`TournamentHamiltonian.Equality.truncated_prefix_max_chain`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/SpectralSupplement/TruncatedPrefix.lean#L93)
- [`TournamentHamiltonian.finite_sum_sq_le_of_prefix_le`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/FiniteVectorOrder.lean#L117)
- [`TournamentHamiltonian.eq_of_finPrefix_le_of_sq_sum_eq`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/Equality/PrefixEquality.lean#L17)

### Lemma 6.4

conclusion with existing endpoint. Spectral extremality and signed-permutation classification, with a separate regular-carousel isomorphism bridge.

- [`PaperSpectralOrbit.paper_6_4`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/PaperSpectralOrbit/Endpoint.lean#L58)
- [`PaperSpectralOrbit.signed_class_iff_paper_conjugation`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/PaperSpectralOrbit/Endpoint.lean#L40)
- [`TournamentHamiltonian.Equality.tournament_exists_signed_permutation_conjugation`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/Equality/SignedPermutationMatrix.lean#L44)
- [`TournamentHamiltonian.Equality.signedPermutationMatrix_orthogonal`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/Equality/SignedPermutationMatrix.lean#L32)
- [`TournamentPaths.regular_pathSpectralRatio_eq_carousel_iff_relabel`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/Tournament/SpectralClassification.lean#L67)

### Lemma 6.5

conclusion with existing endpoint. Integral sixth-moment deficit and quantitative spectral gap for regular non-carousel tournaments.

- [`TournamentHamiltonian.Equality.sixth_moment_gap_sixteen_of_not_signedPermutationTransitive`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/Equality/SpectralClassification.lean#L132)
- [`TournamentHamiltonian.Equality.sixteen_dvd_intSignMatrix_cube_frob_sub_cube_frob`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/Equality/SixthMomentDivisibility.lean#L167)
- [`TournamentHamiltonian.Equality.regular_noncarousel_quantitative_spectral_gap`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/SpectralSupplement/QuantitativeGap.lean#L104)

### Historical Proposition 7.1 only

historical only. The old C_* auxiliary bound, NOT the current sharp-L Proposition 7.1.

- [`PaperEndpointWrappersB.mainBound`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/PaperEndpointWrappersB/MainBound.lean#L37)
- [`PaperEndpointWrappersB.proposition7_1`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/PaperEndpointWrappersB/MainBound.lean#L55)

### Lemma 7.2

conclusion with existing endpoint. Permanent variance bound, with the correct factor between degree variance and score variance.

- [`PaperEndpointWrappersB.lemma7_2`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/PaperEndpointWrappersB/Variance.lean#L23)

### Theorem 8.1

conclusion with existing endpoint. Uniform small-score Hamilton path asymptotics for score bounds o(sqrt(n)).

- [`TournamentHamiltonian.small_score_pathCount_spectral_approximation_eventually`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/GeneralSmallScoreAsymptotic.lean#L70)
- [`TournamentHamiltonian.small_score_pathCount_spectral_error_eventually_small`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/GeneralSmallScoreAsymptotic.lean#L83)

### Corollary 8.2

conclusion with existing endpoint. Explicit odd carousel and even one-vertex-deletion path counts attain L + O(1/n).

- [`PaperCarouselPath.carousel_pathCounts_error_bound`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/PaperCarouselPath/Endpoint.lean#L15)
- [`PaperCarouselPath.corollary8_2`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/PaperCarouselPath/Endpoint.lean#L56)

### Theorem 9.2

conclusion with existing endpoint. Analytic original-coordinate branch and its Hessian. The current short alternative derivation is not mapped step by step.

- [`Tournament.wormald_original_angle_hessian`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/Tournament/HessianTheorem.lean#L29)
- [`Tournament.OriginalCoordinates.regular_original_branch_analytic`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/Tournament/OriginalCoordinates.lean#L202)
- [`Tournament.OriginalCoordinates.regular_original_rawLog_analytic`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/Tournament/OriginalCoordinates.lean#L225)
- [`Tournament.OriginalCoordinates.regular_original_rawLog_exp_analytic`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/Tournament/OriginalCoordinates.lean#L235)

### Corollary 10.2

conclusion with existing endpoint. Actual path/cycle expectation limits in uniform and regular models, and their ratios.

- [`UniformDenseLimit.uniform_avgCycle_tendsto`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/UniformFinal/UniformExpectationLimit.lean#L22)
- [`UniformDenseLimit.uniform_avgPath_tendsto`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/UniformFinal/UniformExpectationLimit.lean#L38)
- [`RegularExpectation.regular_avgCycle_tendsto`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/RegularExpectation/Endpoint.lean#L42)
- [`RegularExpectation.regular_avgPath_tendsto`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/RegularExpectation/Endpoint.lean#L52)
- [`RegularExpectation.regular_expectations_tendsto`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/RegularExpectation/Endpoint.lean#L60)
- [`RegularExpectation.regular_uniform_cycle_ratio_tendsto`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/RegularExpectation/Endpoint.lean#L22)
- [`RegularExpectation.regular_uniform_path_ratio_tendsto`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/RegularExpectation/Endpoint.lean#L31)

### Proposition 10.3

conclusion with existing endpoint. Determinant, spectral-ratio and regular-carousel constant closed forms.

- [`TournamentHamiltonian.transitiveKernel_det`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/TransitiveDeterminant.lean#L172)
- [`TournamentHamiltonian.carouselTournament_kernel_det`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/Carousel.lean#L283)
- [`TournamentHamiltonian.carousel_spectralRatio_eq`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/SkewSpectrum.lean#L570)
- [`TournamentHamiltonian.transitiveRatio_eq_binomialMean`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/PowerApproximation.lean#L83)
- [`TournamentHamiltonian.carouselTournament_score`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/Carousel.lean#L209)
- [`TournamentHamiltonian.regularCarouselConstant_closed_form`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/Carousel/CarouselConstants.lean#L18)
- [`TournamentHamiltonian.carousel_spectralRatio_order_three`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/Carousel/ClosedValues.lean#L8)
- [`TournamentHamiltonian.carousel_spectralRatio_order_five`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/Carousel/ClosedValues.lean#L13)
- [`TournamentHamiltonian.carousel_spectralRatio_order_seven`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/Carousel/ClosedValues.lean#L18)
- [`RegularExpectation.regular_avgCycle_tendsto`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/RegularExpectation/Endpoint.lean#L42)
- [`RegularExpectation.regular_avgPath_tendsto`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/RegularExpectation/Endpoint.lean#L52)

### Corollary 10.5

conclusion with existing endpoint. The same discrete odd-order monotonicity and limit as Corollary 1.5.

- [`TournamentHamiltonian.regularCarouselConstant_monotone_convergent`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/Carousel/Monotonicity.lean#L39)
- [`TournamentHamiltonian.regularCarouselConstant_closed_form`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/Carousel/CarouselConstants.lean#L18)

### Corollary 11.2

conclusion with existing endpoint. The same four-model eventual extremizer conclusion as Corollary 1.4.

- [`FiniteExtremum.eventual_four_models_of_odd`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/FiniteExtremum/Endpoint.lean#L45)
- [`FiniteExtremum.UniformMaximumAt`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/FiniteExtremum/Comparison.lean#L64)
- [`FiniteExtremum.RegularMaximumAt`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/FiniteExtremum/Comparison.lean#L70)
- [`FiniteFamilyGap.CarouselClass`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/FiniteFamilyGap/Scores.lean#L15)
- [`FiniteExtremum.eventual_four_strict_outside`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/FiniteExtremum/Endpoint.lean#L54)

### Section 11.1 (companion Lemma 11.5)

conclusion with existing endpoint. Fair random augmentation identities and normalized expectation bridges; the order-one exception is retained.

- [`TournamentPaths.augmentation_average`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/Tournament/Paths.lean#L162)
- [`TournamentPaths.one_vertex_average_not_quarter`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/Tournament/Paths.lean#L193)
- [`NonregularNormalization.meanPaths_eq_four_meanCycles_succ`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/NonregularNormalization/PathRate.lean#L73)
- [`PaperAugmentationNormalization.normalized_augmentation`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/PaperAugmentationNormalization/Endpoint.lean#L10)
- [`PaperAugmentationNormalization.normalized_finite_augmentation`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/PaperAugmentationNormalization/Endpoint.lean#L28)

### Proposition 7.1 (current sharp-L bound)

same conclusion alternative proof. The sharp maximum endpoints imply the same uniform upper bound; the present 5.2 -> 6.6 -> 7.3 -> 7.1 proof chain is not mapped.

- [`TournamentHamiltonian.sharp_path_asymptotic`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/SharpMain.lean#L26)
- [`TournamentHamiltonian.sharp_path_normalized_error`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/TournamentHamiltonian/SharpMain.lean#L34)
- [`TournamentPaths.maxPathCountFinite_eq_legacy`](https://github.com/LStar404/tournament-hamiltonian-counts-20261028/blob/6d960c34a7827d8e4c8409b967dc403c468388f2/formal/Tournament/SharpBound.lean#L47)

### Lemma 5.2

no new endpoint. Weighted convolution moments and the uniform long-deletion tail have no new endpoint.

- No new mapped endpoint.

### Proposition 6.6

composition not mapped. Existing spectral and closed-form components do not constitute a mapped endpoint for this all-order composition.

- No new mapped endpoint.

### Proposition 7.3

no new endpoint. The score-sensitive upper bound retaining exp(-tau/2 + K_1/n) has no new endpoint; a global sharp bound does not substitute for it.

- No new mapped endpoint.

### Theorem 1.2 / Corollary 8.3

no new endpoint. Degree stability V_deg <= C(epsilon*n^2+n), and O(n) variance for exact maximizers, have no new endpoint. This does not assert regularity, edit-distance stability or carousel isomorphism.

- No new mapped endpoint.

### Section 1.2, remark after Theorem 1.2

no new endpoint. For even n, every tournament has V_deg >= n/4 by integrality of outdegrees. Together with Corollary 8.3 this gives V_deg = Theta(n) for exact maximizers. No new Lean endpoint.

- No new mapped endpoint.

### Corollary 8.4

no new endpoint. With delta=(P(n)-H(T))/mu_n, absolute C,N work uniformly for n>=N and 0<=delta<=(L-1)/4: V_deg(T)<=C(delta*n^2+n). In particular an O(mu_n/n) count gap gives O(n) variance. No new Lean endpoint.

- No new mapped endpoint.

## Reproduction commands and their scope

From the repository root, `python3 formal/scripts/check_sources.py` checks production source tokens. `python3 review/revision-20261111-round2/check_lean_coverage.py` checks the previous English mapping, source identity and pinned evidence (37 rows, 85 endpoint identities); it does not certify the new manuscript statements or this index as a Lean proof.

For a Lean build and registered-endpoint recursive axiom audit in a correctly provisioned pinned environment, run `bash formal/scripts/verify.sh`. This invokes the source check, `lake build`, and `python3 scripts/audit_axioms.py` inside `formal/`; it is not necessarily a cache-free build. The precise historical fresh-project run and key-type commands are recorded in the linked historical summary. No Lean compilation, new type printing, or new recursive axiom audit was run for this index.
