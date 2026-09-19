# Formalization coverage

This matrix describes the checked Lean source, not an intended future development. The status
labels mean:

- **Verified**: proved from definitions and ordinary lower-level hypotheses in the library.
- **Verified under explicit interface**: the mathematical reduction is proved, but a named
  interface supplies external stochastic, geometric, or model data.
- **Assumed model condition**: retained as a hypothesis of the final projected theorem.
- **Out of scope**: no theorem in the current library provides this construction or result.
- **Source discrepancy**: the official v3 PDF contains a displayed identity inconsistent with
  its earlier SEM algebra; the development formalizes the corrected identity instead.

| Topic | Status | Main Lean definitions/theorems | Notes |
|---|---|---|---|
| Simplex coordinate and `sqNorm` bounds | Verified | `IsSimplex`, `simplex_coordinate_bounds`, `simplex_sqNorm_bounds` | Uses the explicit finite sum `sqNorm`, not the default norm on `Fin m → ℝ`. |
| Matrix quadratic identities | Verified | `matrixQuad_add`, `matrixQuad_smul`, `matrixQuad_sum`, `negDRO_q_decomposition` | Finite matrices and coordinate quadratic forms. |
| Fixed-witness curvature transfer | Verified under explicit interface | `fixedWitness_curvature_transfer`, `fixedWitness_direction_explicit` | Requires covariance quadratic nonnegativity and curvature at a fixed witness. |
| Vector Young inequality | Verified | `vector_young_exact` | Derived from a finite sum of coordinatewise squares with the project constants. |
| Population risk expansion from actual moments | Verified | `finitePopulationSquaredRisk_eq_momentRisk`, `finitePopulationSquaredRisk_eq_expandedEnvironmentalRisk` | This is the expanded environmental-risk identity used in Appendix Lemma 1, not official v3 Eq. (13). |
| Corrected additive SEM elimination | Verified / Source discrepancy | `semSchur_mulVec`, `semCovariate_eq_of_structuralEquations`, `semCovariate_eq_inverseNoise`, `scalar_block_inverse_sign_audit` | Eq. (10) forces the positive `GT BYX` term; printed Eq. (97) has the opposite sign. |
| Additive SEM moment relations | Verified under explicit interface | `additiveIntervention_crossMomentRelation`, `additiveIntervention_outcomeMomentRelation`, family-level wrappers | Primitive integrability and systematic/intervention orthogonality remain assumptions. |
| Covariance symmetry and quadratic nonnegativity | Verified | `populationSecondMomentMatrix_symmetric`, `populationSecondMomentMatrix_quadNonneg`, `additiveInterventionFamily_sigmaIsSymm`, `additiveInterventionFamily_sigmaQuadNonneg` | Proved for actual coordinate second moments. The library does not claim every weighted heterogeneity matrix is PSD. |
| Spectral eigenvalue lower bound to curvature | Verified under explicit interface | `shifted_posSemidef_of_le_eigenvalues`, `curvatureAtLeast_of_le_eigenvalues`, `SpectralWitnessAtLeast.curvatureAtLeast` | The eigenvalue lower bound itself is a final hypothesis. |
| Common-term and comparator identities | Verified | `common_unpenalized_identity`, `common_penalized_identity`, `expandedUnpenalizedComparatorIdentity`, `expandedPenalizedComparatorIdentity` | Covers the scalar algebra corresponding to Appendix equations (64)-(67). |
| Concrete primal coefficient pairing | Verified | `expandedPrimalCoefficient_pairing_eq_fixedWitnessDirectionalForm`, `expandedPenalizedPrimalCoefficient_pairing_eq_directionalForm` | Identifies the coordinate coefficient pairing used in the primal recursion. |
| Real radial derivative | Verified | `hasDerivAt_expandedRadialObjective`, `hasDerivAt_expandedPenalizedRadialObjective`, coefficient derivative wrappers | A one-dimensional radial derivative at `t = 1`, not a general Fréchet-gradient theorem. |
| Dual objective linearization | Verified | `expandedObjective_sub_eq_vectorDot_dualGradient`, `expandedPenalizedObjective_sub_le_linearization` | Penalized linearization uses `μ ≥ 0`. |
| Entropy geometry | Verified | `entropyBregman_three_point`, `entropyBregman_uniformWeight_le_log` | Comparator coordinates may be zero. |
| Explicit exponentiated-gradient update | Verified | `egUpdate`, `egUpdate_isPositiveSimplex`, `eg_bregman_decomposition_current` | Uses the ascent sign `+ηg_i`. |
| Finite Pinsker with unnormalized `l1Dist` | Verified | `entropyBregman_eq_finiteKL`, `finitePinsker`, `egUpdate_finitePinsker` | Proves `l1Dist(p,q)^2 / 2 ≤ entropyBregman p q`; no hidden total-variation factor. |
| Dual trajectory regret | Verified | `egTrajectory_cumulative_linearizedRegret_uniform`, `expected_randomEGTrajectory_cumulative_linearizedRegret_of_condMoment_le`, stochastic objective-regret wrappers | The deterministic and expected telescoping chains are both present. |
| Actual Euclidean projection | Verified | `euclideanProjection_unique`, `euclideanProjection_pythagorean`, `euclideanProjection_nonexpansive`, `coordinateEuclideanProjection_hasProjectionDistanceBound` | Constructed for every nonempty closed convex set and transported through an explicit coordinate/Euclidean bridge. |
| Deterministic primal recursion | Verified under explicit interface | `projectedGradientStep_sqDist_le`, `primalTrajectory_scalarRecursion` | Reusable recursion assumes Fejér and feasibility interfaces; the final projected wrappers discharge them with the actual projection. |
| Scalar conditional-expectation bridge | Verified under explicit interface | `integral_mul_condExp_of_predictable`, `integral_mul_eq_of_condExp_ae_eq` | Requires the stated integrability, predictability, boundedness, and sigma-finiteness hypotheses. |
| Predictable vector pairing | Verified under explicit interface | `integral_vectorDot_eq_of_coordinatewise_condExp_ae_eq` | Coordinatewise a.e. conditional unbiasedness is sufficient; no independence is used. |
| Expected primal recursion | Verified under explicit interface | `expected_primal_recursion_of_condExpectedSqNorm_le`, `stochasticPrimalTrajectory_expected_recursion` | Converts conditional oracle bounds and predictable pairings into the expected distance recursion. |
| Fresh conditional sampling law | Assumed model condition | `HasFreshUniformFiniteEnvironmentLaw`, `freshLaw_condExp_selected`, `freshLaw_toFreshRawMoments` | The interface quantifies over every integrable test function. Its consequences are proved, but an explicit sample stream satisfying it is not constructed. |
| Oracle conditional unbiasedness | Verified under explicit interface | `samplePrimalOracle_condUnbiased_expanded`, `sampleUnpenalizedDualOracle_condUnbiased_expanded`, `samplePenalizedDualOracle_condUnbiased_expanded` | Derived from the universal fresh law, predictable iterates, and population moment relations. |
| Concrete oracle integrability | Verified under explicit interface | `integrable_concreteTrajectoryPrimalOracle_coordinate_of_fresh`, `integrable_concreteTrajectoryPrimalOracle_sqNorm_of_fresh`, `integrable_concreteTrajectoryDualOracle_coordinate_of_fresh`, `integrable_concreteTrajectoryDualSize_sq_of_fresh` | Selected mixed/fourth moments, bounded primal iterates, simplex dual iterates, and finite-measure `L² -> L¹` derive all four former technical fields. |
| Explicit oracle moment constants | Verified under explicit interface | `condExp_samplePrimalOracle_sqNorm_le_explicit`, `condExp_sampleDualCoordinateBound_sq_le_explicit`, `concreteTrajectoryPrimal_condMoment_le_explicit`, `concreteTrajectoryDualSize_unpenalized_condMoment_le_explicit`, `concreteTrajectoryDualSize_penalized_condMoment_le_explicit` | Fourth-moment bounds are hypotheses; the displayed constants are derived and already squared quantities. |
| Stochastic dual objective regret | Verified under explicit interface | `stochasticEG_cumulative_unpenalized_objectiveRegret`, `stochasticEG_cumulative_penalized_objectiveRegret` | Uses the same random gradient sequence for the EG update and sampled pairing. |
| Finite-time convergence | Verified under explicit interface | `stochasticNegDRO_additiveSampling_projected_unpenalized_convergence`, penalized counterpart | Final theorem assumes the model, fresh law, spectral condition, and bounded-domain geometry; oracle integrability is now derived. |
| Averaged iterate | Verified under explicit interface | `integral_sqDist_randomPrimalAverage_le_average_integral_sqDist`, the two projected averaged convergence theorems | Bounds `E[sqDist bar_b_T betaStar]`; it is not a last-iterate result. |
| Inverse-square-root rates | Verified under explicit interface | the two projected `*_invSqrt_rate` theorems | Exact specialization `η_b = η_w = 1 / sqrt T`. No `Asymptotics` wrapper is claimed. |
| RMS square-root consequence | Verified under explicit interface | `rms_le_sqrt_bias_add_quarter_rate` | A scalar consequence of an supplied squared-error upper bound, not an expected-norm theorem. |
| Concrete one-round product-space or infinite fresh-stream construction | Out of scope | None | The final theorem assumes `HasFreshUniformFiniteEnvironmentLaw` at each round. |
| Full original SEM/acyclicity assembly into the final wrapper | Out of scope | Partial elimination: `semCovariate_eq_of_structuralEquations` | The final wrapper receives `GT` and realized reduced-form maps directly; it does not derive them from `BXX`, acyclicity, and a block SEM. |
| Literal official v3 Algorithm 1 | Out of scope | None | Official Algorithm 1 performs exact empirical-risk maximization in `w`; the formalized algorithm performs simultaneous stochastic projected-SGD/EG updates. |
| Formal `Asymptotics.IsBigO` rate wrapper | Out of scope | None | The library proves explicit inequalities with `1 / sqrt T` instead. |

The project gives a complete Lean-verified conditional convergence proof for its
finite-dimensional corrected-additive-model, fresh-sample, nearest-point-projected SGD/EG
stochastic NegDRO extension: concrete oracle unbiasedness, moment bounds, oracle integrability,
entropy regret, primal recursion, spectral curvature, Euclidean projection, finite-time bounds,
averaged-iterate bounds, and inverse-square-root rates are all derived from the final stated
model, sampling, moment, spectral, and feasible-set assumptions.
