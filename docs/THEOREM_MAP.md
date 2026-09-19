# Theorem map

This map is organized by mathematical dependency. It lists declarations that expose a reusable
mathematical interface; it intentionally omits routine finite-sum and measurability helpers.
Names below were checked against the current source tree.

## 1. Finite-dimensional algebra

| Mathematical statement | Lean declaration | Source | Immediate dependencies | Main downstream users |
|---|---|---|---|---|
| Explicit coordinate dot product and quadratic form | `vectorDot`, `matrixQuad` | [`QuadraticStructure.lean`](../NegDROFormalization/QuadraticStructure.lean) | Mathlib finite sums and matrices | Almost every deterministic objective module |
| Linear decomposition of the NegDRO quadratic form | `negDRO_q_decomposition` | [`QuadraticStructure.lean`](../NegDROFormalization/QuadraticStructure.lean) | `matrixQuad_sum`, `negDROQ` | `fixedWitness_curvature_transfer` |
| Curvature transfer from the heterogeneity witness to `Q(w0)` | `fixedWitness_curvature_transfer` | [`QuadraticStructure.lean`](../NegDROFormalization/QuadraticStructure.lean) | covariance `QuadNonneg`, coefficient signs, `negDRO_q_decomposition` | `fixedWitness_direction_explicit` |
| Finite-vector Young inequality with exact constants | `vector_young_exact` | [`YoungVector.lean`](../NegDROFormalization/YoungVector.lean) | coordinate squares | fixed-witness direction bound |
| Simplex coordinate and squared-norm bounds | `simplex_coordinate_bounds`, `simplex_sqNorm_bounds` | [`Simplex.lean`](../NegDROFormalization/Simplex.lean) | `IsSimplex`, `sqNorm` | penalty bounds, EG and oracle bounds |
| Scalar comparator identities corresponding to (64)-(67) | `common_unpenalized_identity`, `common_penalized_identity`, `unpenalized_comparator_identity`, `penalized_comparator_identity` | [`Comparator.lean`](../NegDROFormalization/Comparator.lean) | real algebra | expanded comparator reductions |

## 2. Population objective

| Mathematical statement | Lean declaration | Source | Immediate dependencies | Main downstream users |
|---|---|---|---|---|
| Actual squared-loss integral equals its finite moment expansion | `finitePopulationSquaredRisk_eq_momentRisk` | [`PopulationRiskMomentBridge.lean`](../NegDROFormalization/PopulationRiskMomentBridge.lean) | integrable coordinate monomials | environmental-risk bridge |
| Moment risk equals the expanded environmental-risk form | `finitePopulationSquaredRisk_eq_expandedEnvironmentalRisk` | [`PopulationRiskMomentBridge.lean`](../NegDROFormalization/PopulationRiskMomentBridge.lean) | cross/outcome moment identities | additive population bridge |
| Weighted objective closed form | `expandedObjective_eq` | [`PopulationExpansion.lean`](../NegDROFormalization/PopulationExpansion.lean) | simplex coefficient sum, matrix quadratic linearity | comparator and primal coefficient modules |
| Expanded objective equals directional form plus common term | `expandedObjective_eq_directionalForm_add_common`, `expandedPenalizedObjective_eq_directionalForm_add_common` | [`PopulationExpansion.lean`](../NegDROFormalization/PopulationExpansion.lean) | common scalar identities | concrete comparator identities |
| Directional form is the derivative along the real radial path | `hasDerivAt_expandedRadialObjective`, `hasDerivAt_expandedPenalizedRadialObjective` | [`PopulationExpansion.lean`](../NegDROFormalization/PopulationExpansion.lean) | exact radial objective formulas | derivative interpretation of primal coefficient |
| Concrete coordinate coefficient pairs to the directional form | `expandedPrimalCoefficient_pairing_eq_fixedWitnessDirectionalForm`, `expandedPenalizedPrimalCoefficient_pairing_eq_directionalForm` | [`ExpandedPrimalCoefficient.lean`](../NegDROFormalization/ExpandedPrimalCoefficient.lean) | matrix symmetry and finite-sum expansion | stochastic primal direction lower bounds |
| Dual objective difference is exactly/at most its linearization | `expandedObjective_sub_eq_vectorDot_dualGradient`, `expandedPenalizedObjective_sub_le_linearization` | [`DualObjectiveLinearization.lean`](../NegDROFormalization/DualObjectiveLinearization.lean) | finite quadratic identities, `μ ≥ 0` in penalized case | expected and cumulative dual regret |

## 3. Corrected additive-intervention model

| Mathematical statement | Lean declaration | Source | Immediate dependencies | Main downstream users |
|---|---|---|---|---|
| Eq. (10) elimination gives `S X = BYX εY + εX` | `semSchur_mulVec` | [`AdditiveInterventionPopulationBridge.lean`](../NegDROFormalization/AdditiveInterventionPopulationBridge.lean) | displayed structural equations | corrected reduced-form solution |
| A supplied inverse `GT` gives the corrected reduced form | `semCovariate_eq_of_structuralEquations`, `semCovariate_eq_inverseNoise` | [`AdditiveInterventionPopulationBridge.lean`](../NegDROFormalization/AdditiveInterventionPopulationBridge.lean) | `semSchur_mulVec`, matrix product identity | model-level moment calculations |
| Scalar instance audits the sign of the inverse block | `scalar_block_inverse_sign_audit` | [`AdditiveInterventionPopulationBridge.lean`](../NegDROFormalization/AdditiveInterventionPopulationBridge.lean) | explicit `2 × 2` calculation | documentation of the Eq. (97) discrepancy |
| Corrected SEM cross and outcome moments | `additiveIntervention_crossMomentRelation`, `additiveIntervention_outcomeMomentRelation` | [`AdditiveInterventionPopulationBridge.lean`](../NegDROFormalization/AdditiveInterventionPopulationBridge.lean) | primitive integrability and zero cross moments | family-level moment interfaces |
| Actual SEM covariance is symmetric and quadratically nonnegative | `semSecondMoment_symmetric`, `semSecondMoment_quadNonneg` | [`AdditiveInterventionPopulationBridge.lean`](../NegDROFormalization/AdditiveInterventionPopulationBridge.lean) | actual second-moment integrals | final covariance family interfaces |
| Family-level corrected model interfaces | `additiveInterventionFamily_hasCrossMomentRelation`, `additiveInterventionFamily_hasOutcomeMomentRelation`, `additiveInterventionFamily_sigmaQuadNonneg`, `additiveInterventionFamily_sigmaIsSymm` | [`AdditiveInterventionPopulationInterfaces.lean`](../NegDROFormalization/AdditiveInterventionPopulationInterfaces.lean) | model-level theorems above | sampling and spectral assembly |
| Sampling-law moments coincide with model integrals | `additiveInterventionFreshLaw_toFreshPopulationMoments` | [`AdditiveInterventionSamplingBridge.lean`](../NegDROFormalization/AdditiveInterventionSamplingBridge.lean) | universal fresh law and model definitions | final additive sampling bundle |

## 4. Simplex and entropy geometry

| Mathematical statement | Lean declaration | Source | Immediate dependencies | Main downstream users |
|---|---|---|---|---|
| Exact negative-entropy three-point identity | `entropyBregman_three_point` | [`EntropyGeometry.lean`](../NegDROFormalization/EntropyGeometry.lean) | coordinate entropy definitions | EG one-step identities |
| Uniform initial entropy potential is at most `log m` | `entropyBregman_uniformWeight_le_log` | [`EntropyGeometry.lean`](../NegDROFormalization/EntropyGeometry.lean) | simplex entropy bounds, `m > 0` | trajectory regret |
| Bregman divergence equals finite KL for positive vectors | `entropyBregman_eq_finiteKL` | [`FinitePinsker.lean`](../NegDROFormalization/FinitePinsker.lean) | logarithm identities and simplex sums | finite Pinsker |
| Bregman divergence is nonnegative for a possibly boundary comparator | `entropyBregman_nonneg_of_isSimplex_of_pos` | [`FinitePinsker.lean`](../NegDROFormalization/FinitePinsker.lean) | scalar tangent inequality | terminal EG potential |
| Exact finite Pinsker normalization | `finitePinsker` | [`FinitePinsker.lean`](../NegDROFormalization/FinitePinsker.lean) | finite log-sum and binary Pinsker | mirror remainder bound |

## 5. Exponentiated gradient

| Mathematical statement | Lean declaration | Source | Immediate dependencies | Main downstream users |
|---|---|---|---|---|
| Normalized ascent update preserves a positive simplex | `egUpdate_isPositiveSimplex` | [`ExponentiatedGradient.lean`](../NegDROFormalization/ExponentiatedGradient.lean) | positive normalizer and exponential | EG trajectory invariant |
| Exact EG Bregman decomposition | `eg_bregman_decomposition_current` | [`ExponentiatedGradient.lean`](../NegDROFormalization/ExponentiatedGradient.lean) | logarithmic update and three-point identity | one-step mirror bound |
| Pinsker instantiated at the actual EG pair | `egUpdate_finitePinsker` | [`FinitePinsker.lean`](../NegDROFormalization/FinitePinsker.lean) | `finitePinsker`, EG positivity and simplex preservation | hypothesis-free mirror theorem |
| Final one-step EG mirror inequality | `eg_mirror_one_step`, `eg_mirror_hmirror` | [`FinitePinsker.lean`](../NegDROFormalization/FinitePinsker.lean) | exact decomposition, Hölder, completing the square, Pinsker | trajectory regret |
| Pathwise cumulative EG linearized regret | `egTrajectory_cumulative_linearizedRegret_uniform` | [`EGTrajectoryRegret.lean`](../NegDROFormalization/EGTrajectoryRegret.lean) | one-step mirror inequality, initial and terminal potentials | expected EG regret |

## 6. Euclidean projection

| Mathematical statement | Lean declaration | Source | Immediate dependencies | Main downstream users |
|---|---|---|---|---|
| Coordinate inner product, norm square, and distance square agree with `vectorDot`, `sqNorm`, and `sqDist` | `real_inner_toEuclidean`, `norm_sq_toEuclidean`, `dist_sq_toEuclidean` | [`EuclideanProjectionBridge.lean`](../NegDROFormalization/EuclideanProjectionBridge.lean) | `PiLp.continuousLinearEquiv` | transported projection |
| A nearest point exists and is unique | `euclideanProjection_mem`, `euclideanProjection_norm_eq_iInf`, `euclideanProjection_unique` | [`EuclideanProjectionBridge.lean`](../NegDROFormalization/EuclideanProjectionBridge.lean) | Mathlib `exists_norm_eq_iInf_of_complete_convex` | canonical projection map |
| Variational and Pythagorean inequalities | `euclideanProjection_variational`, `euclideanProjection_pythagorean` | [`EuclideanProjectionBridge.lean`](../NegDROFormalization/EuclideanProjectionBridge.lean) | nearest-point characterization | Fejér distance bound |
| Projection is nonexpansive and measurable | `euclideanProjection_nonexpansive`, `euclideanProjection_measurable` | [`EuclideanProjectionBridge.lean`](../NegDROFormalization/EuclideanProjectionBridge.lean) | two variational inequalities and Cauchy-Schwarz | stochastic update measurability |
| Coordinate projection satisfies the old interfaces | `coordinateEuclideanProjection_mapsIntoFeasibleSet`, `coordinateEuclideanProjection_hasProjectionDistanceBound` | [`EuclideanProjectionBridge.lean`](../NegDROFormalization/EuclideanProjectionBridge.lean) | set transport and squared-distance identity | final projected assumptions conversion |

## 7. Deterministic primal trajectory

| Mathematical statement | Lean declaration | Source | Immediate dependencies | Main downstream users |
|---|---|---|---|---|
| One projected step decreases squared distance up to gradient terms | `projectedGradientStep_sqDist_le` | [`PrimalProjectionRecursion.lean`](../NegDROFormalization/PrimalProjectionRecursion.lean) | Fejér interface and exact gradient-step expansion | deterministic trajectory recursion |
| Zero-indexed projected trajectory is feasible | `primalTrajectory_mem` | [`PrimalTrajectory.lean`](../NegDROFormalization/PrimalTrajectory.lean) | initial feasibility and projection feasibility | bounded trajectory estimates |
| Scalar trajectory recursion | `primalTrajectory_scalarRecursion_for_regretToConvergence` | [`PrimalTrajectory.lean`](../NegDROFormalization/PrimalTrajectory.lean) | projected one-step recursion | stochastic primal recursion |
| Deterministic scalar telescoping convergence | `scalar_proposition_A2`, `scalar_theorem_4_3_unpenalized`, `scalar_theorem_3_4_penalized` | [`RegretToConvergence.lean`](../NegDROFormalization/RegretToConvergence.lean) | scalar one-step substitution and finite telescoping | stochastic convergence assembly |

## 8. Conditional expectation and predictability

| Mathematical statement | Lean declaration | Source | Immediate dependencies | Main downstream users |
|---|---|---|---|---|
| Bounded predictable scalar multipliers pull through conditional expectation at integral level | `integral_mul_eq_of_condExp_ae_eq` | [`ConditionalExpectationScalar.lean`](../NegDROFormalization/ConditionalExpectationScalar.lean) | Mathlib conditional expectation | vector pairing |
| Coordinatewise conditional means preserve expected dot products | `integral_vectorDot_eq_of_coordinatewise_condExp_ae_eq` | [`PredictableVectorPairing.lean`](../NegDROFormalization/PredictableVectorPairing.lean) | scalar pull-out and finite-sum integration | expected primal/dual directions |
| Expected projected recursion from a conditional squared-moment bound | `expected_primal_recursion_of_condExpectedSqNorm_le` | [`ExpectedPrimalRecursion.lean`](../NegDROFormalization/ExpectedPrimalRecursion.lean) | exact deterministic recursion and conditional expectation | stochastic primal trajectory |
| Actual primal and EG trajectories are predictable | `randomPrimalTrajectory_displacement_predictable`, `randomEGTrajectory_displacement_predictable` | [`TrajectoryPredictability.lean`](../NegDROFormalization/TrajectoryPredictability.lean) | increasing sigma-algebras, measurable updates and next-round oracles | predictable convergence wrappers |

## 9. Concrete stochastic oracles

| Mathematical statement | Lean declaration | Source | Immediate dependencies | Main downstream users |
|---|---|---|---|---|
| Concrete primal and dual sample gradients | `samplePrimalOracle`, `sampleUnpenalizedDualOracle`, `samplePenalizedDualOracle` | [`ConcreteStochasticOracles.lean`](../NegDROFormalization/ConcreteStochasticOracles.lean) | finite coordinate definitions | joint stochastic state |
| Pointwise oracle bounds | `samplePrimalOracle_sqNorm_le`, `sampleUnpenalizedDualOracle_hasCoordinateAbsBound_explicit`, `samplePenalizedDualOracle_hasCoordinateAbsBound_explicit` | [`ConcreteStochasticOracles.lean`](../NegDROFormalization/ConcreteStochasticOracles.lean), [`ConcreteOracleMomentBounds.lean`](../NegDROFormalization/ConcreteOracleMomentBounds.lean) | simplex/domain bounds and residual inequalities | conditional moment constants |
| Fresh selected moments become raw trajectory moments | `concreteTrajectory_rawMoments_of_fresh` | [`OracleIntegrabilityBridge.lean`](../NegDROFormalization/OracleIntegrabilityBridge.lean) | trajectory predictability, feasibility, simplex invariance, selected mixed/fourth moments | concrete oracle integrability |
| Concrete primal `sqNorm` and coordinate integrability | `integrable_concreteTrajectoryPrimalOracle_sqNorm_of_fresh`, `integrable_concreteTrajectoryPrimalOracle_coordinate_of_fresh` | [`OracleIntegrabilityBridge.lean`](../NegDROFormalization/OracleIntegrabilityBridge.lean) | residual-square domination and finite-measure `L² -> L¹` | final fresh common bundle |
| Concrete dual bound-square and coordinate integrability | `integrable_concreteTrajectoryDualSize_sq_of_fresh`, `integrable_concreteTrajectoryDualOracle_coordinate_of_fresh` | [`OracleIntegrabilityBridge.lean`](../NegDROFormalization/OracleIntegrabilityBridge.lean) | residual-fourth domination, penalty two-square bound, finite-measure `L² -> L¹` | final fresh common bundle |
| Concrete primal population pairing lower bounds | `expected_expandedPrimalCoefficient_unpenalized_lower_bound`, `expected_expandedPrimalCoefficient_penalized_lower_bound` | [`ExpectedConcretePrimalDirection.lean`](../NegDROFormalization/ExpectedConcretePrimalDirection.lean) | conditional unbiasedness and fixed-witness bounds | final stochastic convergence |
| Joint recursive state equals existing primal and EG trajectories | `concreteNegDROState_eq_randomTrajectories` | [`StochasticNegDROExplicitConstants.lean`](../NegDROFormalization/StochasticNegDROExplicitConstants.lean) | concrete oracles and both trajectory recursions | concrete convergence bundles |

## 10. Fresh conditional sampling

| Mathematical statement | Lean declaration | Source | Immediate dependencies | Main downstream users |
|---|---|---|---|---|
| Universal conditional distribution interface | `HasFreshUniformFiniteEnvironmentLaw` | [`FreshSamplingLaw.lean`](../NegDROFormalization/FreshSamplingLaw.lean) | an external probability space and environment laws | all fresh-law specializations |
| Universal law yields selected population monomials | `freshLaw_toFreshPopulationMoments` | [`FreshSamplingLaw.lean`](../NegDROFormalization/FreshSamplingLaw.lean) | integrability of `XX`, `XY`, and `Y²` | oracle conditional unbiasedness |
| Universal law plus fourth moments yields raw conditional bounds | `freshLaw_toFreshRawMoments` | [`FreshSamplingLaw.lean`](../NegDROFormalization/FreshSamplingLaw.lean) | integral Cauchy-Schwarz and fourth moments | concrete oracle moments |
| Fresh moments imply concrete oracle conditional unbiasedness | `concreteTrajectory_condUnbiased_expanded` | [`FreshSamplingConditionalOracles.lean`](../NegDROFormalization/FreshSamplingConditionalOracles.lean) | predictable state and moment relations | sampling convergence wrappers |

## 11. Spectral witness

| Mathematical statement | Lean declaration | Source | Immediate dependencies | Main downstream users |
|---|---|---|---|---|
| Eigenvalue lower bounds imply coordinate curvature | `curvatureAtLeast_of_le_eigenvalues` | [`SpectralCurvatureBridge.lean`](../NegDROFormalization/SpectralCurvatureBridge.lean) | Mathlib Hermitian spectral theorem | spectral witness interface |
| Symmetry plus eigenvalue bound packages a witness | `SpectralWitnessAtLeast`, `SpectralWitnessAtLeast.curvatureAtLeast` | [`SpectralWitnessInterface.lean`](../NegDROFormalization/SpectralWitnessInterface.lean) | previous bridge | additive final assembly |
| Additive SEM supplies symmetry, leaving only the eigenvalue bound | `additiveInterventionFamily_spectralWitnessAtLeast` | [`SpectralWitnessInterface.lean`](../NegDROFormalization/SpectralWitnessInterface.lean) | corrected covariance symmetry | `AdditiveInterventionFreshSamplingAssumptions.toFreshCommon` |

## 12. Final convergence and rates

| Mathematical statement | Lean declaration | Source | Immediate dependencies | Main downstream users |
|---|---|---|---|---|
| Cumulative expected dual objective regret | `stochasticEG_cumulative_unpenalized_objectiveRegret`, `stochasticEG_cumulative_penalized_objectiveRegret` | [`StochasticDualRegret.lean`](../NegDROFormalization/StochasticDualRegret.lean) | expected EG regret and objective linearization | stochastic convergence assembly |
| Concrete finite-time convergence | `stochasticNegDRO_concrete_unpenalized_convergence`, `stochasticNegDRO_concrete_penalized_convergence` | [`StochasticNegDROExplicitConstants.lean`](../NegDROFormalization/StochasticNegDROExplicitConstants.lean) | predictable convergence, concrete moments and oracles | fresh-law wrappers |
| Explicit `1 / sqrt T` normalization | `explicit_unpenalized_rhs_eq_rate`, `explicit_penalized_rhs_eq_rate` | [`StochasticNegDRORates.lean`](../NegDROFormalization/StochasticNegDRORates.lean) | scalar algebra and `T > 0` | inverse-square-root theorem family |
| Jensen bound for the random averaged iterate | `integral_sqDist_randomPrimalAverage_le_average_integral_sqDist` | [`AveragedPrimalIterate.lean`](../NegDROFormalization/AveragedPrimalIterate.lean) | finite-dimensional squared-distance Jensen | averaged convergence wrappers |
| Additive fresh-law convergence with actual projection | `stochasticNegDRO_additiveSampling_projected_unpenalized_convergence`, `stochasticNegDRO_additiveSampling_projected_unpenalized_averaged_convergence`, `stochasticNegDRO_additiveSampling_projected_unpenalized_invSqrt_rate`, `stochasticNegDRO_additiveSampling_projected_penalized_convergence`, `stochasticNegDRO_additiveSampling_projected_penalized_averaged_convergence`, `stochasticNegDRO_additiveSampling_projected_penalized_invSqrt_rate` | [`AdditiveInterventionSamplingProjectedConvergence.lean`](../NegDROFormalization/AdditiveInterventionSamplingProjectedConvergence.lean) | corrected model, fresh law, spectral witness, actual projection, existing convergence and rates | publication-level entry points |
| RMS consequence of a generic explicit squared-error rate | `rms_le_sqrt_bias_add_quarter_rate` | [`StochasticNegDRORates.lean`](../NegDROFormalization/StochasticNegDRORates.lean) | nonnegativity and square-root algebra | optional interpretation only |

## One complete dependency path

For the unpenalized projected finite-time theorem, one explicit upward path is:

```text
stochasticNegDRO_additiveSampling_projected_unpenalized_convergence
  -> AdditiveInterventionFreshSamplingProjectedAssumptions.toBase
  -> stochasticNegDRO_additiveSampling_unpenalized_convergence
  -> AdditiveInterventionFreshSamplingAssumptions.toFreshSamplingUnpenalized
  -> stochasticNegDRO_sampling_unpenalized_convergence
  -> FreshSamplingConcreteUnpenalizedAssumptions.toFreshConcreteUnpenalizedAssumptions
  -> stochasticNegDRO_fresh_unpenalized_convergence
  -> stochasticNegDRO_concrete_unpenalized_convergence
  -> stochasticNegDRO_unpenalized_convergence_of_oracleAdapted
  -> stochasticNegDRO_unpenalized_convergence
  -> stochasticPrimalTrajectory_expected_recursion
     + stochasticEG_cumulative_unpenalized_objectiveRegret
     + expected_expandedPrimalCoefficient_unpenalized_lower_bound
  -> scalar_theorem_4_3_unpenalized
```

The main side branches supplying that path are:

```text
HasFreshUniformFiniteEnvironmentLaw
  -> freshLaw_toFreshPopulationMoments / freshLaw_toFreshRawMoments
  -> concreteTrajectory_condUnbiased_expanded
     / concreteTrajectory_rawMoments_of_fresh
  -> concrete oracle unbiasedness / integrability / moment bounds

hEigen
  -> additiveInterventionFamily_spectralWitnessAtLeast
  -> SpectralWitnessAtLeast.curvatureAtLeast
  -> fixedWitness_direction_explicit

C.Nonempty + IsClosed C + Convex ℝ C
  -> coordinateEuclideanProjection_measurable
  -> coordinateEuclideanProjection_mapsIntoFeasibleSet
  -> coordinateEuclideanProjection_hasProjectionDistanceBound
```
