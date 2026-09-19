# Assumption ledger

The six final projected theorems take one bundle,
`AdditiveInterventionFreshSamplingProjectedAssumptions`, plus the ambient probability-measure
instance. The bundle has **30 named fields**: 8 model/reduced-form fields, 5 sampling fields, and
17 geometry/optimization fields. The penalized theorems additionally take
`hpenalty : 0 ≤ penalty`.

"Retained" below means retained by the current theorem statement. It does not assert logical
minimality.

## A. Model and reduced-form assumptions (8 fields)

| Lean field | Mathematical meaning | Where used | Derived or assumed | Necessary/redundant status |
|---|---|---|---|---|
| `hInt` | For each environment, integrability of `ηY²`, `ηY ηX`, `ηY δ`, `ηX ηX`, `ηX δ`, `δ ηX`, and `δ δ` coordinate products | Corrected SEM moment expansions and population relations | Assumed | Retained primitive model condition |
| `hZero` | `E[ηY δᵀ] = 0`, `E[ηX δᵀ] = 0`, and the transposed coordinate relations | Removes systematic/intervention cross terms | Assumed | Retained model orthogonality condition |
| `hEnvXMeas` | Coordinatewise a.e. strong measurability of every realized environmental covariate map | Fourth-moment and sampling-law specializations | Assumed | Retained analytic condition |
| `hEnvYMeas` | A.e. strong measurability of every realized environmental outcome | Fourth-moment and sampling-law specializations | Assumed | Retained analytic condition |
| `hEnvX4Int` | Integrability of `(sqNorm X_e)^2 = ‖X_e‖₂^4` | Derivation of raw selected-environment moments | Assumed | Retained fourth-moment condition |
| `hEnvY4Int` | Integrability of `Y_e^4` | Derivation of raw selected-environment moments | Assumed | Retained fourth-moment condition |
| `hEnvX4` | `E[(sqNorm X_e)^2] ≤ KX` for every environment | Explicit primal and dual moment constants | Assumed | Retained quantitative moment bound |
| `hEnvY4` | `E[Y_e^4] ≤ KY` for every environment | Explicit primal and dual moment constants | Assumed | Retained quantitative moment bound |

The final entry point receives `GT`, `BYX`, `etaY`, `etaX`, and `delta` directly. It does not
assume `BXX` or acyclicity, and it does not reconstruct `GT` as an inverse inside the final
wrapper. The separate corrected SEM module proves that a supplied inverse of the Schur matrix
has the required positive-sign reduced form.

## B. Sampling assumptions (5 fields)

| Lean field | Mathematical meaning | Where used | Derived or assumed | Necessary/redundant status |
|---|---|---|---|---|
| `hMono` | `mCond t ≤ mCond (t+1)` | Inductive predictability of both trajectories | Assumed | Retained filtration-monotonicity condition |
| `hmCond` | `mCond t ≤ mOmega` | Transfer of conditional measurability to the ambient space | Assumed | Retained sigma-algebra inclusion |
| `hLaw` | At every `t < T`, every integrable test function of the selected fresh pair has the specified uniform-environment conditional expectation | Derives selected population monomials, raw moment bounds, and oracle conditional means | Assumed | Central retained law-level sampling condition |
| `hPrimalMeas` | Round-`t` concrete primal oracle is measurable for `mCond (t+1)` | Primal trajectory predictability | Assumed | Retained adaptedness/measurability condition |
| `hDualMeas` | Round-`t` concrete dual oracle is measurable for `mCond (t+1)` | EG trajectory predictability | Assumed | Retained adaptedness/measurability condition |

The law is formulated using `=ᵐ[mu]` conditional-expectation identities. No pointwise
conditional-unbiasedness or independence between the primal and dual stochastic gradients is
assumed.

## C. Geometry and optimization assumptions (17 fields)

| Lean field | Mathematical meaning | Where used | Derived or assumed | Necessary/redundant status |
|---|---|---|---|---|
| `hCNonempty` | `C` is nonempty | Existence of the nearest-point projection | Assumed | Retained geometric condition |
| `hCClosed` | `C` is closed | Completeness and nearest-point existence | Assumed | Retained geometric condition |
| `hCConvex` | `C` is convex over `ℝ` | Projection variational inequality and uniqueness | Assumed | Retained geometric condition |
| `hm` | `0 < m` | Uniform simplex initialization, division by `m`, and `log m` | Assumed | Retained dimension condition |
| `hT` | `0 < T` | Time averaging and inverse-square-root specialization | Assumed | Retained horizon condition |
| `hetaB` | `0 < etaB` | Primal telescoping division | Assumed | Retained step-size sign condition |
| `hetaW` | `0 < etaW` | Dual regret division | Assumed | Retained step-size sign condition |
| `hB` | `0 ≤ B` | Coordinate and residual bounds | Assumed | Retained sign condition for the radius |
| `hKX` | `0 ≤ KX` | Square roots and fourth-moment inequalities | Assumed | Retained moment-constant sign condition |
| `hKY` | `0 ≤ KY` | Square roots and fourth-moment inequalities | Assumed | Retained moment-constant sign condition |
| `hgamma` | `0 ≤ gamma` | Positive denominator and coefficient signs | Assumed | Retained NegDRO-parameter condition |
| `hlam` | `0 < lam` | Curvature and division by `λ` | Assumed | Retained identification/curvature condition |
| `hInit` | `bInit ∈ C` | Base case for primal feasibility | Assumed | Retained feasibility condition |
| `hbetaStar` | `betaStar ∈ C` | Projection comparison and bounded displacement | Assumed | Retained comparator feasibility condition |
| `hCBall` | Every `b ∈ C` satisfies `sqNorm b ≤ B^2` | Uniform iterate, displacement, and oracle moment bounds | Assumed | Retained bounded-domain condition |
| `hw0` | The deterministic witness/comparator `w0` lies in the simplex | Fixed-witness curvature and comparator regret | Assumed | Retained witness condition; `w0` is not the algorithmic initialization |
| `hEigen` | Every Mathlib eigenvalue of the symmetric heterogeneity matrix at `w0` is at least `lam` | Derived `CurvatureAtLeast`, then the primal direction lower bound | Assumed | Retained genuine spectral heterogeneity condition |

The penalized theorem adds `hpenalty : 0 ≤ penalty`. The unpenalized theorem specializes
`penalty = 0`. All six convergence theorems also require the typeclass
`[IsProbabilityMeasure mu]`.

## D. Interfaces eliminated from the final projected assumptions

The following data occur in lower-level reusable modules or older assumption bundles but are not
fields of `AdditiveInterventionFreshSamplingProjectedAssumptions`:

| Eliminated final field/interface | Current derivation |
|---|---|
| `hRaw` / `HasRawConcreteConditionalMoments` | Derived from selected raw moments and predictable bounded iterates |
| Fresh raw moments | `freshLaw_toFreshRawMoments` from `hLaw`, environmental measurability, fourth-moment integrability, and `KX`, `KY` bounds |
| Fresh population moments | `additiveInterventionFreshLaw_toFreshPopulationMoments` from `hLaw` and model integrability |
| Primal conditional unbiasedness | `samplePrimalOracle_condUnbiased_expanded`, then `concreteTrajectory_condUnbiased_expanded` |
| Dual conditional unbiasedness | `sampleUnpenalizedDualOracle_condUnbiased_expanded` and `samplePenalizedDualOracle_condUnbiased_expanded` |
| Population cross relation | `additiveInterventionFamily_hasCrossMomentRelation` from the corrected SEM moment calculation |
| Population outcome relation | `additiveInterventionFamily_hasOutcomeMomentRelation` from the corrected SEM moment calculation |
| Covariance symmetry | `additiveInterventionFamily_sigmaIsSymm` from actual second moments |
| `QuadNonneg` covariance family | `additiveInterventionFamily_sigmaQuadNonneg` from actual second moments |
| `CurvatureAtLeast` | Derived from `hEigen` by the spectral theorem bridge |
| `hPMeas` | `coordinateEuclideanProjection_measurable` from `hCNonempty`, `hCClosed`, and `hCConvex` |
| `hPFeas` | `coordinateEuclideanProjection_mapsIntoFeasibleSet` |
| `hPDist` | `coordinateEuclideanProjection_hasProjectionDistanceBound` |
| `hPrimalHatInt` | `integrable_concreteTrajectoryPrimalOracle_coordinate_of_fresh`, by first deriving primal `sqNorm` integrability and then finite-measure `L² -> L¹` |
| `hPrimalSqInt` | `integrable_concreteTrajectoryPrimalOracle_sqNorm_of_fresh`, from the residual-square estimate and selected mixed/X-fourth moments |
| `hDualHatInt` | `integrable_concreteTrajectoryDualOracle_coordinate_of_fresh`, from the explicit coordinate bound and finite-measure `L² -> L¹` |
| `hDualSizeSqInt` | `integrable_concreteTrajectoryDualSize_sq_of_fresh`, from residual-fourth integrability and the penalized two-square estimate |

The three projection-interface properties appear when `toBase` constructs an older internal
bundle, but they are proved there and are not assumptions supplied by a caller of the final
projected theorem. The four integrability properties are constructed later when the fresh common
bundle is assembled.

## Summary

The final projected bundle has **30 fields**: 8 model/reduced-form, 5 sampling, and 17
geometry/optimization fields. The theorem is not assumption-free, nor should it be: the fresh
conditional law, finite fourth moments, bounded feasible domain, and spectral heterogeneity are
substantive mathematical conditions. The former four technical oracle-integrability properties
are now derived and are not unfinished proof obligations.
