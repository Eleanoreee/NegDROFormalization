# Completion roadmap

"Complete proof" can refer to materially different targets. This document separates them so
that progress on one target is not reported as completion of another.

## Target A - Complete conditional theorem for this stochastic extension

**Status: Complete.**

The current final theorems are kernel-checked conditional theorems for the project's
fresh-sample projected-SGD/EG algorithm. They start from an explicit list of mathematical model,
sampling, moment, spectral, and feasible-set assumptions and conclude finite-time,
averaged-iterate, and inverse-square-root expected squared-error bounds. The Euclidean projection,
finite Pinsker inequality, conditional-expectation reductions, and rate algebra are proved rather
than postulated at the final interface. Concrete primal-coordinate, primal-`sqNorm`,
dual-coordinate, and dual-bound-square integrability are now derived from the fresh selected
moments, bounded feasible trajectory, simplex EG trajectory, and oracle measurability; they are
not caller-supplied fields.

No meaningful statistical theorem is assumption-free. In particular, the following are genuine
conditions rather than proof gaps:

- finite fourth moments and their numerical bounds;
- a universal fresh conditional sampling law;
- a nonempty closed convex bounded feasible set;
- a simplex spectral witness with an eigenvalue lower bound;
- positivity conditions on the horizon, step sizes, and curvature parameter.

The remaining final assumptions are substantive theorem hypotheses, not unfinished proof
obligations. “Complete” means complete relative to this explicit conditional model; it does not
mean assumption-free. Optional presentation work or further abstractions are not required for
Target A correctness.

## Target B - Fully realized probability-space version

**Status: not yet constructed.**

The present final theorem assumes `HasFreshUniformFiniteEnvironmentLaw` for each used round. A
fully realized version would construct a particular probability space and prove the interface
from that construction. The main steps are:

1. construct an explicit one-round product probability space containing a uniform finite
   environment coordinate and an environment-conditioned observation;
2. prove that the selected pair satisfies `HasFreshUniformFiniteEnvironmentLaw`;
3. construct an infinite fresh sample stream, typically as a countable product;
4. define the stream's natural pre-round filtration;
5. derive oracle adaptedness and the universal conditional law from coordinate independence and
   the natural filtration;
6. instantiate the existing projected convergence theorem with this stream.

This optional work is primarily measure-theoretic infrastructure. If carried out with the same environment
laws and moments, it should not alter the convergence constants. It would replace a distribution-
level sampling assumption with an explicit canonical realization. It is not necessary for the
correctness or completeness of Target A.

## Target C - Literal verification of official v3 Algorithm 1

**Status: a different project scope.**

Algorithm 1 in `arXiv:2412.11850v3` is not the algorithm formalized here. It forms empirical
environment risks, computes an exact penalized maximizer over `w` for the current primal point,
and then takes a primal gradient step using that maximizer. A literal verification would require:

- definitions of finite data sets and empirical environmental risks;
- the exact optimization problem defining the maximizer in `w`;
- existence of a maximizer, and measurable selection if the data or iterate are random;
- the official alternating update and output-selection rule;
- the landscape, smoothness, concentration, and descent analysis used for that update;
- a theorem map aligned to the official theorem numbering and assumptions;
- an explicit decision about how to handle the Eq. (97) sign discrepancy in the source PDF.

Completing Target A does **not** complete Target C. Conversely, work on the official algorithm
should preferably live in a separate module family or branch so that it cannot be confused with
the fresh-sample stochastic extension. Target C is not necessary for the correctness or
completeness of Target A.

## Recommended order

1. Keep documentation, pinned versions, and build/audit commands reproducible.
2. If a canonical realization is independently desired, treat Target B as an optional extension.
3. Treat literal official Algorithm 1, if pursued, as the separate Target C scope.

No additional mathematical module is required to close Target A.
