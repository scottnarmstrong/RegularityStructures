# Comparison of the renormalisation constants for the causal kernel

Import `Phi43.Stochastic.ConstantsComparisonLimits` for the final results.
The kernel is the spatial periodisation of
`hairerKernel N = ∑' n, annShellC N n`, matching the causal `annKernel0C N`
decomposition used by the abstract fixed point. The noncausal `annShell` construction
is not used. Both massive and truncated constants use the same signed periodised
mollifier on `ℝ × T³`; no symmetry or positivity assumption is added.

| Declaration | Statement / proof input |
| --- | --- |
| `hairerWickConstant`, `hairerSunsetConstant` | Spatially periodised versions of [Hai14, (10.33), (10.41)], in `Phi43.Stochastic.ConstantsComparisonDefinitions`. |
| `constantsComparisonR_orderOne_ae` | The local order-one remainder bound, including lattice images and the massive factor. |
| `constantsComparisonR_memLp_four` | The actual remainder is in `L⁴`; its tail is bounded by the integrable massive kernel. |
| `constantsComparison_massivePlusHairer_memLp_fourThirds` | The conjugate-exponent input for C1. |
| `constantsComparison_periodise_convolution_eLpNorm_tendsto_of_memLp` | Signed approximate-identity convergence on `ℝ × T³` for every finite `p > 1` and arbitrary measurable `MemLp` representatives. |
| `constantsComparison_covariance_difference_uniform_bound_unconditional` | The covariance difference is bounded uniformly in `ε` and the base point, by signed Young and Hölder. |
| `constantsComparison_C2_first_majorant`, `constantsComparison_C2_second_majorant` | Integrable uniform majorants of orders three and four for the two terms in the C2 difference. |
| `constantsComparison_C2_integrability` | All four finite-scale Bochner integrals in that difference exist. |
| `constantsComparison_causal_covariance_tendsto` | Actual unregularised covariance limit at nonzero time separation, by a causal time cut and `L⁴ × L^(4/3)` pairing convergence. |
| `constantsComparison_covariance_tendsto_ae`, `constantsComparison_hairerCovariance_tendsto_ae` | The massive and causal truncated covariance limits; the time-zero hyperplane is null. |
| `constantsComparison_wickLimit_tendsto` | The C1 difference converges to `constantsComparison_wickLimit N`. |
| `constantsComparison_sunsetLimit_tendsto` | The C2 difference converges to `constantsComparison_sunsetLimit N`. |
| `constantsComparison_countertermLimit_tendsto` | The counterterm difference converges to `constantsComparison_countertermLimit N`, with the coefficients in [Hai14, (9.21)]. |
| `constantsComparison_limits` | A single triple of finite real limits works for every mollifier; the existential quantifiers precede `∀ ρ`. |

The final theorems take only `N`, `ρ`, and `IsMollifier ρ`. Their limit
definitions contain no mollifier. The reductions from analytic estimates are
`constantsComparison_sunset_tendsto` and `constantsComparison_counterterm_tendsto`.
