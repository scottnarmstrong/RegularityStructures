# BPHZ models for Φ⁴₃: overview of `Phi43/BPHZ`

This directory proves the convergence of the BPHZ models of Φ⁴₃ on ℝ × T³ [Hai14, Theorem 10.22]
(`bphzModels_cauchy`) and, from it, the convergence of the G-models, the models renormalised with
the constants of the statement (`phi43GModels_convergence`). The noise is a regularised white noise
`ξ_ε = ρ_ε ∗ ξ`, the kernel is the truncated heat kernel `K = hairerKernelTorus N`, and
`Ψ = K ∗ ξ_ε`.

## Trees and their explicit fields

The list `fMinus` is the set F₋ of symbols of negative homogeneity. With `κ ∈ (0, 1/16)` their
homogeneities (`homogeneity κ`) are

Ξ −5/2−κ, Ψ −1/2−κ, Ψ² −1−2κ, Ψ³ −3/2−3κ, Ψ²Xᵢ −2κ, I(Ψ³)Ψ −4κ, I(Ψ²)Ψ² −4κ, I(Ψ³)Ψ² −1/2−5κ.

For a smooth noise ζ and constants C = (C₁, C₂), the renormalised model based at z
[Hai14, Section 10.5, (10.32)–(10.43)] is, with Ψ = K ∗ ζ and ⟦·⟧_z the Taylor-subtracted
convolution at z:

- Π̂_z Ξ = ζ, Π̂_z Ψ = Ψ, Π̂_z Ψ² = Ψ² − C₁, Π̂_z Ψ³ = Ψ³ − 3C₁Ψ, Π̂_z Ψ²Xᵢ = (Ψ² − C₁)(xᵢ − zᵢ);
- Π̂_z I(Ψ³)Ψ = ⟦K ∗ (Ψ³ − 3C₁Ψ)⟧_z · Ψ;
- Π̂_z I(Ψ²)Ψ² = ⟦K ∗ (Ψ² − C₁)⟧_z · (Ψ² − C₁) − C₂;
- Π̂_z I(Ψ³)Ψ² = ⟦K ∗ (Ψ³ − 3C₁Ψ)⟧_z · (Ψ² − C₁) − 3C₂Ψ.

`Phi43.BPHZ.TreeFormulas` proves these formulas (`renormalisedPi_basis_*_eq`) for every τ ∈ F₋,
and `Phi43.BPHZ.PositiveTreeFormulas` gives the realisations of the symbols of positive
homogeneity. The BPHZ constants are Hairer's, C₁ = `hairerWickConstant N ρ ε` and
C₂ = `hairerSunsetConstant N ρ ε` [Hai14, (10.33), (10.41)]. The `CanonicalBridge*` modules
identify the abstract canonical data of the lifted noise with these concrete fields on ℝ × T³.

## Moments of the trees

Every tree lies in a Wiener chaos of order at most 5.

- **Second moments** are computed with a finite-dimensional Gaussian diagram formula for Wick
  products: E[∏ᵢ :Xᵢ^{nᵢ}:] is a sum over pairings without self-pairs (Isserlis form). It is
  applied pointwise to the Gaussian field Ψ, whose covariance is Q_ε, followed by Fubini over the
  test function and the inner integrals. This produces the covariance diagrams of
  [Hai14, Section 10.5]. Multiple Wiener integrals are not needed.
- **Kernel calculus.** The singular bounds for the covariance (`hairerCovariance_abs_le`), the
  convolution estimates of [Hai14, Lemma 10.14] and their two-mollifier versions
  (`CrossMollifier*`) give the decay `s(z)^{−a}` of every diagram and the gain `max(ε, ε′)^θ` for
  differences.
- **All moments** follow from the second moments by the equivalence of moments in a finite
  Wiener chaos, in the form of L² limits of cylindrical polynomials of bounded degree
  (`integral_pow_two_mul_le_of_tendsto_cylindricalPolynomial`). The test function is the
  periodised semigroup kernel q^♯_t(x, ·), which is not compactly supported in time; the
  `SemigroupTest*` modules handle the truncation in time.

The `Tree*`, `Product*` and `SemigroupTest*` modules carry this out symbol by symbol, for one model
and for the difference of two models (two scales, two mollifiers).

## The Cauchy property of the BPHZ models

`bphzModels_cauchy` is proved from the Kolmogorov bound for the model norms (`kolmogorov_modelNorm`,
the analogue of [Hai14, Theorem 10.7]) applied to two families of canonical models:

1. **Canonical replacement** (`exists_canonical_replacement`). The given models agree almost
   surely with the canonical models of a modification of the noise, by the uniqueness of the
   renormalised canonical model (`renormalisedCanonicalModel_existsUnique`).
2. **Continuity and measurability** of the canonical models as random models
   (`isContinuousRandomModelOn_canonicalModelOfLift`).
3. **Deterministic entries.** On the polynomial symbols (`piDeterministic`) and on the
   deterministic Γ-entries (`gammaFullDeterministic`) the bounds hold pathwise, and the two models
   agree there.
4. **Π-moments** of the remaining symbols below γ = 1 + 3κ: `q`-th moments of Q_t Π_x e_i (x) of
   order t^{(deg i + κ̄)/4}, with a factor max(ε, ε′)^θ for differences
   (`exists_piSingleBound_all`, `exists_piSubBound_all`; the product symbols enter through
   `BphzCauchyMoments`, which holds by `bphzCauchyMoments_holds`).
5. **Γ-moments** of the random entries Γ_{yx} e_i (j), of order d(y, x)^{deg i − deg j + κ̄}, for
   all pairs x, y (`GammaFull*`, `GammaMoment*`).

## The shifted BPHZ models and the G-models

The G-models are renormalised with the constants of the statement, which differ from Hairer's by
`gModelsShift N ρ c ε`. The comparison of the renormalisation constants (`constantsComparison`)
shows that this shift is bounded and converges as ε → 0.

The Cauchy bound is therefore proved directly for the shifted BPHZ models, with constants
`shiftConst N ρ ε c = (C₁, C₂) + c`, uniformly in `‖c‖ ≤ B` (`ShiftedBphzInputs`,
`bphzModels_cauchy_shifted`); the difference factor is `max(ε, ε′)^θ + ‖c − c′‖`. With a power rate
for the convergence of the constant differences, Markov's inequality and a dyadic Borel–Cantelli
argument give the tightness, the Cauchy property in probability and the almost sure dyadic clause
of `phi43GModels_convergence` (`GModels*`). No Lipschitz bound for the action of the
renormalisation constants on models is needed.
