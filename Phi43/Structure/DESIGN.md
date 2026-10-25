# Design notes: the finite Φ⁴₃ structure and its models

These notes explain the choices behind the finite structure, the kernel, the class of smooth
noises, the renormalised model and the enlarged integration completion. References are to
[Hai14] (M. Hairer, *A theory of regularity structures*, arXiv:1303.5113v4) and [Hos25]
(M. Hoshino, *A semigroup approach to the reconstruction theorem and the multilevel Schauder
estimate*, arXiv:2310.07396v2).

## Parameters and non-integrality

The parameter is `κ ∈ (0, 1/16)`. Every non-polynomial symbol of the retained finite structure has
non-integer homogeneity for all such `κ` (`phi43_nonpolynomial_homogeneity_ne_int`), so the finite
structure itself needs no excluded values. This is not a statement about a larger tree structure:
for example `I(Ψ³)³`, which is not retained, has homogeneity `3/2 - 9κ`, an integer at
`κ = 1/18`. The results on the convergence of the models take `κ` outside the finite set
`Statements.excludedKappa`, whose elements are the numbers `(m/2 - n)/b` in `(0, 1/16)` with
`1 ≤ b ≤ 16` and `0 ≤ n ≤ 4`. A non-polynomial symbol of degree at most four with `b` noises has
homogeneity `k/2 - bκ`, so every resonance of such a symbol lies in this set. Irrationality of `κ`
is not used.

## Kernel

The canonical lift uses the singular part of the causal heat kernel,
`hairerKernel N = Σ_n annShellC N n`, with causal profile `annKernel0C N`
(`Phi43.Structure.CanonicalKernelHairer`). Convolution and its Taylor coefficients are actual
integrals and derivatives: the Taylor data of the lift are, by definition, the value and the
spatial gradient of the convolution [Hai14, (5.12), (8.20)]. The identity of the convolution with
the sum of the shell convolutions, and its differentiated form, are proved, as is admissibility on
all four retained integration sources. Causality of the kernel is used by the fixed point.

Admissibility on the retained sector holds for every `N`: the constant Wick subtraction cancels
in the constant Taylor difference even when the kernel mass is not zero. The vanishing moments of
the kernel are therefore not needed for this step.

## The class of noises

The canonical model is constructed for smooth spatially periodic noise with an explicit polynomial
envelope on its iterated derivatives of orders `0` to `4`
(`canonicalNoise_polyBounded_of_derivatives`, `Phi43.Structure.CanonicalGrowthPremise`). This is the
polynomially weighted framework of [Hos25, Definition 2.1, (2.1)–(2.2)]. Tail integrability of the
whole-space `Q`-regularisation follows from the zeroth-order envelope. The model's `Π` is `Q`
applied to the canonical lift itself, not arbitrary covariant data, and no analytic bound on the
model is an input.

Some growth restriction is necessary. Smooth periodic noise alone, as in the local statement
[Hai14, Proposition 8.27], does not suffice for whole-space `Q`-regularisation: the noise
`ζ(t, x) = exp(π t²)` is smooth and spatially periodic, but its `Q`-convolution at time `π` and
base point zero is not integrable. Moreover no model can have `Π` equal to the totalised
whole-space `Q`-convolution of the lift of this noise on all vectors: the totalised convolutions
of `ζ` and of `ζ + 1` both vanish while that of `1` is `1`, which contradicts linearity. This does
not contradict Hairer's compact-test theorem; it only rules out the unrestricted class for the
global `Q`-form used here.

The polynomial weights `(1 + ‖z‖)^q` are moderate (`canonicalPolynomialWeight_isModerate`). The
compact `Π` and `Γ` bounds do not assert that the constants depend only on the growth constants of
the noise.

## Renormalisation and the renormalised model

The renormalisation table and the group laws cover the retained structure, including `I(Ψ³)` and
`I(Ψ)`, with the coproduct corrections of [Hai14, (9.3)–(9.5)]. The renormalised model is not
obtained by applying the finite coproduct of the truncated structure to the canonical model. On the
truncation, the positive character induced by that coproduct row is not multiplicative on the
auxiliary square: it can take the value `3` on `J(Ψ³)` and `0` on `J(Ψ³)²`, instead of `9`.

The model `canonicalRenormalisedModel` is instead a smooth extension defined from the renormalised
global trees and characters. The integrated-cubic potential is `K*(Ψ³) - 3C₁ K*Ψ`, and the auxiliary
square is the square of that corrected potential. The construction then proves:

* the abstract model fields on every retained symbol, with `Π` exactly `Q` of the explicit functions
  (`canonicalRenormalisedModel_regPi`);
* agreement with the tensor formula [Hai14, (8.34)] on the critical integrated cubic
  (`renormalisedExtensionPi_tensor_iPsiCube`), on the whole sector of negative and integrated
  symbols (`renormalisedExtensionPi_eq_tensor_on_H0`), and the prescribed `Π` on `F₋`
  (`canonicalRenormalisedModel_regPi_tensor_fMinus`);
* causal admissibility, including polynomial compatibility (`canonicalRenormalisedModel_isRealising`);
* compact `Π` and `Γ` bounds and finite compact norms (`canonicalRenormalisedModel_pi_bounds`,
  `canonicalRenormalisedModel_gamma_bounds`, `canonicalRenormalisedModel_normOn_ne_top`);
* a polynomially weighted `PiBoundGrowth` (`canonicalRenormalisedModel_exists_with_piBoundGrowth`).

These give existence of a model satisfying `Statements.IsModerateRenormalisedCanonicalModel`.
Uniqueness below `gamma κ` comes from the weighted determination of the `Π` and `Γ` halves
(`renormalisedCanonicalModel_piDiffNormOn_eq_zero`,
`renormalisedCanonicalModel_gammaDiffNormOn_eq_zero`): the product of two moderate weights is
moderate and dominates both, so the weighted positive-sector argument applies to the difference of
two models.

## The enlarged integration completion

In the original structure, `{Ψ, Ψ², Ψ³}` spans the full source sector of integration, and the
realising statements restrict to this cubic block. The block is still unusable for the fixed point:
commutation of its projection with the structure group is incompatible with polynomial
admissibility.

The finite planted completion of `Phi43.Structure.EnlargedAll` removes this obstruction. Its public
interface is `SymbolF`, `phi43RegularityStructureF`, `phi43OldEmbF`, `phi43PolynomialSectorF`,
`phi43IntegrationF`, `phi43XiFreeF` and `phi43IntegrationExtensionF`. The last is the explicit
`IntegrationExtension` record, with the maps between original and new symbols, the degree-two
polynomial embedding, vanishing of integration on the sources, and the enlarged-group criterion.
The twelve new plants integrate all original products containing `Ψ`; integration vanishes on the
planted symbols and the polynomials. The extension subgroup is closed under products and inverses,
compatible with the original action, and commutes with integration modulo the polynomial space.
The `Ξ`-free block is a sector for structural reasons (`phi43XiFreeF_isSector`), and
`phi43IntegrationF_isAbstractIntegration` verifies [Hai14, Definition 5.7] on the whole block. The
polynomial sector of degree at most two and non-integrality are proved on the same type.

This is a finite integration completion, not the full degree-four tree algebra. A hard degree
truncation followed by zero integration would recreate the same obstruction at the truncation
boundary.

The existence of a model on the enlarged structure is a separate result, obtained from the abstract
extension theorem applied to the source sector (`phi43EnlargedRenormalisedModel`). The polynomial
sector `phi43PolynomialSector` with cutoff `2` on the original structure is kept; the quadratic
modules give a degree-two sector on the original structure as well. Spatial periodicity of the
canonical lift is `canonicalPi_spatial_translation`.

## Joint continuity of the truncated potentials

A model class for singular noise also needs the joint continuity in `(s, t)` of the truncated
potentials `K * (ξ 1_{r ≥ s})(t)` in the closure topology. This is not a consequence of compact `Π`
and `Γ` bounds and must be established separately for any argument that restarts the singular
equation at intermediate times. The smooth models of this directory do not need it.
