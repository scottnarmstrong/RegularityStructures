/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib

/-!
# Uniform moment bound for the regularised Φ⁴₃ equations

A standalone, Mathlib-only statement of the uniform moment bound behind coming down from infinity
for the renormalised dynamical Φ⁴₃ model on `T³`, together with theorems showing that its
hypotheses can be met.

For a mass `a`, an exponent `η' ∈ (-2/3, -1/2)` and a mollifier `ρ`, the classical solutions `u_ε`
of `∂_t u = Δu - u³ + (a + 3C₁^ε - 9C₂^ε) u + ξ_ε`, started from smooth data, satisfy
`sup_x sup_{0<t≤1} √t ‖u_ε(t)‖_{η'} ≤ M_ε` for measurable majorants `M_ε` whose moments are bounded
uniformly in `ε ∈ (0, 1]` by a constant chosen before the probability space. This is the
formulation proved in this repository's `GlobalPhi43` library; its analytic input is Mourrat–Weber
(*The dynamic Φ⁴₃ model comes down from infinity*, Commun. Math. Phys. 356 (2017), (1.27)) and
Moinat–Weber (*Space-time localisation for the dynamic Φ⁴₃ model*, Comm. Pure Appl. Math. 73
(2020), Theorem 2.1).

* `regularisedBound`: the bound.
* `exists_whiteNoise`, `regularisedNoise_exists_unique`, `classicalSolution_exists_unique`,
  `constants_finite`: the hypotheses can be met and the constants are not junk values (the same
  theorems as in `comparators/TheoremA`; the white-noise space is then completed and a smooth bump
  of positive integral normalised to a mollifier, both standard steps).

The definitions are copied verbatim from `comparators/TheoremA`. Conventions: `T³ = ℝ³/ℤ³` is
`UnitAddTorus (Fin 3)`, points of `ℝ³` are functions `Fin 3 → ℝ`, and derivatives are taken on
spatially periodic lifts to `ℝ × ℝ³`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace RegularisedBoundChallenge

/-! ## The torus and space-time -/

/-- The three-torus `T³ = ℝ³/ℤ³`. -/
abbrev Torus3 : Type := UnitAddTorus (Fin 3)

/-- Space-time `ℝ × T³`. -/
abbrev SpaceTime : Type := ℝ × Torus3

/-- The projection `ℝ³ → T³`. -/
def torusProj (y : Fin 3 → ℝ) : Torus3 := fun i => ((y i : ℝ) : UnitAddCircle)

/-- The representative of a point of `T³` in `[0, 1)³`. -/
def torusRep (x : Torus3) : Fin 3 → ℝ := fun i => (AddCircle.equivIco (1 : ℝ) 0 (x i) : ℝ)

/-- The Euclidean square norm `|v|² = v₁² + v₂² + v₃²` on `ℝ³`. -/
def sqNorm3 (v : Fin 3 → ℝ) : ℝ := ∑ i, v i ^ 2

open scoped ContDiff in
/-- A function on `T³` is smooth if its periodic lift to `ℝ³` is smooth. -/
def IsSmoothOnTorus (f : Torus3 → ℝ) : Prop := ContDiff ℝ ∞ (fun y => f (torusProj y))

open scoped ContDiff in
/-- A function on `ℝ × T³` is smooth if its spatially periodic lift to `ℝ × ℝ³` is smooth. -/
def IsSmoothOnSpaceTime (g : SpaceTime → ℝ) : Prop :=
  ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) => g (p.1, torusProj p.2))

/-! ## Heat kernels -/

/-- The heat kernel on `ℝ³`: `gaussKernel t y = (4πt)^{-3/2} exp(-|y|²/(4t))`. -/
def gaussKernel (t : ℝ) (y : Fin 3 → ℝ) : ℝ :=
  (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) * Real.exp (-sqNorm3 y / (4 * t))

/-- The heat kernel on `T³`, `p_t(x) = ∑_{k ∈ ℤ³} (4πt)^{-3/2} exp(-|x + k|²/(4t))`, evaluated at
the representative of `x` in `[0, 1)³`. -/
def heatKernel (t : ℝ) (x : Torus3) : ℝ :=
  ∑' k : Fin 3 → ℤ, gaussKernel t (torusRep x + fun i => (k i : ℝ))

/-- The heat semigroup on `T³`: `(P_s f)(x) = ∫_{ℝ³} γ_s(y) f(x - y) dy`, where `γ_s` is the
heat kernel on `ℝ³` and `x - y` is taken in `T³`. -/
def heatSemigroup (s : ℝ) (f : C(Torus3, ℝ)) (x : Torus3) : ℝ :=
  ∫ y : Fin 3 → ℝ, gaussKernel s y * f (x - torusProj y)

/-- The massive space-time heat kernel `G(t, x) = 1_{t>0} e^{-t} p_t(x)` on `ℝ × T³`, the kernel of
`(∂_t - Δ + 1)⁻¹`. -/
def massiveHeatKernel (z : SpaceTime) : ℝ :=
  if 0 < z.1 then Real.exp (-z.1) * heatKernel z.1 z.2 else 0

/-! ## The Hölder–Besov norm of negative order -/

/-- `‖f‖_η = sup_{0 < s ≤ 1} s^{-η/2} sup_x |P_s f(x)|`, as an extended real. -/
def holderBesovENorm (η : ℝ) (f : C(Torus3, ℝ)) : ℝ≥0∞ :=
  ⨆ s ∈ Ioc (0 : ℝ) 1, ENNReal.ofReal (s ^ (-η / 2)) * ⨆ x, ‖heatSemigroup s f x‖ₑ

/-! ## White noise, mollifiers and the regularised noise -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `X` is a centred Gaussian vector in `ℝⁿ` with covariance matrix `C` under `P`: it is
a.e.-measurable, its law is Gaussian, and it has mean zero and covariance `C`. -/
def IsCentredGaussianVector (P : Measure Ω) {n : ℕ} (X : Ω → Fin n → ℝ)
    (C : Fin n → Fin n → ℝ) : Prop :=
  AEMeasurable X P ∧ ProbabilityTheory.IsGaussian (P.map X) ∧ (∀ i, ∫ ω, X ω i ∂P = 0) ∧
    ∀ i j, ∫ ω, X ω i * X ω j ∂P = C i j

/-- `W` is a space-time white noise on `ℝ × T³` under `P`: each `W h` with `h` square-integrable
is a random variable, and every finite family is a centred Gaussian vector with covariance
`∫ hᵢ hⱼ`. Measurability is required explicitly: in Mathlib the law of a non-measurable map is a
point mass, which counts as Gaussian. -/
def IsWhiteNoise (P : Measure Ω) (W : (SpaceTime → ℝ) → Ω → ℝ) : Prop :=
  (∀ h : SpaceTime → ℝ, MemLp h 2 → Measurable (W h)) ∧
    ∀ (n : ℕ) (h : Fin n → SpaceTime → ℝ), (∀ i, MemLp (h i) 2) →
      IsCentredGaussianVector P (fun ω i => W (h i) ω) fun i j => ∫ z, h i z * h j z

open scoped ContDiff in
/-- The class of mollifiers: smooth, compactly supported functions on `ℝ × ℝ³` with integral one. -/
structure IsMollifier (ρ : ℝ × (Fin 3 → ℝ) → ℝ) : Prop where
  contDiff : ContDiff ℝ ∞ ρ
  hasCompactSupport : HasCompactSupport ρ
  integral_eq_one : ∫ z, ρ z = 1

/-- The parabolic rescaling `ρ_ε(t, x) = ε⁻⁵ ρ(ε⁻² t, ε⁻¹ x)`. -/
def rescale (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ) (z : ℝ × (Fin 3 → ℝ)) : ℝ :=
  ε ^ (-5 : ℤ) * ρ (ε ^ (-2 : ℤ) * z.1, ε⁻¹ • z.2)

/-- The spatial periodisation `ρ_ε^♯(t, x) = ∑_{k ∈ ℤ³} ρ_ε(t, x + k)`. -/
def periodise (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ) (z : SpaceTime) : ℝ :=
  ∑' k : Fin 3 → ℤ, rescale ρ ε (z.1, torusRep z.2 + fun i => (k i : ℝ))

/-- The test function `ρ_{ε,z}(w) = ρ_ε^♯(z - w)`. -/
def mollifierAt (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ) (z : SpaceTime) (w : SpaceTime) : ℝ :=
  periodise ρ ε (z - w)

/-- `ξ` is a regularised noise at scale `ε`, `ξ(z) = W(ρ_{ε,z})`: smooth in space-time for every
`ω`, and for every `z` measurable and almost surely equal to `W(ρ_{ε,z})`. -/
def IsRegularisedNoise (P : Measure Ω) (W : (SpaceTime → ℝ) → Ω → ℝ)
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ) (ξ : Ω → SpaceTime → ℝ) : Prop :=
  (∀ ω, IsSmoothOnSpaceTime (ξ ω)) ∧
    ∀ z, Measurable (fun ω => ξ ω z) ∧ (fun ω => ξ ω z) =ᵐ[P] W (mollifierAt ρ ε z)

/-! ## The renormalisation constants -/

/-- `G_ε(z) = ∫ G(z - w) ρ_ε^♯(w) dw`. -/
def mollifiedKernel (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ) (z : SpaceTime) : ℝ :=
  ∫ w, massiveHeatKernel (z - w) * periodise ρ ε w

/-- `Q_ε(z) = ∫ G_ε(z + w) G_ε(w) dw`, the covariance of the stationary mollified field. -/
def covariance (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ) (z : SpaceTime) : ℝ :=
  ∫ w, mollifiedKernel ρ ε (z + w) * mollifiedKernel ρ ε w

/-- The Wick constant `C₁^ε = ∫ G_ε²`. -/
def wickConstant (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ) : ℝ :=
  ∫ z, mollifiedKernel ρ ε z ^ 2

/-- The logarithmically divergent constant `C₂^ε = 2 ∫ G Q_ε²`. -/
def sunsetConstant (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ) : ℝ :=
  2 * ∫ z, massiveHeatKernel z * covariance ρ ε z ^ 2

/-! ## Classical solutions -/

open scoped ContDiff in
/-- `u` is a classical solution of `∂_t u = Δu - u³ + c u + f` on `[0, ∞) × T³` with `u(0) = u₀`:
continuous on `[0, ∞) × T³`, smooth on `(0, ∞) × T³`, and satisfying the equation pointwise
there. Derivatives are taken on the spatially periodic lift; only `t ≥ 0` matters. -/
structure IsClassicalSolution (c : ℝ) (f : SpaceTime → ℝ) (u₀ : C(Torus3, ℝ))
    (u : ℝ → C(Torus3, ℝ)) : Prop where
  continuousOn : ContinuousOn (fun z : ℝ × Torus3 => u z.1 z.2) (Set.Ici 0 ×ˢ Set.univ)
  initial : u 0 = u₀
  contDiffOn :
    ContDiffOn ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) => u p.1 (torusProj p.2)) (Set.Ioi 0 ×ˢ Set.univ)
  equation : ∀ t, 0 < t → ∀ y : Fin 3 → ℝ,
    deriv (fun s => u s (torusProj y)) t =
      (∑ i, deriv (deriv fun r => u t (torusProj (Function.update y i r))) (y i))
        - u t (torusProj y) ^ 3 + c * u t (torusProj y) + f (t, torusProj y)

/-! ## The theorems -/

open scoped NNReal in
/-- **Uniform moment bound for the regularised equations.** Let `a ∈ ℝ`,
`η' ∈ (-2/3, -1/2)` and `ρ` a mollifier. There is a function `C : [1, ∞) → [0, ∞)` such that for
every complete probability space carrying a space-time white noise `W`, all regularised noises
`ξ ε`, `ε ∈ (0, 1]`, driven by `W`, and the classical solutions `uε ε x ω` of the equation with
counterterm `a + 3C₁^ε - 9C₂^ε`, forcing `ξ ε ω` and smooth initial value `x`, there are measurable
`M ε ≥ 0` with `√t ‖uε ε x ω t‖_{η'} ≤ M ε ω` for every `ω`, every smooth `x` and `t ∈ (0, 1]`, and
`sup_ε 𝔼[(M ε)^p] ≤ C p` for every `p ≥ 1`. -/
theorem regularisedBound :
    ∀ (a : ℝ) (η' : ℝ) (_hη' : η' ∈ Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ)))
      (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (_hρ : IsMollifier ρ),
    ∃ C : ℝ → ℝ≥0,
    ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
      (W : (SpaceTime → ℝ) → Ω → ℝ) (_hW : IsWhiteNoise P W)
      (ξ : ℝ → Ω → SpaceTime → ℝ) (_hξ : ∀ ε ∈ Ioc (0 : ℝ) 1, IsRegularisedNoise P W ρ ε (ξ ε))
      (uε : ℝ → C(Torus3, ℝ) → Ω → ℝ → C(Torus3, ℝ))
      (_hu : ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ x : C(Torus3, ℝ), IsSmoothOnTorus x → ∀ ω, IsClassicalSolution
        (a + 3 * wickConstant ρ ε - 9 * sunsetConstant ρ ε) (ξ ε ω) x (uε ε x ω)),
    ∃ M : ℝ → Ω → ℝ,
      (∀ ε ∈ Ioc (0 : ℝ) 1, Measurable (M ε) ∧ ∀ ω, 0 ≤ M ε ω) ∧
      (∀ ε ∈ Ioc (0 : ℝ) 1, ∀ ω, ∀ x : C(Torus3, ℝ), IsSmoothOnTorus x → ∀ t ∈ Ioc (0 : ℝ) 1,
        ENNReal.ofReal (√t) * holderBesovENorm η' (uε ε x ω t) ≤ ENNReal.ofReal (M ε ω)) ∧
      ∀ p : ℝ, 1 ≤ p →
        ⨆ ε ∈ Ioc (0 : ℝ) 1, ∫⁻ ω, ENNReal.ofReal (M ε ω) ^ p ∂P ≤ C p := by
  sorry

/-- A space-time white noise exists on some probability space. -/
theorem exists_whiteNoise :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (W : (SpaceTime → ℝ) → Ω → ℝ),
      IsProbabilityMeasure P ∧ IsWhiteNoise P W := by
  sorry

/-- For a white noise `W`, a mollifier `ρ` and `ε ∈ (0, 1]`, a regularised noise exists, any two
agree almost surely as functions on space-time, and each is jointly measurable. -/
theorem regularisedNoise_exists_unique :
    ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : (SpaceTime → ℝ) → Ω → ℝ) (_hW : IsWhiteNoise P W)
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (_hρ : IsMollifier ρ) {ε : ℝ} (_hε : ε ∈ Ioc (0 : ℝ) 1),
    (∃ ξ, IsRegularisedNoise P W ρ ε ξ) ∧
      (∀ ξ ξ', IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ ε ξ' →
        ∀ᵐ ω ∂P, ξ ω = ξ' ω) ∧
      ∀ ξ, IsRegularisedNoise P W ρ ε ξ → Measurable fun p : Ω × SpaceTime => ξ p.1 p.2 := by
  sorry

/-- For smooth forcing `f` and smooth initial data `u₀`, the equation
`∂_t u = Δu - u³ + c u + f`, `u(0) = u₀`, has a classical solution, unique on `[0, ∞)`. -/
theorem classicalSolution_exists_unique :
    ∀ (c : ℝ) {f : SpaceTime → ℝ} (_hf : IsSmoothOnSpaceTime f)
    {u₀ : C(Torus3, ℝ)} (_hu₀ : IsSmoothOnTorus u₀),
    (∃ u, IsClassicalSolution c f u₀ u) ∧
      ∀ u u', IsClassicalSolution c f u₀ u → IsClassicalSolution c f u₀ u' →
        ∀ t, 0 ≤ t → u t = u' t := by
  sorry

/-- Every integral in the definitions of `C₁^ε` and `C₂^ε` converges absolutely, the test
functions `ρ_{ε,z}` are square integrable, and `G_ε` and `Q_ε` are continuous and bounded. -/
theorem constants_finite :
    ∀ (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (_hρ : IsMollifier ρ) {ε : ℝ}
    (_hε : ε ∈ Ioc (0 : ℝ) 1),
    Integrable massiveHeatKernel ∧
      (∀ z, MemLp (mollifierAt ρ ε z) 2) ∧
      (∀ z, Integrable fun w => massiveHeatKernel (z - w) * periodise ρ ε w) ∧
      (Continuous (mollifiedKernel ρ ε) ∧ Integrable (mollifiedKernel ρ ε) ∧
        ∃ C, ∀ z, |mollifiedKernel ρ ε z| ≤ C) ∧
      (∀ z, Integrable fun w => mollifiedKernel ρ ε (z + w) * mollifiedKernel ρ ε w) ∧
      (Continuous (covariance ρ ε) ∧ ∃ C, ∀ z, |covariance ρ ε z| ≤ C) ∧
      Integrable (fun z => mollifiedKernel ρ ε z ^ 2) ∧
      Integrable fun z => massiveHeatKernel z * covariance ρ ε z ^ 2 := by
  sorry

end RegularisedBoundChallenge

end
