/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib

/-!
# The reconstruction theorem

A standalone, Mathlib-only statement of the reconstruction theorem of regularity structures
(M. Hairer, *A theory of regularity structures*, Invent. Math. 198 (2014), Theorem 3.10), in the
semigroup formulation of M. Hoshino (*A semigroup approach to the reconstruction theorem and the
multilevel Schauder estimate for singular modelled distributions*, Theorem 4.1), together with its
test-function form for the parabolic scaling of `ℝ⁴`.

Scope: this is a specialisation, not a formalisation of every assertion of either source theorem.
The regularity structure is finite dimensional; `γ > 0`; the model and `D^γ` bounds are global (on
all of `E`) rather than on compact sets, and they are hypotheses rather than part of the notion of
model; the estimates are those of the semigroup formulation, without Hoshino's weights and
regularity-integrability (Besov) conclusions, and without the statement that `R` is a continuous
linear map. The test-function results are restricted to `ℝ⁴` with the parabolic semigroup, to
homogeneities above `-4` below `γ`, and, for uniqueness, to measurable candidate families with a
global bound of exponent above `-4`.

Distributions on a measure space `(E, μ)` are represented through a regularising semigroup
`Q_t` of order `ℓ`: a distribution `Λ` is the family of its regularisations `Λ_t = Q_t Λ`, `t > 0`.
A model `(Π, Γ)` for a regularity structure `𝒯` assigns to each `x ∈ E` a linear map
`Π_x : T → 𝒟'` and to each pair `x, y` an element `Γ_{xy}` of the structure group. A modelled
distribution `f ∈ D^γ` is a map `E → T_{<γ}` with `|f(y) − Γ_{yx} f(x)|_j ≲ d(y, x)^{γ − deg j}`.

* `exists_reconstruction`: for `γ > 0` the reconstruction `Rf = lim_{s ↓ 0} R^t_s f`, defined by
  an explicit formula, is a distribution with
  `|(Q_t (Rf − Π_x f(x)))(x)| ≤ c ‖Π‖ |||f||| t^{γ/ℓ}` for `0 < t ≤ 1`, and it is the only
  distribution satisfying a bound of this order (Hairer's (3.3) and uniqueness).
* `reconstruct_sub_reconstruct_le`: the reconstruction is locally Lipschitz in the model and the
  modelled distribution (Hairer's (3.4)).
* `abs_pairing_rescaledTestFunction_le`: on `ℝ⁴` with the parabolic scaling, the pairing of
  `Rf − Π_x f(x)` with the rescaled test function `φ^λ_x` exists and is bounded by
  `c ‖Π‖ |||f||| λ^γ` (Hairer's bound (3.3) in test-function form).
* `eq_reconstruct_of_abs_pairing_le`: on `ℝ⁴`, a measurable distribution `Λ` with
  `|Λ_u| ≲ u^{α/4}`, `α > -4`, and `|⟨Λ − Π_x f(x), φ^λ_x⟩| ≲ λ^γ` for one test function `φ`
  with `∫ φ ≠ 0` equals `Rf`.

The parabolic semigroup is the explicit product kernel `q_t(s, x) = g_t(s) ∏ᵢ k_t(xᵢ)`, where
`g_t` and `k_t` have Fourier symbols `exp(−t ξ²)` and `exp(−t ξ⁴)`. The theorems
`parabolicKernel_measurable`, `parabolicKernel_integrable_moment`, `parabolicKernel_moment_le` and
`parabolicKernel_semigroup` state that it is a regularising semigroup of order `4`; they are
compared as theorems in their own right.

Constants are existential: `c` depends only on `𝒯`, the semigroup and `γ`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology

namespace ReconstructionChallenge

/-! ## Regularising semigroups and distributions -/

/-- A regularising semigroup on `(E, μ)`: kernels `Q_t(x, y)` with the semigroup property and
moment bounds `∫ |Q_t(x, y)| d(y, x)^r dμ(y) ≤ M_r t^{r/ℓ}` for every `r ≥ 0` and `t > 0`
([Hos25, Definition 2.6 (i), (iii) and (2.2)]). -/
structure RegularisingSemigroup (E : Type*) [MeasurableSpace E] (μ : Measure E) where
  /-- The kernel `Q_t(x, y)`. -/
  kernel : ℝ → E → E → ℝ
  /-- The scaling order `ℓ`: regularity `α` corresponds to the size `t^{α/ℓ}`. -/
  order : ℝ
  order_pos : 0 < order
  /-- The size `d(y, x)` of the increment from `x` to `y`. -/
  scaleDist : E → E → ℝ
  scaleDist_nonneg : ∀ x y, 0 ≤ scaleDist x y
  /-- The moment constants `M_r`. -/
  momentConst : ℝ → ℝ
  momentConst_nonneg : ∀ r, 0 ≤ momentConst r
  measurable_kernel : ∀ t, Measurable (Function.uncurry (kernel t))
  integrable_moment : ∀ ⦃t : ℝ⦄, 0 < t → ∀ ⦃r : ℝ⦄, 0 ≤ r → ∀ x,
    Integrable (fun y => |kernel t x y| * scaleDist y x ^ r) μ
  moment_le : ∀ ⦃t : ℝ⦄, 0 < t → ∀ ⦃r : ℝ⦄, 0 ≤ r → ∀ x,
    ∫ y, |kernel t x y| * scaleDist y x ^ r ∂μ ≤ momentConst r * t ^ (r / order)
  /-- The semigroup property `Q_s Q_t = Q_{s+t}`. -/
  semigroup : ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t → ∀ x y,
    ∫ z, kernel s x z * kernel t z y ∂μ = kernel (s + t) x y

namespace RegularisingSemigroup

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} (K : RegularisingSemigroup E μ)

/-- The action `(Q_t g)(x) = ∫ Q_t(x, y) g(y) dμ(y)` of the semigroup on functions. -/
def apply (t : ℝ) (g : E → ℝ) (x : E) : ℝ := ∫ y, K.kernel t x y * g y ∂μ

/-- The `Q`-distributions: families `(Λ_t)_{t>0}` of functions with `Q_s Λ_t = Λ_{s+t}`, the
integrals converging absolutely, normalised by `Λ_t = 0` for `t ≤ 0`. `Λ t x` is the
regularisation `(Q_t Λ)(x)` of the distribution `Λ`. -/
def distributions : Set (ℝ → E → ℝ) :=
  {Λ | (∀ ⦃t : ℝ⦄, t ≤ 0 → Λ t = 0) ∧
    ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t → ∀ x,
      Integrable (fun y => K.kernel s x y * Λ t y) μ ∧ K.apply s (Λ t) x = Λ (s + t) x}

/-- The diagonal `y ↦ F y t y = Q_t(y, F_y)` of a germ `F`. -/
def diag (F : E → ℝ → E → ℝ) (t : ℝ) (y : E) : ℝ := F y t y

/-- The approximation `R^t_s F`: `x ↦ ∫ Q_{t-s}(x, y) Q_s(y, F_y) dy` for `s < t`, and the
diagonal `x ↦ Q_s(x, F_x)` otherwise. -/
def approx (F : E → ℝ → E → ℝ) (t s : ℝ) (x : E) : ℝ :=
  if s < t then K.apply (t - s) (diag F s) x else diag F s x

/-- The reconstruction of a germ: `(RF)_t(x) = lim_{s ↓ 0} R^t_s F(x)` for `t > 0`, and `0` for
`t ≤ 0`. -/
def reconstruct (F : E → ℝ → E → ℝ) (t : ℝ) (x : E) : ℝ :=
  if 0 < t then limUnder (𝓝[>] (0 : ℝ)) (fun s => K.approx F t s x) else 0

/-- The pairing `⟨Λ, φ⟩ = lim_{s ↓ 0} ∫ Λ_s φ dμ` of a distribution with a test function. -/
def pairing (_K : RegularisingSemigroup E μ) (Λ : ℝ → E → ℝ) (φ : E → ℝ) : ℝ :=
  limUnder (𝓝[>] (0 : ℝ)) fun s => ∫ y, Λ s y * φ y ∂μ

end RegularisingSemigroup

/-! ## Regularity structures, models and modelled distributions -/

variable {ι : Type*}

/-- The subspace `T_{<α} = span {e_i : deg i < α}` of `T = ι → ℝ`. -/
def lowerSubspace (deg : ι → ℝ) (α : ℝ) : Set (ι → ℝ) := {τ | ∀ i, α ≤ deg i → τ i = 0}

/-- A linear map is graded unipotent if `Γ e_i - e_i ∈ T_{<deg i}` for every basis vector. -/
def IsGradedUnipotent [DecidableEq ι] (deg : ι → ℝ) (Γ : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) : Prop :=
  ∀ i, Γ (Pi.single i 1) - Pi.single i 1 ∈ lowerSubspace deg (deg i)

/-- A regularity structure with graded basis `ι`: degrees `deg i` of the basis vectors and a
structure group `G ≤ GL(ι → ℝ)` of graded unipotent maps [Hai14, Definition 2.1]. -/
structure RegularityStructure (ι : Type*) [Fintype ι] [DecidableEq ι] where
  /-- The homogeneity `|e_i| = deg i` of the basis vector `e_i`. -/
  deg : ι → ℝ
  /-- The structure group. -/
  group : Subgroup (LinearMap.GeneralLinearGroup ℝ (ι → ℝ))
  isGradedUnipotent : ∀ g ∈ group, IsGradedUnipotent deg (g : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))

variable [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E] {μ : Measure E}

/-- A model `(Π, Γ)` for `𝒯` on `E` [Hai14, Definition 2.17]: linear maps `Π_x : T → 𝒟'`,
represented through their regularisations by `K`, and `Γ_{xy} ∈ G` with `Π_x Γ_{xy} = Π_y`,
`Γ_{xx} = 1` and `Γ_{xy} Γ_{yz} = Γ_{xz}`, measurable in the sense below. -/
structure Model (𝒯 : RegularityStructure ι) (K : RegularisingSemigroup E μ) where
  /-- `Π_x : T → 𝒟'`. -/
  pi : E → (ι → ℝ) →ₗ[ℝ] (ℝ → E → ℝ)
  pi_mem : ∀ x τ, pi x τ ∈ K.distributions
  /-- `Γ_{xy} ∈ G`. -/
  gamma : E → E → 𝒯.group
  pi_gamma : ∀ x y τ,
    pi x (((gamma x y : LinearMap.GeneralLinearGroup ℝ (ι → ℝ)) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) τ) =
      pi y τ
  gamma_self : ∀ x, gamma x x = 1
  gamma_mul : ∀ x y z, gamma x y * gamma y z = gamma x z
  measurable_diag : ∀ i ⦃t : ℝ⦄, 0 < t → Measurable fun x => pi x (Pi.single i 1) t x
  measurable_pi : ∀ x i ⦃t : ℝ⦄, 0 < t → Measurable (pi x (Pi.single i 1) t)

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ}

/-- `Γ_{xy}` as a linear map of `T`. -/
def gammaMap (M : Model 𝒯 K) (x y : E) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) :=
  ((M.gamma x y : LinearMap.GeneralLinearGroup ℝ (ι → ℝ)) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))

/-- `(Q_t Π_x τ)(z)`: the regularisation of the distribution `Π_x τ`. -/
def regPi (M : Model 𝒯 K) (x : E) (τ : ι → ℝ) (t : ℝ) (z : E) : ℝ := M.pi x τ t z

/-- The model bound `|(Q_t Π_x e_i)(x)| ≤ C t^{deg i/ℓ}` for `deg i < γ`, `0 < t ≤ 1`, `x ∈ S`. -/
def PiBoundOn (M : Model 𝒯 K) (γ C : ℝ) (S : Set E) : Prop :=
  ∀ i, 𝒯.deg i < γ → ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x ∈ S,
    |M.regPi x (Pi.single i 1) t x| ≤ C * t ^ (𝒯.deg i / K.order)

/-- The bound `|(Q_t (Π¹_x − Π²_x) e_i)(x)| ≤ C t^{deg i/ℓ}` on the difference of two models. -/
def PiDiffBoundOn (M₁ M₂ : Model 𝒯 K) (γ C : ℝ) (S : Set E) : Prop :=
  ∀ i, 𝒯.deg i < γ → ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x ∈ S,
    |M₁.regPi x (Pi.single i 1) t x - M₂.regPi x (Pi.single i 1) t x| ≤
      C * t ^ (𝒯.deg i / K.order)

/-- The bounds of `D^γ` on `S` with constant `C`: `|f(x)_i| ≤ C` for `deg i < γ` and
`|(f(y) − Γ_{yx} f(x))_j| ≤ C d(y, x)^{γ − deg j}` for `deg j < γ`. -/
def ModelledBoundOn (M : Model 𝒯 K) (γ C : ℝ) (S : Set E) (f : E → ι → ℝ) : Prop :=
  (∀ x ∈ S, ∀ i, 𝒯.deg i < γ → |f x i| ≤ C) ∧
    ∀ x ∈ S, ∀ y ∈ S, ∀ j, 𝒯.deg j < γ →
      |(f y - M.gammaMap y x (f x)) j| ≤ C * K.scaleDist y x ^ (γ - 𝒯.deg j)

/-- The bound `|||f¹; f²|||_{γ;S} ≤ C` comparing `f¹ ∈ D^γ(M₁)` and `f² ∈ D^γ(M₂)`:
`|f¹(x)_i − f²(x)_i| ≤ C` and
`|(f¹(y) − Γ¹_{yx} f¹(x) − f²(y) + Γ²_{yx} f²(x))_j| ≤ C d(y, x)^{γ − deg j}` [Hai14, (3.2)]. -/
def ModelledDiffBoundOn (M₁ M₂ : Model 𝒯 K) (γ C : ℝ) (S : Set E) (f₁ f₂ : E → ι → ℝ) :
    Prop :=
  (∀ x ∈ S, ∀ i, 𝒯.deg i < γ → |f₁ x i - f₂ x i| ≤ C) ∧
    ∀ x ∈ S, ∀ y ∈ S, ∀ j, 𝒯.deg j < γ →
      |(f₁ y - M₁.gammaMap y x (f₁ x)) j - (f₂ y - M₂.gammaMap y x (f₂ x)) j| ≤
        C * K.scaleDist y x ^ (γ - 𝒯.deg j)

/-- The space `D^γ` of modelled distributions of order `γ`: measurable maps into `T_{<γ}` with
the bounds of `ModelledBoundOn` on all of `E` for some constant. -/
def modelledDistributions (M : Model 𝒯 K) (γ : ℝ) : Set (E → ι → ℝ) :=
  {f | Measurable f ∧ (∀ x, f x ∈ lowerSubspace 𝒯.deg γ) ∧ ∃ C, M.ModelledBoundOn γ C univ f}

/-- The germ `y ↦ Π_y f(y)` of a modelled distribution, through its regularisations. -/
def germ (M : Model 𝒯 K) (f : E → ι → ℝ) (y : E) (t : ℝ) (z : E) : ℝ := M.regPi y (f y) t z

/-- The reconstruction `Rf` of a modelled distribution: the reconstruction of its germ. -/
def reconstruct (M : Model 𝒯 K) (f : E → ι → ℝ) : ℝ → E → ℝ := K.reconstruct (M.germ f)

/-- The distribution `Rf − Π_{x₀} f(x₀)`, through its regularisations. -/
def reconstructSubAt (M : Model 𝒯 K) (f : E → ι → ℝ) (x₀ : E) (t : ℝ) (y : E) : ℝ :=
  M.reconstruct f t y - M.regPi x₀ (f x₀) t y

end Model

/-! ## The parabolic semigroup on `ℝ⁴` -/

/-- Space-time `ℝ⁴ = ℝ × ℝ³`, with time first, and Lebesgue measure. -/
abbrev ParabolicSpace : Type := ℝ × (Fin 3 → ℝ)

/-- The parabolic size `‖z‖_𝔰 = |z₀|^{1/2} + ∑ᵢ |zᵢ|` for the scaling `𝔰 = (2, 1, 1, 1)`. -/
def parabolicNorm (z : ParabolicSpace) : ℝ := Real.sqrt |z.1| + ∑ i, |z.2 i|

/-- The parabolic dilation `S^c z = (c² z₀, c z')`. -/
def parabolicDilate (c : ℝ) (z : ParabolicSpace) : ParabolicSpace := (c ^ 2 * z.1, c • z.2)

/-- The kernel with symbol `ξ ↦ exp(-t ξ^{2j})`:
`symKernel j t b = ∫ exp(-t ξ^{2j}) cos(2π ξ b) dξ`. -/
def symKernel (j : ℕ) (t b : ℝ) : ℝ :=
  ∫ ξ, Real.exp (-(t * ξ ^ (2 * j))) * Real.cos (2 * Real.pi * ξ * b)

/-- The one-dimensional heat kernel `g_t`, with symbol `exp(-t ξ²)`. -/
def heatKernel1D (t b : ℝ) : ℝ := symKernel 1 t b

/-- The quartic kernel `k_t`, with symbol `exp(-t ξ⁴)`. -/
def quarticKernel (t b : ℝ) : ℝ := symKernel 2 t b

/-- The moment `G_s = ∫ |g_1(b)| |b|^s db`. -/
def heatMoment (s : ℝ) : ℝ := ∫ b, |heatKernel1D 1 b| * |b| ^ s

/-- The moment `K_s = ∫ |k_1(b)| |b|^s db`. -/
def quarticMoment (s : ℝ) : ℝ := ∫ b, |quarticKernel 1 b| * |b| ^ s

/-- The parabolic kernel `q_t(s, x) = g_t(s) ∏ᵢ k_t(xᵢ)`. -/
def parabolicKernel (t : ℝ) (z : ParabolicSpace) : ℝ :=
  heatKernel1D t z.1 * ∏ i, quarticKernel t (z.2 i)

/-- The moment constant `M_r = 4^r (G_{r/2} K_0³ + 3 G_0 K_r K_0²)` of the parabolic kernel. -/
def parabolicMomentConst (r : ℝ) : ℝ :=
  (4 : ℝ) ^ r * (heatMoment (r / 2) * quarticMoment 0 ^ 3 +
    3 * (heatMoment 0 * quarticMoment r * quarticMoment 0 ^ 2))

/-- The parabolic kernel is jointly measurable in `(x, y) ↦ q_t(x − y)`. -/
theorem parabolicKernel_measurable :
    ∀ t, Measurable (Function.uncurry fun x y : ParabolicSpace => parabolicKernel t (x - y)) := by
  sorry

/-- The parabolic moments `∫ |q_t(x − y)| ‖y − x‖_𝔰^r dy` are finite for `t > 0`, `r ≥ 0`. -/
theorem parabolicKernel_integrable_moment :
    ∀ ⦃t : ℝ⦄, 0 < t → ∀ ⦃r : ℝ⦄, 0 ≤ r → ∀ x : ParabolicSpace,
      Integrable fun y => |parabolicKernel t (x - y)| * parabolicNorm (y - x) ^ r := by
  sorry

/-- The parabolic moment bound `∫ |q_t(x − y)| ‖y − x‖_𝔰^r dy ≤ M_r t^{r/4}`. -/
theorem parabolicKernel_moment_le :
    ∀ ⦃t : ℝ⦄, 0 < t → ∀ ⦃r : ℝ⦄, 0 ≤ r → ∀ x : ParabolicSpace,
      ∫ y, |parabolicKernel t (x - y)| * parabolicNorm (y - x) ^ r ≤
        parabolicMomentConst r * t ^ (r / 4) := by
  sorry

/-- The semigroup property `q_s ∗ q_t = q_{s+t}`. -/
theorem parabolicKernel_semigroup :
    ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t → ∀ x y : ParabolicSpace,
      ∫ z, parabolicKernel s (x - z) * parabolicKernel t (z - y) =
        parabolicKernel (s + t) (x - y) := by
  sorry

/-- The parabolic semigroup `Q_t(x, y) = q_t(x − y)` of order `4` on `ℝ⁴`, with
`d(y, x) = ‖y − x‖_𝔰`. -/
def parabolicSemigroup : RegularisingSemigroup ParabolicSpace volume where
  kernel t x y := parabolicKernel t (x - y)
  order := 4
  order_pos := four_pos
  scaleDist x y := parabolicNorm (x - y)
  scaleDist_nonneg x y :=
    add_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  momentConst := parabolicMomentConst
  momentConst_nonneg r := by
    unfold parabolicMomentConst heatMoment quarticMoment
    positivity
  measurable_kernel := parabolicKernel_measurable
  integrable_moment := parabolicKernel_integrable_moment
  moment_le := parabolicKernel_moment_le
  semigroup := parabolicKernel_semigroup

/-- `φ^c_z(w) = c⁻⁵ φ((w₀ − z₀)/c², (w' − z')/c)`. -/
def rescaledTestFunction (φ : ParabolicSpace → ℝ) (c : ℝ) (z w : ParabolicSpace) : ℝ :=
  (c ^ 5)⁻¹ * φ (parabolicDilate c⁻¹ (w - z))

open scoped ContDiff in
/-- `B^r`: smooth functions vanishing outside the closed unit parabolic ball, with
`‖D^k φ‖ ≤ 1` for `k ≤ r`. -/
def testFunctionClass (r : ℕ) : Set (ParabolicSpace → ℝ) :=
  {φ | ContDiff ℝ ∞ φ ∧ (∀ w, 1 < parabolicNorm w → φ w = 0) ∧
    ∀ k ≤ r, ∀ w, ‖iteratedFDeriv ℝ k φ w‖ ≤ 1}

/-! ## The theorems -/

/-- **Reconstruction** [Hai14, Theorem 3.10], [Hos25, Theorem 4.1]. For `γ > 0` there is `c ≥ 0`
such that for every model with `‖Π‖ ≤ C_Π` and every `f ∈ D^γ` with `|||f||| ≤ C_f`, the
reconstruction `Rf` is a distribution, `|(Q_t (Rf − Π_x f(x)))(x)| ≤ c C_Π C_f t^{γ/ℓ}` for
`0 < t ≤ 1`, and every distribution `Λ` with `|(Q_t (Λ − Π_x f(x)))(x)| ≤ C' t^{γ/ℓ}` equals
`Rf`. -/
theorem exists_reconstruction :
    ∀ {E : Type*} [MeasurableSpace E] {μ : Measure E} {ι : Type*} [Fintype ι] [DecidableEq ι]
      (𝒯 : RegularityStructure ι) (K : RegularisingSemigroup E μ) [SFinite μ] {γ : ℝ},
      0 < γ →
        ∃ c : ℝ, 0 ≤ c ∧
          ∀ (M : Model 𝒯 K) ⦃CPi Cf : ℝ⦄ ⦃f : E → ι → ℝ⦄,
            M.PiBoundOn γ CPi univ → 0 ≤ CPi → f ∈ M.modelledDistributions γ →
              M.ModelledBoundOn γ Cf univ f → 0 ≤ Cf →
                M.reconstruct f ∈ K.distributions ∧
                  (∀ t ∈ Ioc (0 : ℝ) 1, ∀ x,
                    |M.reconstruct f t x - M.regPi x (f x) t x| ≤
                      c * CPi * Cf * t ^ (γ / K.order)) ∧
                  ∀ Λ ∈ K.distributions,
                    (∃ C' : ℝ, ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x,
                      |Λ t x - M.regPi x (f x) t x| ≤ C' * t ^ (γ / K.order)) →
                    Λ = M.reconstruct f := by
  sorry

/-- **Reconstruction is Lipschitz in the model** [Hai14, Theorem 3.10, (3.4)]. For `γ > 0` there
is `c` such that for two models and `f₁ ∈ D^γ(M₁)`, `f₂ ∈ D^γ(M₂)`,
`|Q_t(Rf₁ − Rf₂ − Π¹_x f₁(x) + Π²_x f₂(x))(x)| ≤ c (C_{f₁} C_{δΠ} + C_{δf} C_{Π₂}) t^{γ/ℓ}`. -/
theorem reconstruct_sub_reconstruct_le :
    ∀ {E : Type*} [MeasurableSpace E] {μ : Measure E} {ι : Type*} [Fintype ι] [DecidableEq ι]
      (𝒯 : RegularityStructure ι) (K : RegularisingSemigroup E μ) [SFinite μ] {γ : ℝ},
      0 < γ →
        ∃ c : ℝ, ∀ (M₁ M₂ : Model 𝒯 K) {CPi₁ CPi₂ CdPi Cf₁ Cf₂ Cdf : ℝ},
          M₁.PiBoundOn γ CPi₁ univ → M₂.PiBoundOn γ CPi₂ univ →
            M₁.PiDiffBoundOn M₂ γ CdPi univ → 0 ≤ CPi₁ → 0 ≤ CPi₂ → 0 ≤ CdPi →
              ∀ {f₁ f₂ : E → ι → ℝ}, f₁ ∈ M₁.modelledDistributions γ →
                f₂ ∈ M₂.modelledDistributions γ → M₁.ModelledBoundOn γ Cf₁ univ f₁ →
                  M₂.ModelledBoundOn γ Cf₂ univ f₂ → M₁.ModelledDiffBoundOn M₂ γ Cdf univ f₁ f₂ →
                    0 ≤ Cf₁ → 0 ≤ Cf₂ → 0 ≤ Cdf → ∀ {t : ℝ}, t ∈ Ioc (0 : ℝ) 1 → ∀ x,
                      |M₁.reconstruct f₁ t x - M₂.reconstruct f₂ t x -
                          (M₁.regPi x (f₁ x) t x - M₂.regPi x (f₂ x) t x)| ≤
                        c * (Cf₁ * CdPi + Cdf * CPi₂) * t ^ (γ / K.order) := by
  sorry

/-- **Reconstruction bound against test functions** [Hai14, Theorem 3.10, (3.3)], parabolic
scaling on `ℝ⁴`. If `-4 < deg i` for `deg i < γ`, then for every `φ ∈ B^4`, `0 < λ ≤ 1` and `x`,
the pairing `⟨Rf − Π_x f(x), φ^λ_x⟩` exists as a limit and is at most `c C_Π C_f λ^γ`. -/
theorem abs_pairing_rescaledTestFunction_le :
    ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] (𝒯 : RegularityStructure ι) {γ : ℝ}, 0 < γ →
      ∃ c : ℝ, ∀ (M : Model 𝒯 parabolicSemigroup) {CPi Cf : ℝ},
        M.PiBoundOn γ CPi univ → 0 ≤ CPi →
          ∀ {f : ParabolicSpace → ι → ℝ}, f ∈ M.modelledDistributions γ →
            M.ModelledBoundOn γ Cf univ f → 0 ≤ Cf → (∀ i, 𝒯.deg i < γ → -4 < 𝒯.deg i) →
              ∀ {φ : ParabolicSpace → ℝ}, φ ∈ testFunctionClass 4 →
                ∀ {lam : ℝ}, 0 < lam → lam ≤ 1 → ∀ x : ParabolicSpace,
                  Tendsto
                      (fun s => ∫ y, M.reconstructSubAt f x s y * rescaledTestFunction φ lam x y)
                      (𝓝[>] 0)
                      (𝓝 (parabolicSemigroup.pairing (M.reconstructSubAt f x)
                        (rescaledTestFunction φ lam x))) ∧
                    |parabolicSemigroup.pairing (M.reconstructSubAt f x)
                        (rescaledTestFunction φ lam x)| ≤ c * CPi * Cf * lam ^ γ := by
  sorry

/-- **Uniqueness against test functions** [Hai14, Theorem 3.10], parabolic scaling on `ℝ⁴`. If
`-4 < deg i` for `deg i < γ` and `Λ` is a measurable distribution with `|Λ_u| ≤ C_Λ u^{α/4}`,
`α > -4`, such that `|⟨Λ − Π_x f(x), φ^λ_x⟩| ≤ C₃ λ^γ` for all `0 < λ ≤ 1` and `x`, for one
`φ ∈ B^4` with `∫ φ ≠ 0`, then `Λ = Rf`. -/
theorem eq_reconstruct_of_abs_pairing_le :
    ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}
      (M : Model 𝒯 parabolicSemigroup) {γ CPi Cf : ℝ} {f : ParabolicSpace → ι → ℝ},
      0 < γ → M.PiBoundOn γ CPi univ → 0 ≤ CPi → f ∈ M.modelledDistributions γ →
        M.ModelledBoundOn γ Cf univ f → 0 ≤ Cf → (∀ i, 𝒯.deg i < γ → -4 < 𝒯.deg i) →
          ∀ {Λ : ℝ → ParabolicSpace → ℝ}, Λ ∈ parabolicSemigroup.distributions →
            (∀ u, 0 < u → Measurable (Λ u)) → ∀ {α CΛ : ℝ}, -4 < α →
              (∀ u ∈ Ioc (0 : ℝ) 1, ∀ y, |Λ u y| ≤ CΛ * u ^ (α / 4)) →
                ∀ {φ : ParabolicSpace → ℝ}, φ ∈ testFunctionClass 4 → ∫ w, φ w ≠ 0 →
                  ∀ {C₃ : ℝ}, (∀ c ∈ Ioc (0 : ℝ) 1, ∀ x,
                      |parabolicSemigroup.pairing (fun t y => Λ t y - M.regPi x (f x) t y)
                        (rescaledTestFunction φ c x)| ≤ C₃ * c ^ γ) →
                    Λ = M.reconstruct f := by
  sorry

end ReconstructionChallenge

end
