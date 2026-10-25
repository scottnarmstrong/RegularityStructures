/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import RegularityStructures.Statements.SchauderEstimate
public import RegularityStructures.Statements.SchauderReconstruction

/-!
# Solution: the multilevel Schauder estimate, proved

This file repeats `Challenge.lean` verbatim and proves each theorem from the corresponding
statement of the library `RegularityStructures`. The `Bridge` section maps the Challenge's
regularising semigroups, regularity structures, models, polynomial sectors and the structures of
the standing hypotheses to the library's. The recursive definitions `lineIter` and `boxSet` are
identified with the library's by induction, and the definitions built on them by rewriting; every
other definition unfolds to the library definition of the same name, the Challenge's sets and
functions being the carriers of the library's submodules and linear maps.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology

namespace SchauderChallenge

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

/-- The model bound `|(Γ_{yx} e_i)_j| ≤ C d(y, x)^{deg i - deg j}` for `deg j < deg i < γ`,
`x, y ∈ S`. -/
def GammaBoundOn (M : Model 𝒯 K) (γ C : ℝ) (S : Set E) : Prop :=
  ∀ i j, 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i → ∀ x ∈ S, ∀ y ∈ S,
    |M.gammaMap y x (Pi.single i 1) j| ≤ C * K.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j)

/-- The bounds of `D^γ` on `S` with constant `C`: `|f(x)_i| ≤ C` for `deg i < γ` and
`|(f(y) − Γ_{yx} f(x))_j| ≤ C d(y, x)^{γ − deg j}` for `deg j < γ`. -/
def ModelledBoundOn (M : Model 𝒯 K) (γ C : ℝ) (S : Set E) (f : E → ι → ℝ) : Prop :=
  (∀ x ∈ S, ∀ i, 𝒯.deg i < γ → |f x i| ≤ C) ∧
    ∀ x ∈ S, ∀ y ∈ S, ∀ j, 𝒯.deg j < γ →
      |(f y - M.gammaMap y x (f x)) j| ≤ C * K.scaleDist y x ^ (γ - 𝒯.deg j)

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
  exact RegularityStructures.parabolicSemigroup.measurable_kernel

/-- The parabolic moments `∫ |q_t(x − y)| ‖y − x‖_𝔰^r dy` are finite for `t > 0`, `r ≥ 0`. -/
theorem parabolicKernel_integrable_moment :
    ∀ ⦃t : ℝ⦄, 0 < t → ∀ ⦃r : ℝ⦄, 0 ≤ r → ∀ x : ParabolicSpace,
      Integrable fun y => |parabolicKernel t (x - y)| * parabolicNorm (y - x) ^ r := by
  exact RegularityStructures.parabolicSemigroup.integrable_moment

/-- The parabolic moment bound `∫ |q_t(x − y)| ‖y − x‖_𝔰^r dy ≤ M_r t^{r/4}`. -/
theorem parabolicKernel_moment_le :
    ∀ ⦃t : ℝ⦄, 0 < t → ∀ ⦃r : ℝ⦄, 0 ≤ r → ∀ x : ParabolicSpace,
      ∫ y, |parabolicKernel t (x - y)| * parabolicNorm (y - x) ^ r ≤
        parabolicMomentConst r * t ^ (r / 4) := by
  exact RegularityStructures.parabolicSemigroup.moment_le

/-- The semigroup property `q_s ∗ q_t = q_{s+t}`. -/
theorem parabolicKernel_semigroup :
    ∀ ⦃s t : ℝ⦄, 0 < s → 0 < t → ∀ x y : ParabolicSpace,
      ∫ z, parabolicKernel s (x - z) * parabolicKernel t (z - y) =
        parabolicKernel (s + t) (x - y) := by
  exact RegularityStructures.parabolicSemigroup.semigroup

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

/-! ## Sectors, polynomials and abstract integration -/

section Integration

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The homogeneous subspace `T_α = span {e_i : deg i = α}`. -/
def homogeneousSubspace (deg : ι → ℝ) (α : ℝ) : Set (ι → ℝ) := {τ | ∀ i, deg i ≠ α → τ i = 0}

/-- The projection `Q_α : T → T_α` onto the homogeneous component of degree `α`. -/
def homogeneousProj (deg : ι → ℝ) (α : ℝ) (τ : ι → ℝ) : ι → ℝ :=
  fun i => if deg i = α then τ i else 0

/-- A sector [Hai14, Definition 2.5]: a graded, `G`-invariant subspace of `T`. -/
structure RegularityStructure.IsSector (𝒯 : RegularityStructure ι) (V : Submodule ℝ (ι → ℝ)) :
    Prop where
  graded : ∀ α, ∀ a ∈ V, homogeneousProj 𝒯.deg α a ∈ V
  invariant : ∀ g ∈ 𝒯.group, ∀ a ∈ V,
    ((g : LinearMap.GeneralLinearGroup ℝ (ι → ℝ)) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) a ∈ V

/-- The parabolic weights `𝔰 = (2, 1, 1, 1)`. -/
def parabolicWeight : Fin 4 → ℕ := ![2, 1, 1, 1]

/-- The parabolic degree `|k|_𝔰 = 2k₀ + k₁ + k₂ + k₃` of a multi-index. -/
def multiDeg (k : Fin 4 →₀ ℕ) : ℕ := Finsupp.weight parabolicWeight k

/-- The multi-indices `k` of parabolic degree `|k|_𝔰 < N`: the basis of the polynomial
regularity structure. -/
abbrev PolyIndex (N : ℕ) : Type := {k : Fin 4 →₀ ℕ // Finsupp.weight parabolicWeight k < N}

theorem finite_polyIndex (N : ℕ) : Finite (PolyIndex N) :=
  Finite.of_injective
    (fun k : PolyIndex N => fun i : Fin 4 => (⟨k.1 i, lt_of_le_of_lt
      (Finsupp.le_weight parabolicWeight (by fin_cases i <;> decide) k.1) k.2⟩ : Fin N))
    fun _ _ h => Subtype.ext (Finsupp.ext fun i => congrArg Fin.val (congrFun h i))

instance instFintypePolyIndex (N : ℕ) : Fintype (PolyIndex N) :=
  haveI := finite_polyIndex N
  Fintype.ofFinite _

/-- The homogeneity `|X^k|_𝔰` of the basis vector `X^k`. -/
def polyDeg (N : ℕ) : PolyIndex N → ℝ := fun k => (Finsupp.weight parabolicWeight k.1 : ℝ)

/-- The abstract polynomials `X^k`, `|k|_𝔰 < N`, inside a regularity structure on `ℝ⁴`: an
injective, degree-preserving embedding of `PolyIndex N` into the basis whose span `T̄` is
invariant under the structure group. -/
structure PolynomialSector (𝒯 : RegularityStructure ι) (N : ℕ) where
  /-- The basis index of `X^k`. -/
  emb : PolyIndex N → ι
  emb_injective : Function.Injective emb
  deg_emb : ∀ k, 𝒯.deg (emb k) = polyDeg N k
  invariant : ∀ g ∈ 𝒯.group, ∀ τ : ι → ℝ, (∀ i, i ∉ Set.range emb → τ i = 0) →
    ∀ i, i ∉ Set.range emb →
      ((g : LinearMap.GeneralLinearGroup ℝ (ι → ℝ)) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) τ i = 0

/-- The span `T̄` of the abstract polynomials. -/
def PolynomialSector.subspace {𝒯 : RegularityStructure ι} {N : ℕ} (P : PolynomialSector 𝒯 N) :
    Set (ι → ℝ) :=
  {τ | ∀ i, i ∉ Set.range P.emb → τ i = 0}

/-- An abstract integration map of order `β` on the sector `V` [Hai14, Definition 5.7]. -/
structure IsAbstractIntegration {𝒯 : RegularityStructure ι} {N : ℕ}
    (P : PolynomialSector 𝒯 N) (V : Submodule ℝ (ι → ℝ)) (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))
    (β : ℝ) : Prop where
  pos : 0 < β
  map_homogeneous : ∀ α, ∀ a ∈ V, a ∈ homogeneousSubspace 𝒯.deg α →
    I a ∈ homogeneousSubspace 𝒯.deg (α + β)
  map_poly : ∀ a ∈ V, a ∈ P.subspace → I a = 0
  comm : ∀ g ∈ 𝒯.group, ∀ a ∈ V,
    I (((g : LinearMap.GeneralLinearGroup ℝ (ι → ℝ)) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) a) -
      ((g : LinearMap.GeneralLinearGroup ℝ (ι → ℝ)) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (I a) ∈ P.subspace

end Integration

/-- The four coordinates `(z₀, z₁, z₂, z₃)` of a point of parabolic space. -/
def parabolicCoords (z : ParabolicSpace) : Fin 4 → ℝ := ![z.1, z.2 0, z.2 1, z.2 2]

/-- Evaluation of a polynomial in four variables at a point of parabolic space. -/
def evalParabolic (p : MvPolynomial (Fin 4) ℝ) (z : ParabolicSpace) : ℝ :=
  MvPolynomial.eval (parabolicCoords z) p

/-- The polynomial `∑ τ_k X^k` with coefficient vector `τ`. -/
def toPoly (N : ℕ) (τ : PolyIndex N → ℝ) : MvPolynomial (Fin 4) ℝ :=
  ∑ k, τ k • MvPolynomial.monomial k.1 (1 : ℝ)

/-- The polynomial `z ↦ (z - x)^τ`. -/
def polyEval {N : ℕ} (x : ParabolicSpace) (τ : PolyIndex N → ℝ) (z : ParabolicSpace) : ℝ :=
  MvPolynomial.eval (parabolicCoords (z - x)) (toPoly N τ)

/-- The regularisations `t ↦ Q_t (z ↦ (z - x)^τ)` of the polynomial `(· - x)^τ`, extended by `0`
to `t ≤ 0`. -/
def polyReg {N : ℕ} (x : ParabolicSpace) (τ : PolyIndex N → ℝ) : ℝ → ParabolicSpace → ℝ :=
  fun t y => if 0 < t then parabolicSemigroup.apply t (polyEval x τ) y else 0

/-- The multi-index factorial `k! = ∏ᵢ kᵢ!`. -/
def multiFactorial (k : Fin 4 →₀ ℕ) : ℕ := ∏ i, (k i).factorial

/-! ## The heat kernel and its decomposition into polynomial-annihilating shells -/

/-- The Euclidean square norm `|v|² = v₁² + v₂² + v₃²` on `ℝ³`. -/
def sqNorm3 (v : Fin 3 → ℝ) : ℝ := ∑ i, v i ^ 2

/-- The heat kernel on `ℝ³`: `gaussKernel t y = (4πt)^{-3/2} exp(-|y|²/(4t))`. -/
def gaussKernel (t : ℝ) (y : Fin 3 → ℝ) : ℝ :=
  (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) * Real.exp (-sqNorm3 y / (4 * t))

/-- The heat kernel `G(t, x) = 1_{t>0} (4πt)^{-3/2} e^{-|x|²/(4t)}` on `ℝ⁴ = ℝ × ℝ³`. -/
def heatKernelR4 (z : ParabolicSpace) : ℝ := if 0 < z.1 then gaussKernel z.1 z.2 else 0

/-- A smooth (away from `0`) parabolic norm `(z₀² + |z'|⁴)^{1/4}`. -/
def smoothParabolicNorm (z : ParabolicSpace) : ℝ := (z.1 ^ 2 + sqNorm3 z.2 ^ 2) ^ (1 / 4 : ℝ)

/-- A smooth cutoff, `1` on `(-∞, 1]` and `0` on `[2, ∞)`. -/
def dyadicCutoff (r : ℝ) : ℝ := Real.smoothTransition (2 - r)

/-- The dyadic bump `χ(r) - χ(2r)`, supported in `[1/2, 2]`. -/
def dyadicBump (r : ℝ) : ℝ := dyadicCutoff r - dyadicCutoff (2 * r)

/-- The `n`-th dyadic piece `G(z) χ_n(z)` of the heat kernel. -/
def heatShell (n : ℕ) (z : ParabolicSpace) : ℝ :=
  heatKernelR4 z * dyadicBump (2 ^ (n + 3) * smoothParabolicNorm z)

/-- The monomial function `z ↦ z^k` on parabolic space. -/
def momentMono (k : Fin 4 →₀ ℕ) (z : ParabolicSpace) : ℝ :=
  evalParabolic (MvPolynomial.monomial k 1) z

/-- The prescribed moments `∫ z^k heatShell 0 / (1 - 2^{-2-|k|_𝔰})` of the correcting bump. -/
def annMoment {N : ℕ} (k : PolyIndex N) : ℝ :=
  (∫ z, momentMono k.1 z * heatShell 0 z) / (1 - (((2 : ℝ) ^ (2 + multiDeg k.1)))⁻¹)

open scoped ContDiff in
/-- A smooth bump supported in the closed unit parabolic ball with the prescribed moments
`annMoment k` for `|k|_𝔰 < N` exists. -/
theorem exists_annBump (N : ℕ) :
    ∃ ψ : ParabolicSpace → ℝ, ContDiff ℝ ∞ ψ ∧ (∀ z, 1 < parabolicNorm z → ψ z = 0) ∧
      ∀ k : PolyIndex N,
        ∫ z, evalParabolic (MvPolynomial.monomial k.1 1) z * ψ z = annMoment k := by
  exact RegularityStructures.exists_annBump N

/-- The correcting bump `ψ`: a choice of a function as in `exists_annBump`. -/
def annBump (N : ℕ) : ParabolicSpace → ℝ := Classical.choose (exists_annBump N)

/-- The `n`-th dyadic rescaling `z ↦ (2^n)^3 h(S^{2^n} z)` of `h`. -/
def scaledShell (h : ParabolicSpace → ℝ) (n : ℕ) (z : ParabolicSpace) : ℝ :=
  ((2 : ℝ) ^ n) ^ 3 * h (parabolicDilate (2 ^ n) z)

/-- The base kernel `K₀ = heatShell 0 - ψ + 2³ ψ(S² ·)`, which annihilates the polynomials of
degree `< N`. -/
def annKernel0 (N : ℕ) (z : ParabolicSpace) : ℝ :=
  heatShell 0 z - annBump N z + 2 ^ 3 * annBump N (parabolicDilate 2 z)

/-- The `n`-th polynomial-annihilating shell `K_n = (2^n)^3 K₀(S^{2^n} z)`; the kernel of the
Schauder estimate is `K = ∑_n K_n`. -/
def annShell (N n : ℕ) (z : ParabolicSpace) : ℝ := scaledShell (annKernel0 N) n z

/-! ## Derivatives and Taylor expansions of the kernel -/

/-- The directional derivative `D_d f = x ↦ f'(x) d`. -/
def dirDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (d : E) (f : E → ℝ) : E → ℝ :=
  fun x => fderiv ℝ f x d

/-- `lineIter [d₁, …, dₙ] f = D_{d₁} ⋯ D_{dₙ} f`. -/
def lineIter {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    List E → (E → ℝ) → E → ℝ
  | [], f => f
  | d :: L, f => dirDeriv d (lineIter L f)

/-- The time direction `(1, 0)` of `ℝ⁴`. -/
def timeDir : ParabolicSpace := (1, 0)

/-- The space direction `(0, eᵢ)` of `ℝ⁴`. -/
def spaceDir (i : Fin 3) : ParabolicSpace := (0, Pi.single i 1)

/-- The coordinate directions of `ℝ⁴`: `0 ↦ (1, 0)`, `i + 1 ↦ (0, eᵢ)`. -/
def coordDir : Fin 4 → ParabolicSpace := Fin.cases timeDir spaceDir

/-- The list of directions of the multi-index `k`: `k_j` copies of `coordDir j`, so that
`lineIter (multiDirs k) = D^k`. -/
def multiDirs (k : Fin 4 →₀ ℕ) : List ParabolicSpace := (Finsupp.toMultiset k).toList.map coordDir

/-- The box of multi-indices supported on `J` with `kᵢ ≤ mᵢ`. -/
def boxSet (m : Fin 4 → ℕ) : List (Fin 4) → Finset (Fin 4 →₀ ℕ)
  | [] => {0}
  | j :: J => ((boxSet m J) ×ˢ (Finset.range (m j + 1))).image
      (fun q => q.1 + Finsupp.single j q.2)

/-- The multi-indices `k` with `|k|_𝔰 < σ`, as a finite set. -/
def taylorIdx (σ : ℝ) : Finset (Fin 4 →₀ ℕ) :=
  (boxSet (fun _ => ⌈σ⌉₊) (List.finRange 4)).filter fun k => (multiDeg k : ℝ) < σ

/-- `k! = ∏ᵢ kᵢ!`, as a real number. -/
def multiFact (k : Fin 4 →₀ ℕ) : ℝ := ∏ i, ((Nat.factorial (k i) : ℕ) : ℝ)

/-- `K^σ_{n;xy}(w) = K_n(y - w) - ∑_{|k|_𝔰 < σ} (y - x)^k/k! D^k K_n(x - w)`,
`K_n = scaledShell h n`. -/
def taylorKernel (h : ParabolicSpace → ℝ) (n : ℕ) (σ : ℝ) (x y : ParabolicSpace)
    (w : ParabolicSpace) : ℝ :=
  scaledShell h n (y - w) - ∑ k ∈ taylorIdx σ,
    (evalParabolic (MvPolynomial.monomial k 1) (y - x) / multiFact k) *
      lineIter (multiDirs k) (scaledShell h n) (x - w)

/-! ## Realising models, `𝒦_γ` and the setting of Theorem 5.12 -/

section Schauder

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

/-- `y ↦ ∑_n ⟨Π_x e_i, K^{deg i + 2}_{n;xy}⟩`: the density of `Π_x I e_i` [Hai14, Remark 5.10]. -/
def realGerm (M : Model 𝒯 parabolicSemigroup) (N : ℕ) (x : ParabolicSpace) (i : ι)
    (y : ParabolicSpace) : ℝ :=
  ∑' n : ℕ, parabolicSemigroup.pairing (fun t z => M.regPi x (Pi.single i 1) t z)
    (taylorKernel (annKernel0 N) n (𝒯.deg i + 2) x y)

/-- The regularisations `t ↦ Q_t g_{x,i}` of the distribution with density `realGerm`, extended
by `0` to `t ≤ 0`. -/
def realReg (M : Model 𝒯 parabolicSemigroup) (N : ℕ) (x : ParabolicSpace) (i : ι) :
    ℝ → ParabolicSpace → ℝ := fun t z =>
  if 0 < t then parabolicSemigroup.apply t (realGerm M N x i) z else 0

/-- The clause of [Hai14, Definition 5.9] on the basis vectors `e_i ∈ V`, `deg i < γ`:
`Q_t Π_x I e_i = Q_t g_{x,i}` for `t > 0`. -/
def Model.RealisesKernel (M : Model 𝒯 parabolicSemigroup) (N : ℕ) (γ : ℝ)
    (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (V : Submodule ℝ (ι → ℝ)) : Prop :=
  ∀ (x : ParabolicSpace) (i : ι), 𝒯.deg i < γ → (Pi.single i 1 : ι → ℝ) ∈ V →
    ∀ t : ℝ, 0 < t → ∀ z : ParabolicSpace,
      M.regPi x (I (Pi.single i 1)) t z = realReg M N x i t z

/-- `Π_x X^k = (· - x)^k` for the abstract polynomials of `P` [Hai14, Assumption 5.3]. -/
def Model.IsPolyCompatible (M : Model 𝒯 parabolicSemigroup) {N' : ℕ}
    (P : PolynomialSector 𝒯 N') : Prop :=
  ∀ (x : ParabolicSpace) (k : PolyIndex N') (t : ℝ) (z : ParabolicSpace),
    M.regPi x (Pi.single (P.emb k) 1) t z = polyReg x (Pi.single k 1) t z

/-- `M` realises the kernel `K = ∑_n K_n` for `I` [Hai14, Definition 5.9]. -/
structure Model.IsRealising (M : Model 𝒯 parabolicSemigroup) (N : ℕ) (γ : ℝ) {N' : ℕ}
    (P : PolynomialSector 𝒯 N') (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (V : Submodule ℝ (ι → ℝ)) :
    Prop where
  realises : M.RealisesKernel N γ I V
  poly : M.IsPolyCompatible P

/-- Joint measurability of `(x, z) ↦ (Q_t Π_x e_i)(z)` for each `i` and `t > 0`. -/
def Model.IsJointMeasurable (M : Model 𝒯 parabolicSemigroup) : Prop :=
  ∀ i, ∀ t : ℝ, 0 < t → Measurable fun p : ParabolicSpace × ParabolicSpace =>
    M.regPi p.1 (Pi.single i 1) t p.2

/-- `jCoeff M N x i k = ∑ₙ ⟨Π_x e_i, D^k K_n(x - ·)⟩`. -/
def jCoeff (M : Model 𝒯 parabolicSemigroup) (N : ℕ) (x : ParabolicSpace) (i : ι)
    (k : Fin 4 →₀ ℕ) : ℝ :=
  ∑' n : ℕ, parabolicSemigroup.pairing (fun t y => M.regPi x (Pi.single i 1) t y)
    (fun y => lineIter (multiDirs k) (annShell N n) (x - y))

open Classical in
/-- `J(x) e_i = ∑_{|k|_𝔰 < deg i + 2} jCoeff / k! · X^k`, as a vector of `T`. -/
def jVec (M : Model 𝒯 parabolicSemigroup) (N : ℕ) {N' : ℕ} (P : PolynomialSector 𝒯 N')
    (x : ParabolicSpace) (i : ι) : ι → ℝ :=
  ∑ k : PolyIndex N', if polyDeg N' k < 𝒯.deg i + 2 then
    (jCoeff M N x i k.1 / multiFactorial k.1) • (Pi.single (P.emb k) 1 : ι → ℝ) else 0

/-- Hairer's `J(x)` [Hai14, (5.11)], extended linearly from the basis. -/
def jMap (M : Model 𝒯 parabolicSemigroup) (N : ℕ) {N' : ℕ} (P : PolynomialSector 𝒯 N')
    (x : ParabolicSpace) (τ : ι → ℝ) : ι → ℝ :=
  ∑ i, τ i • jVec M N P x i

/-- The `n`-th term `⟨Λ, D^k (scaledShell h n)(x - ·)⟩`. -/
def derivShellPairing (Λ : ℝ → ParabolicSpace → ℝ) (h : ParabolicSpace → ℝ) (k : Fin 4 →₀ ℕ)
    (x : ParabolicSpace) (n : ℕ) : ℝ :=
  parabolicSemigroup.pairing Λ (fun y => lineIter (multiDirs k) (scaledShell h n) (x - y))

/-- The coefficient `∑_n ⟨Rf − Π_x f(x), D^k K_n(x − ·)⟩` of `X^k / k!` in `N_γ f(x)`. -/
def nCoeff (M : Model 𝒯 parabolicSemigroup) (N : ℕ) (f : ParabolicSpace → ι → ℝ)
    (x : ParabolicSpace) (k : Fin 4 →₀ ℕ) : ℝ :=
  ∑' n : ℕ, derivShellPairing (M.reconstructSubAt f x) (annKernel0 N) k x n

open Classical in
/-- `(N_γ f)(x) = ∑_{|k|_𝔰 < γ + 2} nCoeff / k! · X^k` [Hai14, (5.16)]. -/
def nVec (M : Model 𝒯 parabolicSemigroup) (N : ℕ) {N' : ℕ} (P : PolynomialSector 𝒯 N')
    (γ : ℝ) (f : ParabolicSpace → ι → ℝ) (x : ParabolicSpace) : ι → ℝ :=
  ∑ k : PolyIndex N', if polyDeg N' k < γ + 2 then
    (nCoeff M N f x k.1 / multiFactorial k.1) • (Pi.single (P.emb k) 1 : ι → ℝ) else 0

/-- `(𝒦_γ f)(x) = I f(x) + J(x) f(x) + (N_γ f)(x)` [Hai14, (5.15)]. -/
def kGamma (M : Model 𝒯 parabolicSemigroup) (N : ℕ) {N' : ℕ} (P : PolynomialSector 𝒯 N')
    (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (γ : ℝ) (f : ParabolicSpace → ι → ℝ) (x : ParabolicSpace) :
    ι → ℝ :=
  I (f x) + jMap M N P x (f x) + nVec M N P γ f x

/-- `K ∗ Λ (z) = ∑_n ⟨Λ, K_n(z - ·)⟩`. -/
def kConv (N : ℕ) (Λ : ℝ → ParabolicSpace → ℝ) (z : ParabolicSpace) : ℝ :=
  ∑' n : ℕ, parabolicSemigroup.pairing Λ (fun w => annShell N n (z - w))

variable {N' : ℕ}

/-- The standing hypotheses of [Hai14, Theorem 5.12]: `M` realises `K` for the abstract
integration map `I` of order `2` on the sector `V`, `V` is spanned by basis vectors
(`basis_mem`), the model bounds hold globally, every homogeneity below `γ` exceeds `-2`, enough
polynomials are present, and `I` has no component along the polynomials. -/
structure SchauderSetting (M : Model 𝒯 parabolicSemigroup) (N : ℕ) (γ : ℝ)
    (P : PolynomialSector 𝒯 N') (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (V : Submodule ℝ (ι → ℝ))
    (CPi CGam CI : ℝ) : Prop where
  pos : 0 < γ
  realising : M.IsRealising N γ P I V
  integration : IsAbstractIntegration P V I 2
  sector : 𝒯.IsSector V
  basis_mem : ∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V
  deg_gt : ∀ j, 𝒯.deg j < γ → -2 < 𝒯.deg j
  piBound : M.PiBoundOn γ CPi univ
  gammaBound : M.GammaBoundOn γ CGam univ
  piBound_nonneg : 0 ≤ CPi
  poly_large : ∀ j, 𝒯.deg j < γ → ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < 𝒯.deg j + 2 →
    multiDeg k < N'
  poly_large' : ∀ l : Fin 4 →₀ ℕ, (multiDeg l : ℝ) < γ + 2 → multiDeg l < N'
  integration_poly : ∀ a ∈ V, ∀ k : PolyIndex N', I a (P.emb k) = 0
  entry_bound : ∀ i j, |I (Pi.single i 1) j| ≤ CI

/-- The non-integrality conditions on `γ` of [Hai14, Theorem 5.12]: `γ + 2 − |k|_𝔰 ∉ ℕ[𝔰]`, and
`|k|_𝔰 ≠ deg i + 2` for the non-polynomial components `i` with `deg i < γ`. -/
structure SchauderNonIntegral (𝒯 : RegularityStructure ι) (γ : ℝ) (N' : ℕ)
    (P : PolynomialSector 𝒯 N') : Prop where
  nonint₁ : ∀ k : PolyIndex N', polyDeg N' k < γ + 2 →
    ∀ l : Fin 4 →₀ ℕ, (multiDeg l : ℝ) ≠ γ + 2 - multiDeg k.1
  nonint₂ : ∀ k : PolyIndex N', polyDeg N' k < γ + 2 →
    ∀ i, i ∉ Set.range P.emb → 𝒯.deg i < γ → (multiDeg k.1 : ℝ) ≠ 𝒯.deg i + 2

end Schauder

/-! ## Bridge to the library -/

namespace Bridge

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E] {μ : Measure E}

/-- A Challenge regularising semigroup as a library one (the same fields). -/
def toK (K : RegularisingSemigroup E μ) : RegularityStructures.RegularisingSemigroup E μ :=
  ⟨K.kernel, K.order, K.order_pos, K.scaleDist, K.scaleDist_nonneg, K.momentConst,
    K.momentConst_nonneg, K.measurable_kernel, K.integrable_moment, K.moment_le, K.semigroup⟩

/-- A Challenge regularity structure as a library one (the same fields). -/
def toT (𝒯 : RegularityStructure ι) : RegularityStructures.RegularityStructure ι :=
  ⟨𝒯.deg, 𝒯.group, 𝒯.isGradedUnipotent⟩

/-- A Challenge model as a library model: `Π_x` corestricted to the distributions. -/
def toM {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ} (M : Model 𝒯 K) :
    RegularityStructures.Model (toT 𝒯) (toK K) where
  pi x := LinearMap.codRestrict _ (M.pi x) (M.pi_mem x)
  gamma := M.gamma
  pi_gamma x y τ := Subtype.ext (M.pi_gamma x y τ)
  gamma_self := M.gamma_self
  gamma_mul := M.gamma_mul
  measurable_diag := M.measurable_diag
  measurable_pi := M.measurable_pi

/-- The parabolic model as a library model over the library's parabolic semigroup. -/
def toMP {𝒯 : RegularityStructure ι} (M : Model 𝒯 parabolicSemigroup) :
    RegularityStructures.Model (toT 𝒯) RegularityStructures.parabolicSemigroup :=
  toM M

/-- A Challenge polynomial sector as a library one (the same fields). -/
def toP {𝒯 : RegularityStructure ι} {N : ℕ} (P : PolynomialSector 𝒯 N) :
    RegularityStructures.PolynomialSector (toT 𝒯) N :=
  ⟨P.emb, P.emb_injective, P.deg_emb, P.invariant⟩

/-! The recursive definitions `lineIter` and `boxSet` agree with the library's by induction; the
definitions built on them agree by rewriting. -/

theorem lineIter_eq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] :
    ∀ (L : List F) (f : F → ℝ), lineIter L f = RegularityStructures.lineIter L f
  | [], _ => rfl
  | d :: L, f => by rw [lineIter, RegularityStructures.lineIter, lineIter_eq L f]; rfl

theorem boxSet_eq (m : Fin 4 → ℕ) :
    ∀ J : List (Fin 4), boxSet m J = RegularityStructures.boxSet m J
  | [] => rfl
  | j :: J => by rw [boxSet, RegularityStructures.boxSet, boxSet_eq m J]

theorem taylorIdx_eq (σ : ℝ) : taylorIdx σ = RegularityStructures.taylorIdx σ := by
  rw [taylorIdx, RegularityStructures.taylorIdx, boxSet_eq]; rfl

theorem taylorKernel_eq (h : ParabolicSpace → ℝ) (n : ℕ) (σ : ℝ) (x y : ParabolicSpace) :
    taylorKernel h n σ x y = RegularityStructures.taylorKernel h n σ x y := by
  funext w
  simp only [taylorKernel, RegularityStructures.taylorKernel, taylorIdx_eq, lineIter_eq]
  rfl

section Defs

variable {𝒯 : RegularityStructure ι} {N' : ℕ} (M : Model 𝒯 parabolicSemigroup) (N : ℕ)
  (P : PolynomialSector 𝒯 N') (x : ParabolicSpace)

theorem realReg_eq (i : ι) : realReg M N x i = RegularityStructures.realReg (toMP M) N x i := by
  have h : realGerm M N x i = RegularityStructures.realGerm (toMP M) N x i := by
    funext y
    simp only [realGerm, RegularityStructures.realGerm, taylorKernel_eq]
    rfl
  funext t z
  simp only [realReg, RegularityStructures.realReg, h]
  rfl

theorem jMap_eq (τ : ι → ℝ) :
    jMap M N P x τ = RegularityStructures.jMap (toMP M) N (toP P) x τ := by
  have h : ∀ i, jVec M N P x i = RegularityStructures.jVec (toMP M) N (toP P) x i := fun i => by
    simp only [jVec, RegularityStructures.jVec, jCoeff, RegularityStructures.jCoeff, lineIter_eq]
    rfl
  simp only [jMap, h]
  rfl

theorem kGamma_eq (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (γ : ℝ) (f : ParabolicSpace → ι → ℝ) :
    kGamma M N P I γ f x = RegularityStructures.kGamma (toMP M) N (toP P) I γ f x := by
  have h : nVec M N P γ f x = RegularityStructures.nVec (toMP M) N (toP P) γ f x := by
    simp only [nVec, RegularityStructures.nVec, nCoeff, RegularityStructures.nCoeff,
      derivShellPairing, RegularityStructures.derivShellPairing, lineIter_eq]
    rfl
  simp only [kGamma, jMap_eq, h]
  rfl

end Defs

theorem toNI {𝒯 : RegularityStructure ι} {γ : ℝ} {N' : ℕ} {P : PolynomialSector 𝒯 N'}
    (h : SchauderNonIntegral 𝒯 γ N' P) :
    RegularityStructures.SchauderNonIntegral (toT 𝒯) γ N' (toP P) :=
  ⟨h.1, h.2⟩

theorem toS {𝒯 : RegularityStructure ι} {N' : ℕ} {M : Model 𝒯 parabolicSemigroup} {N : ℕ}
    {γ CPi CGam CI : ℝ} {P : PolynomialSector 𝒯 N'} {I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)}
    {V : Submodule ℝ (ι → ℝ)} (h : SchauderSetting M N γ P I V CPi CGam CI) :
    RegularityStructures.SchauderSetting (toMP M) N γ (toP P) I V CPi CGam CI :=
  ⟨h.pos, ⟨fun x i hi hV t ht z => (h.realising.1 x i hi hV t ht z).trans
      (congrFun (congrFun (realReg_eq M N x i) t) z), h.realising.2⟩,
    ⟨h.integration.1, h.integration.2, h.integration.3, h.integration.4⟩,
    ⟨h.sector.1, h.sector.2⟩, h.basis_mem, h.deg_gt, h.piBound, h.gammaBound, h.piBound_nonneg,
    h.poly_large, h.poly_large', h.integration_poly, h.entry_bound⟩

end Bridge

open Bridge

/-! ## The theorems -/

/-- **Multilevel Schauder estimate** [Hai14, Theorem 5.12, first part]. Under the standing
hypotheses, for `γ > 0` with homogeneities below `γ` above `-2`, there is `c ≥ 0` such that for
every jointly measurable model and `f ∈ D^γ` with values in `V`, `𝒦_γ f ∈ D^{γ+2}` with constant
`c max(1, C_I) max(1, C_Π) max(C_Γ, 1) C_f`. -/
theorem kGamma_mem_modelledDistributions :
    ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ} {γ : ℝ},
      0 < γ → (∀ j, 𝒯.deg j < γ → -2 < 𝒯.deg j) →
        ∀ (N : ℕ) (P : PolynomialSector 𝒯 N'), N' ≤ N → SchauderNonIntegral 𝒯 γ N' P →
          ∃ c : ℝ, 0 ≤ c ∧
            ∀ (M : Model 𝒯 parabolicSemigroup) {CPi CGam CI Cf : ℝ}
              (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (V : Submodule ℝ (ι → ℝ)),
              SchauderSetting M N γ P I V CPi CGam CI → M.IsJointMeasurable →
                ∀ {f : ParabolicSpace → ι → ℝ}, f ∈ M.modelledDistributions γ →
                  M.ModelledBoundOn γ Cf univ f → 0 ≤ Cf → (∀ x, f x ∈ V) →
                    (fun x => kGamma M N P I γ f x) ∈ M.modelledDistributions (γ + 2) ∧
                      M.ModelledBoundOn (γ + 2) (c * max 1 CI * max 1 CPi * max CGam 1 * Cf)
                        univ fun x => kGamma M N P I γ f x := by
  intro ι _ _ 𝒯 N' γ hγ hdeg N P hN hNI
  obtain ⟨c, hc, h⟩ := RegularityStructures.Statements.Model.kGamma_mem_modelledDistributions
    (𝒯 := toT 𝒯) hγ hdeg N (toP P) hN (toNI hNI)
  refine ⟨c, hc, fun M _ _ _ _ I V hS hJ f hf hfB hCf hV => ?_⟩
  rw [show (fun x => kGamma M N P I γ f x) = _ from funext fun x => kGamma_eq M N P x I γ f]
  exact h (toMP M) I V (toS hS) hJ hf hfB hCf hV

/-- **Reconstruction of `𝒦_γ f`** [Hai14, Theorem 5.12, (5.17)]. Under the standing hypotheses,
if the model is jointly measurable, `γ + 2` is not a parabolic degree, and the model satisfies
the global bound on `Π` up to level `γ + 2`, then `R 𝒦_γ f = K ∗ Rf`: its regularisations are
`Q_t (K ∗ Rf)` for `t > 0`. -/
theorem reconstruct_kGamma :
    ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}
      {M : Model 𝒯 parabolicSemigroup} {N : ℕ} {γ CPi CGam CI : ℝ}
      {P : PolynomialSector 𝒯 N'} {I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)} {V : Submodule ℝ (ι → ℝ)},
      SchauderSetting M N γ P I V CPi CGam CI → N' ≤ N → SchauderNonIntegral 𝒯 γ N' P →
        (∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) ≠ γ + 2) → M.IsJointMeasurable →
          ∀ {CPi' : ℝ}, M.PiBoundOn (γ + 2) CPi' univ → 0 ≤ CPi' →
            ∀ {f : ParabolicSpace → ι → ℝ} {Cf : ℝ}, f ∈ M.modelledDistributions γ →
              M.ModelledBoundOn γ Cf univ f → 0 ≤ Cf → (∀ x, f x ∈ V) →
                (M.reconstruct fun x => kGamma M N P I γ f x) =
                  fun t z => if 0 < t then parabolicSemigroup.apply t (kConv N (M.reconstruct f)) z
                    else 0 := by
  intro ι _ _ 𝒯 N' M N γ CPi CGam CI P I V hS hN hNI hk hJ CPi' hPi' hCPi' f Cf hf hfB hCf hV
  rw [show (fun x => kGamma M N P I γ f x) = _ from funext fun x => kGamma_eq M N P x I γ f]
  exact RegularityStructures.Statements.Model.reconstruct_kGamma (toS hS) hN (toNI hNI) hk hJ
    hPi' hCPi' hf hfB hCf hV

/-- **The series converge.** Under the standing hypotheses, the series defining `jCoeff`
(`deg i < γ`, `|k|_𝔰 < deg i + 2`), `nCoeff` (`|k|_𝔰 < γ + 2`) and `kConv N (Rf)` are summable,
so these `∑'` are genuine sums and not the value `0` that `∑'` assigns to a divergent series. -/
theorem schauder_series_summable :
    ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}
      {M : Model 𝒯 parabolicSemigroup} {N : ℕ} {γ CPi CGam CI : ℝ}
      {P : PolynomialSector 𝒯 N'} {I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)} {V : Submodule ℝ (ι → ℝ)},
      SchauderSetting M N γ P I V CPi CGam CI →
        ∀ {f : ParabolicSpace → ι → ℝ} {Cf : ℝ}, f ∈ M.modelledDistributions γ →
          M.ModelledBoundOn γ Cf univ f → 0 ≤ Cf → ∀ x : ParabolicSpace,
            (∀ i k, 𝒯.deg i < γ → (multiDeg k : ℝ) < 𝒯.deg i + 2 →
              Summable fun n : ℕ => parabolicSemigroup.pairing
                (fun t y => M.regPi x (Pi.single i 1) t y)
                (fun y => lineIter (multiDirs k) (annShell N n) (x - y))) ∧
            (∀ k, (multiDeg k : ℝ) < γ + 2 →
              Summable (derivShellPairing (M.reconstructSubAt f x) (annKernel0 N) k x)) ∧
            Summable fun n : ℕ => parabolicSemigroup.pairing (M.reconstruct f)
              (fun w => annShell N n (x - w)) := by
  intro ι _ _ 𝒯 N' M N γ CPi CGam CI P I V hS f Cf hf hfB hCf x
  have S := toS hS
  have hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j := fun j hj => by linarith [hS.deg_gt j hj]
  refine ⟨fun i k hi hk => ?_, fun k hk => ?_, ?_⟩
  · simp only [lineIter_eq]
    exact RegularityStructures.summable_jCoeff_terms (toMP M) N x i k S.piBound S.gammaBound
      S.piBound_nonneg hi hdeg hk
  · have e : derivShellPairing (M.reconstructSubAt f x) (annKernel0 N) k x =
        RegularityStructures.derivShellPairing ((toMP M).reconstructSubAt f x)
          (RegularityStructures.annKernel0 N) k x := by
      funext n
      simp only [derivShellPairing, RegularityStructures.derivShellPairing, lineIter_eq]
      rfl
    rw [e]
    exact RegularityStructures.summable_nCoeff_terms (toMP M) S.pos S.piBound S.piBound_nonneg hf
      hfB hCf hdeg N x hk
  classical
  set F : Finset ι := Finset.univ.filter (fun i => (toT 𝒯).deg i < γ) with hF
  let Λj : Option ι → ℝ → ParabolicSpace → ℝ := fun o t w =>
    Option.elim o ((toMP M).reconstructSubAt f x t w)
      (fun i => (toMP M).regPi x (Pi.single i 1) t w)
  let c : Option ι → ℝ := fun o => Option.elim o 1 (fun i => f x i)
  have hΛ : ∀ j ∈ Finset.insertNone F, RegularityStructures.KRegular (Λj j) x := by
    rintro (_ | i) hj
    · exact RegularityStructures.Model.kRegular_reconstructSubAt S.pos S.deg_gt S.piBound
        S.piBound_nonneg hf hfB hCf x
    · exact (toMP M).kRegular_regPi_single S.deg_gt S.piBound S.gammaBound S.piBound_nonneg
        (Finset.mem_filter.1 (Finset.mem_insertNone.1 hj i rfl)).2 x
  have hR : (toMP M).reconstruct f = fun t w => ∑ j ∈ Finset.insertNone F, c j * Λj j t w := by
    funext t w
    have e := (toMP M).regPi_eq_sum_filter (hf.2.1 x) x t w
    rw [← hF] at e
    simp only [Finset.sum_insertNone, c, Λj, Option.elim_none, Option.elim_some, one_mul,
      RegularityStructures.Model.reconstructSubAt, e]
    ring
  have key : Summable fun n : ℕ => RegularityStructures.parabolicSemigroup.pairing
      ((toMP M).reconstruct f) (fun w => RegularityStructures.annShell N n (x - w)) := by
    rw [hR]
    simp only [RegularityStructures.pairing_annShell_finset_sum (Finset.insertNone F) Λj c hΛ N _ x]
    exact summable_sum fun j hj => ((hΛ j hj).summable_pairing N x).mul_left (c j)
  exact key

end SchauderChallenge

end
