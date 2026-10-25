# Design: the deterministic analytic core (Analysis, Abstract)

Sources: [Hos25] = arXiv:2310.07396v2, [Hai14] = arXiv:1303.5113v4, [CZ20] = arXiv:2005.09287v3,
[BCZ23] = arXiv:2301.07517v2.

## 1. Geometry

* `ParabolicSpace := ℝ × (Fin 3 → ℝ)`, time first. No `EuclideanSpace`.
* Parabolic size `parabolicNorm z = |z₀|^{1/2} + ∑ᵢ |zᵢ|` ([Hos25, §2.1], `‖x‖_s` with
  `s = (2,1,1,1)`). Triangle inequality (`parabolicNorm_add_le`) and exact scaling under
  `parabolicDilate c z = (c² z₀, c z')` (`parabolicNorm_parabolicDilate`).
* Test functions `φ^λ_z(w) = λ⁻⁵ φ((w₀ − z₀)/λ², (w' − z')/λ)` (`rescaledTestFunction`,
  `integral_rescaledTestFunction`); the class `B^r` of smooth functions supported in the closed
  unit parabolic ball with `‖D^k φ‖_∞ ≤ 1` for `k ≤ r` (`testFunctionClass`).
* Polynomials: `MvPolynomial (Fin 4) ℝ`, parabolic degree = weighted total degree with weights
  `(2,1,1,1)` (`evalParabolic_parabolicDilate`).
* Lattices: dyadic parabolic lattice points `latticePoint` and cells `latticeCell`, used by the
  singular reconstruction (§7).

## 2. Regularising semigroup (`RegularityStructures.Analysis.Semigroup.Basic`)

`RegularisingSemigroup E μ` is an *interface*: kernels `Q_t(x, y)` with

* the semigroup property `∫ Q_s(x,z) Q_t(z,y) dz = Q_{s+t}(x,y)`;
* moment bounds `∫ |Q_t(x,y)| d(y,x)^r dy ≤ M_r t^{r/ℓ}` for all `r ≥ 0`, `t > 0`;
* joint measurability.

This is [Hos25, Def. 2.6 (i), (iii), (2.2)] with weight `w = 1`. The time-derivative bound (iv)
is not in the interface: in the representation below the reconstruction does not need it.
Results stated for an arbitrary `RegularisingSemigroup` hold for the concrete kernel below, and
conversely the abstract layer does not depend on the particular kernel.

### Concrete kernel on ℝ⁴

`ℓ = 4`, `Q_t(x,y) = q_t(x − y)`, `q_t(z) = g_t(z₀) k_t(z₁) k_t(z₂) k_t(z₃)` with `g_t` the 1D heat
kernel (`heatKernel1D`, scale `t^{1/2}`) and `k_t = 𝓕⁻¹(e^{−t|ξ|⁴})` the 1D quartic kernel
(`quarticKernel`, scale `t^{1/4}`), i.e. the fundamental solution of `∂_t − ∂₀² + ∑ᵢ ∂ᵢ⁴`
([Hos25, Example 2.7], with the spatial bi-Laplacian replaced by the anisotropic `∑ᵢ ∂ᵢ⁴` so that
the kernel is a tensor product of 1D kernels): `parabolicKernel`, `parabolicKernel_eq_scale`,
`integral_parabolicKernel`, `parabolicSemigroup`, `parabolicGenerator`, and the time-derivative
bound `abs_parabolicTimeDeriv_le`. Bounds come from the Schwartz property of `e^{−ξ⁴}` and exact
scaling; the semigroup property from the Fourier transform of convolutions. It is **not** the
causal heat kernel that solves the PDE (that one is `heatKernelR4`, §6).

## 3. Distributions: `Q`-families

A distribution is represented by its regularisations: `K.distributions` is the submodule of
families `Λ : ℝ → E → ℝ` with `Q_s Λ_t = Λ_{s+t}` (absolutely convergent), `Λ_t = 0` for
`t ≤ 0`. `Λ t x` means `(Q_t Λ)(x) = ⟨Λ, Q_t(x, ·)⟩`.

Why: [Hos25] defines `B^{α,Q}` as a completion and uses its elements only through `Q_t Λ`
(identity (2.5)). Taking the families as the objects removes the completion: the reconstruction
`Rf` *is* the family `t ↦ lim_{s↓0} R^t_s f`, step (4) of [Hos25, Thm 4.1] disappears, and
uniqueness is a two-line argument (`|Λ_t| ≤ M₀ sup|Λ_s| → 0`). The families are genuine
distributions: every tempered distribution `ξ` gives one by `Λ_t(x) = ⟨ξ, Q_t(x,·)⟩` (white noise
included), and for growth `‖Λ_t‖_∞ ≲ t^{α/ℓ}` the limit `⟨Λ, φ⟩ = lim_{t↓0} ∫ Λ_t φ` exists for
test functions and determines the family. The bridge to test functions is the pairing
`RegularisingSemigroup.pairing` of `RegularityStructures.Analysis.Semigroup.Pairing`, with the
bound `|⟨Λ, φ^λ_x⟩| ≲ λ^γ` for `Λ` of local order `γ` at `x` [Hai14, Theorem 3.10, (3.3)]. It is
abstract: it needs a symmetric, jointly measurable kernel, a distance `scaleDist`, and a generator
pair `(φ, ψ = Lφ)`. It requires every homogeneity below `γ` to exceed `-ℓ` (for `ℓ = 4` and Φ⁴₃,
whose lowest homogeneity is `-5/2-κ`, this holds; the `Q`-form of the bound has no such
restriction).

The interface does not include conservativity `∫ Q_t(x, y) dy = 1` ([Hos25, Def. 2.6 (ii)]).
The theorems do not need it, but the reading of a `Q`-family as a distribution does
(`Q_t φ → φ`, `RegularityStructures.Analysis.Semigroup.Consistency`); the concrete kernel
satisfies it (`integral_parabolicKernel`). A degenerate interface instance (zero kernel) has
`distributions = {0}` and makes every statement trivial; the concrete `parabolicSemigroup` is
non-degenerate.

Norms are global (`p = q = ∞` in [Hos25]). Polynomially moderate weights
(`IsModerateWeight ρ p`: `ρ ≥ 1`, `ρ(z) ≤ ρ(y)(1 + d(z, y))^p`, i.e. `w = 1/ρ` with `w*`
polynomial) are covered by the weighted model bounds `PiBoundGrowth` and `GammaBoundGrowth`,
bundled with the moderateness of the weights in `Model.GrowthModel`; the weighted modelled
distributions carry the `(1 + d)^q` growth of `f(y) − Γ_{yx} f(x)` that stationary random models
produce. Exponential weights are not covered.

## 4. Regularity structures

* **Graded basis.** A finite index type `ι` with `deg : ι → ℝ`; the model space is `T = ι → ℝ`,
  `T_α = span{e_i : deg i = α}` (`homogeneousSubspace`). Every finite-dimensional graded space is
  of this form after choosing a graded basis; the linear equivalence `ι → ℝ ≃ₗ ι →₀ ℝ` connects to
  the `Symbol →₀ ℝ` representation of the Φ⁴₃ sector. Norms are coordinatewise (equivalent on
  finite dimensions). A finite index set is automatically bounded below.
* **Structure group.** `RegularityStructure ι` bundles `deg` and a subgroup `G` of
  `LinearMap.GeneralLinearGroup ℝ (ι → ℝ)` all of whose elements are graded-unipotent
  (`IsGradedUnipotent`): `Γ e_i − e_i ∈ span{e_j : deg j < deg i}` (i.e. `Γτ − τ ∈ T_{<α}` for
  `τ ∈ T_α`) [Hai14, Definition 2.1].
* **Models.** `Model 𝒯 K`: `Π : E → T →ₗ[ℝ] K.distributions`, `Γ : E → E → G` with
  `Π_x Γ_{xy} = Π_y`, `Γ_{xx} = 1`, `Γ_{xy} Γ_{yz} = Γ_{xz}`, and measurability of the diagonal
  `x ↦ (Π_x e_i)_t(x)`. Analytic bounds are predicates with explicit constants:
  `|(Π_x e_i)_t(x)| ≤ C t^{deg i/ℓ}` ([Hos25, Def. 3.2], `PiBoundOn`) and
  `|(Γ_{yx} e_i)_j| ≤ C d(y,x)^{deg i − deg j}` (`GammaBoundOn`); the norms are the corresponding
  suprema, with characterisation lemmas (`piNormOn_le_iff`), also on subsets `S ⊆ E` (local
  norms). Hairer's model norm only uses pairs at distance at most `1` [Hai14, (2.17)];
  `GammaDiffBoundNearOn` and its single-model analogue restrict the `Γ`-bound accordingly, and the
  far-pair bound does not follow from the near-pair one with a polynomial constant.
* **Modelled distributions.** `D^γ` consists of the measurable `f : E → T` with
  `f(x) ∈ T_{<γ}`, `|f(x)_j| ≤ C`, `|(f(y) − Γ_{yx} f(x))_j| ≤ C d(y,x)^{γ − deg j}`
  ([Hos25, Def. 3.5], [Hai14, Def. 3.1]); the singular spaces `D^{γ,η}_P` on a time slab are
  `Model.SlabSpace`.
* **Polynomials.** `polynomialStructure` is the polynomial regularity structure `T̄_N` with
  parabolic scaling [Hai14, Section 2.2]; `PolynomialSector` embeds it into a given structure.

## 5. Reconstruction in `Q`-form

Two layers.

1. **Germ layer**, no regularity structure: a germ `F : E → K.distributions` whose diagonal is
   measurable and bounded, and which is coherent,
   `|(F_y − F_z)_t(z)| ≤ C ∑_{a ∈ A} t^{a/ℓ} d(z,y)^{γ−a}` (`A` finite, `a < γ`), has a unique
   reconstruction `Λ ∈ K.distributions` with `|Λ_t(x) − (F_x)_t(x)| ≤ c C t^{γ/ℓ}`, `t ≤ 1`, `c`
   depending only on `K, γ, A`. This is [Hos25, Thm 4.1] for the coherent germ
   `F_x = Π_x f(x)` (cf. [CZ20, Thm 5.1], [BCZ23]); reconstruction is linear in `F`.
2. **Model layer**: `F_y = Π_y f(y)` is a coherent germ with `C = C_Π · C_f`; continuity in the
   model follows from linearity and uniqueness applied to the difference germ `Π¹ f¹ − Π² f²`,
   whose coherence constant is `‖Π¹ − Π²‖ ‖f¹‖ + ‖Π²‖ ‖f¹; f²‖`.

For a model realised by continuous functions, `Rf` is the function `x ↦ (Π_x f(x))(x)`
[Hai14, Remark 3.15] (`pointwiseReconstruct`, `RegularityStructures.Abstract.QFamilyContinuousModel`).

The `Q`-form reconstruction is not exactly local: `Q_t(x, ·)` has unbounded support. This is
harmless for modelled distributions defined on all of space-time, but not for the singular spaces
on a time slab, which are reconstructed by a different construction (§7).

## 6. Kernel decomposition and the multilevel Schauder estimate

Any regularising semigroup works for reconstruction. Hoshino's semigroup proof of the multilevel
Schauder estimate [Hos25, Definition 5.1 (i)] additionally needs the Green function to be
`∫₀¹ K_t dt` with `∫ K_{t−s}(x,z) Q_s(z,y) dz = K_t(x,y)`. For the heat operator this holds
when `Q` is generated by `∂₀² − (Δ − 1)²` (then `K_t = (∂₀ + Δ − 1) Q_t`, [Hos25, Example 5.3]),
but **not** for the tensor-product generator `∂₀² − ∑ᵢ ∂ᵢ⁴` of §2: `∂₀² − ∑ᵢ ∂ᵢ⁴` is not
divisible by `∂₀ − Δ`. The Schauder estimate is therefore proved with Hairer's kernel
decomposition [Hai14, Assumption 5.1, Lemma 5.5], which does not involve `Q`.

* **Causal decomposition.** For every `N`, `heatKernelR4 = Σ_n annShellC N n + annRemainderC N`
  away from `0` (`heatKernelR4_eq_tsum_annShellC`); the shells satisfy [Hai14, Assumption 5.1]
  with `β = 2`, annihilate polynomials of parabolic degree `≤ N − 1` [Hai14, Assumption 5.4], and
  shells and remainder vanish with all derivatives for `t ≤ 0` (`annShellC_eq_zero_of_nonpos`).
  The moment-correcting bump of [Hai14, Lemma 5.5] is chosen in `{t > 0}`
  (`exists_moment_bump_causal`); causality is needed for the vanishing bound of [Hai14,
  Theorem 7.1]. The non-causal decomposition `heatShell` is also available.
* **Profiles.** Only three properties of the shell profile are used: smoothness, support in the
  closed unit parabolic ball, and vanishing moments of parabolic degree `< N`. They form
  `ShellProfile`; the shells are `scaledShell h n`, and the causal profile `annKernel0C N` is an
  instance. The coefficients `J(x)` [Hai14, (5.11)] are `jCoeffP` and `jMapP`, the realising
  germ is `realGermP`, and realising models are `Model.RealisesKernelP` and `Model.IsRealisingP`
  ([Hai14, Definition 5.9, Remark 5.10] in `Q`-form, with `Π_x X^k` the `Q`-family of
  `(· − x)^k`, Assumption 5.3).
* **Realising models.** `(Q_t Π_x I e_i)(z) = Σ_n ∫ Q_t(z, y) ⟨Π_x e_i, K^{deg i}_{n;xy}⟩ dy`,
  where `K^α_{n;xy}` is the Taylor kernel of [Hai14, (5.14)] (`taylorKernel`). The `n`-sum
  converges by the Taylor bound `Σ_n |⟨Λ, K^α_{n;xy}⟩| ≲ ‖y−x‖^{α+2}` for `Λ` of local order `α` at
  `x` (exponents `> −2`, `α + 2 ∉ ℕ`); integrability in `y` needs its polynomial-growth version.
* **Lemma 5.16.** For realising models `Γ_{yx}(I + J(x)) e_i − (I + J(y)) Γ_{yx} e_i = 0`. In
  [Hai14] this follows from (5.12) and the vanishing of a polynomial distribution of local order
  above its degree; in `Q`-form, a polynomial `P` with `|Q_u P(y)| ≲ Σ u^{a/ℓ} d^{…}` of order above
  its degree is zero.
* **Non-integrality.** The hypothesis that `deg i + 2 − |k|` is not an integer must range over
  the non-polynomial symbols only (`i ∉ range P.emb`): over all basis indices it is unsatisfiable,
  since the polynomial symbols have integer degrees. The polynomial components vanish instead by
  the polynomial annihilation of the kernel (Assumption 5.4, `N' ≤ N`). The joint satisfiability of
  the hypotheses of the Φ⁴₃ fixed point is witnessed on a small structure with a symbol `τ` of
  degree `-1/2`, an integrated symbol of degree `3/2`, and the polynomials
  (`RegularityStructures.Abstract.Singular.Phi4FixedPointInstanceStructure`); there the Taylor
  pairings of polynomials vanish, so `I X^k = 0` is realised.
* **Sectors.** The degree bound `−2 < deg j` is only needed for the basis vectors `e_j ∈ V`, the
  sector on which `𝒦_γ` acts (`degreesBelowIn`). The structure may contain further basis vectors
  of degree `≤ −2` outside `V`, such as the Φ⁴₃ noise symbol of degree `−5/2 − κ`.

Further hypotheses beyond Hairer's statement: the non-integrality conditions, `I` without
`T̄`-components, joint measurability of the model (`Model.IsJointMeasurable`), and the model bound
at level `γ + 2` for [Hai14, (5.17)].

## 7. Singular reconstruction and [Hai14, Theorem 7.1]

The integration operator of the fixed point acts on the slab space
`Model.SlabSpace timeZeroDist ⊤ (γ₀+2α) η'' (timeSlab T)`: with the singular bound on the slab, the
vanishing bound `|𝒦₀ g x|_ℓ ≤ C‖g‖ ‖x‖_P^{ηK−ℓ}`, values in `T_{<γK}`, and `C` uniform in `T`. This
is [Hai14, Thm 7.1] (via Prop 6.16 and Prop 6.9) for a non-anticipative `K`.

### Why not the `Q`-form

* Hairer's Prop 6.9 uses exactly local reconstruction on test functions supported away from `P`
  (Lemma 6.7). The `Q`-form reconstruction is built from a globally coherent germ.
* Singular `f` cannot be fed to the global germ theorem: `(Π_y f(y))_s(y)` blows up like
  `‖y‖_P^{η−a}` and is not integrable across `P` when `a > η + 2`.
* Slab elements vanish for `t > T`, so their germ is incoherent across `{t = T}`. Since the
  `Q`-form reconstruction is not exactly local (its kernel is not causal), it would give constants
  involving the modelled distribution on all of `{t > 0}`, not its slab norm.
* Extending `f` from a time window by evaluating it at a fixed time (`f(τ_m y)` or `Γ_{y,τ_m y} f(τ_m y)`) is not
  coherent (the `Γ`-transport spreads components); a sharp or scalar smooth cutoff of the germ
  breaks coherence beyond order 1.
* Taylor-lifted cutoffs `χ̂ ⋆ f` need products `X^k ⋆ τ` in `𝒯`; the finite Φ⁴₃ structure does
  not contain all of them (e.g. `X_i Ψ³`).

### Lattice reconstruction

The construction follows the telescoping of [Hai14, Prop 7.2], with **finite lattice sums**
instead of wavelets and Fubini:

* causal lattice partition of unity on `ℝ⁴`: `b(s) = σ(s) − σ(s − 1)` (`σ = Real.smoothTransition`),
  supported in `(0, 2)`, `∑_{k∈ℤ} b(s − k) = 1`; level-`n` cells
  `χ_{n,k}(w) = ∏ b((S^{2^n} w)_i − k_i)` (`latticeCell`), lattice points `z_{n,k} = S^{2^{-n}} k`
  (`latticePoint`). `χ_{n,k}(w) ≠ 0` forces `z_{n,k}` to lie strictly **before** `w` in time, which
  gives constants depending only on the slab;
* `S_n f ψ = ∑_k ⟨Π_{z_{n,k}} f(z_{n,k}), ψ χ_{n,k}⟩` (`latticeApprox`, finite for compactly
  supported `ψ`); the increment `S_n − S_{n−1} = ∑_{k,l} ⟨Π_{z_k}(f(z_k) − Γ_{z_k z_l} f(z_l)),
  ψ χ_{n,k} χ_{n−1,l}⟩` by `∑_l χ_{n−1,l} = 1`, bounded by the test-function model bound
  [Hai14, (2.15)] and lattice point counting;
* `⟨R_T f, ψ⟩ = lim_n S_n f ψ` (`Model.latticeRecon`); the local bound [Hai14, (6.6)] and the
  layer bound in `C^{α∧η}` [Hai14, Prop 6.9].

For a model realised by smooth functions (`Model.IsSmoothFunctionModelBelow`), the lattice
reconstruction is the pointwise one [Hai14, Remark 3.15].

### The singular Schauder estimate

Kernel `K_n = scaledShell h n` for a causal profile `h` (`D^k K_n(x − ·)` is supported in
`{y₀ < x₀}`). `R f` is the lattice reconstruction, and
`⟨Rf − Π_x f(x), φ⟩ := latticeRecon f φ − ⟨Π_x f(x), φ⟩`. Tools: (i) every kernel test function
used is a scaled test function at its centre with explicit constants (`IsScaledTest`;
`D^k K_n(x−·)`: radius `2^{-n}`, `A R^5 ≍ 2^{(|k|−2)n}`; Taylor kernels `K^{k,γ}_{n;yx}`: extra
factor `Σ_{|ℓ|≥γ+2−|k|} (d 2^n)^{|ℓ|}`; time-Taylor remainders at `x̄ = (0, x')`: extra factor
`(x₀ 4^n)^m`), converted by `exists_eq_smul_rescaledTestFunction`; (ii) linearity of the lattice
reconstruction in the test function.

* `nCoeffS f x k = Σ_n (latticeRecon f (D^kK_n(x−·)) − ⟨Π_x f(x), D^kK_n(x−·)⟩)`,
  `kGammaS f x = I f(x) + jMapP x f(x) + Σ_{|k|<γ+2} nCoeffS f x k / k! X^k`.
* Sup bound (`ηK = α∧η + 2`, `ηK ∉ ℕ`): at scales `2^{-n} ≤ w(x)/c` use the local bound (6.6),
  `Σ 2^{(|k|−2−γ)n} w^{η−γ} ≍ w^{η+2−|k|}`. At scales `2^{-n} > w(x)/c` the `X^k`-coefficient is
  `⟨Rf, D^kK_n(x−·)⟩ − Σ_{deg i ≤ |k|−2} f(x)_i ⟨Π_x e_i, D^kK_n(x−·)⟩` (the sum is empty when
  `|k| < ηK` since `deg i ≥ α`). Since `⟨Rf, ψ⟩ = 0` for `ψ` supported in `{t < 0}` (lattice points
  before `supp ψ` have `f = 0`), `⟨Rf, D^kK_n(x−·)⟩ = ⟨Rf, D^kK_n(x−·) − Σ_{j<m} x₀^j/j!
  ∂_t^j D^kK_n(x̄−·)⟩`, a remainder of size `(x₀4^n)^m 2^{(|k|−2)n}` at scale `2^{-n}`; the layer
  bound gives `Σ_{2^{-n} ≥ w} (w² 4^n)^m 2^{(|k|−2−α∧η)n} ≍ w^{ηK−|k|}` for `2m > ηK − |k|`.
  Non-polynomial components: `(𝒦f)_{Iτ} = f_τ`, and `w^{(η−deg τ)∧0} ≤ w^{α∧η−deg τ}`.
* Increments (`d = d(x,y) ≤ W = min(w(x), w(y))`): as in [Hai14, Theorem 5.12], with regimes
  `2^{-n} ≤ d` (term by term, local bound at both points), `d < 2^{-n} ≤ W/c` (Taylor kernel at
  `x`, local bound), `2^{-n} > W/c` (Taylor kernel paired with `Rf` via the layer bound,
  `Σ_{2^{-n} ≥ W} d^{γ+2−|k|} 2^{(γ−α∧η)n} ≍ d^{γ+2−|k|} W^{ηK−γ−2}`, and the `Π_x` terms).
* Smooth remainder: the remainder `R = G − K` of the decomposition is lifted as
  `R_γ f(x) = Σ_k X^k/k! ⟨Rf, D^k R(x − ·)⟩` [Hai14, (7.7)], pairing the lattice reconstruction
  with the non-compactly supported `D^k R(x − ·)`. Only smoothness, causality and spatial decay of
  the derivatives on bounded times are used (`RemKernel`, with `annRemainderC N` as an instance),
  so the operator `kGammaRemG` of Theorem 7.1 is stated for a generic kernel pair `(h, r)`
  (`KernelPair`) and the specific kernel of [Hai14, Lemma 5.5] is an instance.

The fixed-point operator is `𝒦₀ g := (𝒦_γ + R_γ)(Pr g)` for the coordinate projection `Pr` onto a
block of symbols of degree `> −2` (`blockProj`). This needs `Γ_{xy}` to commute with the
projection. When the block is invariant under the whole structure group this holds for every model
(`isBlockInvariant_univ_erase`: if a symbol `ξ` is fixed by `G` and no `Γ e_i`, `i ≠ ξ`, has a
`ξ`-component, then the complement of `ξ` is a block); for Φ⁴₃ the block is the `Ξ`-free symbols,
and the projection is harmless on `U³`.

### Model bounds on a time window

The singular chain does not use global (`univ`) model bounds. A time cutoff of the noise does not
give them for renormalised models: far from the noise window `Π̂_x Ψ² = −C₁^ε`, which is not
uniformly bounded in `ε`. Purely local `Q`-form bounds on a set are not enough either, since `Q_t`
is non-local. The chain therefore uses the model bounds only on Hairer's window
`hairerTimeWindow = [−1, 2] × ℝ³` [Hai14, Theorem 7.1], together with a purely qualitative growth
of the regularisations, which is used only for the existence of pairings. Base points of the slab
`(0, T]`, `T ≤ 1`, together with the look-back of the kernel stay in the window, and all constants
depend only on the window constants. Stationary random models satisfy the weighted bounds of
`Model.GrowthModel` almost surely, and these give window bounds with constants `C_Π · sup_W ρ`;
this matches Hairer's `|||Z|||_{γ;O}`. The `Γ`-bounds are only required for pairs of points at
distance at most `1` (`GammaNearOn`).

For the extension theorem [Hai14, Theorem 5.14] (`IntExtHyp`, `IntExtHyp.intExtend`), the window
bounds at level `γ` give the `Γ`-bound of the integrated symbols at level `γ + 2` on the slab. They
do not give the `Π`-bound of `I e_i` at level `γ + 2`: `Q_t Π̂_x I e_i (x)` involves the germ at all
points, weighted by the non-compactly supported kernel `Q_t(x, ·)`, hence the model at times
outside the window.

### Results

* [Hai14, Theorem 7.1] on the slab for a kernel pair, window bounds and near-pair `Γ`-bounds:
  `Model.exists_singularBoundOn_kGammaRemG_win_near`.
* The Φ⁴₃ fixed point `U = −𝒦(U³) + v` on the slab for admissible models realising the causal
  kernel:
  `exists_unique_phi4_fixedPoint_causal_win_near`
  (`RegularityStructures.Abstract.Singular.Phi4FixedPointWinNear`).
* Lipschitz dependence of the fixed point on `(v, Z)`:
  `singularDiffBoundOn_phi4_fixedPoint_causal_win_near`, through the abstract
  `singularDiffBoundOn_slab_fixedPoint`. Constants depend on the model sizes (local Lipschitz).

## 8. Two models: the difference structure

The local Lipschitz half of Theorem 7.1 needs `|||𝒦¹g; 𝒦²ḡ||| ≤ c |||g; ḡ||| + ε_𝒦` with
`ε_𝒦 ≲ |||Z; Z̄|||`. It is reduced to the single-model theorem by a difference structure. With
`ι⊕ = {non-polynomial i} ⊕ ι`, `Π⊕_x(a,b) = λ⁻¹(Π¹_x − Π²_x)a + Π²_x b`,
`Γ⊕_{xy}(a,b) = (Q Γ¹_{xy} a, λ⁻¹(Γ¹_{xy} − Γ²_{xy})a + Γ²_{xy} b)` (`Q` drops polynomial components,
harmless since `Π¹ − Π²` vanishes on polynomials and `Γ¹ = Γ²` on polynomials), the group generated
by the `Γ⊕`, the polynomial sector in the second block, `I⊕ = I ⊕ I`, and `f⊕ = (λ Q f₁, f₁ − f₂)`:
the second block of `𝒦⊕ f⊕` is `𝒦¹f₁ − 𝒦²f₂`, its `Γ⊕`-increments are exactly the two-model
increments, and the single-model Theorem 7.1 for `(M⊕, f⊕)` with `λ = |||Z; Z̄|||` gives the local
Lipschitz bound (`TwoModel.structSumU`, `Model.exists_singularDiffBoundOn_kGammaRemG_win_near`).

## 9. Uniqueness, restarts and the late-slab gain

Uniqueness among all solutions on the slab by the continuity argument needs a gain on late slabs:
for `g` vanishing on `(0, s]`, `g ∈ D^{γ̄,η''}_{P_s}` with norm `≤ ‖g‖` uniformly in `s` (smaller
weights help), so Theorem 7.1 relative to `P_s = {t = s}` gives the vanishing bound
`w_s^{η_K − ℓ}`. But the slab norm is weighted at `P_0`, and for components of degree `ℓ > η_K` the
`P_s`-bound blows up at `P_s` while the `P_0`-bound gives only a gain in `t`, not in `t − s`. A
uniform `C (t − s)^θ` would need an interpolation using the high-order vanishing of `g` at `s`
(constant `s^{(η'' − γ̄)/2}`), which degenerates as `s → 0`.

The argument is therefore run in `P_s`-weighted norms on `(s, s+h]`, with `s` dyadic
(`ρ_s = √|t − s|`), never converting back to `P_0`:

* the restriction `D^{γ,η}_{P_0} → D^{γ,η}_{P_s}` on `t > s` has constant `min(1,√s)^{η−γ}`;
* the gain is Theorem 7.1 for the time-translated model `M.translate (s,0)` (`Model.translate`;
  the constants are uniform in the model), combined with the short-time gain for modelled
  distributions vanishing at `P_s` (`Model.singularBoundOn_of_vanishing`) and the Lipschitz bound
  of the cube in `ρ_s`-weighted norms;
* the lattice reconstruction and the remainder lift are covariant under dyadic translations, and
  the weight plane can be shifted (`RegularityStructures.Abstract.Translate`).

Dyadic restart times suffice: maximal solutions are glued along a dense set of times. Restarting
at time `s` uses the lift of `P_t a`, `a ∈ 𝒞^η` [Hai14, Lemma 7.5], time slices of the
function-like part of the solution together with a model hypothesis on the slices of `Ψ`
[Hai14, (9.19)], and the restart identity [Hai14, Proposition 7.11]. For singular models the
slices of `Ψ` require the joint continuity in `(s, t)` of the truncated potentials
`K∗(ξ 1_{r≥s})(t)` in the closure topology; this is a hypothesis on the model class, not a
consequence of the model bounds.

## 10. Parameters of the Φ⁴₃ application

The theorems of this layer take the non-integrality conditions as explicit hypotheses on the
structure; for Φ⁴₃ they are discharged from `κ ∉ Statements.excludedKappa`. The kernel of the
application is the causal decomposition of §6, which satisfies `ShellProfile` with causality, so
the singular chain (generic in the profile `h` and the remainder `r`) applies to it verbatim.
