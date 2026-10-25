/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.RegularityStructure
public import RegularityStructures.Analysis.Semigroup.Basic
public import Mathlib.Basic.ENNReal.Inv

/-!
# Models

A model `(Π, Γ)` for a regularity structure `𝒯` on a space `E` [Hai14, Definition 2.17],
[Hos25, Definition 3.2] consists of

* linear maps `Π_x : T → 𝒟'`, here `T →ₗ[ℝ] K.distributions`: a distribution is recorded through
  its regularisations `(Q_t Π_x τ)(z)` by the regularising semigroup `K` (see
  the design notes of the `Abstract` library);
* structure-group elements `Γ_{xy} ∈ G` with `Π_x Γ_{xy} = Π_y`, `Γ_{xx} = 1`,
  `Γ_{xy} Γ_{yz} = Γ_{xz}`.

We also require the regularisations `z ↦ (Q_t Π_x e_i)(z)` and the diagonal
`x ↦ (Q_t Π_x e_i)(x)` to be measurable (for models of interest both are continuous).

The analytic bounds are predicates with explicit constants, on a set `S ⊆ E`:

* `PiBoundOn γ C S`: `|(Q_t Π_x e_i)(x)| ≤ C t^{deg i/ℓ}` for `deg i < γ`, `0 < t ≤ 1`,
  `x ∈ S` ([Hos25, Definition 3.2 (2)], `p = ∞`, `w = 1`);
* `GammaBoundOn γ C S`: `|(Γ_{yx} e_i)_j| ≤ C d(y, x)^{deg i − deg j}` for
  `deg j < deg i < γ`, `x, y ∈ S` ([Hai14, (2.15)]).

The norms `piNormOn`, `gammaNormOn` are the best constants (in `ℝ≥0∞`); `piNormOn_le_iff` and
`gammaNormOn_le_iff` characterise them. With `S` compact these are the local model norms of
[Hai14, Definition 2.17]; with `S = univ` the global norms of [Hos25].

Sources: [Hai14] = arXiv:1303.5113v4; [Hos25] = arXiv:2310.07396v2.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E}

/-- A model `(Π, Γ)` for `𝒯` on `E`, with distributions represented through `K`
[Hai14, Definition 2.17]. -/
structure Model (𝒯 : RegularityStructure ι) (K : RegularisingSemigroup E μ) where
  /-- `Π_x : T → 𝒟'`. -/
  pi : E → (ι → ℝ) →ₗ[ℝ] K.distributions
  /-- `Γ_{xy} ∈ G`. -/
  gamma : E → E → 𝒯.group
  pi_gamma : ∀ x y τ,
    pi x (((gamma x y : LinearMap.GeneralLinearGroup ℝ (ι → ℝ)) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) τ) =
      pi y τ
  gamma_self : ∀ x, gamma x x = 1
  gamma_mul : ∀ x y z, gamma x y * gamma y z = gamma x z
  measurable_diag : ∀ i ⦃t : ℝ⦄, 0 < t →
    Measurable fun x => (pi x (Pi.single i 1) : ℝ → E → ℝ) t x
  measurable_pi : ∀ x i ⦃t : ℝ⦄, 0 < t → Measurable ((pi x (Pi.single i 1) : ℝ → E → ℝ) t)

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ}

/-- `Γ_{xy}` as a linear map of `T`. -/
def gammaMap (M : Model 𝒯 K) (x y : E) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) :=
  ((M.gamma x y : LinearMap.GeneralLinearGroup ℝ (ι → ℝ)) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))

/-- `(Q_t Π_x τ)(z)`: the regularisation of the distribution `Π_x τ`. -/
def regPi (M : Model 𝒯 K) (x : E) (τ : ι → ℝ) (t : ℝ) (z : E) : ℝ :=
  (M.pi x τ : ℝ → E → ℝ) t z

/-- The bound `|(Q_t Π_x e_i)(x)| ≤ C t^{deg i/ℓ}` for `deg i < γ`, `0 < t ≤ 1`, `x ∈ S`. -/
def PiBoundOn (M : Model 𝒯 K) (γ C : ℝ) (S : Set E) : Prop :=
  ∀ i, 𝒯.deg i < γ → ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x ∈ S,
    |M.regPi x (Pi.single i 1) t x| ≤ C * t ^ (𝒯.deg i / K.order)

/-- The bound `|(Γ_{yx} e_i)_j| ≤ C d(y, x)^{deg i - deg j}` for `deg j < deg i < γ`,
`x, y ∈ S`. -/
def GammaBoundOn (M : Model 𝒯 K) (γ C : ℝ) (S : Set E) : Prop :=
  ∀ i j, 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i → ∀ x ∈ S, ∀ y ∈ S,
    |M.gammaMap y x (Pi.single i 1) j| ≤ C * K.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j)

/-- The `Π`-part of the model norm on `S`: the best constant in `PiBoundOn`. -/
def piNormOn (M : Model 𝒯 K) (γ : ℝ) (S : Set E) : ℝ≥0∞ :=
  ⨅ (C : ℝ≥0) (_ : M.PiBoundOn γ C S), (C : ℝ≥0∞)

/-- The `Γ`-part of the model norm on `S`: the best constant in `GammaBoundOn`. -/
def gammaNormOn (M : Model 𝒯 K) (γ : ℝ) (S : Set E) : ℝ≥0∞ :=
  ⨅ (C : ℝ≥0) (_ : M.GammaBoundOn γ C S), (C : ℝ≥0∞)

/-- The model norm `‖Π‖_{γ;S} + ‖Γ‖_{γ;S}` [Hai14, (2.16)]. -/
def normOn (M : Model 𝒯 K) (γ : ℝ) (S : Set E) : ℝ≥0∞ :=
  M.piNormOn γ S + M.gammaNormOn γ S

/-- The bound `|(Q_t (Π¹_x − Π²_x) e_i)(x)| ≤ C t^{deg i/ℓ}` on the difference of two models. -/
def PiDiffBoundOn (M₁ M₂ : Model 𝒯 K) (γ C : ℝ) (S : Set E) : Prop :=
  ∀ i, 𝒯.deg i < γ → ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x ∈ S,
    |M₁.regPi x (Pi.single i 1) t x - M₂.regPi x (Pi.single i 1) t x| ≤
      C * t ^ (𝒯.deg i / K.order)

/-- The bound `|((Γ¹_{yx} − Γ²_{yx}) e_i)_j| ≤ C d(y, x)^{deg i − deg j}` on the difference of
two models. -/
def GammaDiffBoundOn (M₁ M₂ : Model 𝒯 K) (γ C : ℝ) (S : Set E) : Prop :=
  ∀ i j, 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i → ∀ x ∈ S, ∀ y ∈ S,
    |M₁.gammaMap y x (Pi.single i 1) j - M₂.gammaMap y x (Pi.single i 1) j| ≤
      C * K.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j)

end Model

end RegularityStructures

end

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace RegularityStructures

/-- The best constant of a closed, upward-closed family of admissible constants is admissible:
`⨅_{C admissible} C ≤ c ↔ c admissible`. -/
theorem iInf_nnreal_le_iff {P : ℝ≥0 → Prop} (hmono : ∀ ⦃a b⦄, a ≤ b → P a → P b)
    (hclosed : ∀ c : ℝ≥0, (∀ ε : ℝ≥0, 0 < ε → P (c + ε)) → P c) (c : ℝ≥0) :
    (⨅ (C : ℝ≥0) (_ : P C), (C : ℝ≥0∞)) ≤ c ↔ P c := by
  refine ⟨fun h => hclosed c fun ε hε => ?_, fun h => iInf₂_le c h⟩
  have hlt : (⨅ (C : ℝ≥0) (_ : P C), (C : ℝ≥0∞)) < ((c + ε : ℝ≥0) : ℝ≥0∞) :=
    h.trans_lt (by exact_mod_cast lt_add_of_pos_right c hε)
  obtain ⟨C, hC⟩ := iInf_lt_iff.1 hlt
  obtain ⟨hPC, hC'⟩ := iInf_lt_iff.1 hC
  exact hmono (by exact_mod_cast hC'.le) hPC

/-- If `x ≤ (c + ε) r` for every `ε > 0` and `r ≥ 0`, then `x ≤ c r`. -/
theorem le_mul_of_forall_pos_le_add_mul {x r : ℝ} {c : ℝ≥0} (hr : 0 ≤ r)
    (h : ∀ ε : ℝ≥0, 0 < ε → x ≤ ((c + ε : ℝ≥0) : ℝ) * r) : x ≤ c * r := by
  by_contra hlt
  rw [not_le] at hlt
  rcases hr.eq_or_lt with hr0 | hr0
  · have := h 1 one_pos
    rw [← hr0, mul_zero] at this hlt
    linarith
  · set δ : ℝ := (x - c * r) / (2 * r) with hδ
    have hδpos : 0 < δ := div_pos (by linarith) (by linarith)
    have h1 := h ⟨δ, hδpos.le⟩ hδpos
    have h2 : ((c + ⟨δ, hδpos.le⟩ : ℝ≥0) : ℝ) * r = c * r + (x - c * r) / 2 := by
      change ((c : ℝ) + δ) * r = _
      rw [add_mul, hδ]
      field_simp
    linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E}

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ} (M : Model 𝒯 K)

theorem PiBoundOn.mono {γ C C' : ℝ} {S : Set E} (h : M.PiBoundOn γ C S) (hC : C ≤ C') :
    M.PiBoundOn γ C' S := fun i hi t ht x hx =>
  (h i hi t ht x hx).trans
    (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg ht.1.le _))

theorem GammaBoundOn.mono {γ C C' : ℝ} {S : Set E} (h : M.GammaBoundOn γ C S) (hC : C ≤ C') :
    M.GammaBoundOn γ C' S := fun i j hi hj x hx y hy =>
  (h i j hi hj x hx y hy).trans
    (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (K.scaleDist_nonneg _ _) _))

theorem piNormOn_le_iff {γ : ℝ} {S : Set E} (C : ℝ≥0) :
    M.piNormOn γ S ≤ C ↔ M.PiBoundOn γ C S :=
  iInf_nnreal_le_iff (P := fun C : ℝ≥0 => M.PiBoundOn γ C S) (fun _ _ hab h => h.mono M (by exact_mod_cast hab))
    (fun c hc i hi t ht x hx => le_mul_of_forall_pos_le_add_mul (Real.rpow_nonneg ht.1.le _)
      fun ε hε => hc ε hε i hi t ht x hx) C

theorem gammaNormOn_le_iff {γ : ℝ} {S : Set E} (C : ℝ≥0) :
    M.gammaNormOn γ S ≤ C ↔ M.GammaBoundOn γ C S :=
  iInf_nnreal_le_iff (P := fun C : ℝ≥0 => M.GammaBoundOn γ C S) (fun _ _ hab h => h.mono M (by exact_mod_cast hab))
    (fun c hc i j hi hj x hx y hy => le_mul_of_forall_pos_le_add_mul
      (Real.rpow_nonneg (K.scaleDist_nonneg _ _) _)
      fun ε hε => hc ε hε i j hi hj x hx y hy) C

theorem gammaMap_self (x : E) : M.gammaMap x x = LinearMap.id := by
  rw [gammaMap, M.gamma_self]
  rfl

theorem gammaMap_comp (x y z : E) : M.gammaMap x y ∘ₗ M.gammaMap y z = M.gammaMap x z := by
  simp only [gammaMap, ← M.gamma_mul x y z]
  rfl

theorem pi_gammaMap (x y : E) (τ : ι → ℝ) : M.pi x (M.gammaMap x y τ) = M.pi y τ :=
  M.pi_gamma x y τ

theorem regPi_gammaMap (x y : E) (τ : ι → ℝ) (t : ℝ) (z : E) :
    M.regPi x (M.gammaMap x y τ) t z = M.regPi y τ t z := by
  simp [regPi, pi_gammaMap]

theorem isGradedUnipotent_gammaMap (x y : E) : IsGradedUnipotent 𝒯.deg (M.gammaMap x y) :=
  𝒯.isGradedUnipotent _ (M.gamma x y).2

theorem regPi_add (x : E) (τ σ : ι → ℝ) (t : ℝ) (z : E) :
    M.regPi x (τ + σ) t z = M.regPi x τ t z + M.regPi x σ t z := by
  simp [regPi]

theorem regPi_smul (x : E) (c : ℝ) (τ : ι → ℝ) (t : ℝ) (z : E) :
    M.regPi x (c • τ) t z = c * M.regPi x τ t z := by
  simp [regPi]

theorem regPi_sub (x : E) (τ σ : ι → ℝ) (t : ℝ) (z : E) :
    M.regPi x (τ - σ) t z = M.regPi x τ t z - M.regPi x σ t z := by
  simp [regPi]

/-- `(Q_t Π_x τ)(z) = ∑_i τ_i (Q_t Π_x e_i)(z)`. -/
theorem regPi_eq_sum (x : E) (τ : ι → ℝ) (t : ℝ) (z : E) :
    M.regPi x τ t z = ∑ i, τ i * M.regPi x (Pi.single i 1) t z := by
  conv_lhs => rw [eq_sum_single τ]
  simp [regPi, map_sum, Finset.sum_apply]

theorem regPi_mem (x : E) (τ : ι → ℝ) : (fun t z => M.regPi x τ t z) ∈ K.distributions :=
  (M.pi x τ).2

theorem measurable_regPi (x : E) (τ : ι → ℝ) {t : ℝ} (ht : 0 < t) :
    Measurable (M.regPi x τ t) := by
  have h : M.regPi x τ t = fun z => ∑ i, τ i * M.regPi x (Pi.single i 1) t z := by
    funext z
    exact M.regPi_eq_sum x τ t z
  rw [h]
  exact Finset.measurable_sum _ fun i _ => (M.measurable_pi x i ht).const_mul _

end Model

end RegularityStructures

end
