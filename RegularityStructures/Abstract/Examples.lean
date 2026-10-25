/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Reconstruction

/-!
# Examples: the hypotheses of the reconstruction theorem are satisfiable

* `RegularisingSemigroup.ofFunction g`: a bounded measurable function `g` is a `Q`-distribution,
  with regularisations `Q_t g` (`ofFunction_mem`).
* `singleStructure α`: the regularity structure with one basis vector `Ξ` of degree `α` and trivial
  structure group.
* `constModel ξ`: for a `Q`-distribution `ξ` with measurable regularisations, the model
  `Π_x Ξ = ξ`, `Γ_{xy} = 1`. If `|(Q_t ξ)(x)| ≤ C t^{α/ℓ}`, then every constant `f ≡ c Ξ` lies in
  `D^γ` and its reconstruction is `c ξ` (`reconstruct_const`), for every `γ > max α 0`.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace RegularityStructures

variable {E : Type*} [MeasurableSpace E] {μ : Measure E}

/-- The `Q`-distribution of a function: `t ↦ Q_t g` for `t > 0`, and `0` for `t ≤ 0`. -/
def RegularisingSemigroup.ofFunction (K : RegularisingSemigroup E μ) (g : E → ℝ) :
    ℝ → E → ℝ :=
  fun t x => if 0 < t then K.apply t g x else 0

/-- The regularity structure with a single basis vector of degree `α` and trivial structure
group. -/
def singleStructure (α : ℝ) : RegularityStructure Unit where
  deg _ := α
  group := ⊥
  isGradedUnipotent g hg := by
    rw [Subgroup.mem_bot] at hg
    subst hg
    exact isGradedUnipotent_id

/-- The model `Π_x Ξ = ξ`, `Γ_{xy} = 1` of the single-symbol structure. -/
def constModel (K : RegularisingSemigroup E μ) (α : ℝ) (ξ : K.distributions)
    (hξ : ∀ ⦃t : ℝ⦄, 0 < t → Measurable ((ξ : ℝ → E → ℝ) t)) :
    Model (singleStructure α) K where
  pi _ := (LinearMap.proj () : (Unit → ℝ) →ₗ[ℝ] ℝ).smulRight ξ
  gamma _ _ := 1
  pi_gamma _ _ _ := rfl
  gamma_self _ := rfl
  gamma_mul _ _ _ := mul_one 1
  measurable_diag _ t ht := by
    simpa using hξ ht
  measurable_pi _ _ t ht := by
    simpa using hξ ht

end RegularityStructures

end

public section

open MeasureTheory Set

namespace RegularityStructures

variable {E : Type*} [MeasurableSpace E] {μ : Measure E}

theorem RegularisingSemigroup.ofFunction_mem (K : RegularisingSemigroup E μ) [SFinite μ]
    {g : E → ℝ} (hg : Measurable g) {B : ℝ} (hB : ∀ y, |g y| ≤ B) :
    K.ofFunction g ∈ K.distributions := by
  refine ⟨fun t ht => funext fun x => by simp [ofFunction, not_lt.2 ht], fun s t hs ht x => ?_⟩
  have h : K.ofFunction g t = K.apply t g := funext fun y => by simp [ofFunction, ht]
  rw [h]
  refine ⟨K.integrable_kernel_mul_of_bound hs x (K.measurable_apply t hg)
    (K.abs_apply_le_of_bound ht hB), ?_⟩
  rw [K.apply_apply hs ht hg hB]
  simp [ofFunction, add_pos hs ht]

section Const

variable (K : RegularisingSemigroup E μ) (α : ℝ) (ξ : K.distributions)
  (hξ : ∀ ⦃t : ℝ⦄, 0 < t → Measurable ((ξ : ℝ → E → ℝ) t))

theorem constModel_regPi (x : E) (τ : Unit → ℝ) (t : ℝ) (z : E) :
    (constModel K α ξ hξ).regPi x τ t z = τ () * (ξ : ℝ → E → ℝ) t z := by
  simp [Model.regPi, constModel]

theorem constModel_gammaMap (x y : E) : (constModel K α ξ hξ).gammaMap x y = LinearMap.id :=
  rfl

theorem constModel_piBoundOn {γ C : ℝ}
    (hC : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x, |(ξ : ℝ → E → ℝ) t x| ≤ C * t ^ (α / K.order)) :
    (constModel K α ξ hξ).PiBoundOn γ C univ := by
  intro i _ t ht x _
  rw [constModel_regPi, Pi.single_eq_same, one_mul]
  exact hC t ht x

theorem constModel_modelledBoundOn (γ c : ℝ) :
    (constModel K α ξ hξ).ModelledBoundOn γ |c| univ (fun _ _ => c : E → Unit → ℝ) :=
  ⟨fun _ _ _ _ => le_rfl, fun _ _ _ _ _ _ => by
    simp [constModel_gammaMap, Real.rpow_nonneg (K.scaleDist_nonneg _ _),
      mul_nonneg (abs_nonneg c)]⟩

/-- Constant modelled distributions `f ≡ c Ξ` belong to `D^γ` for `γ > α`. -/
theorem const_mem_modelledDistributions {γ : ℝ} (hαγ : α < γ) (c : ℝ) :
    (fun _ _ => c : E → Unit → ℝ) ∈ (constModel K α ξ hξ).modelledDistributions γ :=
  ⟨measurable_const, fun _ _ hi => absurd hαγ (not_lt.2 hi), |c|,
    constModel_modelledBoundOn K α ξ hξ γ c⟩

/-- The reconstruction of the constant modelled distribution `c Ξ` is `c ξ`. -/
theorem reconstruct_const [SFinite μ] {γ C : ℝ} (hγ : 0 < γ) (hαγ : α < γ) (hC0 : 0 ≤ C)
    (hC : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x, |(ξ : ℝ → E → ℝ) t x| ≤ C * t ^ (α / K.order)) (c : ℝ) :
    (constModel K α ξ hξ).reconstruct (fun _ _ => c) = c • (ξ : ℝ → E → ℝ) := by
  refine ((constModel K α ξ hξ).eq_reconstruct hγ (constModel_piBoundOn K α ξ hξ hC) hC0
    (const_mem_modelledDistributions K α ξ hξ hαγ c) (constModel_modelledBoundOn K α ξ hξ γ c)
    (abs_nonneg c) (K.distributions.smul_mem c ξ.2) (C' := 0) fun t _ x => ?_).symm
  rw [constModel_regPi]
  simp

end Const

end RegularityStructures

end
