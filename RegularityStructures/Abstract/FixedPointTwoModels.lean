/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.FixedPointTheorem
public import RegularityStructures.Abstract.Model

/-!
# Lipschitz dependence of the fixed point on the model

[Hai14, Theorem 7.8], last statement: if `F` is *strongly* locally Lipschitz, the solution map
`(v, Z) ↦ U` is locally Lipschitz, the distance between solutions for two models `Z = (Π, Γ)` and
`Z̄ = (Π̄, Γ̄)` being measured by `|||U; Ū|||_{γ,η;T}` (`Model.SingularDiffBoundOn`). The two
solutions live in different spaces (`D^{γ,η}_P` depends on `Γ`), so the argument is not Banach's
theorem but the iteration of the affine contraction `a ↦ c L a + ε` on the closed predicate
`a ↦ |||U; Ū||| ≤ a` (`le_of_forall_imp_mul_add`).

Hypotheses, for solutions `U = 𝒦 (F U) + v` (model `M₁`) and `Ū = 𝒦̄ (F̄ Ū) + v̄` (model `M₂`)
of norm `≤ R`:

* `𝒦, 𝒦̄`: `|||𝒦 g; 𝒦̄ ḡ|||_{γ,η} ≤ c |||g; ḡ|||_{γ',η'} + ε_𝒦` for `|||g|||, |||ḡ||| ≤ B` (in
  [Hai14, Theorem 7.1], `c = C T^θ` and `ε_𝒦 = C T^θ |||Z; Z̄|||`);
* `F, F̄`: `|||F u; F̄ ū|||_{γ',η'} ≤ L |||u; ū|||_{γ,η} + ε_F` for `|||u|||, |||ū||| ≤ R` (strong
  local Lipschitz property; `ε_F = L |||Z; Z̄|||`), and `|||F u|||, |||F̄ ū||| ≤ B`;
* `|||v; v̄|||_{γ,η} ≤ δ_v`, and `c L < 1`.

Conclusion (`Model.singularDiffBoundOn_slab_fixedPoint`):
`|||U; Ū|||_{γ,η;T} ≤ (δ_v + c ε_F + ε_𝒦) / (1 − c L)`; with the time `T ≤ fixedPointTime`
(`Model.singularDiffBoundOn_slab_fixedPoint_of_le_fixedPointTime`) the factor is `2`.

Source: [Hai14] = arXiv:1303.5113v4, Theorem 7.8 and its proof.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E}

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ} {M₁ M₂ : Model 𝒯 K}
  {ρ : E → ℝ} {V V' : Submodule ℝ (ι → ℝ)} {γ η γ' η' : ℝ} {S : Set E}

/-- **Lipschitz dependence on the model** ([Hai14, Theorem 7.8], strongly locally Lipschitz
case): `|||U; Ū|||_{γ,η;T} ≤ (δ_v + c ε_F + ε_𝒦) / (1 − c L)` for solutions `U` (model `M₁`)
and `Ū` (model `M₂`) of norm `≤ R`. -/
theorem singularDiffBoundOn_slab_fixedPoint {c L R B εF ε𝒦 δv : ℝ} (hc : 0 ≤ c) (hL : 0 ≤ L)
    (hεF : 0 ≤ εF) (hε𝒦 : 0 ≤ ε𝒦) (hδv : 0 ≤ δv) (hcL : c * L < 1)
    (𝒦₁ : M₁.SlabSpace ρ V' γ' η' S →ₗ[ℝ] M₁.SlabSpace ρ V γ η S)
    (𝒦₂ : M₂.SlabSpace ρ V' γ' η' S →ₗ[ℝ] M₂.SlabSpace ρ V γ η S)
    (h𝒦 : ∀ g₁ g₂ b, ‖g₁‖ ≤ B → ‖g₂‖ ≤ B → 0 ≤ b →
      M₁.SingularDiffBoundOn M₂ ρ γ' η' b S g₁.val g₂.val →
      M₁.SingularDiffBoundOn M₂ ρ γ η (c * b + ε𝒦) S (𝒦₁ g₁).val (𝒦₂ g₂).val)
    (F₁ : M₁.SlabSpace ρ V γ η S → M₁.SlabSpace ρ V' γ' η' S)
    (F₂ : M₂.SlabSpace ρ V γ η S → M₂.SlabSpace ρ V' γ' η' S)
    (hF : ∀ u₁ u₂ a, ‖u₁‖ ≤ R → ‖u₂‖ ≤ R → 0 ≤ a →
      M₁.SingularDiffBoundOn M₂ ρ γ η a S u₁.val u₂.val →
      M₁.SingularDiffBoundOn M₂ ρ γ' η' (L * a + εF) S (F₁ u₁).val (F₂ u₂).val)
    (hF₁B : ∀ u, ‖u‖ ≤ R → ‖F₁ u‖ ≤ B) (hF₂B : ∀ u, ‖u‖ ≤ R → ‖F₂ u‖ ≤ B)
    {v₁ U₁ : M₁.SlabSpace ρ V γ η S} {v₂ U₂ : M₂.SlabSpace ρ V γ η S}
    (hv : M₁.SingularDiffBoundOn M₂ ρ γ η δv S v₁.val v₂.val) (hU₁ : ‖U₁‖ ≤ R)
    (hU₂ : ‖U₂‖ ≤ R) (hfix₁ : U₁ = 𝒦₁ (F₁ U₁) + v₁) (hfix₂ : U₂ = 𝒦₂ (F₂ U₂) + v₂) :
    M₁.SingularDiffBoundOn M₂ ρ γ η ((δv + c * εF + ε𝒦) / (1 - c * L)) S U₁.val U₂.val := by
  have hq0 : 0 ≤ c * L := mul_nonneg hc hL
  have hstep : ∀ a, 0 ≤ a → M₁.SingularDiffBoundOn M₂ ρ γ η a S U₁.val U₂.val →
      M₁.SingularDiffBoundOn M₂ ρ γ η (c * L * a + (δv + c * εF + ε𝒦)) S U₁.val U₂.val := by
    intro a ha hU
    have hFU := hF U₁ U₂ a hU₁ hU₂ ha hU
    have h𝒦U := h𝒦 (F₁ U₁) (F₂ U₂) (L * a + εF) (hF₁B U₁ hU₁) (hF₂B U₂ hU₂)
      (add_nonneg (mul_nonneg hL ha) hεF) hFU
    have hsum := h𝒦U.add hv
    have e₁ : (𝒦₁ (F₁ U₁)).val + v₁.val = U₁.val := by
      rw [← SlabSpace.val_add, ← hfix₁]
    have e₂ : (𝒦₂ (F₂ U₂)).val + v₂.val = U₂.val := by
      rw [← SlabSpace.val_add, ← hfix₂]
    rw [e₁, e₂] at hsum
    refine hsum.mono (le_of_eq ?_)
    ring
  have h₀ : M₁.SingularDiffBoundOn M₂ ρ γ η (‖U₁‖ + ‖U₂‖) S U₁.val U₂.val :=
    singularDiffBoundOn_of_singularBoundOn U₁.singularBoundOn_norm U₂.singularBoundOn_norm
  exact le_of_forall_imp_mul_add (P := fun a => M₁.SingularDiffBoundOn M₂ ρ γ η a S U₁.val U₂.val)
    hq0 hcL (by positivity) (fun a b hab h => h.mono hab)
    (fun a h => SingularDiffBoundOn.of_forall_lt h) h₀ hstep

/-- **Lipschitz dependence on the model with the explicit time**: for
`0 < T ≤ fixedPointTime C θ L₀ A R₀ p`, `c = C T^θ`, `L = L₀ (2 + R₀)^p` and solutions of norm
`≤ R₀ + 1`: `|||U; Ū|||_{γ,η;T} ≤ 2 (δ_v + C T^θ ε_F + ε_𝒦)`. -/
theorem singularDiffBoundOn_slab_fixedPoint_of_le_fixedPointTime {C θ L₀ A R₀ T B εF ε𝒦 δv : ℝ}
    {p : ℕ} (hC : 0 ≤ C) (hθ : 0 < θ) (hL₀ : 0 ≤ L₀) (hA : 0 ≤ A) (hR₀ : 0 ≤ R₀) (hT : 0 < T)
    (hTT₀ : T ≤ fixedPointTime C θ L₀ A R₀ p) (hεF : 0 ≤ εF) (hε𝒦 : 0 ≤ ε𝒦) (hδv : 0 ≤ δv)
    (𝒦₁ : M₁.SlabSpace ρ V' γ' η' S →ₗ[ℝ] M₁.SlabSpace ρ V γ η S)
    (𝒦₂ : M₂.SlabSpace ρ V' γ' η' S →ₗ[ℝ] M₂.SlabSpace ρ V γ η S)
    (h𝒦 : ∀ g₁ g₂ b, ‖g₁‖ ≤ B → ‖g₂‖ ≤ B → 0 ≤ b →
      M₁.SingularDiffBoundOn M₂ ρ γ' η' b S g₁.val g₂.val →
      M₁.SingularDiffBoundOn M₂ ρ γ η (C * T ^ θ * b + ε𝒦) S (𝒦₁ g₁).val (𝒦₂ g₂).val)
    (F₁ : M₁.SlabSpace ρ V γ η S → M₁.SlabSpace ρ V' γ' η' S)
    (F₂ : M₂.SlabSpace ρ V γ η S → M₂.SlabSpace ρ V' γ' η' S)
    (hF : ∀ u₁ u₂ a, ‖u₁‖ ≤ R₀ + 1 → ‖u₂‖ ≤ R₀ + 1 → 0 ≤ a →
      M₁.SingularDiffBoundOn M₂ ρ γ η a S u₁.val u₂.val →
      M₁.SingularDiffBoundOn M₂ ρ γ' η' (L₀ * (2 + R₀) ^ p * a + εF) S (F₁ u₁).val (F₂ u₂).val)
    (hF₁B : ∀ u, ‖u‖ ≤ R₀ + 1 → ‖F₁ u‖ ≤ B) (hF₂B : ∀ u, ‖u‖ ≤ R₀ + 1 → ‖F₂ u‖ ≤ B)
    {v₁ U₁ : M₁.SlabSpace ρ V γ η S} {v₂ U₂ : M₂.SlabSpace ρ V γ η S}
    (hv : M₁.SingularDiffBoundOn M₂ ρ γ η δv S v₁.val v₂.val) (hU₁ : ‖U₁‖ ≤ R₀ + 1)
    (hU₂ : ‖U₂‖ ≤ R₀ + 1) (hfix₁ : U₁ = 𝒦₁ (F₁ U₁) + v₁) (hfix₂ : U₂ = 𝒦₂ (F₂ U₂) + v₂) :
    M₁.SingularDiffBoundOn M₂ ρ γ η (2 * (δv + C * T ^ θ * εF + ε𝒦)) S U₁.val U₂.val := by
  have hsmall := mul_rpow_mul_le_one_of_le_fixedPointTime hC hθ hL₀ hA hR₀ hT.le hTT₀
  have hc : 0 ≤ C * T ^ θ := mul_nonneg hC (Real.rpow_nonneg hT.le _)
  have hL : 0 ≤ L₀ * (2 + R₀) ^ p := by positivity
  have hcL : C * T ^ θ * (L₀ * (2 + R₀) ^ p) * 2 ≤ 1 := by
    have : C * T ^ θ * (L₀ * (2 + R₀) ^ p) * 2 ≤
        C * T ^ θ * (A + L₀ * (2 + R₀) ^ p * (3 + R₀)) := by
      have := mul_nonneg hc hL
      nlinarith
    linarith
  have h := singularDiffBoundOn_slab_fixedPoint hc hL hεF hε𝒦 hδv (by linarith) 𝒦₁ 𝒦₂ h𝒦 F₁ F₂
    hF hF₁B hF₂B hv hU₁ hU₂ hfix₁ hfix₂
  refine h.mono ?_
  have hε : 0 ≤ δv + C * T ^ θ * εF + ε𝒦 := by positivity
  rw [div_le_iff₀ (by linarith)]
  nlinarith [mul_nonneg hc hL]

end Model

end RegularityStructures

end
