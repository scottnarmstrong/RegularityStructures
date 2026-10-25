/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.WeightedSingularCube
public import RegularityStructures.Abstract.WeightedSingularTwoModels
public import RegularityStructures.Abstract.Model

/-!
# The cube on singular modelled distributions for two models

Two applications of the two-model bound of [Hai14, Proposition 6.12]: for `U ∈ D^{γ₀,η₀}_P(V)`
modelled for `(Π, Γ)` and `Ū ∈ D^{γ₀,η₀}_P(V)` modelled for `(Π̄, Γ̄)`, both with constant `C`,
`|||U; Ū|||_{γ₀,η₀} ≤ δ` and `‖Γ − Γ̄‖ ≤ δ_Γ`,
`|||U³; Ū³|||_{γ₀+2α, η''} ≤ c² (3 C² δ + 4 C³ δ_Γ) (1 + C_Γ)⁴`
(`Model.singularDiffBoundOn_truncCube`), with the exponent conditions of
`Model.singularBoundOn_truncCube`.

Source: [Hai14] = arXiv:1303.5113v4, Proposition 6.12.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E}

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ}

theorem SingularDiffBoundOn.congr {M₁ M₂ : Model 𝒯 K} {ρ : E → ℝ} {γ η C : ℝ} {S : Set E}
    {f g f' g' : E → ι → ℝ} (h : M₁.SingularDiffBoundOn M₂ ρ γ η C S f g)
    (hf : ∀ x ∈ S, 0 < ρ x → f x = f' x) (hg : ∀ x ∈ S, 0 < ρ x → g x = g' x) :
    M₁.SingularDiffBoundOn M₂ ρ γ η C S f' g' := by
  refine ⟨fun x hx hρ i hi => ?_, fun x hx y hy hρx hρy hd j hj => ?_⟩
  · rw [← hf x hx hρ, ← hg x hx hρ]
    exact h.1 x hx hρ i hi
  · rw [← hf x hx hρx, ← hf y hy hρy, ← hg x hx hρx, ← hg y hy hρy]
    exact h.2 x hx y hy hρx hρy hd j hj

theorem SingularDiffBoundOn.mono {M₁ M₂ : Model 𝒯 K} {ρ : E → ℝ} {γ η C C' : ℝ} {S : Set E}
    {f g : E → ι → ℝ} (h : M₁.SingularDiffBoundOn M₂ ρ γ η C S f g) (hC : C ≤ C') :
    M₁.SingularDiffBoundOn M₂ ρ γ η C' S f g := by
  refine ⟨fun x hx hρ i hi => (h.1 x hx hρ i hi).trans ?_,
    fun x hx y hy hρx hρy hd j hj => (h.2 x hx y hy hρx hρy hd j hj).trans ?_⟩
  · exact mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (singularWeight_pos hρ).le _)
  · refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC
      (Real.rpow_nonneg (K.scaleDist_nonneg _ _) _)) (Real.rpow_nonneg ?_ _)
    exact (lt_min (singularWeight_pos hρx) (singularWeight_pos hρy)).le

end Model

end RegularityStructures

end
