/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.WeightedSingularProduct
public import RegularityStructures.Abstract.ProductCube
public import RegularityStructures.Abstract.Model

/-!
# Triple products and cubes of singular modelled distributions

The Φ⁴₃ nonlinearity `U ↦ Q_{<γ} (U ⋆ U ⋆ U)` on the singular spaces `D^{γ,η}_P` of
[Hai14, Definition 6.2], by two applications of [Hai14, Proposition 6.12]. For a sector `V` of
regularity `α`, a sector `W ⊇ V ⋆ V` of regularity `2α`, `Uᵢ ∈ D^{γ₀,η₀}_P(V)`, and exponents
`η' ≤ (η₀ + α) ∧ 2η₀`, `η' ≤ γ₀ + α` (inner product) and `η'' ≤ (η₀ + 2α) ∧ (η' + α) ∧ (η₀ + η')`,
`η'' ≤ γ₀ + 2α` (outer product):
`|||Q_{<γ₀+2α} (U₁ ⋆ (U₂ ⋆ U₃))|||_{γ₀+2α, η''; S} ≤ c² C₁ C₂ C₃ (1 + C_Γ)⁴`
(`Model.singularBoundOn_truncTripleMul`). The conditions `η' ≤ γ₀ + α` and `η'' ≤ γ₀ + 2α` are
the hypothesis `η ≤ γ` of Proposition 6.12, which is necessary (see
`RegularityStructures.Abstract.WeightedSingularProduct`).

Consequences for the cube: the bound (`Model.singularBoundOn_truncCube`), membership in
`D^{γ₀+2α, η''}_P` (`Model.truncCube_mem_singularModelledDistributions`) and the local Lipschitz
bound (`Model.singularBoundOn_truncCube_sub`).

Source: [Hai14] = arXiv:1303.5113v4, Proposition 6.12 and §9.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E}

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ} (M : Model 𝒯 K)

theorem SingularBoundOn.congr {ρ : E → ℝ} {γ η C : ℝ} {S : Set E} {f g : E → ι → ℝ}
    (hf : M.SingularBoundOn ρ γ η C S f) (hfg : ∀ x ∈ S, 0 < ρ x → f x = g x) :
    M.SingularBoundOn ρ γ η C S g := by
  refine ⟨fun x hx hρ i hi => ?_, fun x hx y hy hρx hρy hd j hj => ?_⟩
  · rw [← hfg x hx hρ]
    exact hf.1 x hx hρ i hi
  · rw [← hfg x hx hρx, ← hfg y hy hρy]
    exact hf.2 x hx y hy hρx hρy hd j hj

theorem SingularBoundOn.add {ρ : E → ℝ} {γ η A B : ℝ} {S : Set E} {u v : E → ι → ℝ}
    (hu : M.SingularBoundOn ρ γ η A S u) (hv : M.SingularBoundOn ρ γ η B S v) :
    M.SingularBoundOn ρ γ η (A + B) S (u + v) := by
  refine ⟨fun x hx hρ i hi => ?_, fun x hx y hy hρx hρy hd j hj => ?_⟩
  · simp only [Pi.add_apply, add_mul]
    exact (abs_add_le _ _).trans (add_le_add (hu.1 x hx hρ i hi) (hv.1 x hx hρ i hi))
  · have h : (u + v) y - M.gammaMap y x ((u + v) x) =
        (u y - M.gammaMap y x (u x)) + (v y - M.gammaMap y x (v x)) := by
      simp only [Pi.add_apply, map_add]
      abel
    rw [h, Pi.add_apply, add_mul, add_mul]
    exact (abs_add_le _ _).trans (add_le_add (hu.2 x hx y hy hρx hρy hd j hj)
      (hv.2 x hx y hy hρx hρy hd j hj))

end Model

end RegularityStructures

end
