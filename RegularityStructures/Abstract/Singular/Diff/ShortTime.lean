/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.FixedPointShortTime
public import RegularityStructures.Abstract.FixedPointTimeSlab
public import RegularityStructures.Abstract.WeightedSingularCubeTwoModels
public import RegularityStructures.Abstract.Model

/-!
# The short-time gain for the two-model singular bound

Difference versions of `Model.singularBoundOn_of_vanishing` and `Model.singularBoundOn_shortTime`:
if `|f₁(x)_i − f₂(x)_i| ≤ C ‖x‖_P^{η + κ − deg i}` and `|||f₁; f₂|||_{γ,η+κ;S} ≤ C`, then on a slab
where `‖x‖_P ≤ r`, `|||f₁; f₂|||_{γ,η;S} ≤ r^κ C`.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E}

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ}

/-- **The short-time gain for differences**: on a slab where `‖x‖_P ≤ r`, the vanishing bound
`|f₁(x)_i − f₂(x)_i| ≤ C ‖x‖_P^{η + κ − deg i}` and the bound of `D^{γ,η+κ}` give
`|||f₁; f₂|||_{γ,η;S} ≤ r^κ C`. -/
theorem singularDiffBoundOn_of_vanishing (M₁ M₂ : Model 𝒯 K) {ρ : E → ℝ} {γ η κ C r : ℝ}
    {S : Set E} {f₁ f₂ : E → ι → ℝ} (hκ : 0 ≤ κ) (hC : 0 ≤ C)
    (hS : ∀ x ∈ S, 0 < ρ x → singularWeight ρ x ≤ r)
    (hsup : ∀ x ∈ S, 0 < ρ x → ∀ i, 𝒯.deg i < γ →
      |f₁ x i - f₂ x i| ≤ C * singularWeight ρ x ^ (η + κ - 𝒯.deg i))
    (hf : M₁.SingularDiffBoundOn M₂ ρ γ (η + κ) C S f₁ f₂) :
    M₁.SingularDiffBoundOn M₂ ρ γ η (r ^ κ * C) S f₁ f₂ := by
  refine ⟨fun x hx hρ i hi => ?_, fun x hx y hy hρx hρy hd j hj => ?_⟩
  · have hw0 := singularWeight_pos hρ
    have hexp : η + κ - 𝒯.deg i = (η - 𝒯.deg i) + κ := by ring
    refine (hsup x hx hρ i hi).trans ?_
    rw [hexp, mul_comm (r ^ κ) C, mul_assoc]
    exact mul_le_mul_of_nonneg_left (rpow_add_le_rpow_mul_rpow_min hw0 (hS x hx hρ)
      (singularWeight_le_one ρ x) hκ) hC
  · have hw0 : 0 < min (singularWeight ρ x) (singularWeight ρ y) :=
      lt_min (singularWeight_pos hρx) (singularWeight_pos hρy)
    have hwr : min (singularWeight ρ x) (singularWeight ρ y) ≤ r :=
      (min_le_left _ _).trans (hS x hx hρx)
    have hexp : η + κ - γ = (η - γ) + κ := by ring
    have hd0 : 0 ≤ K.scaleDist y x ^ (γ - 𝒯.deg j) :=
      Real.rpow_nonneg (K.scaleDist_nonneg _ _) _
    refine (hf.2 x hx y hy hρx hρy hd j hj).trans ?_
    calc C * K.scaleDist y x ^ (γ - 𝒯.deg j) *
          min (singularWeight ρ x) (singularWeight ρ y) ^ (η + κ - γ)
        = C * (K.scaleDist y x ^ (γ - 𝒯.deg j) *
          min (singularWeight ρ x) (singularWeight ρ y) ^ ((η - γ) + κ)) := by
          rw [hexp, mul_assoc]
      _ ≤ C * (K.scaleDist y x ^ (γ - 𝒯.deg j) *
          (r ^ κ * min (singularWeight ρ x) (singularWeight ρ y) ^ (η - γ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (rpow_add_le_rpow_mul_rpow hw0 hwr hκ) hd0) hC
      _ = r ^ κ * C * K.scaleDist y x ^ (γ - 𝒯.deg j) *
          min (singularWeight ρ x) (singularWeight ρ y) ^ (η - γ) := by ring

/-- **The short-time gain for differences on a slab** `ρ ≤ T^{1/𝔰₀}`: constant `T^{κ/𝔰₀} C`. -/
theorem singularDiffBoundOn_shortTime (M₁ M₂ : Model 𝒯 K) {ρ : E → ℝ}
    {γ η κ C T s : ℝ} {S : Set E} {f₁ f₂ : E → ι → ℝ} (hκ : 0 ≤ κ) (hC : 0 ≤ C) (hT : 0 ≤ T)
    (hS : ∀ x ∈ S, 0 < ρ x → ρ x ≤ T ^ s⁻¹)
    (hsup : ∀ x ∈ S, 0 < ρ x → ∀ i, 𝒯.deg i < γ →
      |f₁ x i - f₂ x i| ≤ C * singularWeight ρ x ^ (η + κ - 𝒯.deg i))
    (hf : M₁.SingularDiffBoundOn M₂ ρ γ (η + κ) C S f₁ f₂) :
    M₁.SingularDiffBoundOn M₂ ρ γ η (T ^ (κ / s) * C) S f₁ f₂ := by
  have h := singularDiffBoundOn_of_vanishing M₁ M₂ hκ hC
    (fun x hx hρ => singularWeight_le_rpow_inv (hS x hx hρ)) hsup hf
  rwa [rpow_inv_rpow_eq hT] at h

end Model

namespace Model

variable {𝒯 : RegularityStructure ι}

/-- **The short-time gain for differences on the time slab** `(0, T] × ℝ³`, `ρ = timeZeroDist`:
constant `T^{κ/2} C`. -/
theorem singularDiffBoundOn_timeSlab {μ : Measure ParabolicSpace}
    {K : RegularisingSemigroup ParabolicSpace μ} (M₁ M₂ : Model 𝒯 K) {γ η κ C T : ℝ}
    {f₁ f₂ : ParabolicSpace → ι → ℝ} (hκ : 0 ≤ κ) (hC : 0 ≤ C) (hT : 0 ≤ T)
    (hsup : ∀ x ∈ timeSlab T, 0 < timeZeroDist x → ∀ i, 𝒯.deg i < γ →
      |f₁ x i - f₂ x i| ≤ C * singularWeight timeZeroDist x ^ (η + κ - 𝒯.deg i))
    (hf : M₁.SingularDiffBoundOn M₂ timeZeroDist γ (η + κ) C (timeSlab T) f₁ f₂) :
    M₁.SingularDiffBoundOn M₂ timeZeroDist γ η (T ^ (κ / 2) * C) (timeSlab T) f₁ f₂ :=
  singularDiffBoundOn_shortTime M₁ M₂ hκ hC hT
    (fun _ hx _ => timeZeroDist_le_rpow_of_mem_timeSlab hx) hsup hf

end Model

end RegularityStructures

end
