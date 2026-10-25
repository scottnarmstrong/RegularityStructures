/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Model

/-!
# Singular modelled distributions `D^{γ,η}_P`

[Hai14, Definition 6.2]: modelled distributions that are of class `D^γ` away from a set `P`
(for Φ⁴₃ the time-zero hyperplane) and may blow up at `P` with an exponent `η`. With
`‖x‖_P = 1 ∧ d(x, P)` and `‖x, y‖_P = ‖x‖_P ∧ ‖y‖_P`, the norm `|||f|||_{γ,η}` is the best
constant `C` in

* `|f(x)_ℓ| ≤ C ‖x‖_P^{(η − ℓ) ∧ 0}` for `x ∉ P`, `ℓ < γ`, and
* `|(f(y) − Γ_{yx} f(x))_ℓ| ≤ C d(y, x)^{γ − ℓ} ‖x, y‖_P^{η − γ}` for `x, y ∉ P` with
  `d(y, x) ≤ ‖x, y‖_P`, `ℓ < γ`.

In the abstract setting the distance to `P` is a function `ρ : E → ℝ` and `P = {ρ = 0}` (only `x`
with `0 < ρ x` matter); `singularWeight ρ x = 1 ∧ ρ(x)` is `‖x‖_P`. Hairer's set `K_P` also requires
`x ≠ y`; for `x = y` the increment vanishes (`Γ_{xx} = 1`), so dropping that condition does not
change the space. As for `D^γ` in this formalisation the bounds are global, measurability is part of
the definition, and `f` is required to take values in `T_{<γ}` off `P`.

Main definitions:

* `singularWeight ρ x = ‖x‖_P`;
* `Model.SingularBoundOn M ρ γ η C S f`: the bounds of Definition 6.2 on `S` with constant `C`;
* `Model.singularModelledDistributions M ρ γ η`: the space `D^{γ,η}_P` (global bounds);
* `Model.SingularDiffBoundOn M₁ M₂ ρ γ η C S f g`: the bound `|||f; g|||_{γ,η;S} ≤ C` comparing
  singular modelled distributions for two models.

Source: [Hai14] = arXiv:1303.5113v4, §6, Definition 6.2.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E}

/-- `‖x‖_P = 1 ∧ d(x, P)`, where `ρ x` is the distance from `x` to `P`. -/
def singularWeight (ρ : E → ℝ) (x : E) : ℝ :=
  min 1 (ρ x)

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ}

/-- The bounds of `D^{γ,η}_P` [Hai14, Definition 6.2] on `S` with constant `C`:
`|f(x)_i| ≤ C ‖x‖_P^{(η − deg i) ∧ 0}` for `x ∉ P`, and
`|(f(y) − Γ_{yx} f(x))_j| ≤ C d(y, x)^{γ − deg j} ‖x, y‖_P^{η − γ}` for `x, y ∉ P` with
`d(y, x) ≤ ‖x, y‖_P`, in degrees `< γ`. -/
def SingularBoundOn (M : Model 𝒯 K) (ρ : E → ℝ) (γ η C : ℝ) (S : Set E) (f : E → ι → ℝ) :
    Prop :=
  (∀ x ∈ S, 0 < ρ x → ∀ i, 𝒯.deg i < γ →
      |f x i| ≤ C * singularWeight ρ x ^ min (η - 𝒯.deg i) 0) ∧
    ∀ x ∈ S, ∀ y ∈ S, 0 < ρ x → 0 < ρ y →
      K.scaleDist y x ≤ min (singularWeight ρ x) (singularWeight ρ y) →
      ∀ j, 𝒯.deg j < γ →
        |(f y - M.gammaMap y x (f x)) j| ≤
          C * K.scaleDist y x ^ (γ - 𝒯.deg j) *
            min (singularWeight ρ x) (singularWeight ρ y) ^ (η - γ)

/-- The comparison `|||f; g|||_{γ,η;S} ≤ C` of singular modelled distributions `f` for `M₁`
and `g` for `M₂` [Hai14, Definition 6.2]. -/
def SingularDiffBoundOn (M₁ M₂ : Model 𝒯 K) (ρ : E → ℝ) (γ η C : ℝ) (S : Set E)
    (f g : E → ι → ℝ) : Prop :=
  (∀ x ∈ S, 0 < ρ x → ∀ i, 𝒯.deg i < γ →
      |f x i - g x i| ≤ C * singularWeight ρ x ^ min (η - 𝒯.deg i) 0) ∧
    ∀ x ∈ S, ∀ y ∈ S, 0 < ρ x → 0 < ρ y →
      K.scaleDist y x ≤ min (singularWeight ρ x) (singularWeight ρ y) →
      ∀ j, 𝒯.deg j < γ →
        |(f y - M₁.gammaMap y x (f x)) j - (g y - M₂.gammaMap y x (g x)) j| ≤
          C * K.scaleDist y x ^ (γ - 𝒯.deg j) *
            min (singularWeight ρ x) (singularWeight ρ y) ^ (η - γ)

end Model

end RegularityStructures

end

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E}

omit [MeasurableSpace E] in
theorem singularWeight_le_one (ρ : E → ℝ) (x : E) : singularWeight ρ x ≤ 1 :=
  min_le_left _ _

omit [MeasurableSpace E] in
theorem singularWeight_pos {ρ : E → ℝ} {x : E} (h : 0 < ρ x) : 0 < singularWeight ρ x :=
  lt_min one_pos h

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ} (M : Model 𝒯 K)

theorem SingularBoundOn.mono {ρ : E → ℝ} {γ η C C' : ℝ} {S : Set E} {f : E → ι → ℝ}
    (h : M.SingularBoundOn ρ γ η C S f) (hC : C ≤ C') : M.SingularBoundOn ρ γ η C' S f := by
  refine ⟨fun x hx hρ i hi => (h.1 x hx hρ i hi).trans ?_,
    fun x hx y hy hρx hρy hd j hj => (h.2 x hx y hy hρx hρy hd j hj).trans ?_⟩
  · exact mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (singularWeight_pos hρ).le _)
  · refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC
      (Real.rpow_nonneg (K.scaleDist_nonneg _ _) _)) (Real.rpow_nonneg ?_ _)
    exact (lt_min (singularWeight_pos hρx) (singularWeight_pos hρy)).le

theorem SingularBoundOn.nonneg {ρ : E → ℝ} {γ η C : ℝ} {S : Set E} {f : E → ι → ℝ}
    (h : M.SingularBoundOn ρ γ η C S f) {x : E} (hx : x ∈ S) (hρ : 0 < ρ x) {i : ι}
    (hi : 𝒯.deg i < γ) : 0 ≤ C := by
  have h1 := (abs_nonneg _).trans (h.1 x hx hρ i hi)
  have h3 : 0 < singularWeight ρ x ^ min (η - 𝒯.deg i) 0 :=
    Real.rpow_pos_of_pos (singularWeight_pos hρ) _
  exact nonneg_of_mul_nonneg_left h1 h3

end Model

end RegularityStructures

end
