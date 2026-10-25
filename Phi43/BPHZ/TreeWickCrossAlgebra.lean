/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Second differences of powers of the cross covariances

With `a = Q_{εε}`, `b = Q_{εε'}`, `c = Q_{ε'ε}`, `d = Q_{ε'ε'}` and
`σ = a + b + c + d`, `r = a - b - c + d`, `e₁ = a + b - c - d`, `e₂ = a - b + c - d` one has the
exact identities
`a² - b² - c² + d² = (r σ + e₁ e₂) / 2` and
`a³ - b³ - c³ + d³ = (3 (e₁² r + e₂² r + 2 e₁ e₂ σ + σ² r) + r³) / 16`.
Since `|σ|, |r|, |eᵢ| ≲ s⁻¹`, `|r| ≲ (max ε ε')^(2θ) s^(-1-2θ)` and
`|eᵢ| ≲ (max ε ε')^θ s^(-1-θ)`, this gives `(max ε ε')^(2θ)` smallness of both second differences
with the full singularity `s⁻²` (respectively `s⁻³`) of the undifferenced quantity, up to `s^(-2θ)`.
-/

public section

namespace RegularityStructures.Phi43

open RegularityStructures

private theorem abs_mul3_le {x y z u v w : ℝ} (hx : |x| ≤ u) (hy : |y| ≤ v) (hz : |z| ≤ w)
    (hv : 0 ≤ v) : |x * y * z| ≤ u * v * w := by
  rw [abs_mul, abs_mul]
  have hu : 0 ≤ u := (abs_nonneg _).trans hx
  exact mul_le_mul (mul_le_mul hx hy (abs_nonneg _) hu) hz (abs_nonneg _) (by positivity)

private theorem abs_add4_le (x y z w : ℝ) : |x + y + z + w| ≤ |x| + |y| + |z| + |w| := by
  calc |x + y + z + w| ≤ |x + y + z| + |w| := abs_add_le _ _
    _ ≤ |x + y| + |z| + |w| := add_le_add (abs_add_le _ _) le_rfl
    _ ≤ |x| + |y| + |z| + |w| := add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl

theorem treeWick_alg_sq {σ r e₁ e₂ A μ p q : ℝ} (hA : 0 ≤ A) (hμ : 0 ≤ μ) (hp : 0 ≤ p)
    (hq : 0 ≤ q) (hσ : |σ| ≤ A * p) (hr : |r| ≤ A * (μ ^ 2 * p * q ^ 2))
    (h₁ : |e₁| ≤ A * (μ * p * q)) (h₂ : |e₂| ≤ A * (μ * p * q)) :
    |(r * σ + e₁ * e₂) / 2| ≤ A ^ 2 * (μ ^ 2 * p ^ 2 * q ^ 2) := by
  have t1 : |r * σ| ≤ A * (μ ^ 2 * p * q ^ 2) * (A * p) := by
    rw [abs_mul]
    exact mul_le_mul hr hσ (abs_nonneg _) (by positivity)
  have t2 : |e₁ * e₂| ≤ A * (μ * p * q) * (A * (μ * p * q)) := by
    rw [abs_mul]
    exact mul_le_mul h₁ h₂ (abs_nonneg _) (by positivity)
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2), div_le_iff₀ (by norm_num)]
  calc |r * σ + e₁ * e₂| ≤ |r * σ| + |e₁ * e₂| := abs_add_le _ _
    _ ≤ _ := add_le_add t1 t2
    _ = _ := by ring

theorem treeWick_alg_cube {σ r e₁ e₂ A μ p q : ℝ} (hA : 0 ≤ A) (hμ : 0 ≤ μ) (hp : 0 ≤ p)
    (hq : 0 ≤ q) (hσ : |σ| ≤ A * p) (hr₁ : |r| ≤ A * p) (hr : |r| ≤ A * (μ ^ 2 * p * q ^ 2))
    (h₁ : |e₁| ≤ A * p) (h₂ : |e₂| ≤ A * p) (h₁' : |e₁| ≤ A * (μ * p * q))
    (h₂' : |e₂| ≤ A * (μ * p * q)) :
    |(3 * (e₁ ^ 2 * r + e₂ ^ 2 * r + 2 * (e₁ * e₂ * σ) + σ ^ 2 * r) + r ^ 3) / 16| ≤
      A ^ 3 * (μ ^ 2 * p ^ 3 * q ^ 2) := by
  have hAp : 0 ≤ A * p := by positivity
  have hmain : 0 ≤ A * (μ ^ 2 * p * q ^ 2) := by positivity
  have hsq : ∀ {x : ℝ}, |x| ≤ A * p → |x ^ 2| ≤ (A * p) * (A * p) := fun {x} h => by
    rw [abs_pow, sq]
    exact mul_le_mul h h (abs_nonneg _) hAp
  have t1 : |e₁ ^ 2 * r| ≤ (A * p) * (A * p) * (A * (μ ^ 2 * p * q ^ 2)) := by
    rw [abs_mul]
    exact mul_le_mul (hsq h₁) hr (abs_nonneg _) (by positivity)
  have t2 : |e₂ ^ 2 * r| ≤ (A * p) * (A * p) * (A * (μ ^ 2 * p * q ^ 2)) := by
    rw [abs_mul]
    exact mul_le_mul (hsq h₂) hr (abs_nonneg _) (by positivity)
  have t3 : |e₁ * e₂ * σ| ≤ (A * (μ * p * q)) * (A * (μ * p * q)) * (A * p) :=
    abs_mul3_le h₁' h₂' hσ (by positivity)
  have t4 : |σ ^ 2 * r| ≤ (A * p) * (A * p) * (A * (μ ^ 2 * p * q ^ 2)) := by
    rw [abs_mul]
    exact mul_le_mul (hsq (hσ)) hr (abs_nonneg _) (by positivity)
  have t5 : |r ^ 3| ≤ (A * p) * (A * p) * (A * (μ ^ 2 * p * q ^ 2)) := by
    rw [abs_pow, pow_succ, pow_two]
    exact mul_le_mul (mul_le_mul hr₁ hr₁ (abs_nonneg _) hAp) hr (abs_nonneg _) (by positivity)
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 16), div_le_iff₀ (by norm_num)]
  calc |3 * (e₁ ^ 2 * r + e₂ ^ 2 * r + 2 * (e₁ * e₂ * σ) + σ ^ 2 * r) + r ^ 3|
      ≤ 3 * (|e₁ ^ 2 * r| + |e₂ ^ 2 * r| + 2 * |e₁ * e₂ * σ| + |σ ^ 2 * r|) + |r ^ 3| := by
        refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        refine (abs_add4_le _ _ _ _).trans (le_of_eq ?_)
        rw [abs_mul (2 : ℝ), abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ 3 * ((A * p) * (A * p) * (A * (μ ^ 2 * p * q ^ 2)) +
          (A * p) * (A * p) * (A * (μ ^ 2 * p * q ^ 2)) +
          2 * ((A * (μ * p * q)) * (A * (μ * p * q)) * (A * p)) +
          (A * p) * (A * p) * (A * (μ ^ 2 * p * q ^ 2))) +
          (A * p) * (A * p) * (A * (μ ^ 2 * p * q ^ 2)) := by
        gcongr
    _ = _ := by ring

end RegularityStructures.Phi43

end
