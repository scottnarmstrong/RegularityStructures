/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.AffineDyadicStep
public import Mathlib.Analysis.SpecificLimits.Basic

/-! Convergence and quantitative tails of the coefficients selected on
successive past balls. The actual affine approximation errors are consumed. -/
public noncomputable section

namespace GlobalPhi43.Local

open Filter RegularityStructures
open scoped Topology

/-- Affine approximants at the dyadic radii have a single spatial coefficient
limit when gamma>1. This derives the geometric increment from approximation
errors; it does not assume the increment as an additional analytic input. -/
theorem affine_coefficient_limit (f : ParabolicSpace → ℝ) (x : ParabolicSpace)
    (c : ℕ → ℝ) (ν : ℕ → Fin 3 → ℝ) {R γ H : ℝ} (hR : 0 < R) (hγ : 1 < γ)
    (happrox : ∀ n, ∀ y ∈ pastBall x (R * (1 / 2 : ℝ) ^ n),
      |f y - spatialAffine x (c n) (ν n) y| ≤ H * (R * (1 / 2 : ℝ) ^ n) ^ γ) :
    ∃ a : Fin 3 → ℝ, Tendsto ν atTop (𝓝 a) ∧ ∀ n,
      ‖ν n - a‖ ≤
        (8 * H * (1 + (1 / 2 : ℝ) ^ γ) * R ^ (γ - 1)) *
          ((1 / 2 : ℝ) ^ (γ - 1)) ^ n / (1 - (1 / 2 : ℝ) ^ (γ - 1)) := by
  let C := 8 * H * (1 + (1 / 2 : ℝ) ^ γ) * R ^ (γ - 1)
  let q := (1 / 2 : ℝ) ^ (γ - 1)
  have hq : q < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) (by linarith)
  have hstep (n : ℕ) : dist (ν n) (ν (n + 1)) ≤ C * q ^ n := by
    rw [dist_eq_norm]
    have hRn : 0 < R * (1 / 2 : ℝ) ^ n := by positivity
    have hradius : R * (1 / 2 : ℝ) ^ (n + 1) = (R * (1 / 2 : ℝ) ^ n) / 2 := by
      rw [pow_succ]; ring
    have hb := affine_dyadic_step f x (c n) (c (n + 1)) (ν n) (ν (n + 1)) hRn
      (happrox n) (by simpa only [hradius] using happrox (n + 1))
    calc
      _ ≤ 8 * H * (1 + (1 / 2 : ℝ) ^ γ) * (R * (1 / 2 : ℝ) ^ n) ^ (γ - 1) := hb
      _ = C * q ^ n := by
        rw [Real.mul_rpow hR.le (by positivity), ← Real.rpow_pow_comm (by norm_num)]
        dsimp [C, q]
        ring
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric q C hq hstep)
  refine ⟨a, ha, fun n => ?_⟩
  simpa only [dist_eq_norm] using dist_le_of_le_geometric_of_tendsto q C hq hstep ha n

end GlobalPhi43.Local
