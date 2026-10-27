/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.RadiusGeometry
public import Mathlib.Algebra.Order.Archimedean.Basic

/-! A strictly larger dyadic radius for every nonzero tested distance. -/
public section

namespace GlobalPhi43.Local

theorem exists_dyadic_radius {R ρ : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) :
    ∃ n : ℕ, ρ < R * (1 / 2 : ℝ) ^ n ∧ R * (1 / 2 : ℝ) ^ n ≤ 4 * ρ := by
  have hR : 0 < R := hρ.trans hρR
  by_cases hsmall : ρ < R / 2
  · have hx : 0 < 2 * ρ / R := by positivity
    have hx₁ : 2 * ρ / R ≤ 1 := (div_le_one hR).2 (by linarith)
    obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near_of_lt_one hx hx₁
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    have hl : 2 * ρ ≤ R * (1 / 2 : ℝ) ^ n := by
      have h := (div_le_iff₀ hR).mp hn'
      nlinarith
    have hu : R * (1 / 2 : ℝ) ^ n < 4 * ρ := by
      have h := (lt_div_iff₀ hR).mp hn
      rw [pow_succ] at h
      nlinarith
    exact ⟨n, by linarith, hu.le⟩
  · exact ⟨0, by simpa using hρR, by simp; linarith⟩

end GlobalPhi43.Local
