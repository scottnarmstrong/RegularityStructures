/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.AffineProbeComparison

/-! The coefficient increment in the causal affine selection argument. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures

/-- Approximation at R and R/2 controls the coefficient difference at order
R^(gamma-1), using two probes strictly inside the common past ball. -/
theorem affine_dyadic_step (f : ParabolicSpace → ℝ) (x : ParabolicSpace)
    (c₁ c₂ : ℝ) (ν₁ ν₂ : Fin 3 → ℝ) {R γ H : ℝ} (hR : 0 < R)
    (h₁ : ∀ y ∈ pastBall x R, |f y - spatialAffine x c₁ ν₁ y| ≤ H * R ^ γ)
    (h₂ : ∀ y ∈ pastBall x (R / 2),
      |f y - spatialAffine x c₂ ν₂ y| ≤ H * (R / 2) ^ γ) :
    ‖ν₁ - ν₂‖ ≤ 8 * H * (1 + (1 / 2 : ℝ) ^ γ) * R ^ (γ - 1) := by
  have heq : 2 * (H * R ^ γ + H * (R / 2) ^ γ) / (R / 4) =
      8 * H * (1 + (1 / 2 : ℝ) ^ γ) * R ^ (γ - 1) := by
    have hmul : R / 2 = R * (1 / 2) := by ring
    rw [hmul, Real.mul_rpow hR.le (by norm_num), Real.rpow_sub_one hR.ne']
    field_simp
    ring
  rw [← heq]
  apply (pi_norm_le_iff_of_nonempty (ν₁ - ν₂)).2
  intro i
  simpa only [Pi.sub_apply, Real.norm_eq_abs] using
    affine_coefficients_compare f x c₁ c₂ ν₁ ν₂ (by linarith : 0 < R / 4)
      (by linarith : R / 4 < R / 2)
      (fun y hy => h₁ y ⟨by linarith [hy.1], hy.2⟩) h₂ i

end GlobalPhi43.Local
