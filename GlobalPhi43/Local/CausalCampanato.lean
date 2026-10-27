/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.AffineIdentification
public import GlobalPhi43.Local.AffineRemainderApprox

/-! The causal Campanato embedding from actual affine approximation errors.
The caloric/PDE estimate furnishing those errors remains a separate step. -/
public noncomputable section

namespace GlobalPhi43.Local

open Filter RegularityStructures
open scoped Topology

/-- A single coefficient controls all dyadic past balls. The constant depends
only on gamma and the incoming affine approximation budget H. -/
theorem causal_campanato_dyadic (f : ParabolicSpace → ℝ) (x : ParabolicSpace)
    (c : ℕ → ℝ) (ν : ℕ → Fin 3 → ℝ) {R γ H : ℝ}
    (hR : 0 < R) (hγ : 1 < γ) (hf : ContinuousAt f x) (hzero : f x = 0)
    (happrox : ∀ n, ∀ y ∈ pastBall x (R * (1 / 2 : ℝ) ^ n),
      |f y - spatialAffine x (c n) (ν n) y| ≤ H * (R * (1 / 2 : ℝ) ^ n) ^ γ) :
    ∃ a : Fin 3 → ℝ, Tendsto ν atTop (𝓝 a) ∧ ∀ n,
      ∀ y ∈ pastBall x (R * (1 / 2 : ℝ) ^ n),
        |f y - spatialLinear a (y - x)| ≤
          (2 * H + 24 * H * (1 + (1 / 2 : ℝ) ^ γ) /
            (1 - (1 / 2 : ℝ) ^ (γ - 1))) * (R * (1 / 2 : ℝ) ^ n) ^ γ := by
  obtain ⟨a, ha, htail⟩ := affine_coefficient_limit f x c ν hR hγ happrox
  refine ⟨a, ha, fun n y hy => ?_⟩
  have hρ : 0 < R * (1 / 2 : ℝ) ^ n := by positivity
  let K := 8 * H * (1 + (1 / 2 : ℝ) ^ γ) / (1 - (1 / 2 : ℝ) ^ (γ - 1))
  have heq : (8 * H * (1 + (1 / 2 : ℝ) ^ γ) * R ^ (γ - 1)) *
      ((1 / 2 : ℝ) ^ (γ - 1)) ^ n / (1 - (1 / 2 : ℝ) ^ (γ - 1)) =
      K * (R * (1 / 2 : ℝ) ^ n) ^ (γ - 1) := by
    rw [Real.mul_rpow hR.le (by positivity), ← Real.rpow_pow_comm (by norm_num)]
    dsimp [K]
    ring
  have ht : ‖ν n - a‖ ≤ K * (R * (1 / 2 : ℝ) ^ n) ^ (γ - 1) := by
    simpa only [heq] using htail n
  have hb := remainder_of_affine_approximation f x (c n) (ν n) a hρ hf hzero (happrox n) ht hy
  calc
    _ ≤ 2 * (H * (R * (1 / 2 : ℝ) ^ n) ^ γ) +
        3 * (K * (R * (1 / 2 : ℝ) ^ n) ^ (γ - 1)) * (R * (1 / 2 : ℝ) ^ n) := hb
    _ = _ := by
      rw [Real.rpow_sub_one hρ.ne']
      dsimp [K]
      field_simp
      ring

/-- In the smooth setting the common coefficient is the spatial derivative;
no extra derivative norm appears in the remainder estimate. -/
theorem causal_campanato_derivative (f : ParabolicSpace → ℝ) (x : ParabolicSpace)
    (D : ParabolicSpace →L[ℝ] ℝ) (hf : HasFDerivAt f D x) (hzero : f x = 0)
    (c : ℕ → ℝ) (ν : ℕ → Fin 3 → ℝ) {R γ H : ℝ} (hR : 0 < R) (hγ : 1 < γ)
    (happrox : ∀ n, ∀ y ∈ pastBall x (R * (1 / 2 : ℝ) ^ n),
      |f y - spatialAffine x (c n) (ν n) y| ≤ H * (R * (1 / 2 : ℝ) ^ n) ^ γ) :
    ∀ n, ∀ y ∈ pastBall x (R * (1 / 2 : ℝ) ^ n),
      |f y - spatialLinear (fun i => D (0, Pi.single i 1)) (y - x)| ≤
        (2 * H + 24 * H * (1 + (1 / 2 : ℝ) ^ γ) /
          (1 - (1 / 2 : ℝ) ^ (γ - 1))) * (R * (1 / 2 : ℝ) ^ n) ^ γ := by
  obtain ⟨a, ha, hb⟩ := causal_campanato_dyadic f x c ν hR hγ hf.continuousAt hzero happrox
  rw [affine_limit_eq_spatial_derivative f x D hf c ν a hR hγ happrox ha] at hb
  exact hb

end GlobalPhi43.Local
