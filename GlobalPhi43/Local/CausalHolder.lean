/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.CausalCampanato
public import GlobalPhi43.Local.DyadicRadius

/-! The causal Holder conclusion of the affine Campanato embedding. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures

/-- The same spatial derivative controls every nonzero past pair below R,
with a constant depending only on gamma and the affine approximation budget.
The PDE/caloric proof of that budget is not assumed proved here. -/
theorem causal_campanato_holder (f : ParabolicSpace → ℝ) (x : ParabolicSpace)
    (D : ParabolicSpace →L[ℝ] ℝ) (hf : HasFDerivAt f D x) (hzero : f x = 0)
    (c : ℕ → ℝ) (ν : ℕ → Fin 3 → ℝ) {R γ H : ℝ}
    (hR : 0 < R) (hγ : 1 < γ) (hH : 0 ≤ H)
    (happrox : ∀ n, ∀ y ∈ pastBall x (R * (1 / 2 : ℝ) ^ n),
      |f y - spatialAffine x (c n) (ν n) y| ≤ H * (R * (1 / 2 : ℝ) ^ n) ^ γ)
    {y : ParabolicSpace} (hy : y ∈ pastBall x R) (hρ : 0 < pdist x y) :
    |f y - spatialLinear (fun i => D (0, Pi.single i 1)) (y - x)| ≤
      ((4 : ℝ) ^ γ * (2 * H + 24 * H * (1 + (1 / 2 : ℝ) ^ γ) /
        (1 - (1 / 2 : ℝ) ^ (γ - 1)))) * pdist x y ^ γ := by
  obtain ⟨n, hn, hn'⟩ := exists_dyadic_radius hρ hy.1
  have hb := causal_campanato_derivative f x D hf hzero c ν hR hγ happrox n y ⟨hn, hy.2⟩
  have hden : 0 < 1 - (1 / 2 : ℝ) ^ (γ - 1) := by
    have h := Real.rpow_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) (by linarith : 0 < γ - 1)
    linarith
  have hC : 0 ≤ 2 * H + 24 * H * (1 + (1 / 2 : ℝ) ^ γ) /
      (1 - (1 / 2 : ℝ) ^ (γ - 1)) := by positivity
  calc
    _ ≤ (2 * H + 24 * H * (1 + (1 / 2 : ℝ) ^ γ) /
        (1 - (1 / 2 : ℝ) ^ (γ - 1))) * (4 * pdist x y) ^ γ :=
      hb.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) hn' (by linarith)) hC)
    _ = _ := by rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hρ.le]; ring

end GlobalPhi43.Local
