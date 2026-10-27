/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.AffineCoefficientLimit
public import GlobalPhi43.Local.AffineSlopeError
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! The limiting coefficient of the past-ball approximants is the spatial
derivative of the smooth section. Intercepts cancel, so no centre value or
bound on derivatives enters the approximation budget. -/
public noncomputable section

namespace GlobalPhi43.Local

open Filter RegularityStructures
open scoped Topology

/-- Identification from the actual affine approximation errors and local
Fréchet differentiability. Only the spatial derivative survives the probes. -/
theorem affine_limit_eq_spatial_derivative
    (f : ParabolicSpace → ℝ) (x : ParabolicSpace)
    (D : ParabolicSpace →L[ℝ] ℝ) (hf : HasFDerivAt f D x)
    (c : ℕ → ℝ) (ν : ℕ → Fin 3 → ℝ) (a : Fin 3 → ℝ)
    {R γ H : ℝ} (hR : 0 < R) (hγ : 1 < γ)
    (happrox : ∀ n, ∀ y ∈ pastBall x (R * (1 / 2 : ℝ) ^ n),
      |f y - spatialAffine x (c n) (ν n) y| ≤ H * (R * (1 / 2 : ℝ) ^ n) ^ γ)
    (ha : Tendsto ν atTop (𝓝 a)) :
    a = fun i => D (0, Pi.single i 1) := by
  let ρ : ℕ → ℝ := fun n => R * (1 / 2 : ℝ) ^ n
  have hρpos (n : ℕ) : 0 < ρ n := by dsimp [ρ]; positivity
  have hρ : Tendsto ρ atTop (𝓝 0) := by
    simpa [ρ] using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).const_mul R
  have hs : Tendsto (fun n => ρ n / 4) atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨by simpa using hρ.div_const 4, Eventually.of_forall fun n => by
      change 0 < ρ n / 4; positivity⟩
  have hpow : Tendsto (fun n => 8 * H * (ρ n) ^ (γ - 1)) atTop (𝓝 0) := by
    have hc := (Real.continuousAt_rpow_const 0 (γ - 1) (.inr (by linarith))).tendsto.comp hρ
    simpa [Real.zero_rpow (by linarith : γ - 1 ≠ 0)] using hc.const_mul (8 * H)
  funext i
  let g : ℕ → ℝ := fun n =>
    (f (coefficientProbe x (ρ n / 4) i) - f (verticalProbe x (ρ n / 4))) / (ρ n / 4)
  have hg : Tendsto g atTop (𝓝 (D (0, Pi.single i 1))) := (probe_slope_tendsto f x D hf i).comp hs
  have herr : Tendsto (fun n => dist (g n) (ν n i)) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => dist_nonneg) _ hpow
    intro n
    simpa only [Real.dist_eq, g, ρ] using
      affine_probe_slope_error f x (c n) (ν n) (hρpos n) (happrox n) i
  have hν : Tendsto (fun n => ν n i) atTop (𝓝 (D (0, Pi.single i 1))) := hg.congr_dist herr
  exact tendsto_nhds_unique ((continuous_apply i).tendsto a |>.comp ha) hν

end GlobalPhi43.Local
