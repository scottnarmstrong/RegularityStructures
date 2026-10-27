/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.PastAffineError

/-! Causal Campanato embedding from the actual affine infima, retaining the
original allowance even at zero. -/
@[expose] public noncomputable section

namespace GlobalPhi43.Local

open Filter RegularityStructures
open scoped Topology

def campanatoFactor (γ : ℝ) : ℝ :=
  (4 : ℝ) ^ γ * (2 + 24 * (1 + (1 / 2 : ℝ) ^ γ) / (1 - (1 / 2 : ℝ) ^ (γ - 1)))

/-- Infimum-based approximation bounds imply the causal Holder estimate
with exactly H, by choosing near-minimizers and letting their allowance vanish. -/
theorem causal_holder_of_affine_error (f : ParabolicSpace → ℝ) (x : ParabolicSpace)
    (D : ParabolicSpace →L[ℝ] ℝ) (hf : HasFDerivAt f D x) (hzero : f x = 0)
    {R γ H : ℝ} (hR : 0 < R) (hγ : 1 < γ) (hH : 0 ≤ H)
    (herror : ∀ n, pastAffineError f x (R * (1 / 2 : ℝ) ^ n) ≤
      ENNReal.ofReal (H * (R * (1 / 2 : ℝ) ^ n) ^ γ))
    {y : ParabolicSpace} (hy : y ∈ pastBall x R) (hρ : 0 < pdist x y) :
    |f y - spatialLinear (fun i => D (0, Pi.single i 1)) (y - x)| ≤
      (campanatoFactor γ * H) * pdist x y ^ γ := by
  have hδ (δ : ℝ) (hδ : 0 < δ) :
      |f y - spatialLinear (fun i => D (0, Pi.single i 1)) (y - x)| ≤
        (campanatoFactor γ * (H + δ)) * pdist x y ^ γ := by
    have hchoices (n : ℕ) := exists_past_affine_approximation f x
      (by positivity : 0 < R * (1 / 2 : ℝ) ^ n) hH hδ (herror n)
    choose c ν hc using hchoices
    have hh := causal_campanato_holder f x D hf hzero c ν hR hγ (by linarith : 0 ≤ H + δ) hc hy hρ
    convert hh using 1; unfold campanatoFactor; ring
  have hlim : Tendsto (fun δ : ℝ => (campanatoFactor γ * (H + δ)) * pdist x y ^ γ)
      (𝓝[>] 0) (𝓝 ((campanatoFactor γ * H) * pdist x y ^ γ)) := by
    have hc : ContinuousAt (fun δ : ℝ => (campanatoFactor γ * (H + δ)) * pdist x y ^ γ) 0 := by fun_prop
    simpa only [add_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  filter_upwards [self_mem_nhdsWithin] with δ hpos
  exact hδ δ hpos

end GlobalPhi43.Local
