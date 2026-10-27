/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.RadiusGeometry
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! Uniform choices for the two distinct absorptions in the radius-local Schauder estimate. -/
public section

namespace GlobalPhi43.Local

open Filter
open scoped Topology

/-- Choose epsilon before the domain, germ, majorants and all data. The first
inequality absorbs the affine scale term; the second absorbs the sampled
small-past remainder after the fixed 7/8 loss of depth. -/
theorem exists_causal_absorption_parameter {γ : ℝ} (hγ : 0 < γ) (hγ₂ : γ < 2)
    (C₁ C₂ : ℝ) : ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 4 ∧
      C₁ * ε ^ (2 - γ) < 1 / 2 ∧
      C₂ * (ε ^ γ + ε ^ (2 + γ)) * (8 / 7 : ℝ) ^ γ < 1 / 2 := by
  have hheat : Tendsto (fun ε : ℝ => C₁ * ε ^ (2 - γ)) (𝓝[>] 0) (𝓝 0) := by
    have hc := (Real.continuousAt_rpow_const 0 (2 - γ) (.inr (by linarith))).tendsto
    simpa [Real.zero_rpow (by linarith : 2 - γ ≠ 0)] using
      (hc.const_mul C₁).mono_left nhdsWithin_le_nhds
  have hrem : Tendsto (fun ε : ℝ =>
      C₂ * (ε ^ γ + ε ^ (2 + γ)) * (8 / 7 : ℝ) ^ γ) (𝓝[>] 0) (𝓝 0) := by
    have h₁ := (Real.continuousAt_rpow_const 0 γ (.inr hγ.le)).tendsto
    have h₂ := (Real.continuousAt_rpow_const 0 (2 + γ) (.inr (by linarith))).tendsto
    simpa [Real.zero_rpow hγ.ne', Real.zero_rpow (by linarith : 2 + γ ≠ 0)] using
      (((h₁.add h₂).const_mul C₂).mul_const ((8 / 7 : ℝ) ^ γ)).mono_left nhdsWithin_le_nhds
  have hpos : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε := self_mem_nhdsWithin
  have hquarter : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < 1 / 4 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4)).filter_mono nhdsWithin_le_nhds
  exact (hpos.and (hquarter.and
    ((hheat.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).and
      (hrem.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))))).exists

/-- The scale and sampled-remainder absorptions are separate. This scalar
step consumes their actual inequalities and loses only the displayed factor. -/
theorem two_stage_causal_absorption {F Q P a b H : ℝ}
    (hF : 0 ≤ F) (hQ : 0 ≤ Q) (hH : 0 ≤ H)
    (ha : a ≤ 1 / 2) (hbH : b * H ≤ 1 / 4)
    (hscale : F ≤ a * F + P + b * Q) (hembed : Q ≤ H * F) :
    Q ≤ 4 * H * P := by
  have hscale' : F ≤ 2 * P + 2 * b * Q := by
    nlinarith [mul_le_mul_of_nonneg_right ha hF]
  have hbound := mul_le_mul_of_nonneg_left hscale' hH
  have habs := mul_le_mul_of_nonneg_right hbH hQ
  nlinarith

end GlobalPhi43.Local
