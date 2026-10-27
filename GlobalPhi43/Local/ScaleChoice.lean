/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic

/-! Uniform large-scale and small-constant selection for the closing estimate. -/
public noncomputable section

namespace GlobalPhi43.Local

open Filter
open scoped Topology BigOperators

/-- Both c-free errors decay with k for every admissible loss. -/
theorem exists_large_scale {κ C : ℝ} (hκ : κ < 1 / 14) :
    ∃ k : ℝ, 2 < k ∧
      C * k ^ (-1 / 2 + 3 * κ) < 1 / 2 ∧
      C * k ^ (-1 / 6 + κ) < 1 / 2 := by
  have ha : 0 < -(-1 / 2 + 3 * κ) := by linarith
  have hb : 0 < -(-1 / 6 + κ) := by linarith
  have hlim₁ : Tendsto (fun k : ℝ => C * k ^ (-1 / 2 + 3 * κ)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop ha).const_mul C
  have hlim₂ : Tendsto (fun k : ℝ => C * k ^ (-1 / 6 + κ)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop hb).const_mul C
  have h₁ := hlim₁.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  have h₂ := hlim₂.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  exact ((eventually_gt_atTop (2 : ℝ)).and (h₁.and h₂)).exists

/-- Once k (hence Q) is fixed, a single positive c makes both cube-root errors small.
The order is essential: Q may depend on k, and c is chosen afterwards. -/
theorem exists_small_constant (C Q : ℝ) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
      C * (c * Q) ^ (1 / 3 : ℝ) < 1 / 2 ∧
      C * c ^ (1 / 3 : ℝ) < 1 / 2 := by
  have hpow : Continuous (fun x : ℝ => x ^ (1 / 3 : ℝ)) :=
    Real.continuous_rpow_const (by norm_num)
  have hlim₁ : Tendsto (fun c : ℝ => C * (c * Q) ^ (1 / 3 : ℝ))
      (𝓝[>] 0) (𝓝 0) := by
    have hcont : ContinuousAt (fun c : ℝ => (c * Q) ^ (1 / 3 : ℝ)) 0 :=
      hpow.continuousAt.comp (continuousAt_id.mul_const Q)
    simpa using (hcont.tendsto.const_mul C).mono_left nhdsWithin_le_nhds
  have hlim₂ : Tendsto (fun c : ℝ => C * c ^ (1 / 3 : ℝ))
      (𝓝[>] 0) (𝓝 0) := by
    simpa using ((hpow.continuousAt (x := (0 : ℝ))).tendsto.const_mul C).mono_left nhdsWithin_le_nhds
  have h₁ := hlim₁.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  have h₂ := hlim₂.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  have hpos : ∀ᶠ c : ℝ in 𝓝[>] 0, 0 < c := self_mem_nhdsWithin
  have hle : ∀ᶠ c : ℝ in 𝓝[>] 0, c ≤ 1 :=
    (eventually_le_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  exact (hpos.and (hle.and (h₁.and h₂))).exists

end GlobalPhi43.Local
