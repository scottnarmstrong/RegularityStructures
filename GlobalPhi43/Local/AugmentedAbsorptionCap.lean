/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.DefectBudget

/-! The final Schauder absorption cap is selected before every datum.
The formal-source price and the already-proved defect insertion remain
separate until this scalar composition. -/
public section

namespace GlobalPhi43.Local

 theorem exists_augmented_absorption_cap {K C : ℝ} (hK : 0 < K) (hC : 0 ≤ C) :
    ∃ c₀ > 0, c₀ ≤ 1 ∧ ∃ A > 0, ∀ (M S c : ℝ), 0 ≤ M → 0 ≤ S →
      0 ≤ c → c ≤ c₀ →
      S ≤ K * (C * (M + c * (S + M)) + 4 * c * M) → S ≤ A * M := by
  let c₀ := 1 / (2 * (K * C + 1))
  have hKC : 0 ≤ K * C := mul_nonneg hK.le hC
  have hd : 0 < 2 * (K * C + 1) := by positivity
  have hc₀ : 0 < c₀ := by dsimp [c₀]; positivity
  have hc₀1 : c₀ ≤ 1 := by dsimp [c₀]; apply (div_le_one hd).mpr; linarith
  refine ⟨c₀, hc₀, hc₀1, 2 * K * (2 * C + 4), by positivity, ?_⟩
  intro M S c hM hS hc hcc hbound
  have hc1 : c ≤ 1 := hcc.trans hc₀1
  have hsmall : (K * C) * c ≤ 1 / 2 := by
    have hh := (le_div_iff₀ hd).mp hcc
    nlinarith
  have hcm : c * M ≤ M := mul_le_of_le_one_left hM hc1
  have hp : C * (M + c * (S + M)) + 4 * c * M ≤
      C * c * S + (2 * C + 4) * M := by
    nlinarith only [mul_le_mul_of_nonneg_left hcm hC, hcm]
  have hh := hbound.trans (mul_le_mul_of_nonneg_left hp hK.le)
  have hs := mul_le_mul_of_nonneg_right hsmall hS
  nlinarith only [hh, hs]

end GlobalPhi43.Local
