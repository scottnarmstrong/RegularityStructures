/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.LocalSupIteration

/-! A single data radius supplies all nine tree powers and three defect
powers in the paid finite iteration, without separate norm finiteness. -/
public noncomputable section

namespace GlobalPhi43.Local

open MW20

 theorem uniform_power_root_le {H p : ℝ} (hH : 0 ≤ H) (hp : 0 < p) :
    (H ^ p) ^ p⁻¹ ≤ H :=
  (Real.rpow_inv_le_iff_of_pos (Real.rpow_nonneg hH _) hH hp).mpr le_rfl

 theorem uniform_defect_scale_le {H : ℝ} (hH : 0 ≤ H) : defectScale (H ^ 3) (H ^ 2) (H ^ 3) ≤ H := by
  have h₃ : (H ^ 3) ^ (1 / 3 : ℝ) ≤ H := by
    simpa only [Real.rpow_ofNat, one_div] using uniform_power_root_le hH (by norm_num : (0 : ℝ) < 3)
  have h₂ : (H ^ 2) ^ (1 / 2 : ℝ) ≤ H := by
    simpa only [Real.rpow_ofNat, one_div] using uniform_power_root_le hH (by norm_num : (0 : ℝ) < 2)
  exact max_le h₃ (max_le h₂ h₃)

 theorem uniform_tree_scale_le {H κ : ℝ} (hH : 0 ≤ H) (hκ : κ < 1 / 2) :
    nineTreeScale κ (fun τ => H ^ τ.degree κ) ≤ H := by
  unfold nineTreeScale treeRadiusMajorant
  apply Finset.sup'_le
  intro τ _
  simp only [div_one]
  exact uniform_power_root_le hH (τ.degree_pos hκ)

 theorem uniform_augmented_data_scale_le {H κ : ℝ} (hH : 0 ≤ H) (hκ : κ < 1 / 2) :
    max (nineTreeScale κ (fun τ => H ^ τ.degree κ)) (defectScale (H ^ 3) (H ^ 2) (H ^ 3)) ≤ H :=
  max_le (uniform_tree_scale_le hH hκ) (uniform_defect_scale_le hH)

end GlobalPhi43.Local
