/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.DefectStopping

/-! The literal defect part of K_data and its stopping attachment. -/
public noncomputable section

namespace GlobalPhi43.Local

/-- The three amplitudes in the local theorem: cube, square, cube. -/
@[expose] def defectScale (E₁ E₂ E₃ : ℝ) : ℝ :=
  max (E₁ ^ (1 / 3 : ℝ)) (max (E₂ ^ (1 / 2 : ℝ)) (E₃ ^ (1 / 3 : ℝ)))

theorem defectScale_nonneg {E₁ E₂ E₃ : ℝ} (h₁ : 0 ≤ E₁) :
    0 ≤ defectScale E₁ E₂ E₃ :=
  (Real.rpow_nonneg h₁ _).trans (le_max_left _ _)

/-- Taking the finite maximum supplies exactly the three amplitude bounds. -/
theorem defectScale_powers {E₁ E₂ E₃ : ℝ}
    (h₁ : 0 ≤ E₁) (h₂ : 0 ≤ E₂) (h₃ : 0 ≤ E₃) :
    E₁ ≤ defectScale E₁ E₂ E₃ ^ 3 ∧
      E₂ ≤ defectScale E₁ E₂ E₃ ^ 2 ∧ E₃ ≤ defectScale E₁ E₂ E₃ ^ 3 := by
  have hK := defectScale_nonneg (E₂ := E₂) (E₃ := E₃) h₁
  have hc (E : ℝ) (hE : 0 ≤ E)
      (hr : E ^ (1 / 3 : ℝ) ≤ defectScale E₁ E₂ E₃) :
      E ≤ defectScale E₁ E₂ E₃ ^ 3 := by
    have h := (Real.rpow_inv_le_iff_of_pos hE hK (by norm_num : (0 : ℝ) < 3)).mp
      (by simpa only [one_div] using hr)
    simpa only [Real.rpow_ofNat] using h
  refine ⟨hc E₁ h₁ (le_max_left _ _), ?_, hc E₃ h₃ ?_⟩
  · have hr : E₂ ^ (1 / 2 : ℝ) ≤ defectScale E₁ E₂ E₃ :=
      (le_max_left _ _).trans (le_max_right _ _)
    have h := (Real.rpow_inv_le_iff_of_pos h₂ hK (by norm_num : (0 : ℝ) < 2)).mp
      (by simpa only [one_div] using hr)
    simpa only [Real.rpow_ofNat] using h
  · exact (le_max_right _ _).trans (le_max_right _ _)

/-- The augmented stopping bound with the displayed defect roots, rather than
an independently supplied data majorant. The same c is retained. -/
theorem mass_bound_of_defect_scale_failure {c M E₁ E₂ E₃ : ℝ}
    (hc : 0 < c) (hc₁ : c ≤ 1) (hM : 0 ≤ M)
    (h₁ : 0 ≤ E₁) (h₂ : 0 ≤ E₂) (h₃ : 0 ≤ E₃)
    (hfail : ¬ DefectSmall c M E₁ E₂ E₃) :
    M ≤ (2 / c) * defectScale E₁ E₂ E₃ := by
  obtain ⟨hK₁, hK₂, hK₃⟩ := defectScale_powers h₁ h₂ h₃
  exact mass_bound_of_defect_not_small hc hc₁ hM (defectScale_nonneg h₁)
    hK₁ hK₂ hK₃ hfail

end GlobalPhi43.Local
