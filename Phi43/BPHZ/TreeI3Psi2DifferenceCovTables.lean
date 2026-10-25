/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2DifferenceTables

/-!
# Pointwise consequences of the bound data of the cross covariance tables

If `I3Psi2TablesBd A μ θ Q₁₁ Q₁₂ Q₂₁ Q₂₂` then each of the four covariances is bounded by
`4 A s(x)⁻¹` and `|Q₁₁ - Q₂₂| ≤ 4 A μ s(x)^(-(1+θ))`.
-/

public section

namespace RegularityStructures.Phi43

open RegularityStructures

/-- Each entry of the table is bounded by four times the bound on the Walsh coordinates. -/
theorem I3Psi2TablesBd.abs_entries_le {A μ θ : ℝ} {Q₁₁ Q₁₂ Q₂₁ Q₂₂ : SpaceTime → ℝ}
    (h : I3Psi2TablesBd A μ θ Q₁₁ Q₁₂ Q₂₁ Q₂₂) {x : SpaceTime} (hx : 0 < torusParabolicSize x) :
    |Q₁₁ x| ≤ 4 * (A * torusParabolicSize x ^ (-(1 : ℝ))) ∧
    |Q₁₂ x| ≤ 4 * (A * torusParabolicSize x ^ (-(1 : ℝ))) ∧
    |Q₂₁ x| ≤ 4 * (A * torusParabolicSize x ^ (-(1 : ℝ))) ∧
    |Q₂₂ x| ≤ 4 * (A * torusParabolicSize x ^ (-(1 : ℝ))) := by
  obtain ⟨⟨hm, hu, hv, hw, -, -, -⟩, -, -⟩ := h x hx
  simp only [I3PsiDiffTable.mean, I3PsiDiffTable.du, I3PsiDiffTable.dv, I3PsiDiffTable.dw] at hm hu hv hw
  set P := A * torusParabolicSize x ^ (-(1 : ℝ))
  rw [abs_le] at hm hu hv hw
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [abs_le] <;> constructor <;> linarith

/-- `|Q₁₁ - Q₂₂| ≤ 4 A μ s^(-(1+θ))`. -/
theorem I3Psi2TablesBd.abs_diag_sub_le {A μ θ : ℝ} {Q₁₁ Q₁₂ Q₂₁ Q₂₂ : SpaceTime → ℝ}
    (h : I3Psi2TablesBd A μ θ Q₁₁ Q₁₂ Q₂₁ Q₂₂) {x : SpaceTime} (hx : 0 < torusParabolicSize x) :
    |Q₁₁ x - Q₂₂ x| ≤ (4 * A) * μ * torusParabolicSize x ^ (-(1 + θ)) := by
  obtain ⟨⟨-, -, -, -, hu, hv, -⟩, -, -⟩ := h x hx
  simp only [I3PsiDiffTable.du, I3PsiDiffTable.dv] at hu hv
  have e : torusParabolicSize x ^ (-(1 + θ)) =
      torusParabolicSize x ^ (-(1 : ℝ)) * torusParabolicSize x ^ (-θ) := by
    rw [← Real.rpow_add hx]; congr 1; ring
  rw [e]
  set P := A * torusParabolicSize x ^ (-(1 : ℝ))
  set q := torusParabolicSize x ^ (-θ)
  rw [abs_le] at hu hv ⊢
  have : (4 * A) * μ * (torusParabolicSize x ^ (-(1 : ℝ)) * q) = 4 * (μ * P * q) := by
    simp only [P]; ring
  rw [this]
  constructor <;> linarith [hu.1, hu.2, hv.1, hv.2]

end RegularityStructures.Phi43

end
