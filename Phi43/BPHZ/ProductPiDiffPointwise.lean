/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3PsiCrossTables
public import Phi43.BPHZ.TreeI3PsiCrossPointwise

/-!
# Pointwise bounds for the second differences of the block kernel of `I(Ψ²)Ψ`

With `C₁₁, C₁₂, C₂₁, C₂₂` the cross covariances `Q_{ρε,ρε}, Q_{ρε,ρ'ε'}, Q_{ρ'ε',ρε}, Q_{ρ'ε',ρ'ε'}`,
the second difference of `isqBlockKernel` over the scales `(e₁, e₂)` splits into
* `E₁(x₁, x₂) = Δ²[Q_{e₁e₂}(x₁)² Q_{e₁e₂}(x₂)]`,
* `E₂(x₁, x₂, x₃) = Δ²[Q_{e₁e₂}(x₁) Q_{e₁e₂}(x₂) Q_{e₁e₂}(x₃)]`,
* `E₃(x₁, x₂, x₃) = Δ²[Q_{e₁e₁}(x₁) Q_{e₁e₂}(x₂) Q_{e₂e₂}(x₃)]`,
each bounded by `K (max ε ε')^(2θ)` times the sum of products of powers in which exactly one
exponent is raised by `2θ` (`isqDiffE1_abs_le`, `isqDiffE2_abs_le`, `isqDiffE3_abs_le`).
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

open RegularityStructures

variable (N : ℕ) (ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ)

/-- `Δ²[Q_{e₁e₂}(x₁)² Q_{e₁e₂}(x₂)]`. -/
def isqDiffE1 (ε ε' : ℝ) (x₁ x₂ : SpaceTime) : ℝ :=
  hairerCrossCovarianceTwo N ρ ε ρ ε x₁ ^ 2 * hairerCrossCovarianceTwo N ρ ε ρ ε x₂ -
    hairerCrossCovarianceTwo N ρ ε ρ' ε' x₁ ^ 2 * hairerCrossCovarianceTwo N ρ ε ρ' ε' x₂ -
    hairerCrossCovarianceTwo N ρ' ε' ρ ε x₁ ^ 2 * hairerCrossCovarianceTwo N ρ' ε' ρ ε x₂ +
    hairerCrossCovarianceTwo N ρ' ε' ρ' ε' x₁ ^ 2 * hairerCrossCovarianceTwo N ρ' ε' ρ' ε' x₂

/-- `Δ²[Q_{e₁e₂}(x₁) Q_{e₁e₂}(x₂) Q_{e₁e₂}(x₃)]`. -/
def isqDiffE2 (ε ε' : ℝ) (x₁ x₂ x₃ : SpaceTime) : ℝ :=
  hairerCrossCovarianceTwo N ρ ε ρ ε x₁ * hairerCrossCovarianceTwo N ρ ε ρ ε x₂ *
      hairerCrossCovarianceTwo N ρ ε ρ ε x₃ -
    hairerCrossCovarianceTwo N ρ ε ρ' ε' x₁ * hairerCrossCovarianceTwo N ρ ε ρ' ε' x₂ *
      hairerCrossCovarianceTwo N ρ ε ρ' ε' x₃ -
    hairerCrossCovarianceTwo N ρ' ε' ρ ε x₁ * hairerCrossCovarianceTwo N ρ' ε' ρ ε x₂ *
      hairerCrossCovarianceTwo N ρ' ε' ρ ε x₃ +
    hairerCrossCovarianceTwo N ρ' ε' ρ' ε' x₁ * hairerCrossCovarianceTwo N ρ' ε' ρ' ε' x₂ *
      hairerCrossCovarianceTwo N ρ' ε' ρ' ε' x₃

/-- `Δ²[Q_{e₁e₁}(x₁) Q_{e₁e₂}(x₂) Q_{e₂e₂}(x₃)]`. -/
def isqDiffE3 (ε ε' : ℝ) (x₁ x₂ x₃ : SpaceTime) : ℝ :=
  hairerCrossCovarianceTwo N ρ ε ρ ε x₁ * hairerCrossCovarianceTwo N ρ ε ρ ε x₂ *
      hairerCrossCovarianceTwo N ρ ε ρ ε x₃ -
    hairerCrossCovarianceTwo N ρ ε ρ ε x₁ * hairerCrossCovarianceTwo N ρ ε ρ' ε' x₂ *
      hairerCrossCovarianceTwo N ρ' ε' ρ' ε' x₃ -
    hairerCrossCovarianceTwo N ρ' ε' ρ' ε' x₁ * hairerCrossCovarianceTwo N ρ' ε' ρ ε x₂ *
      hairerCrossCovarianceTwo N ρ ε ρ ε x₃ +
    hairerCrossCovarianceTwo N ρ' ε' ρ' ε' x₁ * hairerCrossCovarianceTwo N ρ' ε' ρ' ε' x₂ *
      hairerCrossCovarianceTwo N ρ' ε' ρ' ε' x₃

end RegularityStructures.Phi43

end

public section

namespace RegularityStructures.Phi43

open RegularityStructures

/-- Mixed second difference of a product of three tables. -/
theorem I3PsiDiffTable.abs_prod_three_le_sq {μ P₁ P₂ P₃ Q₁ Q₂ Q₃ : ℝ} {t₁ t₂ t₃ : I3PsiDiffTable}
    (hμ : 0 ≤ μ) (h₁ : 0 ≤ Q₁) (h₂ : 0 ≤ Q₂) (h₃ : 0 ≤ Q₃)
    (b₁ : I3PsiDiffTable.Bd μ P₁ Q₁ t₁) (b₂ : I3PsiDiffTable.Bd μ P₂ Q₂ t₂)
    (b₃ : I3PsiDiffTable.Bd μ P₃ Q₃ t₃) :
    |t₁.a * t₂.a * t₃.a - t₁.b * t₂.b * t₃.b - t₁.c * t₂.c * t₃.c + t₁.d * t₂.d * t₃.d| ≤
      1024 * μ ^ 2 * (P₁ * P₂ * P₃) * (Q₁ ^ 2 + Q₂ ^ 2 + Q₃ ^ 2) := by
  have b₄ : I3PsiDiffTable.Bd μ 1 0 ⟨1, 1, 1, 1⟩ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [I3PsiDiffTable.mean, I3PsiDiffTable.du, I3PsiDiffTable.dv, I3PsiDiffTable.dw]
    all_goals norm_num
  have := I3PsiDiffTable.abs_prod_four_le_sq hμ h₁ h₂ h₃ le_rfl b₁ b₂ b₃ b₄
  simpa using this

end RegularityStructures.Phi43

end
