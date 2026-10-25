/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3PsiDifferenceAlgebra

/-!
# Mixed second differences of products of five `2 × 2` tables

The covariance of the difference of the fields of `I(Ψ³) Ψ²` involves products of five cross
covariances.  The bound data `Bd μ P Q` of `TreeI3PsiDifferenceAlgebra` multiplies as in the group
algebra of `ℤ/2 × ℤ/2`, so the mixed second difference of a product of five tables is bounded by
`5120 μ² P₁ ⋯ P₅ (Q₁² + ⋯ + Q₅²)`.
-/

public section

namespace RegularityStructures.Phi43

namespace I3PsiDiffTable

/-- **Mixed second difference of a product of five tables.**
`|∏ aⱼ - ∏ bⱼ - ∏ cⱼ + ∏ dⱼ| ≤ 1024 μ² P₁⋯P₅ (Q₁ + ⋯ + Q₅)²`. -/
theorem abs_prod_five_le {μ P₁ P₂ P₃ P₄ P₅ Q₁ Q₂ Q₃ Q₄ Q₅ : ℝ}
    {t₁ t₂ t₃ t₄ t₅ : I3PsiDiffTable} (hμ : 0 ≤ μ) (h₁ : 0 ≤ Q₁) (h₂ : 0 ≤ Q₂) (h₃ : 0 ≤ Q₃)
    (h₄ : 0 ≤ Q₄) (h₅ : 0 ≤ Q₅) (b₁ : Bd μ P₁ Q₁ t₁) (b₂ : Bd μ P₂ Q₂ t₂) (b₃ : Bd μ P₃ Q₃ t₃)
    (b₄ : Bd μ P₄ Q₄ t₄) (b₅ : Bd μ P₅ Q₅ t₅) :
    |t₁.a * t₂.a * t₃.a * t₄.a * t₅.a - t₁.b * t₂.b * t₃.b * t₄.b * t₅.b -
        t₁.c * t₂.c * t₃.c * t₄.c * t₅.c + t₁.d * t₂.d * t₃.d * t₄.d * t₅.d| ≤
      1024 * μ ^ 2 * (P₁ * P₂ * P₃ * P₄ * P₅) * (Q₁ + Q₂ + Q₃ + Q₄ + Q₅) ^ 2 := by
  have b12 := Bd.mul hμ h₁ h₂ b₁ b₂
  have b123 := Bd.mul hμ (add_nonneg h₁ h₂) h₃ b12 b₃
  have b1234 := Bd.mul hμ (add_nonneg (add_nonneg h₁ h₂) h₃) h₄ b123 b₄
  have b12345 := Bd.mul hμ (add_nonneg (add_nonneg (add_nonneg h₁ h₂) h₃) h₄) h₅ b1234 b₅
  have hw := b12345.2.2.2.2.2.2
  have e : t₁.a * t₂.a * t₃.a * t₄.a * t₅.a - t₁.b * t₂.b * t₃.b * t₄.b * t₅.b -
      t₁.c * t₂.c * t₃.c * t₄.c * t₅.c + t₁.d * t₂.d * t₃.d * t₄.d * t₅.d =
      4 * ((((t₁.mul t₂).mul t₃).mul t₄).mul t₅).dw := by
    simp only [mul, dw]; ring
  rw [e, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  have : 4 * (μ ^ 2 * (4 * (4 * (4 * (4 * P₁ * P₂) * P₃) * P₄) * P₅) *
      (Q₁ + Q₂ + Q₃ + Q₄ + Q₅) ^ 2) =
      1024 * μ ^ 2 * (P₁ * P₂ * P₃ * P₄ * P₅) * (Q₁ + Q₂ + Q₃ + Q₄ + Q₅) ^ 2 := by ring
  rw [← this]
  exact mul_le_mul_of_nonneg_left hw (by norm_num)

/-- **Mixed second difference of a product of five tables, quadratic form.**
`|∏ aⱼ - ∏ bⱼ - ∏ cⱼ + ∏ dⱼ| ≤ 5120 μ² P₁⋯P₅ (Q₁² + ⋯ + Q₅²)`. -/
theorem abs_prod_five_le_sq {μ P₁ P₂ P₃ P₄ P₅ Q₁ Q₂ Q₃ Q₄ Q₅ : ℝ}
    {t₁ t₂ t₃ t₄ t₅ : I3PsiDiffTable} (hμ : 0 ≤ μ) (h₁ : 0 ≤ Q₁) (h₂ : 0 ≤ Q₂) (h₃ : 0 ≤ Q₃)
    (h₄ : 0 ≤ Q₄) (h₅ : 0 ≤ Q₅) (b₁ : Bd μ P₁ Q₁ t₁) (b₂ : Bd μ P₂ Q₂ t₂) (b₃ : Bd μ P₃ Q₃ t₃)
    (b₄ : Bd μ P₄ Q₄ t₄) (b₅ : Bd μ P₅ Q₅ t₅) :
    |t₁.a * t₂.a * t₃.a * t₄.a * t₅.a - t₁.b * t₂.b * t₃.b * t₄.b * t₅.b -
        t₁.c * t₂.c * t₃.c * t₄.c * t₅.c + t₁.d * t₂.d * t₃.d * t₄.d * t₅.d| ≤
      5120 * μ ^ 2 * (P₁ * P₂ * P₃ * P₄ * P₅) * (Q₁ ^ 2 + Q₂ ^ 2 + Q₃ ^ 2 + Q₄ ^ 2 + Q₅ ^ 2) := by
  refine (abs_prod_five_le hμ h₁ h₂ h₃ h₄ h₅ b₁ b₂ b₃ b₄ b₅).trans ?_
  have hP₁ : 0 ≤ P₁ := (abs_nonneg _).trans b₁.1
  have hP₂ : 0 ≤ P₂ := (abs_nonneg _).trans b₂.1
  have hP₃ : 0 ≤ P₃ := (abs_nonneg _).trans b₃.1
  have hP₄ : 0 ≤ P₄ := (abs_nonneg _).trans b₄.1
  have hP₅ : 0 ≤ P₅ := (abs_nonneg _).trans b₅.1
  have hcs : (Q₁ + Q₂ + Q₃ + Q₄ + Q₅) ^ 2 ≤ 5 * (Q₁ ^ 2 + Q₂ ^ 2 + Q₃ ^ 2 + Q₄ ^ 2 + Q₅ ^ 2) := by
    nlinarith [sq_nonneg (Q₁ - Q₂), sq_nonneg (Q₁ - Q₃), sq_nonneg (Q₁ - Q₄), sq_nonneg (Q₁ - Q₅),
      sq_nonneg (Q₂ - Q₃), sq_nonneg (Q₂ - Q₄), sq_nonneg (Q₂ - Q₅), sq_nonneg (Q₃ - Q₄),
      sq_nonneg (Q₃ - Q₅), sq_nonneg (Q₄ - Q₅)]
  have hc : 0 ≤ 1024 * μ ^ 2 * (P₁ * P₂ * P₃ * P₄ * P₅) := by positivity
  calc 1024 * μ ^ 2 * (P₁ * P₂ * P₃ * P₄ * P₅) * (Q₁ + Q₂ + Q₃ + Q₄ + Q₅) ^ 2
      ≤ 1024 * μ ^ 2 * (P₁ * P₂ * P₃ * P₄ * P₅) *
        (5 * (Q₁ ^ 2 + Q₂ ^ 2 + Q₃ ^ 2 + Q₄ ^ 2 + Q₅ ^ 2)) :=
        mul_le_mul_of_nonneg_left hcs hc
    _ = _ := by ring

end I3PsiDiffTable

end RegularityStructures.Phi43

end
