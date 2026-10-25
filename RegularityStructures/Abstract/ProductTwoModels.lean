/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.ProductTwoModelsBounds

/-!
# Products of modelled distributions for two models

[Hai14, Proposition 4.10]: for two models `(Π, Γ)`, `(Π̄, Γ̄)`, `f₁ ∈ D^{γ₁}(V; Γ)`,
`f₂ ∈ D^{γ₂}(W; Γ)`, `g₁ ∈ D^{γ₁}(V; Γ̄)`, `g₂ ∈ D^{γ₂}(W; Γ̄)`,
`|||f₁ ⋆ f₂; g₁ ⋆ g₂|||_γ ≲ |||f₁; g₁|||_{γ₁} + |||f₂; g₂|||_{γ₂} + ‖Γ − Γ̄‖`, uniformly over
bounded norms. We prove the explicit form (`Model.modelledDiffBoundOn_truncMul`):
`|||f₁ ⋆_γ f₂; g₁ ⋆_γ g₂|||_{γ;S} ≤ c (δ₁ C₂ + C₁ δ₂ + 2 C₁ C₂ δ_Γ) (1 + C_Γ)²`
with `c = (3 + |ι|⁴) ‖⋆‖`, where `C₁` bounds `f₁` and `g₁`, `C₂` bounds `f₂`, `C_Γ` bounds `Γ`
and `Γ̄`, `δ₁ = |||f₁; g₁|||`, `δ₂ = |||f₂; g₂|||` and `δ_Γ = ‖Γ − Γ̄‖` (all on `S`).

As for [Hai14, Theorem 4.7], the global (unrestricted in `d(y, x)`) form of `|||·;·|||` used
here needs a separate argument for `d(y, x) ≥ 1`.

Source: [Hai14] = arXiv:1303.5113v4, Proposition 4.10 and its proof, (4.7).
-/

public section

open MeasureTheory Set

namespace RegularityStructures

/-- The final arithmetic of [Hai14, Proposition 4.10]. -/
theorem three_add_card_pow_le_of_le {Z W T N : ℝ} (hZ : Z ≤ T) (hW : W ≤ T) :
    Z + Z + Z + N ^ 4 * W ≤ (3 + N ^ 4) * T := by
  have hN : 0 ≤ N ^ 4 := by positivity
  have := mul_le_mul_of_nonneg_left hW hN
  nlinarith

theorem abs_add_add_add_sub_sub_add_le (a b c d e f g : ℝ) :
    |a + b + c + d - e - f + g| ≤ |a| + |b| + |c| + |d| + |e| + |f| + |g| := by
  rw [abs_le]
  constructor <;> linarith [neg_abs_le a, le_abs_self a, neg_abs_le b, le_abs_self b,
    neg_abs_le c, le_abs_self c, neg_abs_le d, le_abs_self d, neg_abs_le e, le_abs_self e,
    neg_abs_le f, le_abs_self f, neg_abs_le g, le_abs_self g]

namespace Model

/-- The constant `B = (C₁ δ_Γ + δ₁ (1 + C_Γ)) C₂ (1 + C_Γ) + C₁ (1 + C_Γ) (C₂ δ_Γ + δ₂ (1 + C_Γ))`
is at most `(1 + C_Γ)² (δ₁ C₂ + C₁ δ₂ + 2 C₁ C₂ δ_Γ)`. -/
theorem twoModels_const_le {C₁ C₂ δ₁ δ₂ CΓ δΓ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hCΓ : 0 ≤ CΓ) (hδΓ : 0 ≤ δΓ) :
    (C₁ * δΓ + δ₁ * (1 + CΓ)) * (C₂ * (1 + CΓ)) + C₁ * (1 + CΓ) * (C₂ * δΓ + δ₂ * (1 + CΓ)) ≤
      (δ₁ * C₂ + C₁ * δ₂ + 2 * C₁ * C₂ * δΓ) * (1 + CΓ) ^ 2 := by
  have h : 0 ≤ C₁ * C₂ * δΓ * CΓ := by positivity
  nlinarith

end Model

end RegularityStructures

end
