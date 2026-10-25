/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductDiagramDiff1

/-!
# The difference cross and chain pieces of `I(Ψ²)Ψ`

For second-difference functions `E₂, E₃` of three arguments with
`|E(x₁, x₂, x₃)| ≤ K μ (s₁^(-(1+σ)) s₂^(-1) s₃^(-1) + s₁^(-1) s₂^(-(1+σ)) s₃^(-1) +
s₁^(-1) s₂^(-1) s₃^(-(1+σ)))`, the integrands `a(w) b(v) E₂(w - v, w - z', z - v)` and
`a(w) b(v) E₃(w - z, w - v, v - z')` are integrable with iterated integral bounded by
`C c₁ c₂ K μ (1 + T) s(z)^η s(z')^η`, `2 η + σ < 1`.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

theorem rpow_neg_sub_flip_le' {c w : SpaceTime} {g g' : ℝ} (hg : 0 ≤ g) (hgg : g ≤ g')
    (hc : 0 < torusParabolicSize (c - w)) :
    torusParabolicSize (w - c) ^ (-g) ≤ 2 ^ g' * singularPow g c w := by
  refine (rpow_neg_sub_flip_le hg hc).trans ?_
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (by norm_num) hgg)
    (singularPow_nonneg _ _ _)

private theorem measurable_ab' {a b : SpaceTime → ℝ} (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun p : SpaceTime × SpaceTime => |a p.1| * |b p.2|) :=
  ((continuous_abs.measurable.comp ha).comp measurable_fst).mul
    ((continuous_abs.measurable.comp hb).comp measurable_snd)

/-- The nonnegative cross majorant. -/
theorem productCross_majorant_integral {Θ θ₁ θ₂ g₁ g₂ g₃ : ℝ} (hθ₁ : 0 ≤ θ₁) (hθ₁Θ : θ₁ ≤ Θ)
    (hθ₂ : 0 ≤ θ₂) (hθ₂Θ : θ₂ ≤ Θ) (hg₁ : 0 < g₁) (hg₂ : 0 ≤ g₂) (hg₃ : 0 ≤ g₃)
    (hg₁5 : g₁ < 5) (hβ5 : 3 + θ₂ + g₃ < 5) (hβγ : 5 < 3 + θ₂ + g₃ + g₁)
    (hout : 3 + θ₁ + g₂ + (3 + θ₂ + g₃ + g₁ - 5) < 5) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {c₁ c₂ T T' M : ℝ} {z z' : SpaceTime} {a b : SpaceTime → ℝ},
      0 ≤ c₁ → 0 ≤ c₂ → 0 ≤ M → 0 ≤ T → IsGainKernel Θ c₁ T z a → IsGainKernel Θ c₂ T' z' b →
      Integrable (Function.uncurry fun w v => |a w| * |b v| * (M * (singularPow g₁ w v *
          singularPow g₂ z' w * singularPow g₃ z v))) (volume.prod volume) ∧
        ∫ w, ∫ v, |a w| * |b v| * (M * (singularPow g₁ w v * singularPow g₂ z' w *
          singularPow g₃ z v)) ≤ C * (c₁ * c₂ * M) *
          (torusParabolicSize z ^ θ₁ * torusParabolicSize z' ^ θ₂) * (1 + T) := by
  obtain ⟨C, hC, h⟩ := productCrossGen_bound (Θ := Θ) hθ₁ hθ₁Θ hθ₂ hθ₂Θ hg₁ hg₂ hg₃ hg₁5 hβ5
    hβγ hout
  refine ⟨C, hC, ?_⟩
  intro c₁ c₂ T T' M z z' a b hc₁ hc₂ hM hT ha hb
  have hm : Measurable (fun p : SpaceTime × SpaceTime => |a p.1| * |b p.2| *
      (M * (singularPow g₁ p.1 p.2 * singularPow g₂ z' p.1 * singularPow g₃ z p.2))) :=
    (measurable_ab' ha.1 hb.1).mul (measurable_const.mul (((measurable_singularPow_pair g₁).mul
      (measurable_singularPow_fst g₂ z')).mul (measurable_singularPow_snd g₃ z)))
  have := h (F := fun w v => |a w| * |b v| * (M * (singularPow g₁ w v * singularPow g₂ z' w *
    singularPow g₃ z v))) hc₁ hc₂ hM hT ha hb hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun w => Filter.Eventually.of_forall fun v => by
      rw [abs_of_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        (mul_nonneg hM (mul_nonneg (mul_nonneg (singularPow_nonneg _ _ _)
          (singularPow_nonneg _ _ _)) (singularPow_nonneg _ _ _))))])
  exact ⟨this.1, (le_abs_self _).trans this.2⟩

/-- The nonnegative chain majorant. -/
theorem productChain_majorant_integral {Θ θ₁ θ₂ g₁ g₂ g₃ : ℝ} (hθ₁ : 0 ≤ θ₁) (hθ₁Θ : θ₁ ≤ Θ)
    (hθ₂ : 0 ≤ θ₂) (hθ₂Θ : θ₂ ≤ Θ) (hg₁ : 0 ≤ g₁) (hg₂ : 0 < g₂) (hg₃ : 0 ≤ g₃)
    (hg₂5 : g₂ < 5) (hβ5 : 3 + θ₂ + g₃ < 5) (hβγ : 5 < 3 + θ₂ + g₃ + g₂)
    (hout : 3 + θ₁ + g₁ + (3 + θ₂ + g₃ + g₂ - 5) < 5) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {c₁ c₂ T T' M : ℝ} {z z' : SpaceTime} {a b : SpaceTime → ℝ},
      0 ≤ c₁ → 0 ≤ c₂ → 0 ≤ M → 0 ≤ T → IsGainKernel Θ c₁ T z a → IsGainKernel Θ c₂ T' z' b →
      Integrable (Function.uncurry fun w v => |a w| * |b v| * (M * (singularPow g₁ z w *
          singularPow g₂ w v * singularPow g₃ z' v))) (volume.prod volume) ∧
        ∫ w, ∫ v, |a w| * |b v| * (M * (singularPow g₁ z w * singularPow g₂ w v *
          singularPow g₃ z' v)) ≤ C * (c₁ * c₂ * M) *
          (torusParabolicSize z ^ θ₁ * torusParabolicSize z' ^ θ₂) * (1 + T) := by
  obtain ⟨C, hC, h⟩ := productChainGen_bound (Θ := Θ) hθ₁ hθ₁Θ hθ₂ hθ₂Θ hg₁ hg₂ hg₃ hg₂5 hβ5
    hβγ hout
  refine ⟨C, hC, ?_⟩
  intro c₁ c₂ T T' M z z' a b hc₁ hc₂ hM hT ha hb
  have hm : Measurable (fun p : SpaceTime × SpaceTime => |a p.1| * |b p.2| *
      (M * (singularPow g₁ z p.1 * singularPow g₂ p.1 p.2 * singularPow g₃ z' p.2))) :=
    (measurable_ab' ha.1 hb.1).mul (measurable_const.mul (((measurable_singularPow_fst g₁ z).mul
      (measurable_singularPow_pair g₂)).mul (measurable_singularPow_snd g₃ z')))
  have := h (F := fun w v => |a w| * |b v| * (M * (singularPow g₁ z w * singularPow g₂ w v *
    singularPow g₃ z' v))) hc₁ hc₂ hM hT ha hb hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun w => Filter.Eventually.of_forall fun v => by
      rw [abs_of_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        (mul_nonneg hM (mul_nonneg (mul_nonneg (singularPow_nonneg _ _ _)
          (singularPow_nonneg _ _ _)) (singularPow_nonneg _ _ _))))])
  exact ⟨this.1, (le_abs_self _).trans this.2⟩

end RegularityStructures

end
