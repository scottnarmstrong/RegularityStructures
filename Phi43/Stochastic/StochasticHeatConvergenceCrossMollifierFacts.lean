/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.StochasticHeatConvergenceMollifierMomentUniform
public import Phi43.Torus.KernelBoundsCovariance

/-!
# Cancellation for two different mollifiers

The two unit-mass periodisations need not come from the same profile. Their difference still has
zero mass, and its parabolic moment has a scale-uniform bound. These are the deterministic
cancellation inputs to the convergence of the noise potentials (`phi43Noise_cauchy`), following
[Hai14, Proposition 9.5, (9.14)--(9.17)].
-/

public noncomputable section

open MeasureTheory Real

namespace RegularityStructures.Phi43

private theorem integrable_periodise_weight (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ)
    {ε θ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hθ : 0 ≤ θ) :
    Integrable (fun v : SpaceTime => |periodise ρ ε v| * torusParabolicSize v ^ θ) := by
  obtain ⟨B, hB, hsupp⟩ := periodise_support_parabolic_bound ρ hρ
  have hm : Measurable (fun v : SpaceTime => torusParabolicSize v ^ θ) :=
    (continuous_rpow_const hθ).measurable.comp measurable_torusParabolicSize
  apply ((integrable_periodise ρ hρ hε).norm.mul_const ((B * ε) ^ θ)).mono'
    ((measurable_periodise ρ hρ).norm.mul hm).aestronglyMeasurable
  filter_upwards [] with v
  change ‖|periodise ρ ε v| * torusParabolicSize v ^ θ‖ ≤
    |periodise ρ ε v| * (B * ε) ^ θ
  rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _)
    (rpow_nonneg (torusParabolicSize_nonneg _) _))]
  by_cases hv : periodise ρ ε v = 0
  · simp only [hv, abs_zero, zero_mul, le_refl]
  · exact mul_le_mul_of_nonneg_left
      (rpow_le_rpow (torusParabolicSize_nonneg _) (hsupp hε hε1 v hv) hθ) (abs_nonneg _)

theorem integrable_abs_periodise_cross_sub_parabolic_moment
    (ρ ρ' : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ')
    {ε ε' θ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hε' : 0 < ε') (hε'1 : ε' ≤ 1)
    (hθ : 0 ≤ θ) :
    Integrable (fun v : SpaceTime => |periodise ρ ε v - periodise ρ' ε' v| *
      torusParabolicSize v ^ θ) := by
  have hm : Measurable (fun v : SpaceTime => torusParabolicSize v ^ θ) :=
    (continuous_rpow_const hθ).measurable.comp measurable_torusParabolicSize
  apply ((integrable_periodise_weight ρ hρ hε hε1 hθ).add
    (integrable_periodise_weight ρ' hρ' hε' hε'1 hθ)).mono'
      (((measurable_periodise ρ hρ).sub (measurable_periodise ρ' hρ')).norm.mul hm).aestronglyMeasurable
  filter_upwards [] with v
  change ‖|periodise ρ ε v - periodise ρ' ε' v| * torusParabolicSize v ^ θ‖ ≤
    |periodise ρ ε v| * torusParabolicSize v ^ θ +
      |periodise ρ' ε' v| * torusParabolicSize v ^ θ
  rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _)
    (rpow_nonneg (torusParabolicSize_nonneg _) _)), ← add_mul]
  apply mul_le_mul_of_nonneg_right _ (rpow_nonneg (torusParabolicSize_nonneg _) _)
  exact abs_sub _ _

theorem integral_abs_periodise_cross_sub_parabolic_moment_bound
    (ρ ρ' : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ')
    {θ : ℝ} (hθ : 0 ≤ θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ε ε' : ℝ},
      0 < ε → ε ≤ 1 → 0 < ε' → ε' ≤ 1 →
      (∫ v : SpaceTime, |periodise ρ ε v - periodise ρ' ε' v| *
        torusParabolicSize v ^ θ) ≤ C * (max ε ε') ^ θ := by
  obtain ⟨C, hC, hb⟩ := integral_abs_periodise_mul_parabolicSize_rpow_le_uniform ρ hρ hθ
  obtain ⟨C', hC', hb'⟩ := integral_abs_periodise_mul_parabolicSize_rpow_le_uniform ρ' hρ' hθ
  refine ⟨C + C', add_nonneg hC hC', ?_⟩
  intro ε ε' hε hε1 hε' hε'1
  calc
    _ ≤ ∫ v : SpaceTime, |periodise ρ ε v| * torusParabolicSize v ^ θ +
        |periodise ρ' ε' v| * torusParabolicSize v ^ θ := by
      apply integral_mono (integrable_abs_periodise_cross_sub_parabolic_moment
        ρ ρ' hρ hρ' hε hε1 hε' hε'1 hθ)
        ((integrable_periodise_weight ρ hρ hε hε1 hθ).add
          (integrable_periodise_weight ρ' hρ' hε' hε'1 hθ))
      intro v
      change |periodise ρ ε v - periodise ρ' ε' v| * torusParabolicSize v ^ θ ≤
        |periodise ρ ε v| * torusParabolicSize v ^ θ +
          |periodise ρ' ε' v| * torusParabolicSize v ^ θ
      rw [← add_mul]
      exact mul_le_mul_of_nonneg_right (abs_sub _ _)
        (rpow_nonneg (torusParabolicSize_nonneg _) _)
    _ = (∫ v : SpaceTime, |periodise ρ ε v| * torusParabolicSize v ^ θ) +
        ∫ v : SpaceTime, |periodise ρ' ε' v| * torusParabolicSize v ^ θ :=
      integral_add (integrable_periodise_weight ρ hρ hε hε1 hθ)
        (integrable_periodise_weight ρ' hρ' hε' hε'1 hθ)
    _ ≤ C * ε ^ θ + C' * ε' ^ θ := add_le_add (hb hε hε1) (hb' hε' hε'1)
    _ ≤ C * (max ε ε') ^ θ + C' * (max ε ε') ^ θ := add_le_add
      (mul_le_mul_of_nonneg_left (rpow_le_rpow hε.le (le_max_left _ _) hθ) hC)
      (mul_le_mul_of_nonneg_left (rpow_le_rpow hε'.le (le_max_right _ _) hθ) hC')
    _ = _ := (add_mul _ _ _).symm

theorem integral_abs_periodise_cross_sub_le
    (ρ ρ' : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ')
    {ε ε' : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hε' : 0 < ε') (hε'1 : ε' ≤ 1) :
    (∫ v : SpaceTime, |periodise ρ ε v - periodise ρ' ε' v|) ≤
      (∫ y : ParabolicSpace, |ρ y|) + ∫ y : ParabolicSpace, |ρ' y| := by
  calc
    _ ≤ ∫ v : SpaceTime, |periodise ρ ε v| + |periodise ρ' ε' v| :=
      integral_mono ((integrable_periodise ρ hρ hε).sub
        (integrable_periodise ρ' hρ' hε')).norm
        ((integrable_periodise ρ hρ hε).norm.add (integrable_periodise ρ' hρ' hε').norm)
        (fun v => abs_sub _ _)
    _ = _ := integral_add (integrable_periodise ρ hρ hε).norm
      (integrable_periodise ρ' hρ' hε').norm
    _ ≤ _ := add_le_add
      ((integral_abs_periodise_le ρ hρ hε hε1).trans_eq (integral_abs_rescale_eq ρ hε))
      ((integral_abs_periodise_le ρ' hρ' hε' hε'1).trans_eq (integral_abs_rescale_eq ρ' hε'))

end RegularityStructures.Phi43

end
