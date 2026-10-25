/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.NoiseTreeScaling

/-!
# Fractional parabolic moments of the rescaled mollifier

For `ε > 0`: `∫ |ρ_ε(y)| ‖y‖^a dy = ε^a ∫ |ρ(y)| ‖y‖^a dy`
(`integral_abs_rescale_mul_parabolicNorm_rpow`) and the integrand is integrable.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

theorem integrable_abs_rescale_mul_parabolicNorm_rpow (ρ : ℝ × (Fin 3 → ℝ) → ℝ)
    (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε) {a : ℝ} (ha : 0 ≤ a) :
    Integrable (fun y => |rescale ρ ε y| * parabolicNorm y ^ a) := by
  have hc : Continuous (rescale ρ ε) := by
    unfold rescale
    apply Continuous.const_mul
    exact hρ.contDiff.continuous.comp (by fun_prop)
  have hp : Continuous (fun y : ParabolicSpace => parabolicNorm y ^ a) :=
    continuous_parabolicNorm.rpow_const fun _ => Or.inr ha
  exact (hc.norm.mul hp).integrable_of_hasCompactSupport
    ((hasCompactSupport_rescale ρ hρ hε).norm.mul_right)

theorem integral_abs_rescale_mul_parabolicNorm_rpow (ρ : ℝ × (Fin 3 → ℝ) → ℝ) {ε : ℝ}
    (hε : 0 < ε) (a : ℝ) :
    ∫ y, |rescale ρ ε y| * parabolicNorm y ^ a = ε ^ a * ∫ y, |ρ y| * parabolicNorm y ^ a := by
  have hpt : ∀ y : ℝ × (Fin 3 → ℝ), |rescale ρ ε y| * parabolicNorm y ^ a =
      (ε ^ (-5 : ℤ) * ε ^ a) *
        (|ρ (parabolicDilate ε⁻¹ y)| * parabolicNorm (parabolicDilate ε⁻¹ y) ^ a) := by
    intro y
    have h1 : |rescale ρ ε y| = ε ^ (-5 : ℤ) * |ρ (parabolicDilate ε⁻¹ y)| := by
      rw [rescale, abs_mul, abs_of_pos (zpow_pos hε _)]
      congr 2
      simp [parabolicDilate, inv_pow]
    have h2 : parabolicNorm y = ε * parabolicNorm (parabolicDilate ε⁻¹ y) := by
      rw [parabolicNorm_parabolicDilate_inv hε y, ← mul_assoc, mul_inv_cancel₀ hε.ne', one_mul]
    rw [h1]
    conv_lhs => rw [h2]
    rw [Real.mul_rpow hε.le (parabolicNorm_nonneg _)]
    ring
  have hcomp := integral_comp_parabolicDilate (fun y => |ρ y| * parabolicNorm y ^ a)
    (inv_pos.mpr hε)
  simp_rw [hpt]
  rw [integral_const_mul, hcomp]
  have h5 : ((ε⁻¹) ^ 5)⁻¹ = ε ^ 5 := by
    rw [inv_pow, inv_inv]
  rw [h5]
  have : ε ^ (-5 : ℤ) * ε ^ a * ε ^ 5 = ε ^ a := by
    rw [mul_assoc, mul_comm (ε ^ a), ← mul_assoc, show ε ^ 5 = ε ^ (5 : ℤ) by norm_cast,
      ← zpow_add₀ hε.ne']
    norm_num
  rw [← mul_assoc, this]

end RegularityStructures.Phi43

end
