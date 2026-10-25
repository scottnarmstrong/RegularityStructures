/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ModelRegPiXiMollify

/-!
# Smeared periodised semigroup kernel versus the kernel

`∫ (ψ ⋆ ρ_ε^♯ - ψ)² ≤ C ε^a lam^(-(5 + a))` for `ψ = q^♯_t(x, ·)`, `a ∈ [0, 1]`
(`noiseSmearedTest_semigroupPeriodised_sub_sq_integral_le`).
-/

public section

open MeasureTheory
open scoped ENNReal

namespace RegularityStructures.Phi43

open RegularityStructures

theorem integrable_semigroupPeriodised_sq {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (x : ParabolicSpace) :
    Integrable (fun w => semigroupPeriodised t x w ^ 2) := by
  obtain ⟨B, hB0, hB⟩ := exists_semigroupTestProfile_semigroupPeriodised
  have h := hB ht ht1 x
  refine (h.integrable_abs.const_mul (B * ((t ^ (1 / 4 : ℝ)) ^ 5)⁻¹)).mono'
    ((h.measurable.pow_const 2).aestronglyMeasurable) (Filter.Eventually.of_forall fun w => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq]
  calc semigroupPeriodised t x w * semigroupPeriodised t x w
      = |semigroupPeriodised t x w| * |semigroupPeriodised t x w| := (abs_mul_abs_self _).symm
    _ ≤ B * ((t ^ (1 / 4 : ℝ)) ^ 5)⁻¹ * |semigroupPeriodised t x w| :=
        mul_le_mul_of_nonneg_right (h.abs_le w) (abs_nonneg _)

/-- Shift-square integral of the periodised kernel at a projected translation. -/
theorem exists_integral_sq_semigroupPeriodised_add_sub_le {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ {t : ℝ}, 0 < t → t ≤ 1 → ∀ (x y : ParabolicSpace),
      ∫ u : SpaceTime, (semigroupPeriodised t x (u + spaceTimeProj y) -
          semigroupPeriodised t x u) ^ 2 ≤
        c * (((t ^ (1 / 4 : ℝ)) ^ 5)⁻¹ * ((t ^ (1 / 4 : ℝ))⁻¹) ^ a) * parabolicNorm y ^ a := by
  obtain ⟨K, hK0, hK⟩ := exists_integral_abs_semigroupPeriodised_add_sub_le_rpow ha0 ha1
  obtain ⟨B, hB0, hB⟩ := exists_semigroupTestProfile_semigroupPeriodised
  refine ⟨2 * B * K, by positivity, fun {t} ht ht1 x y => ?_⟩
  have hlam : 0 < t ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos ht _
  set ψ := semigroupPeriodised t x with hψ
  have h := hB ht ht1 x
  set Bψ : ℝ := B * ((t ^ (1 / 4 : ℝ)) ^ 5)⁻¹ with hBψ
  have hBψ0 : 0 ≤ Bψ := by positivity
  have hs : Integrable (fun u => ψ (u + spaceTimeProj y)) := h.integrable.comp_add_right _
  have habs : Integrable (fun u => |ψ (u + spaceTimeProj y) - ψ u|) := (hs.sub h.integrable).abs
  have hsq : Integrable (fun u => (ψ (u + spaceTimeProj y) - ψ u) ^ 2) :=
    integrable_shift_diff_sq_of_bounded h.measurable (integrable_semigroupPeriodised_sq ht ht1 x) _
  have hpt : ∀ u, (ψ (u + spaceTimeProj y) - ψ u) ^ 2 ≤ 2 * Bψ * |ψ (u + spaceTimeProj y) - ψ u| := by
    intro u
    have h1 : |ψ (u + spaceTimeProj y) - ψ u| ≤ 2 * Bψ := by
      calc _ ≤ |ψ (u + spaceTimeProj y)| + |ψ u| := abs_sub _ _
        _ ≤ 2 * Bψ := by linarith [h.abs_le (u + spaceTimeProj y), h.abs_le u]
    calc (ψ (u + spaceTimeProj y) - ψ u) ^ 2
        = |ψ (u + spaceTimeProj y) - ψ u| * |ψ (u + spaceTimeProj y) - ψ u| := by
          rw [← sq, sq_abs]
      _ ≤ 2 * Bψ * |ψ (u + spaceTimeProj y) - ψ u| :=
          mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
  have hmain := hK ht ht1 x y
  rw [Real.mul_rpow (inv_nonneg.2 hlam.le) (parabolicNorm_nonneg y)] at hmain
  calc ∫ u : SpaceTime, (ψ (u + spaceTimeProj y) - ψ u) ^ 2
      ≤ ∫ u : SpaceTime, 2 * Bψ * |ψ (u + spaceTimeProj y) - ψ u| :=
        integral_mono hsq (habs.const_mul _) hpt
    _ = 2 * Bψ * ∫ u : SpaceTime, |ψ (u + spaceTimeProj y) - ψ u| := integral_const_mul _ _
    _ ≤ 2 * Bψ * (K * (((t ^ (1 / 4 : ℝ))⁻¹) ^ a * parabolicNorm y ^ a)) :=
        mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = _ := by rw [hBψ]; ring

end RegularityStructures.Phi43

end
