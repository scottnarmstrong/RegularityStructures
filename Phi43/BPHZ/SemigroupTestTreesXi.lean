/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestKernel
public import Phi43.BPHZ.NoiseTreeFubini

/-!
# Second moment of the tested noise `Ξ` against the periodised semigroup kernel

For a regularised noise `ξ` at scale `ε ∈ (0, 1]`, `t ∈ (0, 1]`, `lam = t^(1/4)` and a base point
`x`,
`E|∫ ξ q^♯_t(x, ·)|² ≤ C lam⁻⁵`
with `C` independent of `ε`, `t` and `x` (`regularisedNoise_semigroupPeriodised_second_moment_le`).
The pairing is a first-chaos variable `W g`, `g = ρ_ε^♯ ⋆ q^♯_t(x, ·)`, and the `L²` Young
inequality gives `‖g‖₂ ≤ ‖ρ‖₁ ‖q^♯_t‖₂`, where `‖q^♯_t‖₂² ≤ sup |q^♯_t| · ‖q^♯_t‖₁ ≤ B lam⁻⁵ M`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- **Second moment of the tested noise `Ξ`, semigroup test.**  Uniform in `ε ∈ (0, 1]`,
`t ∈ (0, 1]` and `x ∈ ℝ⁴`. -/
theorem regularisedNoise_semigroupPeriodised_second_moment_le {ρ : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ {t : ℝ}, 0 < t → t ≤ 1 → ∀ x : ParabolicSpace,
        ∫ ω, |∫ w, ξ ω w * semigroupPeriodised t x w| ^ 2 ∂P ≤
          C * (t ^ (1 / 4 : ℝ)) ^ (-(5 : ℝ)) := by
  obtain ⟨B, hB0, hB⟩ := exists_semigroupTestProfile_semigroupPeriodised
  have hM0 : 0 ≤ parabolicMomentConst 0 := by
    have := (hB (t := 1) one_pos le_rfl 0).mom_zero_nonneg
    exact this
  refine ⟨(∫ z : ParabolicSpace, |ρ z|) ^ 2 * (B * parabolicMomentConst 0),
    mul_nonneg (sq_nonneg _) (mul_nonneg hB0 hM0), ?_⟩
  intro Ω _ P W ε ξ hW hε hξ t ht ht1 x
  have h := hB ht ht1 x
  have hlam : 0 < t ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos ht _
  set ψ : SpaceTime → ℝ := semigroupPeriodised t x with hψ
  have hψm : Measurable ψ := h.measurable
  have hψ1 : Integrable ψ := h.integrable
  have hsq : Integrable (fun w => ψ w ^ 2) := by
    refine (h.integrable_abs.const_mul (B * ((t ^ (1 / 4 : ℝ)) ^ 5)⁻¹)).mono'
      (hψm.pow_const 2).aestronglyMeasurable (Filter.Eventually.of_forall fun w => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq]
    have := h.abs_le w
    calc ψ w * ψ w = |ψ w| * |ψ w| := (abs_mul_abs_self _).symm
      _ ≤ B * ((t ^ (1 / 4 : ℝ)) ^ 5)⁻¹ * |ψ w| :=
        mul_le_mul_of_nonneg_right this (abs_nonneg _)
  have hψ2 : MemLp ψ 2 := (memLp_two_iff_integrable_sq hψm.aestronglyMeasurable).2 hsq
  have hint : ∫ w, ψ w ^ 2 ≤ B * ((t ^ (1 / 4 : ℝ)) ^ 5)⁻¹ * parabolicMomentConst 0 := by
    have hle : ∀ w, ψ w ^ 2 ≤ B * ((t ^ (1 / 4 : ℝ)) ^ 5)⁻¹ * |ψ w| := fun w => by
      have := h.abs_le w
      calc ψ w ^ 2 = |ψ w| * |ψ w| := by rw [sq]; exact (abs_mul_abs_self _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right this (abs_nonneg _)
    calc ∫ w, ψ w ^ 2 ≤ ∫ w, B * ((t ^ (1 / 4 : ℝ)) ^ 5)⁻¹ * |ψ w| :=
          integral_mono hsq (h.integrable_abs.const_mul _) hle
      _ = B * ((t ^ (1 / 4 : ℝ)) ^ 5)⁻¹ * ∫ w, |ψ w| := integral_const_mul _ _
      _ ≤ B * ((t ^ (1 / 4 : ℝ)) ^ 5)⁻¹ * parabolicMomentConst 0 :=
          mul_le_mul_of_nonneg_left h.integral_abs_le (by positivity)
  have := hW.isProbabilityMeasure
  obtain ⟨B', hB'⟩ := bounded_periodise ρ hρ hε.1
  have hΞ := regularisedNoise_measurable_uncurry P W ρ ε ξ hξ
  obtain ⟨hg, hae⟩ := noise_pairing_ae_eq_whiteNoise_of_jointVersion hW
    (measurable_periodise ρ hρ) (integrable_periodise ρ hρ hε.1) hB' hψm hψ1 hψ2 hΞ
    (fun w => (hξ.2 w).2)
  obtain ⟨-, hyoung⟩ := noiseSmearedTest_sq_integral_le hρ hε hψm hψ2
  have hrpow : (t ^ (1 / 4 : ℝ)) ^ (-(5 : ℝ)) = ((t ^ (1 / 4 : ℝ)) ^ 5)⁻¹ := by
    rw [Real.rpow_neg hlam.le]
    norm_cast
  rw [hrpow]
  calc ∫ ω, |∫ w, ξ ω w * ψ w| ^ 2 ∂P
      = ∫ ω, |W (noiseSmearedTest ρ ε ψ) ω| ^ 2 ∂P := by
        refine integral_congr_ae ?_
        filter_upwards [hae] with ω hω
        have : ∫ w, ξ ω w * ψ w = ∫ w, ψ w * ξ ω w :=
          integral_congr_ae (Filter.Eventually.of_forall fun w => mul_comm _ _)
        rw [this, hω]
        rfl
    _ = ∫ u, noiseSmearedTest ρ ε ψ u ^ 2 := whiteNoise_pairing_abs_sq_integral hW hg
    _ ≤ (∫ z : ParabolicSpace, |ρ z|) ^ 2 * ∫ w, ψ w ^ 2 := hyoung
    _ ≤ (∫ z : ParabolicSpace, |ρ z|) ^ 2 * (B * ((t ^ (1 / 4 : ℝ)) ^ 5)⁻¹ *
          parabolicMomentConst 0) := mul_le_mul_of_nonneg_left hint (sq_nonneg _)
    _ = _ := by ring

end RegularityStructures.Phi43

end
