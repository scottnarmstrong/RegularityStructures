/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI2Psi2CrossMajorant
public import Phi43.BPHZ.TreeI2Psi2DifferenceMean

/-!
# The difference of the means of the field of `I(Ψ²) Ψ²` at two mollifiers

For scales `a, b ∈ (0, 1]` and `θ ∈ (0, 1]`,
`|m_{ρ,a}(y) - m_{ρ',b}(y)| ≤ C (max a b)^θ s(y - x)^(-θ)` (`abs_i2Psi2Mean_sub_le_cross`), where
`m_{ρ,s}(y) = -2 ∫ K(x - w) Q_{ρ,s}(w - y)² dw` (`i2Psi2Mean`).  The proof uses the table
`(Q_{ρa,ρa}, Q_{ρa,ρa}, Q_{ρ'b,ρ'b}, Q_{ρ'b,ρ'b})`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

private theorem rpow_two_add_theta_cross {θ : ℝ} (hθ : 0 < θ) (u : SpaceTime) :
    (torusParabolicSize u ^ (-(1 : ℝ))) ^ 2 * torusParabolicSize u ^ (-θ) =
      torusParabolicSize u ^ (-(2 + θ)) := by
  have h0 := torusParabolicSize_nonneg u
  rw [← Real.rpow_natCast, ← Real.rpow_mul h0, ← Real.rpow_add' h0 (by push_cast; linarith)]
  congr 1
  push_cast
  ring

/-- **The difference of the means.** -/
theorem abs_i2Psi2Mean_sub_le_cross (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ)
    (hρ' : IsMollifier ρ') {θ : ℝ}
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {a b : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → 0 < a → a ≤ 1 → 0 < b → b ≤ 1 → IsRegularisedNoise P W ρ a ξ →
      IsRegularisedNoise P W ρ' b ξ' → ∀ x y : SpaceTime, 0 < torusParabolicSize (y - x) →
        |i2Psi2Mean N ρ x a y - i2Psi2Mean N ρ' x b y| ≤
          C * (max a b) ^ θ * torusParabolicSize (y - x) ^ (-θ) := by
  obtain ⟨A, hA, h⟩ := i2Psi2CrossTwo_tables_bd N ρ ρ' hρ hρ' hθ hθ1
  obtain ⟨B, hB, hK⟩ := i2Psi2KernelHyp_hairerKernelTorus N
  obtain ⟨C0, hC0, h0⟩ := integrable_and_abs_integral_diff_chaos0_le hθ hθ1
  refine ⟨16 * A ^ 2 * (C0 * B), by positivity, ?_⟩
  intro Ω _ P W a b ξ ξ' hW ha ha1 hb hb1 hξ hξ' x y hr
  obtain ⟨-, hf⟩ := h ha ha1 hb hb1
  have hμ : 0 ≤ (max a b) ^ θ := Real.rpow_nonneg (le_max_of_le_left ha.le) _
  have ia := integrable_hairerKernelTorus_sub_mul_sq N hρ ha hW hξ x y
  have ib := integrable_hairerKernelTorus_sub_mul_sq N hρ' hb hW hξ' x y
  have hQm : ∀ s : ℝ, Measurable (fun w : SpaceTime => hairerCovariance N ρ s (w - y) ^ 2) :=
    fun s => ((measurable_hairerCovariance N hρ s).comp
      (measurable_id.sub measurable_const)).pow_const 2
  have hQm' : ∀ s : ℝ, Measurable (fun w : SpaceTime => hairerCovariance N ρ' s (w - y) ^ 2) :=
    fun s => ((measurable_hairerCovariance N hρ' s).comp
      (measurable_id.sub measurable_const)).pow_const 2
  have hmeas : AEStronglyMeasurable (fun w => hairerKernelTorus N (x - w) *
      (hairerCovariance N ρ a (w - y) ^ 2 - hairerCovariance N ρ' b (w - y) ^ 2)) volume :=
    (((measurable_constantsComparison_hairerKernelTorus N).comp
      (measurable_const.sub measurable_id)).mul ((hQm a).sub (hQm' b))).aestronglyMeasurable
  have hbd : ∀ᵐ w : SpaceTime ∂volume, |hairerKernelTorus N (x - w) *
      (hairerCovariance N ρ a (w - y) ^ 2 - hairerCovariance N ρ' b (w - y) ^ 2)| ≤
      (8 * A ^ 2 * (max a b) ^ θ) * (|hairerKernelTorus N (x - w)| *
        torusParabolicSize (y - w) ^ (-(2 + θ))) := by
    filter_upwards [ae_torusParabolicSize_sub_pos y] with w hw
    have f2 := (hf (w - y) (by rwa [neg_sub])).2.1
    rw [neg_sub] at f2
    have := abs_sq_sub_sq_le_of_bd f2
    rw [abs_mul]
    have e : 4 * (max a b) ^ θ * (A * torusParabolicSize (y - w) ^ (-(1 : ℝ))) ^ 2 *
        (2 * torusParabolicSize (y - w) ^ (-θ)) =
        8 * A ^ 2 * (max a b) ^ θ * ((torusParabolicSize (y - w) ^ (-(1 : ℝ))) ^ 2 *
          torusParabolicSize (y - w) ^ (-θ)) := by ring
    rw [e, rpow_two_add_theta_cross hθ] at this
    calc |hairerKernelTorus N (x - w)| * |hairerCovariance N ρ a (w - y) ^ 2 -
          hairerCovariance N ρ' b (w - y) ^ 2|
        ≤ |hairerKernelTorus N (x - w)| * (8 * A ^ 2 * (max a b) ^ θ *
          torusParabolicSize (y - w) ^ (-(2 + θ))) :=
          mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ = _ := by ring
  have hc : 0 ≤ 8 * A ^ 2 * (max a b) ^ θ := by positivity
  obtain ⟨hi, hb2⟩ := h0 hK hc hmeas x y hr hbd
  have e : i2Psi2Mean N ρ x a y - i2Psi2Mean N ρ' x b y =
      -2 * ∫ w, hairerKernelTorus N (x - w) *
        (hairerCovariance N ρ a (w - y) ^ 2 - hairerCovariance N ρ' b (w - y) ^ 2) := by
    unfold i2Psi2Mean
    have : ∀ w, hairerKernelTorus N (x - w) *
        (hairerCovariance N ρ a (w - y) ^ 2 - hairerCovariance N ρ' b (w - y) ^ 2) =
        hairerKernelTorus N (x - w) * hairerCovariance N ρ a (w - y) ^ 2 -
          hairerKernelTorus N (x - w) * hairerCovariance N ρ' b (w - y) ^ 2 := fun w => by ring
    simp_rw [this]
    rw [integral_sub ia ib]
    ring
  rw [e, abs_mul, abs_neg, abs_two]
  calc 2 * |∫ w, hairerKernelTorus N (x - w) *
        (hairerCovariance N ρ a (w - y) ^ 2 - hairerCovariance N ρ' b (w - y) ^ 2)|
      ≤ 2 * (8 * A ^ 2 * (max a b) ^ θ * (C0 * B * torusParabolicSize (y - x) ^ (-θ))) :=
        mul_le_mul_of_nonneg_left hb2 (by norm_num)
    _ = _ := by ring

end RegularityStructures.Phi43

end
