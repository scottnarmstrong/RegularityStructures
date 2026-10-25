/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI2Psi2DiagramMultiChaosTwo

/-!
# Chaos `0` of the difference bound for `I(Ψ²) Ψ²`

The mean of the field is `m(y) = -2 ∫ K(x - w) Q(w - y)² dw`.  For two scales the difference
`m_ε(y) - m_ε'(y)` involves `Q_ε² - Q_ε'²`, which gains a factor `(max ε ε')^θ` at the price of the
exponent `2 + θ` instead of `2`; the total order `5 + θ` is then above the critical `5`, with no
logarithmic loss.  The deterministic input is
`∫ |K(x - w)| s(y - w)^(-(2+θ)) dw ≲ B s(y - x)^(-θ)`
(`i2Psi2LintBound_diff_chaos0`), and its consequence for integrands dominated by it
(`integrable_and_abs_integral_diff_chaos0_le`).
-/

public section

open MeasureTheory

namespace RegularityStructures

/-- **Chaos `0` of the difference**, lower-integral form:
`∫ |K(x - w)| s(y - w)^(-(2+θ)) ≲ B s(y - x)^(-θ)`, `θ ∈ (0, 1]`. -/
theorem i2Psi2LintBound_diff_chaos0 {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K : SpaceTime → ℝ} {B : ℝ}, i2Psi2KernelHyp K B →
      ∀ x y : SpaceTime, 0 < torusParabolicSize (y - x) →
        i2Psi2LintBound volume (fun w => |K (x - w)| * torusParabolicSize (y - w) ^ (-(2 + θ)))
          (C * B * torusParabolicSize (y - x) ^ (-θ)) := by
  obtain ⟨CG, hCG, hG⟩ := i2Psi2LintBound_rpow_mul_rpow_of_gt (a := 3) (b := 2 + θ)
    (by norm_num) (by norm_num) (by linarith) (by linarith) (by linarith)
  refine ⟨2 * CG, by positivity, ?_⟩
  intro K B hK x y hr
  obtain ⟨hB, -, -, hKb, -⟩ := id hK
  have hyx : 0 < torusParabolicSize (x - y) := torusParabolicSize_pos_of_sub_pos hr
  have g := hG x y hyx
  have e : (5 : ℝ) - 3 - (2 + θ) = -θ := by ring
  rw [e] at g
  have c := g.const_mul (c := B) hB
  have t := torusParabolicSize_sub_rpow_neg_le (a := x) (b := y) (e := θ) hθ.le hθ1 hr
  refine c.mono_ae ?_ ?_
  · filter_upwards [ae_torusParabolicSize_sub_pos x] with w hx
    have hk := hKb _ hx
    have n2 : 0 ≤ torusParabolicSize (y - w) ^ (-(2 + θ)) :=
      Real.rpow_nonneg (torusParabolicSize_nonneg _) _
    calc |K (x - w)| * torusParabolicSize (y - w) ^ (-(2 + θ))
        ≤ (B * torusParabolicSize (x - w) ^ (-(3 : ℝ))) * torusParabolicSize (y - w) ^ (-(2 + θ)) :=
          mul_le_mul_of_nonneg_right hk n2
      _ = _ := by ring
  · calc B * (CG * torusParabolicSize (x - y) ^ (-θ))
        ≤ B * (CG * (2 * torusParabolicSize (y - x) ^ (-θ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left t hCG) hB
      _ = _ := by ring

/-- **Integrability and a bound for integrands dominated by the chaos-`0` majorant.** -/
theorem integrable_and_abs_integral_diff_chaos0_le {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K : SpaceTime → ℝ} {B : ℝ}, i2Psi2KernelHyp K B →
      ∀ {f : SpaceTime → ℝ} {c : ℝ}, 0 ≤ c → AEStronglyMeasurable f volume →
        ∀ x y : SpaceTime, 0 < torusParabolicSize (y - x) →
          (∀ᵐ w : SpaceTime ∂volume, |f w| ≤
            c * (|K (x - w)| * torusParabolicSize (y - w) ^ (-(2 + θ)))) →
          Integrable f ∧ |∫ w, f w| ≤ c * (C * B * torusParabolicSize (y - x) ^ (-θ)) := by
  obtain ⟨C, hC, h⟩ := i2Psi2LintBound_diff_chaos0 hθ hθ1
  refine ⟨C, hC, ?_⟩
  intro K B hK f c hc hf x y hr hbd
  obtain ⟨hB, -, -, -, -⟩ := id hK
  have hb := (h hK x y hr).const_mul hc
  have hM : 0 ≤ c * (C * B * torusParabolicSize (y - x) ^ (-θ)) :=
    mul_nonneg hc (mul_nonneg (mul_nonneg hC hB) (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
  exact abs_integral_le_of_i2Psi2LintBound hf (hb.mono_ae hbd le_rfl) hM

end RegularityStructures

end
