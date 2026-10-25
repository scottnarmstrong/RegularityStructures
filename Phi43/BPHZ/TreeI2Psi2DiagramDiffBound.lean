/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI2Psi2DiagramMultiZero

/-!
# The deterministic diagram bounds for the difference of `I(Ψ²) Ψ²` (facade)

[Hai14, (10.3)], with `F = i2Psi2DiffF θ δ r r' d`:

* `integrable_and_abs_integral_diff_chaos4_le`: an integrand dominated by `c · i2Psi2Maj4` is
  integrable on `ℝ^5 × ℝ^5` with `|∫| ≤ c C B² F`;
* `integrable_and_abs_integral_diff_chaos2_le`: the same for `i2Psi2Maj2`;
* `integrable_and_abs_integral_diff_chaos0_le`: the chaos-`0` integral, bounded by `c C B s^(-θ)`.
-/

public section

open MeasureTheory

namespace RegularityStructures

/-- **Chaos `4` of the difference**: integrability and the bound for dominated integrands. -/
theorem integrable_and_abs_integral_diff_chaos4_le {θ δ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 8)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K : SpaceTime → ℝ} {B : ℝ}, i2Psi2KernelHyp K B →
      ∀ {f : SpaceTime × SpaceTime → ℝ} {c : ℝ}, 0 ≤ c → AEStronglyMeasurable f volume →
        ∀ x y y' : SpaceTime, i2Psi2PointCfg x y y' →
          (∀ᵐ q : SpaceTime × SpaceTime ∂volume, |f q| ≤ c * i2Psi2Maj4 θ K x y y' q) →
          Integrable f ∧ |∫ q, f q| ≤ c * (C * B ^ 2 * i2Psi2DiffF θ δ
            (torusParabolicSize (y - x)) (torusParabolicSize (y' - x))
            (torusParabolicSize (y - y'))) := by
  obtain ⟨C, hC, h⟩ := i2Psi2LintBound_diff_chaos4 hθ hθ1 hδ hδ1
  refine ⟨C, hC, ?_⟩
  intro K B hK f c hc hf x y y' hcfg hbd
  obtain ⟨hr, -, hr', -, hd⟩ := id hcfg
  have hFn := i2Psi2DiffF_nonneg (θ := θ) (δ := δ) hr hr' hd
  have hM : 0 ≤ c * (C * B ^ 2 * i2Psi2DiffF θ δ (torusParabolicSize (y - x))
      (torusParabolicSize (y' - x)) (torusParabolicSize (y - y'))) :=
    mul_nonneg hc (mul_nonneg (mul_nonneg hC (sq_nonneg B)) hFn)
  exact abs_integral_le_of_i2Psi2LintBound hf (((h hK x y y' hcfg).const_mul hc).mono_ae hbd le_rfl) hM

/-- **Chaos `2` of the difference**: integrability and the bound for dominated integrands. -/
theorem integrable_and_abs_integral_diff_chaos2_le {θ δ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 8)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K : SpaceTime → ℝ} {B : ℝ}, i2Psi2KernelHyp K B →
      ∀ {f : SpaceTime × SpaceTime → ℝ} {c : ℝ}, 0 ≤ c → AEStronglyMeasurable f volume →
        ∀ x y y' : SpaceTime, i2Psi2PointCfg x y y' →
          (∀ᵐ q : SpaceTime × SpaceTime ∂volume, |f q| ≤ c * i2Psi2Maj2 θ K x y y' q) →
          Integrable f ∧ |∫ q, f q| ≤ c * (C * B ^ 2 * i2Psi2DiffF θ δ
            (torusParabolicSize (y - x)) (torusParabolicSize (y' - x))
            (torusParabolicSize (y - y'))) := by
  obtain ⟨C, hC, h⟩ := i2Psi2LintBound_diff_chaos2 hθ hθ1 hδ hδ1
  refine ⟨C, hC, ?_⟩
  intro K B hK f c hc hf x y y' hcfg hbd
  obtain ⟨hr, -, hr', -, hd⟩ := id hcfg
  have hFn := i2Psi2DiffF_nonneg (θ := θ) (δ := δ) hr hr' hd
  have hM : 0 ≤ c * (C * B ^ 2 * i2Psi2DiffF θ δ (torusParabolicSize (y - x))
      (torusParabolicSize (y' - x)) (torusParabolicSize (y - y'))) :=
    mul_nonneg hc (mul_nonneg (mul_nonneg hC (sq_nonneg B)) hFn)
  exact abs_integral_le_of_i2Psi2LintBound hf (((h hK x y y' hcfg).const_mul hc).mono_ae hbd le_rfl) hM

end RegularityStructures

end
