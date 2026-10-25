/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.StochasticHeatConvergenceConvolution

/-!
# Deterministic covariance Fubini for the pathwise heat convolution

Boundedness and L¹ integrability of the periodised mollifier justify the full covariance
Fubini calculation. In particular the double massive-kernel average of the forcing covariance
is the squared L² norm of the mollified kernel. No Fubini input is left as a hypothesis.

Source: the statement, equation (2.2) and Definition 2.5.
-/

public noncomputable section

open MeasureTheory Real

namespace RegularityStructures.Phi43

theorem integrable_massive_mollifierAt_covariance_product
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε)
    (z : SpaceTime) :
    Integrable (fun q : (SpaceTime × SpaceTime) × SpaceTime =>
      massiveHeatKernel (z - q.1.1) * massiveHeatKernel (z - q.1.2) *
        mollifierAt ρ ε q.1.1 q.2 * mollifierAt ρ ε q.1.2 q.2)
      (((volume : Measure SpaceTime).prod volume).prod volume) := by
  let φ : SpaceTime → ℝ := fun x => massiveHeatKernel (z - x)
  let k : SpaceTime → SpaceTime → ℝ := mollifierAt ρ ε
  obtain ⟨D, hD⟩ := bounded_periodise ρ hρ hε
  let M : ℝ := ∫ v : SpaceTime, |periodise ρ ε v|
  have hφm : Measurable φ := measurable_massiveHeatKernel.comp (measurable_const.sub measurable_id)
  have hφi : Integrable φ := integrable_comp_sub_left_spaceTime integrable_massiveHeatKernel z
  have hkm : Measurable (fun q : SpaceTime × SpaceTime => k q.1 q.2) :=
    (measurable_periodise ρ hρ).comp (measurable_fst.sub measurable_snd)
  have hki (x : SpaceTime) : Integrable (k x) :=
    integrable_comp_sub_left_spaceTime (integrable_periodise ρ hρ hε) x
  have hki2 (x y : SpaceTime) : Integrable (fun v => k x v * k y v) :=
    (memLp_mollifierAt ρ hρ hε x).integrable_mul (memLp_mollifierAt ρ hρ hε y)
  have hnorm (x y : SpaceTime) : (∫ v, |k x v * k y v|) ≤ D * M := by
    calc
      _ ≤ ∫ v : SpaceTime, D * |k y v| := by
        apply integral_mono (hki2 x y).norm ((hki y).norm.const_mul D)
        intro v
        change |k x v * k y v| ≤ D * |k y v|
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hD (x - v)) (abs_nonneg _)
      _ = D * M := by
        rw [integral_const_mul]
        congr 1
        exact integral_comp_sub_left_spaceTime (fun v => |periodise ρ ε v|) y
  let H : (SpaceTime × SpaceTime) × SpaceTime → ℝ := fun q =>
    (φ q.1.1 * φ q.1.2) * (k q.1.1 q.2 * k q.1.2 q.2)
  have hHm : Measurable H :=
    ((hφm.comp (measurable_fst.comp measurable_fst)).mul
      (hφm.comp (measurable_snd.comp measurable_fst))).mul
      ((hkm.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul
        (hkm.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
  have hHi : Integrable H (((volume : Measure SpaceTime).prod volume).prod volume) := by
    apply (integrable_prod_iff hHm.aestronglyMeasurable).mpr
    constructor
    · filter_upwards [] with q
      exact (hki2 q.1 q.2).const_mul (φ q.1 * φ q.2)
    · apply ((hφi.norm.mul_prod hφi.norm).mul_const (D * M)).mono'
        hHm.aestronglyMeasurable.norm.integral_prod_right'
      filter_upwards [] with q
      rw [Real.norm_of_nonneg (integral_nonneg fun v => norm_nonneg _)]
      calc
        _ = (‖φ q.1‖ * ‖φ q.2‖) * ∫ v, |k q.1 v * k q.2 v| := by
          simp only [H, norm_mul, Real.norm_eq_abs, abs_mul]
          exact integral_const_mul _ _
        _ ≤ (‖φ q.1‖ * ‖φ q.2‖) * (D * M) :=
          mul_le_mul_of_nonneg_left (hnorm q.1 q.2)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  apply hHi.congr
  filter_upwards [] with q
  dsimp [H, φ, k]
  ring

theorem integral_massive_mollifierAt_covariance_pair_eq
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε)
    (z : SpaceTime) :
    (∫ x : SpaceTime, ∫ y : SpaceTime,
      massiveHeatKernel (z - x) * massiveHeatKernel (z - y) *
        (∫ v : SpaceTime, mollifierAt ρ ε x v * mollifierAt ρ ε y v)) =
      ∫ v : SpaceTime, mollifiedKernel ρ ε (z - v) ^ 2 := by
  let H : (SpaceTime × SpaceTime) × SpaceTime → ℝ := fun q =>
    massiveHeatKernel (z - q.1.1) * massiveHeatKernel (z - q.1.2) *
      mollifierAt ρ ε q.1.1 q.2 * mollifierAt ρ ε q.1.2 q.2
  have hHi : Integrable H (((volume : Measure SpaceTime).prod volume).prod volume) :=
    integrable_massive_mollifierAt_covariance_product ρ hρ hε z
  have hin (q : SpaceTime × SpaceTime) :
      ∫ v, H (q, v) = massiveHeatKernel (z - q.1) * massiveHeatKernel (z - q.2) *
        ∫ v : SpaceTime, mollifierAt ρ ε q.1 v * mollifierAt ρ ε q.2 v := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with v
    dsimp [H]
    ring
  have hcov : Integrable (fun q : SpaceTime × SpaceTime =>
      massiveHeatKernel (z - q.1) * massiveHeatKernel (z - q.2) *
        ∫ v : SpaceTime, mollifierAt ρ ε q.1 v * mollifierAt ρ ε q.2 v)
      ((volume : Measure SpaceTime).prod volume) := by
    apply hHi.integral_prod_left.congr
    exact Filter.Eventually.of_forall hin
  calc
    _ = ∫ q : SpaceTime × SpaceTime, (∫ v, H (q, v))
        ∂((volume : Measure SpaceTime).prod volume) := by
      rw [← integral_prod _ hcov]
      simp_rw [hin]
    _ = ∫ v : SpaceTime, ∫ q : SpaceTime × SpaceTime, H (q, v)
        ∂((volume : Measure SpaceTime).prod volume) :=
      integral_integral_swap hHi
    _ = ∫ v : SpaceTime, mollifiedKernel ρ ε (z - v) ^ 2 := by
      apply integral_congr_ae
      filter_upwards [] with v
      rw [← integral_massiveHeatKernel_mul_mollifierAt_eq_mollifiedKernel ρ z v]
      rw [pow_two, ← integral_prod_mul]
      apply integral_congr_ae
      filter_upwards [] with q
      dsimp [H]
      ring

end RegularityStructures.Phi43

end
