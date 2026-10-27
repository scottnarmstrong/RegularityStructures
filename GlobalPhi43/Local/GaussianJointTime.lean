/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import RegularityStructures.PDE.HeatTime
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import RegularityStructures.Analysis.Parabolic.Basic

/-! Differentiation of the actual Gaussian average of a space-time test.
The differentiation formula assumes global bounds on the test and its derivative. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures RegularityStructures.PDE MeasureTheory Filter Topology Set Real

/-- Differentiate jointly in time and in the parabolically rescaled spatial
argument, with an integrable Gaussian bound valid on a time neighbourhood. -/
theorem hasDerivAt_gaussian_joint_average
    {φ : ParabolicSpace → ℝ} {Dφ : ParabolicSpace → ParabolicSpace →L[ℝ] ℝ}
    (hφ : ∀ p, HasFDerivAt φ (Dφ p) p) (hDc : Continuous Dφ) {B C : ℝ}
    (hB : ∀ p, |φ p| ≤ B) (hC : ∀ p, ‖Dφ p‖ ≤ C)
    {t : ℝ} (ht : 0 < t) (y : Fin 3 → ℝ) :
    HasDerivAt (fun s => ∫ z : Fin 3 → ℝ, gaussKernel 1 z * φ (s, y - √s • z))
      (∫ z : Fin 3 → ℝ, gaussKernel 1 z * Dφ (t, y - √t • z) (1, -(2 * √t)⁻¹ • z)) t := by
  have hfc : Continuous φ := continuous_iff_continuousAt.2 fun p => (hφ p).continuousAt
  have hC0 : 0 ≤ C := (norm_nonneg (Dφ 0)).trans (hC 0)
  let F' : ℝ → (Fin 3 → ℝ) → ℝ := fun s z =>
    gaussKernel 1 z * Dφ (s, y - √s • z) (1, -(2 * √s)⁻¹ • z)
  have hdiff : ∀ z, ∀ s, 0 < s →
      HasDerivAt (fun s => gaussKernel 1 z * φ (s, y - √s • z)) (F' s z) s := by
    intro z s hs
    have h1 : HasDerivAt (fun s => y - √s • z) (-(2 * √s)⁻¹ • z) s := by
      simpa [one_div, neg_smul] using ((Real.hasDerivAt_sqrt hs.ne').smul_const z).const_sub y
    exact ((hφ _).comp_hasDerivAt s ((hasDerivAt_id s).prodMk h1)).const_mul (gaussKernel 1 z)
  let c : ℝ := (2 * √(t / 2))⁻¹
  have ht2 : 0 < t / 2 := half_pos ht
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hbound : ∀ z, ∀ s ∈ Metric.ball t (t / 2),
      ‖F' s z‖ ≤ C * (gaussKernel 1 z + c * (‖z‖ * gaussKernel 1 z)) := by
    intro z s hs
    have hs' : t / 2 < s := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs
      linarith
    have hs0 : 0 < s := lt_trans ht2 hs'
    have hsq := Real.sqrt_le_sqrt hs'.le
    have hsq0 : 0 < √(t / 2) := Real.sqrt_pos.2 ht2
    have hi : (2 * √s)⁻¹ ≤ c := inv_anti₀ (by positivity) (by linarith)
    have hn : ‖((1 : ℝ), -(2 * √s)⁻¹ • z)‖ ≤ 1 + c * ‖z‖ := by
      rw [Prod.norm_def, norm_one, norm_smul, norm_neg, Real.norm_of_nonneg (by positivity)]
      apply max_le
      · linarith [mul_nonneg hc0 (norm_nonneg z)]
      · nlinarith [mul_le_mul_of_nonneg_right hi (norm_nonneg z)]
    calc
      ‖F' s z‖ = gaussKernel 1 z * ‖Dφ (s, y - √s • z) (1, -(2 * √s)⁻¹ • z)‖ := by
        dsimp [F']; rw [abs_mul, abs_of_nonneg (gaussKernel_one_nonneg z)]
      _ ≤ gaussKernel 1 z * (C * (1 + c * ‖z‖)) := by
        apply mul_le_mul_of_nonneg_left _ (gaussKernel_one_nonneg z)
        exact ((Dφ _).le_opNorm _).trans (mul_le_mul (hC _) hn (norm_nonneg _) hC0)
      _ = _ := by ring
  have hi : Integrable (fun z : Fin 3 → ℝ => gaussKernel 1 z * φ (t, y - √t • z)) := by
    apply (integrable_gaussKernel_one.mul_const B).mono'
      (by fun_prop : Continuous (fun z : Fin 3 → ℝ => gaussKernel 1 z * φ (t, y - √t • z))).aestronglyMeasurable
    apply ae_of_all
    intro z
    rw [norm_mul, Real.norm_of_nonneg (gaussKernel_one_nonneg z), Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hB _) (gaussKernel_one_nonneg z)
  have hib : Integrable (fun z : Fin 3 → ℝ => C * (gaussKernel 1 z + c * (‖z‖ * gaussKernel 1 z))) :=
    (integrable_gaussKernel_one.add (integrable_norm_mul_gaussKernel_one.const_mul c)).const_mul C
  have hcontF : Continuous (F' t) := by dsimp [F']; fun_prop
  obtain ⟨_, hD⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun s z => gaussKernel 1 z * φ (s, y - √s • z)) (F' := F')
    (bound := fun z => C * (gaussKernel 1 z + c * (‖z‖ * gaussKernel 1 z)))
    (Metric.ball_mem_nhds t ht2)
    (Eventually.of_forall fun s => (by fun_prop : Continuous _).aestronglyMeasurable)
    hi hcontF.aestronglyMeasurable (Eventually.of_forall fun z s hs => hbound z s hs) hib
    (Eventually.of_forall fun z s hs => hdiff z s (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs
      linarith))
  exact hD

end GlobalPhi43.Local
