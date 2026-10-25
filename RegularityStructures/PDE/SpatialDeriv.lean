/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.PDE.Duhamel
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Spatial derivatives commute with the heat operator and the Duhamel integral

If `g ∈ C(T³, E)` has a continuous derivative `Dg` (on the periodic lift), then so does
`P_t g`, with derivative `P_t Dg`. If every `h(s)` has derivative `Dh(s)` and `Dh` is a continuous
path, then the Duhamel integral `∫₀ᵗ P_{t-s} h(s) ds` has derivative `∫₀ᵗ P_{t-s} Dh(s) ds`.
Both are differentiation under the integral sign with the derivative falling on the data.
-/

public section

open MeasureTheory Set Filter Topology Real
open scoped Interval

namespace RegularityStructures.PDE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `P_t` maps `C¹` functions to `C¹` functions, and `D (P_t g) = P_t (D g)`. -/
theorem hasTorusDeriv_heatOp [CompleteSpace E] {g : C(Torus3, E)} {Dg : C(Torus3, Fin 3 → E)}
    (hg : HasTorusDeriv g Dg) (t : ℝ) : HasTorusDeriv (heatOp t g) (heatOp t Dg) := by
  intro y
  simp_rw [heatOp_torusProj]
  have hdiff : ∀ (z y' : Fin 3 → ℝ), HasFDerivAt
      (fun y' : Fin 3 → ℝ => gaussKernel 1 z • g (torusProj (y' - √t • z)))
      (gaussKernel 1 z • ofPartials (Dg (torusProj (y' - √t • z)))) y' := by
    intro z y'
    have h1 : HasFDerivAt (fun y' : Fin 3 → ℝ => g (torusProj (y' - √t • z)))
        (ofPartials (Dg (torusProj (y' - √t • z)))) y' := by
      have := (hg (y' - √t • z)).comp y' ((hasFDerivAt_id y').sub_const (√t • z))
      simpa [Function.comp_def] using this
    exact h1.const_smul (gaussKernel 1 z)
  have hint : ∫ z, gaussKernel 1 z • ofPartials (Dg (torusProj (y - √t • z))) =
      ofPartials (∫ z, gaussKernel 1 z • Dg (torusProj (y - √t • z))) := by
    have hs : ∀ z, gaussKernel 1 z • ofPartials (Dg (torusProj (y - √t • z))) =
        ofPartials (gaussKernel 1 z • Dg (torusProj (y - √t • z))) := fun z => (map_smul _ _ _).symm
    simp_rw [hs]
    exact ofPartials.integral_comp_comm
      (by simpa [torusProj_sub] using integrable_heatOp_integrand Dg t (torusProj y))
  rw [← hint]
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (s := univ) (bound := fun z =>
      gaussKernel 1 z * (‖(ofPartials : (Fin 3 → E) →L[ℝ] (Fin 3 → ℝ) →L[ℝ] E)‖ * ‖Dg‖))
    univ_mem (Eventually.of_forall fun y' => ?_) ?_ ?_ ?_
    (integrable_gaussKernel_one.mul_const _) (Eventually.of_forall fun z y' _ => hdiff z y')
  · simpa [torusProj_sub] using
      (continuous_heatOp_integrand_right g t (torusProj y')).aestronglyMeasurable
  · simpa [torusProj_sub] using integrable_heatOp_integrand g t (torusProj y)
  · exact (continuous_gaussKernel_one.smul (ofPartials.continuous.comp (Dg.continuous.comp
      (continuous_torusProj.comp (by fun_prop))))).aestronglyMeasurable
  · refine Eventually.of_forall fun z y' _ => ?_
    rw [norm_smul, Real.norm_of_nonneg (gaussKernel_one_nonneg z)]
    exact mul_le_mul_of_nonneg_left (((ofPartials (E := E)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (Dg.norm_coe_le_norm _) (norm_nonneg _)))
      (gaussKernel_one_nonneg z)

variable [CompleteSpace E]

/-- The Duhamel integral maps `C¹` paths to `C¹` functions, and
`D ∫₀ᵗ P_{t-s} h(s) ds = ∫₀ᵗ P_{t-s} Dh(s) ds`. -/
theorem hasTorusDeriv_duhamel {h : ℝ → C(Torus3, E)} {Dh : ℝ → C(Torus3, Fin 3 → E)}
    (hh : Continuous h) (hDh : Continuous Dh) {t : ℝ} (ht : 0 ≤ t)
    (hd : ∀ s ∈ Icc 0 t, HasTorusDeriv (h s) (Dh s)) :
    HasTorusDeriv (duhamel h t) (duhamel Dh t) := by
  intro y
  have heq : (fun y' => duhamel h t (torusProj y')) =
      fun y' => ∫ s in (0 : ℝ)..t, heatOp (t - s) (h s) (torusProj y') := by
    funext y'
    exact duhamel_apply hh t _
  rw [heq, duhamel_apply hDh]
  have hcont : ∀ y' : Fin 3 → ℝ, Continuous fun s => heatOp (t - s) (h s) (torusProj y') :=
    fun y' => (continuous_eval_const (torusProj y')).comp
      ((continuous_duhamel_integrand hh).comp (Continuous.prodMk continuous_const continuous_id))
  have hcont' : Continuous fun s => heatOp (t - s) (Dh s) (torusProj y) :=
    (continuous_eval_const (torusProj y)).comp
      ((continuous_duhamel_integrand hDh).comp (Continuous.prodMk continuous_const continuous_id))
  have hint : ∫ s in (0 : ℝ)..t, ofPartials (heatOp (t - s) (Dh s) (torusProj y)) =
      ofPartials (∫ s in (0 : ℝ)..t, heatOp (t - s) (Dh s) (torusProj y)) :=
    ContinuousLinearMap.intervalIntegral_comp_comm (𝕜 := ℝ) (E := Fin 3 → E)
      (F := (Fin 3 → ℝ) →L[ℝ] E) (ofPartials (E := E)) (hcont'.intervalIntegrable 0 t)
  rw [← hint]
  set C : ℝ := ‖(ofPartials : (Fin 3 → E) →L[ℝ] (Fin 3 → ℝ) →L[ℝ] E)‖ with hC
  have hbound_int : IntervalIntegrable (fun s => C * ‖Dh s‖) volume 0 t := by
    have : Continuous fun s => ‖Dh s‖ := continuous_norm.comp hDh
    exact (continuous_const.mul this).intervalIntegrable 0 t
  have hF'meas : AEStronglyMeasurable
      (fun s => ofPartials (heatOp (t - s) (Dh s) (torusProj y))) (volume.restrict (Ι 0 t)) :=
    ((ofPartials (E := E)).continuous.comp hcont').aestronglyMeasurable
  have hbound : ∀ᵐ s ∂volume, s ∈ Ι 0 t → ∀ y' ∈ (univ : Set (Fin 3 → ℝ)),
      ‖ofPartials (heatOp (t - s) (Dh s) (torusProj y'))‖ ≤ C * ‖Dh s‖ :=
    Eventually.of_forall fun s _ y' _ => ((ofPartials (E := E)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (norm_heatOp_apply_le _ _ _) (norm_nonneg _))
  have hdiff : ∀ᵐ s ∂volume, s ∈ Ι 0 t → ∀ y' ∈ (univ : Set (Fin 3 → ℝ)),
      HasFDerivAt (fun y' => heatOp (t - s) (h s) (torusProj y'))
        (ofPartials (heatOp (t - s) (Dh s) (torusProj y'))) y' := by
    refine Eventually.of_forall fun s hs y' _ => ?_
    rw [uIoc_of_le ht] at hs
    exact hasTorusDeriv_heatOp (hd s (Ioc_subset_Icc_self hs)) (t - s) y'
  exact intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le univ_mem
    (Eventually.of_forall fun y' => (hcont y').aestronglyMeasurable)
    ((hcont y).intervalIntegrable _ _) hF'meas hbound hbound_int hdiff

end RegularityStructures.PDE

end
