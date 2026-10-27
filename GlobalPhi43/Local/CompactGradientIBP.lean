/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.MeasureTheory.Integral.CompactlySupported
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Tactic

/-! Remove the derivative of h from a compact cutoff-gradient term.
Every integrability obligation follows from compact cutoff support. -/
public noncomputable section

namespace GlobalPhi43.Local

open MeasureTheory
open scoped ContDiff

 theorem compact_gradient_integration_by_parts {k a h : (Fin 3 → ℝ) → ℝ}
    (hk : ContDiff ℝ 1 k) (ha : ContDiff ℝ 1 a) (hh : ContDiff ℝ 1 h)
    (hca : HasCompactSupport a) (v : Fin 3 → ℝ) :
    (∫ z : Fin 3 → ℝ, (k z * a z) * fderiv ℝ h z v) =
      -(∫ z : Fin 3 → ℝ, (fderiv ℝ k z v * a z + k z * fderiv ℝ a z v) * h z) := by
  let f : (Fin 3 → ℝ) → ℝ := fun z => k z * a z
  have hf : ContDiff ℝ 1 f := hk.mul ha
  have hcf : HasCompactSupport f := hca.mul_left
  have hdfc : Continuous (fun z => fderiv ℝ f z v) :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdhc : Continuous (fun z => fderiv ℝ h z v) :=
    (hh.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hi1 : Integrable (fun z => fderiv ℝ f z v * h z) :=
    (hdfc.mul hh.continuous).integrable_of_hasCompactSupport (hcf.fderiv_apply ℝ v).mul_right
  have hi2 : Integrable (fun z => f z * fderiv ℝ h z v) :=
    (hf.continuous.mul hdhc).integrable_of_hasCompactSupport hcf.mul_right
  have hi3 : Integrable (fun z => f z * h z) :=
    (hf.continuous.mul hh.continuous).integrable_of_hasCompactSupport hcf.mul_right
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) hi1 hi2 hi3
    (fun z _ => hf.differentiable one_ne_zero z) (fun z _ => hh.differentiable one_ne_zero z)
  have he (z : Fin 3 → ℝ) : fderiv ℝ f z v =
      fderiv ℝ k z v * a z + k z * fderiv ℝ a z v := by
    have hm := ((hk.differentiable one_ne_zero z).hasFDerivAt.mul
      (ha.differentiable one_ne_zero z).hasFDerivAt).fderiv
    change fderiv ℝ (k * a) z v = _
    rw [hm]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  simp_rw [he] at hibp
  exact hibp

end GlobalPhi43.Local
