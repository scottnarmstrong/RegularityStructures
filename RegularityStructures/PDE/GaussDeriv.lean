/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.PDE.HeatOp
public import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Derivative and first moment of the unit Gaussian on `ℝ³`

For `γ₁ = gaussKernel 1`:

* `integrable_norm_mul_gaussKernel_one`: `z ↦ |z| γ₁(z)` is integrable;
* `fderiv_gaussKernel_one_single`: `∂_i γ₁(z) = -(z_i / 2) γ₁(z)`.

These are the inputs of the integration by parts behind `∂_t P_t g = P_t Δg`.
-/

public section

open MeasureTheory Real Filter

namespace RegularityStructures.PDE

/-- `|z_i| γ₁(z)` is integrable on `ℝ³`. -/
theorem integrable_abs_mul_gaussKernel_one (i : Fin 3) :
    Integrable fun z : Fin 3 → ℝ => |z i| * gaussKernel 1 z := by
  have hb : 0 < (4 * (1 : ℝ))⁻¹ := by norm_num
  let f : Fin 3 → ℝ → ℝ := fun l v =>
    (if l = i then |v| else 1) * exp (-(4 * (1 : ℝ))⁻¹ * v ^ 2)
  have hf : ∀ l, Integrable (f l) := by
    intro l
    by_cases h : l = i
    · have := (integrable_mul_exp_neg_mul_sq hb).abs
      refine this.congr (Eventually.of_forall fun v => ?_)
      simp only [f, h, ite_true, abs_mul, abs_of_pos (exp_pos _)]
    · simpa [f, h] using integrable_exp_neg_mul_sq hb
  have h := (Integrable.fintype_prod (ι := Fin 3) (μ := fun _ => (volume : Measure ℝ))
    (f := f) hf).const_mul ((4 * π * 1) ^ (-(3 : ℝ) / 2))
  refine h.congr (Eventually.of_forall fun z => ?_)
  simp only [f, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, ite_true]
  rw [gaussKernel_eq_prod]
  ring

/-- `|z| γ₁(z)` is integrable on `ℝ³`. -/
theorem integrable_norm_mul_gaussKernel_one :
    Integrable fun z : Fin 3 → ℝ => ‖z‖ * gaussKernel 1 z := by
  have hsum : Integrable fun z : Fin 3 → ℝ => ∑ i, |z i| * gaussKernel 1 z :=
    integrable_finsetSum _ fun i _ => integrable_abs_mul_gaussKernel_one i
  refine hsum.mono' (continuous_norm.mul continuous_gaussKernel_one).aestronglyMeasurable
    (Eventually.of_forall fun z => ?_)
  have hγ := gaussKernel_one_nonneg z
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg z) hγ), ← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ hγ
  refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg (z i))).2 fun i => ?_
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun j => |z j|) (fun j _ => abs_nonneg (z j))
    (Finset.mem_univ i)

theorem sqNorm3_add_smul_single (z : Fin 3 → ℝ) (i : Fin 3) (r : ℝ) :
    sqNorm3 (z + r • Pi.single i 1) = sqNorm3 z + 2 * r * z i + r ^ 2 := by
  unfold sqNorm3
  fin_cases i <;> simp [Fin.sum_univ_three, Pi.single_apply] <;> ring

theorem differentiable_gaussKernel_one : Differentiable ℝ (gaussKernel 1) := by
  unfold gaussKernel sqNorm3
  fun_prop

/-- `∂_i γ₁(z) = -(z_i / 2) γ₁(z)`. -/
theorem fderiv_gaussKernel_one_single (z : Fin 3 → ℝ) (i : Fin 3) :
    fderiv ℝ (gaussKernel 1) z (Pi.single i 1) = -(z i / 2) * gaussKernel 1 z := by
  have hline : HasDerivAt (fun r : ℝ => z + r • (Pi.single i 1 : Fin 3 → ℝ))
      (Pi.single i 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single i 1 : Fin 3 → ℝ)).const_add z
  have h1 := (differentiable_gaussKernel_one
    (z + (0 : ℝ) • Pi.single i 1)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hline
  simp only [zero_smul, add_zero] at h1
  have hfun : (fun r : ℝ => gaussKernel 1 (z + r • Pi.single i 1)) = fun r =>
      (4 * π * 1) ^ (-(3 : ℝ) / 2) * exp (-(sqNorm3 z + 2 * r * z i + r ^ 2) / (4 * 1)) := by
    funext r
    rw [gaussKernel, sqNorm3_add_smul_single]
  have h2 : HasDerivAt (fun r : ℝ => (4 * π * 1) ^ (-(3 : ℝ) / 2) *
      exp (-(sqNorm3 z + 2 * r * z i + r ^ 2) / (4 * 1))) (-(z i / 2) * gaussKernel 1 z) 0 := by
    have hp : HasDerivAt (fun r : ℝ => -(sqNorm3 z + 2 * r * z i + r ^ 2) / (4 * 1))
        (-(2 * z i) / 4) 0 := by
      have := ((((hasDerivAt_id (0 : ℝ)).const_mul (2 * z i)).add
        ((hasDerivAt_id (0 : ℝ)).pow 2)).const_add (sqNorm3 z)).neg.div_const (4 * 1)
      convert this using 1
      · funext r
        simp
        ring
      · simp
    have := (hp.exp).const_mul ((4 * π * 1) ^ (-(3 : ℝ) / 2))
    convert this using 1
    rw [gaussKernel]
    simp only [mul_zero, zero_mul, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow]
    ring
  rw [← hfun] at h2
  exact h1.unique h2

end RegularityStructures.PDE

end
