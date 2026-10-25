/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.PDE.HeatOp
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The heat operator is the heat semigroup of `RegularityStructures.Torus.HeatKernel`

For `t > 0` and `g ∈ C(T³)`, `heatOp t g = heatSemigroup t g`: the substitution `y = √t z` turns
`∫ γ_t(y) g(x - y) dy` into `∫ γ₁(z) g(x - √t z) dz`, because `γ₁(z) = t^{3/2} γ_t(√t z)`.

Consequently the facts proved for `heatOp` (joint continuity in `(t, g)`, `P_0 = id`, strong
continuity, commutation with translations, smoothing of derivatives, the heat equation) apply to
`heatSemigroup` for positive times.
-/

public section

open MeasureTheory Real

namespace RegularityStructures.PDE

/-- `γ₁(z) = (√t)³ γ_t(√t z)` for `t > 0`. -/
theorem gaussKernel_one_eq {t : ℝ} (ht : 0 < t) (z : Fin 3 → ℝ) :
    gaussKernel 1 z = √t ^ 3 * gaussKernel t (√t • z) := by
  have hsq : sqNorm3 (√t • z) = t * sqNorm3 z := by
    simp only [sqNorm3, Pi.smul_apply, smul_eq_mul, mul_pow, Real.sq_sqrt ht.le, Finset.mul_sum]
  have hexp : -sqNorm3 (√t • z) / (4 * t) = -sqNorm3 z / (4 * 1) := by
    rw [hsq]
    field_simp
  have hpre : √t ^ 3 * (4 * π * t) ^ (-(3 : ℝ) / 2) = (4 * π * 1) ^ (-(3 : ℝ) / 2) := by
    have h4π : 0 ≤ 4 * π := by positivity
    rw [mul_one, Real.mul_rpow h4π ht.le, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
      ← Real.rpow_mul ht.le, mul_left_comm, ← Real.rpow_add ht]
    norm_num
  rw [gaussKernel, gaussKernel, hexp, ← mul_assoc, hpre]

/-- **The heat operator is the heat semigroup.** -/
theorem heatOp_eq_heatSemigroup {t : ℝ} (ht : 0 < t) (g : C(Torus3, ℝ)) (x : Torus3) :
    heatOp t g x = heatSemigroup t g x := by
  set F : (Fin 3 → ℝ) → ℝ := fun y => gaussKernel t y * g (x - torusProj y) with hF
  have h1 : heatOp t g x = √t ^ 3 * ∫ z, F (√t • z) := by
    rw [heatOp_apply, ← integral_const_mul]
    congr 1
    funext z
    rw [smul_eq_mul, gaussKernel_one_eq ht z, hF]
    ring
  have hst : 0 < √t := Real.sqrt_pos.2 ht
  rw [h1, Measure.integral_comp_smul, Module.finrank_fin_fun, smul_eq_mul, ← mul_assoc,
    abs_of_pos (by positivity), mul_inv_cancel₀ (by positivity), one_mul]
  rfl

end RegularityStructures.PDE

end
