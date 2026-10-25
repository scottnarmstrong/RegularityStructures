/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Heat kernels on the three-torus

* `gaussKernel t y = (4πt)^{-3/2} exp(-|y|²/(4t))`, the heat kernel on `ℝ³`;
* `heatKernel t`, its periodisation `p_t` on `T³` (the statement, equation (2.1));
* `heatSemigroup s f`, the heat semigroup `P_s` acting on `C(T³)` by convolution with the Gaussian
  on `ℝ³`;
* `massiveHeatKernel`, the kernel `G(t, x) = 1_{t>0} e^{-t} p_t(x)` of `(∂_t - Δ + 1)⁻¹`
  (equation (2.2)).

The lemmas show that `gaussKernel s` is a probability density for `s > 0`, so `P_s` is linear
and contracts the supremum norm.

Source: the statement, Section 2.
-/

@[expose] public noncomputable section

open MeasureTheory Real

namespace RegularityStructures

/-- The heat kernel on `ℝ³`: `gaussKernel t y = (4πt)^{-3/2} exp(-|y|²/(4t))`. -/
def gaussKernel (t : ℝ) (y : Fin 3 → ℝ) : ℝ :=
  (4 * π * t) ^ (-(3 : ℝ) / 2) * exp (-sqNorm3 y / (4 * t))

/-- The heat kernel on `T³`, `p_t(x) = ∑_{k ∈ ℤ³} (4πt)^{-3/2} exp(-|x + k|²/(4t))`, evaluated at the
representative of `x` in `[0, 1)³`. -/
def heatKernel (t : ℝ) (x : Torus3) : ℝ :=
  ∑' k : Fin 3 → ℤ, gaussKernel t (torusRep x + fun i => (k i : ℝ))

/-- The heat semigroup on `T³`: `(P_s f)(x) = ∫_{ℝ³} γ_s(y) f(x - y) dy`, where `γ_s` is the
heat kernel on `ℝ³` and `x - y` is taken in `T³`. -/
def heatSemigroup (s : ℝ) (f : C(Torus3, ℝ)) (x : Torus3) : ℝ :=
  ∫ y : Fin 3 → ℝ, gaussKernel s y * f (x - torusProj y)

/-- The massive space-time heat kernel `G(t, x) = 1_{t>0} e^{-t} p_t(x)` on `ℝ × T³`. -/
def massiveHeatKernel (z : SpaceTime) : ℝ :=
  if 0 < z.1 then exp (-z.1) * heatKernel z.1 z.2 else 0

end RegularityStructures

end

/-! ### The Gaussian density on `ℝ³` -/

public section

open MeasureTheory Real

namespace RegularityStructures

theorem gaussKernel_eq_prod (t : ℝ) (y : Fin 3 → ℝ) :
    gaussKernel t y = (4 * π * t) ^ (-(3 : ℝ) / 2) * ∏ i, exp (-(4 * t)⁻¹ * y i ^ 2) := by
  have h : -(∑ i, y i ^ 2) / (4 * t) = ∑ i, -(4 * t)⁻¹ * y i ^ 2 := by
    rw [← Finset.mul_sum]
    ring
  rw [gaussKernel, ← Real.exp_sum, sqNorm3, h]

theorem gaussKernel_nonneg {t : ℝ} (ht : 0 < t) (y : Fin 3 → ℝ) : 0 ≤ gaussKernel t y := by
  unfold gaussKernel
  have : 0 < 4 * π * t := by positivity
  positivity

theorem integrable_gaussKernel {s : ℝ} (hs : 0 < s) : Integrable (gaussKernel s) := by
  have hb : 0 < (4 * s)⁻¹ := by positivity
  have h := Integrable.fintype_prod (ι := Fin 3) (μ := fun _ => (volume : Measure ℝ))
    (f := fun _ v => exp (-(4 * s)⁻¹ * v ^ 2)) fun _ => integrable_exp_neg_mul_sq hb
  have h' := h.const_mul ((4 * π * s) ^ (-(3 : ℝ) / 2))
  refine h'.congr (Filter.Eventually.of_forall fun y => ?_)
  simp only
  rw [gaussKernel_eq_prod]

theorem integral_gaussKernel {s : ℝ} (hs : 0 < s) : ∫ y, gaussKernel s y = 1 := by
  have ha : 0 < 4 * π * s := by positivity
  simp_rw [gaussKernel_eq_prod]
  rw [integral_const_mul]
  rw [integral_fintype_prod_volume_eq_pow (ι := Fin 3) (fun v : ℝ => exp (-(4 * s)⁻¹ * v ^ 2)),
    integral_gaussian, Fintype.card_fin]
  have hpi : π / (4 * s)⁻¹ = 4 * π * s := by field_simp
  rw [hpi, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ha.le, ← Real.rpow_add ha]
  norm_num

/-! ### The heat semigroup -/

theorem integrable_heatSemigroup_integrand {s : ℝ} (hs : 0 < s) (f : C(Torus3, ℝ))
    (x : Torus3) : Integrable fun y : Fin 3 → ℝ => gaussKernel s y * f (x - torusProj y) := by
  have hcont : Continuous fun y : Fin 3 → ℝ => f (x - torusProj y) := by
    have hp : Continuous torusProj :=
      continuous_pi fun i => (AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_apply i)
    exact f.continuous.comp (continuous_const.sub hp)
  refine (integrable_gaussKernel hs).mul_bdd (c := ‖f‖) hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => f.norm_coe_le_norm _)

theorem heatSemigroup_add {s : ℝ} (hs : 0 < s) (f g : C(Torus3, ℝ)) (x : Torus3) :
    heatSemigroup s (f + g) x = heatSemigroup s f x + heatSemigroup s g x := by
  unfold heatSemigroup
  rw [← integral_add (integrable_heatSemigroup_integrand hs f x)
    (integrable_heatSemigroup_integrand hs g x)]
  congr 1
  ext y
  simp [mul_add]

theorem heatSemigroup_neg (s : ℝ) (f : C(Torus3, ℝ)) (x : Torus3) :
    heatSemigroup s (-f) x = -heatSemigroup s f x := by
  unfold heatSemigroup
  rw [← integral_neg]
  congr 1
  ext y
  simp

theorem heatSemigroup_zero (s : ℝ) (x : Torus3) : heatSemigroup s 0 x = 0 := by
  simp [heatSemigroup]

/-! ### Values for nonpositive times

The statement defines `γ_t`, `p_t` and `P_t` only for `t > 0`. The Lean functions are total. For
`t ≤ 0` they are zero, because `(4πt)^{-3/2}` is `0` at `t = 0` and is `exp(…) cos(-3π/2) = 0` for
`t < 0`. No result uses these values. -/

theorem gaussKernel_of_nonpos {t : ℝ} (ht : t ≤ 0) (y : Fin 3 → ℝ) : gaussKernel t y = 0 := by
  unfold gaussKernel
  rcases ht.lt_or_eq with ht | rfl
  · have h4 : 4 * π * t < 0 := by nlinarith [Real.pi_pos]
    rw [Real.rpow_def_of_neg h4]
    have hc : Real.cos (-(3 : ℝ) / 2 * π) = 0 := by
      rw [show -(3 : ℝ) / 2 * π = -(π / 2) - π by ring, Real.cos_sub_pi, Real.cos_neg,
        Real.cos_pi_div_two, neg_zero]
    rw [hc, mul_zero, zero_mul]
  · simp [Real.zero_rpow (by norm_num : -(3 : ℝ) / 2 ≠ 0)]

theorem heatSemigroup_of_nonpos {s : ℝ} (hs : s ≤ 0) (f : C(Torus3, ℝ)) (x : Torus3) :
    heatSemigroup s f x = 0 := by
  simp [heatSemigroup, gaussKernel_of_nonpos hs]

/-- `P_s` contracts the supremum norm. -/
theorem norm_heatSemigroup_le {s : ℝ} (hs : 0 < s) (f : C(Torus3, ℝ)) (x : Torus3) :
    ‖heatSemigroup s f x‖ ≤ ‖f‖ := by
  unfold heatSemigroup
  calc ‖∫ y, gaussKernel s y * f (x - torusProj y)‖
      ≤ ∫ y, gaussKernel s y * ‖f‖ := by
        refine norm_integral_le_of_norm_le ((integrable_gaussKernel hs).mul_const _)
          (Filter.Eventually.of_forall fun y => ?_)
        rw [norm_mul, Real.norm_of_nonneg (gaussKernel_nonneg hs y)]
        exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (gaussKernel_nonneg hs y)
    _ = ‖f‖ := by rw [integral_mul_const, integral_gaussKernel hs, one_mul]

end RegularityStructures

end
