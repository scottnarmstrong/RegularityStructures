/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2DiagramBasic
public import Phi43.BPHZ.TreeI3Psi2DiagramPointwise
public import Phi43.BPHZ.TreeI3PsiPrincipal
public import RegularityStructures.Probability.SpaceTimeMeasure

/-!
# Basic integrability facts for the chaos-`1` part of `I(Ψ³)Ψ²`

Let `J` be a measurable kernel which is bounded and integrable (these qualitative properties
never enter the constants) and `Q(x) = ∫ J(x + w) J(w) dw`.  We record

* integrability of functions with a singular bound on a time slab (`integrable_of_slab_bound`);
* boundedness and evenness of `Q`;
* the identity `∫ J(a - y) J(b - y) dy = Q(a - b)`;
* integrability of `δK(z, ·)`, of `K Q²` and of `δK(z, ·) Q(· - z)²`.
-/

public section

open MeasureTheory

namespace RegularityStructures

/-- On the slab `|t| ≤ T` the parabolic size is at most `√T + 1`. -/
theorem torusParabolicSize_le_sqrt_add_one {w : SpaceTime} {T : ℝ} (hw : |w.1| ≤ T) :
    torusParabolicSize w ≤ √T + 1 := by
  have h1 : √|w.1| ≤ √T := Real.sqrt_le_sqrt hw
  have h2 := torusSpatialNorm_le_seven_eighth w.2
  unfold torusParabolicSize
  linarith

/-- A measurable function with a singular bound of order `p < 5`, supported on a time slab, is
integrable. -/
theorem integrable_of_slab_bound {f : SpaceTime → ℝ} {B p T : ℝ} (hB : 0 ≤ B) (hf : Measurable f) (hp : 0 < p)
    (hp5 : p < 5) (hs : ∀ x : SpaceTime, T < |x.1| → f x = 0)
    (hb : ∀ x, 0 < torusParabolicSize x → |f x| ≤ B * torusParabolicSize x ^ (-p)) :
    Integrable f := by
  have iL := integrable_singularLocalWeight hp hp5 (by positivity : 0 < √|T| + 1)
  refine Integrable.mono' (iL.const_mul B) hf.aestronglyMeasurable ?_
  filter_upwards [ae_torusParabolicSize_pos_spaceTime] with x hx
  rw [Real.norm_eq_abs]
  by_cases hT : |x.1| ≤ T
  · have h3 := torusParabolicSize_le_sqrt_add_one hT
    have h4 : √T ≤ √|T| := Real.sqrt_le_sqrt (le_abs_self T)
    have : singularLocalWeight p (√|T| + 1) x = torusParabolicSize x ^ (-p) := by
      simp [singularLocalWeight, hx, show torusParabolicSize x ≤ √|T| + 1 by linarith]
    rw [this]
    exact hb x hx
  · rw [hs x (not_le.1 hT), abs_zero]
    exact mul_nonneg hB (singularLocalWeight_nonneg _ _ _)

/-- `Q = J ⋆ J^-` is bounded by `M ‖J‖₁` when `J` is bounded by `M`. -/
theorem abs_Q_le_of_hQJ {J Q : SpaceTime → ℝ} {M : ℝ} (hJm : Measurable J)
    (hJb : ∀ x, |J x| ≤ M) (hJi : Integrable J) (hQJ : ∀ x, Q x = ∫ w, J (x + w) * J w)
    (x : SpaceTime) : |Q x| ≤ M * ∫ w, |J w| := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hJb 0)
  have i1 : Integrable (fun w => M * |J w|) := hJi.norm.const_mul M
  have i2 : Integrable (fun w => |J (x + w) * J w|) := by
    have hm : Measurable (fun w => J (x + w) * J w) :=
      (hJm.comp (measurable_const.add measurable_id)).mul hJm
    refine Integrable.mono' i1 (continuous_abs.measurable.comp hm).aestronglyMeasurable (Filter.Eventually.of_forall fun w => ?_)
    rw [Real.norm_eq_abs, abs_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hJb _) (abs_nonneg _)
  rw [hQJ x]
  calc |∫ w, J (x + w) * J w| ≤ ∫ w, |J (x + w) * J w| := by
        simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun w => J (x + w) * J w)
    _ ≤ ∫ w, M * |J w| := by
        refine integral_mono i2 i1 fun w => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hJb _) (abs_nonneg _)
    _ = _ := by rw [integral_const_mul]

/-- `∫ J(a - y) J(b - y) dy = Q(a - b)`. -/
theorem integral_J_mul_J {J Q : SpaceTime → ℝ} (hQJ : ∀ x, Q x = ∫ w, J (x + w) * J w)
    (a b : SpaceTime) : ∫ y, J (a - y) * J (b - y) = Q (a - b) := by
  have h := integral_comp_sub_left_spaceTime (fun y => J (a - y) * J (b - y)) b
  rw [← h, hQJ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  have e1 : a - (b - w) = a - b + w := by abel
  have e2 : b - (b - w) = w := by abel
  simp only [e1, e2]

/-- A kernel with a singular bound of order `3` supported in `|t| ≤ 1` is integrable. -/
theorem integrable_K {K : SpaceTime → ℝ} {B : ℝ} (hB : 0 ≤ B) (hKm : Measurable K)
    (hKs : ∀ x : SpaceTime, 1 < |x.1| → K x = 0)
    (hK : ∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ))) :
    Integrable K :=
  integrable_of_slab_bound hB hKm (by norm_num) (by norm_num) hKs hK

/-- The recentred kernel `δK(z, ·)` is integrable. -/
theorem integrable_i3Psi2dK {K : SpaceTime → ℝ} (hKi : Integrable K) (z : SpaceTime) :
    Integrable (fun w => i3Psi2dK K z w) :=
  (integrable_comp_sub_left_spaceTime hKi z).sub (hKi.comp_neg)

end RegularityStructures

end
