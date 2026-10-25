/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestTreesI2Psi2Single2
public import Phi43.BPHZ.SemigroupTestTreesI2Psi2Terms
public import Phi43.BPHZ.SemigroupTestTreesI2Psi2Alg

/-!
# The global covariance bound of `I(Ψ²) Ψ²`: abstract form

`i2Psi2CovAbs K Q x y y'` is the covariance of the field of `I(Ψ²) Ψ²`: the chaos-`4` integral, the
chaos-`2` integral and the product of the two means.  `i2Psi2CovAbs_bound_global` bounds it, for
arbitrary `x, y, y'` (no smallness) and `D` bounding `s(a - b)` on the relevant time window, by
`C (1 + D)² (1 + |y.1 - x.1| + |y'.1 - x.1|) (s(y - y')^(-2) + s(y - y')^(-1) +
s(y - y')^(-1/2) + s(x - y)^(-1/2) + s(x - y')^(-1/2))`.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The covariance of the field of `I(Ψ²) Ψ²` in terms of the kernel `K` and the covariance `Q`. -/
def i2Psi2CovAbs (K Q : SpaceTime → ℝ) (x y y' : SpaceTime) : ℝ :=
  (∫ q : SpaceTime × SpaceTime, i2Psi2Increment K x y q.1 * i2Psi2Increment K x y' q.2 *
      (4 * Q (q.1 - q.2) ^ 2 * Q (y - y') ^ 2 + 4 * Q (q.1 - y') ^ 2 * Q (y - q.2) ^ 2 +
        16 * (Q (q.1 - q.2) * Q (q.1 - y') * Q (y - q.2) * Q (y - y')))) +
  (∫ q : SpaceTime × SpaceTime, i2Psi2Increment K x y q.1 * i2Psi2Increment K x y' q.2 *
      (16 * Q (q.1 - y) * Q (q.2 - y') *
        (Q (q.1 - q.2) * Q (y - y') + Q (q.1 - y') * Q (y - q.2)))) +
  (-2 * ∫ w, K (x - w) * Q (w - y) ^ 2) * (-2 * ∫ w, K (x - w) * Q (w - y') ^ 2)

end RegularityStructures

end

public section

open MeasureTheory Set

namespace RegularityStructures

/-- The decomposition of the covariance into the six terms. -/
theorem i2Psi2CovAbs_eq {K Q : SpaceTime → ℝ} {x y y' : SpaceTime}
    (i1 : Integrable (Function.uncurry fun w v =>
      i2Psi2Increment K x y w * i2Psi2Increment K x y' v * Q (w - v) ^ 2) (volume.prod volume))
    (i3 : Integrable (Function.uncurry fun w v => i2Psi2Increment K x y w *
      i2Psi2Increment K x y' v * (Q (w - v) * Q (w - y') * Q (y - v))) (volume.prod volume))
    (i4 : Integrable (Function.uncurry fun w v => i2Psi2Increment K x y w *
      i2Psi2Increment K x y' v * (Q (w - y) * Q (v - y') * Q (w - v))) (volume.prod volume))
    (i2a : Integrable (fun w => i2Psi2Increment K x y w * Q (w - y') ^ 2))
    (i2b : Integrable (fun v => i2Psi2Increment K x y' v * Q (y - v) ^ 2))
    (i5a : Integrable (fun w => i2Psi2Increment K x y w * (Q (w - y) * Q (w - y'))))
    (i5b : Integrable (fun v => i2Psi2Increment K x y' v * (Q (v - y') * Q (y - v)))) :
    i2Psi2CovAbs K Q x y y' =
      4 * Q (y - y') ^ 2 * (∫ w, ∫ v, i2Psi2Increment K x y w * i2Psi2Increment K x y' v *
          Q (w - v) ^ 2) +
        4 * ((∫ w, i2Psi2Increment K x y w * Q (w - y') ^ 2) *
          ∫ v, i2Psi2Increment K x y' v * Q (y - v) ^ 2) +
        16 * Q (y - y') * (∫ w, ∫ v, i2Psi2Increment K x y w * i2Psi2Increment K x y' v *
          (Q (w - v) * Q (w - y') * Q (y - v))) +
        16 * Q (y - y') * (∫ w, ∫ v, i2Psi2Increment K x y w * i2Psi2Increment K x y' v *
          (Q (w - y) * Q (v - y') * Q (w - v))) +
        16 * ((∫ w, i2Psi2Increment K x y w * (Q (w - y) * Q (w - y'))) *
          ∫ v, i2Psi2Increment K x y' v * (Q (v - y') * Q (y - v))) +
        (-2 * ∫ w, K (x - w) * Q (w - y) ^ 2) * (-2 * ∫ w, K (x - w) * Q (w - y') ^ 2) := by
  have i2 : Integrable (fun q : SpaceTime × SpaceTime =>
      (i2Psi2Increment K x y q.1 * Q (q.1 - y') ^ 2) *
        (i2Psi2Increment K x y' q.2 * Q (y - q.2) ^ 2)) (volume) :=
    i2a.mul_prod i2b
  have i5 : Integrable (fun q : SpaceTime × SpaceTime =>
      (i2Psi2Increment K x y q.1 * (Q (q.1 - y) * Q (q.1 - y'))) *
        (i2Psi2Increment K x y' q.2 * (Q (q.2 - y') * Q (y - q.2)))) volume :=
    i5a.mul_prod i5b
  have e2 : ∫ q : SpaceTime × SpaceTime, (i2Psi2Increment K x y q.1 * Q (q.1 - y') ^ 2) *
      (i2Psi2Increment K x y' q.2 * Q (y - q.2) ^ 2) =
      (∫ w, i2Psi2Increment K x y w * Q (w - y') ^ 2) *
        ∫ v, i2Psi2Increment K x y' v * Q (y - v) ^ 2 :=
    integral_prod_mul (μ := (volume : Measure SpaceTime)) (ν := volume)
      (fun w => i2Psi2Increment K x y w * Q (w - y') ^ 2)
      (fun v => i2Psi2Increment K x y' v * Q (y - v) ^ 2)
  have e5 : ∫ q : SpaceTime × SpaceTime,
      (i2Psi2Increment K x y q.1 * (Q (q.1 - y) * Q (q.1 - y'))) *
        (i2Psi2Increment K x y' q.2 * (Q (q.2 - y') * Q (y - q.2))) =
      (∫ w, i2Psi2Increment K x y w * (Q (w - y) * Q (w - y'))) *
        ∫ v, i2Psi2Increment K x y' v * (Q (v - y') * Q (y - v)) :=
    integral_prod_mul (μ := (volume : Measure SpaceTime)) (ν := volume)
      (fun w => i2Psi2Increment K x y w * (Q (w - y) * Q (w - y')))
      (fun v => i2Psi2Increment K x y' v * (Q (v - y') * Q (y - v)))
  have k1 : ∫ q : SpaceTime × SpaceTime, i2Psi2Increment K x y q.1 * i2Psi2Increment K x y' q.2 *
      Q (q.1 - q.2) ^ 2 = ∫ w, ∫ v, i2Psi2Increment K x y w * i2Psi2Increment K x y' v *
        Q (w - v) ^ 2 := integral_prod _ i1
  have k3 : ∫ q : SpaceTime × SpaceTime, i2Psi2Increment K x y q.1 * i2Psi2Increment K x y' q.2 *
      (Q (q.1 - q.2) * Q (q.1 - y') * Q (y - q.2)) = ∫ w, ∫ v, i2Psi2Increment K x y w *
        i2Psi2Increment K x y' v * (Q (w - v) * Q (w - y') * Q (y - v)) := integral_prod _ i3
  have k4 : ∫ q : SpaceTime × SpaceTime, i2Psi2Increment K x y q.1 * i2Psi2Increment K x y' q.2 *
      (Q (q.1 - y) * Q (q.2 - y') * Q (q.1 - q.2)) = ∫ w, ∫ v, i2Psi2Increment K x y w *
        i2Psi2Increment K x y' v * (Q (w - y) * Q (v - y') * Q (w - v)) := integral_prod _ i4
  have pt4 : ∀ q : SpaceTime × SpaceTime,
      i2Psi2Increment K x y q.1 * i2Psi2Increment K x y' q.2 *
        (4 * Q (q.1 - q.2) ^ 2 * Q (y - y') ^ 2 + 4 * Q (q.1 - y') ^ 2 * Q (y - q.2) ^ 2 +
          16 * (Q (q.1 - q.2) * Q (q.1 - y') * Q (y - q.2) * Q (y - y'))) =
      4 * Q (y - y') ^ 2 * (i2Psi2Increment K x y q.1 * i2Psi2Increment K x y' q.2 *
          Q (q.1 - q.2) ^ 2) +
        4 * ((i2Psi2Increment K x y q.1 * Q (q.1 - y') ^ 2) *
          (i2Psi2Increment K x y' q.2 * Q (y - q.2) ^ 2)) +
        16 * Q (y - y') * (i2Psi2Increment K x y q.1 * i2Psi2Increment K x y' q.2 *
          (Q (q.1 - q.2) * Q (q.1 - y') * Q (y - q.2))) := fun q => by ring
  have pt2 : ∀ q : SpaceTime × SpaceTime,
      i2Psi2Increment K x y q.1 * i2Psi2Increment K x y' q.2 *
        (16 * Q (q.1 - y) * Q (q.2 - y') *
          (Q (q.1 - q.2) * Q (y - y') + Q (q.1 - y') * Q (y - q.2))) =
      16 * Q (y - y') * (i2Psi2Increment K x y q.1 * i2Psi2Increment K x y' q.2 *
          (Q (q.1 - y) * Q (q.2 - y') * Q (q.1 - q.2))) +
        16 * ((i2Psi2Increment K x y q.1 * (Q (q.1 - y) * Q (q.1 - y'))) *
          (i2Psi2Increment K x y' q.2 * (Q (q.2 - y') * Q (y - q.2)))) := fun q => by ring
  unfold i2Psi2CovAbs
  set A : SpaceTime → ℝ := i2Psi2Increment K x y with hA
  set A' : SpaceTime → ℝ := i2Psi2Increment K x y' with hA'
  set c : ℝ := Q (y - y') with hc
  have f1 : Integrable (fun q : SpaceTime × SpaceTime =>
      4 * c ^ 2 * (A q.1 * A' q.2 * Q (q.1 - q.2) ^ 2)) volume :=
    i1.const_mul (4 * c ^ 2)
  have f2 : Integrable (fun q : SpaceTime × SpaceTime =>
      4 * ((A q.1 * Q (q.1 - y') ^ 2) * (A' q.2 * Q (y - q.2) ^ 2))) volume :=
    i2.const_mul 4
  have f3 : Integrable (fun q : SpaceTime × SpaceTime =>
      16 * c * (A q.1 * A' q.2 * (Q (q.1 - q.2) * Q (q.1 - y') * Q (y - q.2))))
      volume := i3.const_mul (16 * c)
  have f4 : Integrable (fun q : SpaceTime × SpaceTime =>
      16 * c * (A q.1 * A' q.2 * (Q (q.1 - y) * Q (q.2 - y') * Q (q.1 - q.2))))
      volume := i4.const_mul (16 * c)
  have f5 : Integrable (fun q : SpaceTime × SpaceTime =>
      16 * ((A q.1 * (Q (q.1 - y) * Q (q.1 - y'))) * (A' q.2 * (Q (q.2 - y') * Q (y - q.2)))))
      volume := i5.const_mul 16
  have f12 : Integrable (fun q : SpaceTime × SpaceTime =>
      4 * c ^ 2 * (A q.1 * A' q.2 * Q (q.1 - q.2) ^ 2) +
        4 * ((A q.1 * Q (q.1 - y') ^ 2) * (A' q.2 * Q (y - q.2) ^ 2))) volume :=
    f1.add f2
  have f45 : Integrable (fun q : SpaceTime × SpaceTime =>
      16 * c * (A q.1 * A' q.2 * (Q (q.1 - y) * Q (q.2 - y') * Q (q.1 - q.2))) +
        16 * ((A q.1 * (Q (q.1 - y) * Q (q.1 - y'))) *
          (A' q.2 * (Q (q.2 - y') * Q (y - q.2))))) volume := f4.add f5
  simp only [pt4, pt2]
  rw [integral_add f12 f3, integral_add f1 f2, integral_add f4 f5, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul, k1, k3, k4,
    e2, e5]
  ring

/-- **Global covariance bound for `I(Ψ²) Ψ²`, abstract form.** -/
theorem i2Psi2CovAbs_bound_global {B : ℝ} (hB0 : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K Q : SpaceTime → ℝ}, SingularKernelData K Q B →
      ∀ (x y y' : SpaceTime) {D : ℝ}, 0 ≤ D →
      (∀ a b : SpaceTime, |a.1 - x.1| ≤ |y.1 - x.1| + |y'.1 - x.1| + 2 →
        |b.1 - x.1| ≤ |y.1 - x.1| + |y'.1 - x.1| + 2 → torusParabolicSize (a - b) ≤ D) →
      0 < torusParabolicSize (y - y') → 0 < torusParabolicSize (x - y) →
      0 < torusParabolicSize (x - y') →
        |i2Psi2CovAbs K Q x y y'| ≤ C * ((1 + D) ^ 2 * (1 + |y.1 - x.1| + |y'.1 - x.1|)) *
          (torusParabolicSize (y - y') ^ (-(2 : ℝ)) + torusParabolicSize (y - y') ^ (-(1 : ℝ)) +
            torusParabolicSize (y - y') ^ (-(1 / 2 : ℝ)) +
            torusParabolicSize (x - y) ^ (-(1 / 2 : ℝ)) +
            torusParabolicSize (x - y') ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨Csq, hCsq, hsq⟩ := i2Psi2_sq_term_global
  obtain ⟨Ccr, hCcr, hcr⟩ := i2Psi2_cross_term_global
  obtain ⟨Cch, hCch, hch⟩ := i2Psi2_chain_term_global
  obtain ⟨Cs2, hCs2, hs2⟩ := i2Psi2_single_two_global
  obtain ⟨Cs11, hCs11, hs11⟩ := i2Psi2_single_one_one_global
  obtain ⟨Cm, hCm, hm⟩ := i2Psi2_mean_global
  refine ⟨4 * Csq * B ^ 6 * (80 / (5 - (3 + 1 / 4)) + 2) + 64 * Cs2 ^ 2 * B ^ 6 +
    16 * Ccr * B ^ 6 * (80 / (5 - (4 + 1 / 4)) + 2) +
    16 * Cch * B ^ 6 * (80 / (5 - (4 + 1 / 4)) + 2) + 512 * Cs11 ^ 2 * B ^ 6 + Cm ^ 2 * B ^ 6,
    by positivity, ?_⟩
  intro K Q h x y y' D hD0 hD hyy hxy hxy'
  have hyy' : 0 < torusParabolicSize (y' - y) := torusParabolicSize_sub_pos_symm hyy
  have hx1 : (0 : ℝ) ≤ |y.1 - x.1| := abs_nonneg _
  have hx2 : (0 : ℝ) ≤ |y'.1 - x.1| := abs_nonneg _
  have hD1 : ∀ w v : SpaceTime, |w.1 - x.1| ≤ |y.1 - x.1| + 1 → |v.1 - x.1| ≤ |y'.1 - x.1| + 1 →
      torusParabolicSize (w - v) ≤ D := fun w v hw hv => hD w v (by linarith) (by linarith)
  have hDy' : ∀ w : SpaceTime, |w.1 - x.1| ≤ |y.1 - x.1| + 1 → torusParabolicSize (y' - w) ≤ D :=
    fun w hw => hD y' w (by linarith) (by linarith)
  have hDy : ∀ w : SpaceTime, |w.1 - x.1| ≤ |y'.1 - x.1| + 1 → torusParabolicSize (y - w) ≤ D :=
    fun w hw => hD y w (by linarith) (by linarith)
  have hDm : ∀ w : SpaceTime, |w.1 - x.1| ≤ 1 → torusParabolicSize (y - w) ≤ D :=
    fun w hw => hD y w (by linarith) (by linarith)
  have hDm' : ∀ w : SpaceTime, |w.1 - x.1| ≤ 1 → torusParabolicSize (y' - w) ≤ D :=
    fun w hw => hD y' w (by linarith) (by linarith)
  have hQm := h.measurable_Q
  -- the six bounds
  obtain ⟨i1, b1⟩ := hsq h x y y' hD0 hD1
  obtain ⟨i3, b3⟩ := hcr h x y y' hD0 hD1
  obtain ⟨i4, b4⟩ := hch h x y y' hD0 hD1
  have hGa : ∀ᵐ w : SpaceTime ∂volume, |Q (w - y') ^ 2| ≤ (4 * B ^ 2) * singularPow 2 y' w := by
    filter_upwards [ae_torusParabolicSize_sub_pos y'] with w hw
    rw [abs_of_nonneg (sq_nonneg _)]
    simpa [singularPow] using sq_cov_flip_le hB0 h.Q_bound hw
  have hGb : ∀ᵐ v : SpaceTime ∂volume, |Q (y - v) ^ 2| ≤ B ^ 2 * singularPow 2 y v := by
    filter_upwards [ae_torusParabolicSize_sub_pos y] with v hv
    rw [abs_of_nonneg (sq_nonneg _)]
    simpa [singularPow] using sq_cov_le h.Q_bound hv
  obtain ⟨i2a, b2a⟩ := hs2 h x y y' (G := fun w => Q (w - y') ^ 2) hD0 (by positivity) hyy hxy' hDy'
    ((hQm.comp (measurable_id.sub measurable_const)).pow_const 2).aestronglyMeasurable hGa
  obtain ⟨i2b, b2b⟩ := hs2 h x y' y (G := fun v => Q (y - v) ^ 2) hD0 (by positivity) hyy' hxy hDy
    ((hQm.comp (measurable_const.sub measurable_id)).pow_const 2).aestronglyMeasurable hGb
  have hGc : ∀ᵐ w : SpaceTime ∂volume, |Q (w - y) * Q (w - y')| ≤
      (4 * B ^ 2) * (singularPow 1 y w * singularPow 1 y' w) := by
    filter_upwards [ae_torusParabolicSize_sub_pos y, ae_torusParabolicSize_sub_pos y'] with w a b
    have q1 := abs_Q_flip_le hB0 h.Q_bound a
    have q2 := abs_Q_flip_le hB0 h.Q_bound b
    rw [abs_mul]
    calc |Q (w - y)| * |Q (w - y')| ≤ (2 * B * singularPow 1 y w) * (2 * B * singularPow 1 y' w) :=
          mul_le_mul q1 q2 (abs_nonneg _) (mul_nonneg (mul_nonneg (by norm_num) hB0)
            (singularPow_nonneg _ _ _))
      _ = _ := by ring
  have hGd : ∀ᵐ v : SpaceTime ∂volume, |Q (v - y') * Q (y - v)| ≤
      (2 * B ^ 2) * (singularPow 1 y' v * singularPow 1 y v) := by
    filter_upwards [ae_torusParabolicSize_sub_pos y', ae_torusParabolicSize_sub_pos y] with v a b
    have q1 := abs_Q_flip_le hB0 h.Q_bound a
    have q2 := abs_Q_le_singularPow h.Q_bound b
    rw [abs_mul]
    calc |Q (v - y')| * |Q (y - v)| ≤ (2 * B * singularPow 1 y' v) * (B * singularPow 1 y v) :=
          mul_le_mul q1 q2 (abs_nonneg _) (mul_nonneg (mul_nonneg (by norm_num) hB0)
            (singularPow_nonneg _ _ _))
      _ = _ := by ring
  obtain ⟨i5a, b5a⟩ := hs11 h x y y' (G := fun w => Q (w - y) * Q (w - y')) hD0 (by positivity)
    hyy hxy' hDy' ((hQm.comp (measurable_id.sub measurable_const)).mul
      (hQm.comp (measurable_id.sub measurable_const))).aestronglyMeasurable hGc
  obtain ⟨i5b, b5b⟩ := hs11 h x y' y (G := fun v => Q (v - y') * Q (y - v)) hD0 (by positivity)
    hyy' hxy hDy ((hQm.comp (measurable_id.sub measurable_const)).mul
      (hQm.comp (measurable_const.sub measurable_id))).aestronglyMeasurable hGd
  have bMa := hm h x y hD0 hxy hDm
  have bMb := hm h x y' hD0 hxy' hDm'
  rw [i2Psi2CovAbs_eq i1 i3 i4 i2a i2b i5a i5b]
  set X1 := ∫ w, ∫ v, i2Psi2Increment K x y w * i2Psi2Increment K x y' v * Q (w - v) ^ 2 with hX1
  set X3 := ∫ w, ∫ v, i2Psi2Increment K x y w * i2Psi2Increment K x y' v *
    (Q (w - v) * Q (w - y') * Q (y - v)) with hX3
  set X4 := ∫ w, ∫ v, i2Psi2Increment K x y w * i2Psi2Increment K x y' v *
    (Q (w - y) * Q (v - y') * Q (w - v)) with hX4
  set X2a := ∫ w, i2Psi2Increment K x y w * Q (w - y') ^ 2 with hX2a
  set X2b := ∫ v, i2Psi2Increment K x y' v * Q (y - v) ^ 2 with hX2b
  set X5a := ∫ w, i2Psi2Increment K x y w * (Q (w - y) * Q (w - y')) with hX5a
  set X5b := ∫ v, i2Psi2Increment K x y' v * (Q (v - y') * Q (y - v)) with hX5b
  set Ma := -2 * ∫ w, K (x - w) * Q (w - y) ^ 2 with hMa
  set Mb := -2 * ∫ w, K (x - w) * Q (w - y') ^ 2 with hMb
  set U : ℝ := D ^ (1 / 4 : ℝ) with hU
  set d1 : ℝ := torusParabolicSize (y - y') ^ (-(1 : ℝ)) with hd1
  set d2 : ℝ := torusParabolicSize (y - y') ^ (-(2 : ℝ)) with hd2
  set p1 : ℝ := torusParabolicSize (y - y') ^ (-(1 / 4 : ℝ)) with hp1
  set p2 : ℝ := torusParabolicSize (y' - y) ^ (-(1 / 4 : ℝ)) with hp2
  set p3 : ℝ := torusParabolicSize (x - y) ^ (-(1 / 4 : ℝ)) with hp3
  set p4 : ℝ := torusParabolicSize (x - y') ^ (-(1 / 4 : ℝ)) with hp4
  have nn : ∀ s e : ℝ, 0 ≤ s → 0 ≤ s ^ e := fun s e hs => Real.rpow_nonneg hs e
  have hU0 : 0 ≤ U := nn _ _ hD0
  have hUD : U ≤ 1 + D := rpow_quarter_le_one_add hD0
  have hd10 : 0 ≤ d1 := nn _ _ (torusParabolicSize_nonneg _)
  have hd20 : 0 ≤ d2 := nn _ _ (torusParabolicSize_nonneg _)
  have hp10 : 0 ≤ p1 := nn _ _ (torusParabolicSize_nonneg _)
  have hp20 : 0 ≤ p2 := nn _ _ (torusParabolicSize_nonneg _)
  have hp30 : 0 ≤ p3 := nn _ _ (torusParabolicSize_nonneg _)
  have hp40 : 0 ≤ p4 := nn _ _ (torusParabolicSize_nonneg _)
  have hp2le : p2 ≤ 2 * p1 :=
    torusParabolicSize_sub_rpow_neg_le (a := y') (b := y) (e := 1 / 4) (by norm_num)
      (by norm_num) hyy
  have hc2 : Q (y - y') ^ 2 ≤ B ^ 2 * d2 := sq_cov_le h.Q_bound hyy
  have hc1 : |Q (y - y')| ≤ B * d1 := h.Q_bound _ hyy
  have h1 : |4 * Q (y - y') ^ 2 * X1| ≤ 4 * (B ^ 2 * d2) *
      (Csq * B ^ 4 * U * (80 / (5 - (3 + 1 / 4)) + 2 * (|y.1 - x.1| + 1))) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * Q (y - y') ^ 2)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hc2 (by norm_num)) (by simpa [hU] using b1)
      (abs_nonneg _) (by positivity)
  have h2 : |4 * (X2a * X2b)| ≤ 4 * ((Cs2 * B * (4 * B ^ 2) * U * (p1 + p4)) *
      (Cs2 * B * B ^ 2 * U * (p2 + p3))) := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4), abs_mul]
    exact mul_le_mul_of_nonneg_left (mul_le_mul (by simpa [hU] using b2a)
      (by simpa [hU] using b2b) (abs_nonneg _) (by
        have := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCs2 hB0) (by positivity : (0 : ℝ) ≤
          4 * B ^ 2)) hU0) (add_nonneg hp10 hp40)
        exact this)) (by norm_num)
  have h3 : |16 * Q (y - y') * X3| ≤ 16 * (B * d1) *
      (Ccr * B ^ 5 * U * (80 / (5 - (4 + 1 / 4)) + 2 * (|y.1 - x.1| + 1))) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 16)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hc1 (by norm_num)) (by simpa [hU] using b3)
      (abs_nonneg _) (by positivity)
  have h4 : |16 * Q (y - y') * X4| ≤ 16 * (B * d1) *
      (Cch * B ^ 5 * U * (80 / (5 - (4 + 1 / 4)) + 2 * (|y.1 - x.1| + 1))) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 16)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hc1 (by norm_num)) (by simpa [hU] using b4)
      (abs_nonneg _) (by positivity)
  have h5 : |16 * (X5a * X5b)| ≤ 16 * ((Cs11 * B * (4 * B ^ 2) * U * (p1 + p4)) *
      (Cs11 * B * (2 * B ^ 2) * U * (p2 + p3))) := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 16), abs_mul]
    exact mul_le_mul_of_nonneg_left (mul_le_mul (by simpa [hU] using b5a)
      (by simpa [hU] using b5b) (abs_nonneg _) (by
        have := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCs11 hB0) (by positivity : (0 : ℝ) ≤
          4 * B ^ 2)) hU0) (add_nonneg hp10 hp40)
        exact this)) (by norm_num)
  have h6 : |Ma * Mb| ≤ (Cm * B ^ 3 * U * p3) * (Cm * B ^ 3 * U * p4) := by
    rw [abs_mul]
    exact mul_le_mul (by simpa [hU] using bMa) (by simpa [hU] using bMb) (abs_nonneg _)
      (mul_nonneg (mul_nonneg (mul_nonneg hCm (pow_nonneg hB0 3)) hU0) hp30)
  have key := i2Psi2_combine (B := B) (Csq := Csq) (Ccr := Ccr) (Cch := Cch) (Cs2 := Cs2)
    (Cs11 := Cs11) (Cm := Cm) (a0 := 80 / (5 - (3 + 1 / 4))) (a1 := 80 / (5 - (4 + 1 / 4)))
    (D := D) (U := U) (t := |y.1 - x.1|) (t' := |y'.1 - x.1|) (d1 := d1) (d2 := d2) (p1 := p1)
    (p2 := p2) (p3 := p3) (p4 := p4) hB0 hCsq hCcr hCch (by norm_num) (by norm_num) hD0 hU0 hUD
    hx1 hx2 hd10 hd20 hp10 hp2le hp20 hp30 hp40 h1 h2 h3 h4 h5 h6
  have s1 := rpow_neg_quarter_sq (torusParabolicSize_nonneg (y - y'))
  have s3 := rpow_neg_quarter_sq (torusParabolicSize_nonneg (x - y))
  have s4 := rpow_neg_quarter_sq (torusParabolicSize_nonneg (x - y'))
  rw [s1, s3, s4] at key
  exact key

end RegularityStructures

end
