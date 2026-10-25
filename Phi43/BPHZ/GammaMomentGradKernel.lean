/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.GammaMomentMajorant
public import Phi43.BPHZ.HairerKernelTaylorTorus
public import Phi43.BPHZ.HairerKernelTaylorLift
public import Phi43.BPHZ.TreeI2Psi2DifferenceMean
public import Phi43.BPHZ.TreeI3Psi2TestedSize
public import RegularityStructures.Torus.KernelBoundsLatticeLift
public import Phi43.Stochastic.ConstantsComparisonKernelLp
import Mathlib.Tactic

/-!
# The gradient increment kernel and the Taylor remainder kernel

For `x y : SpaceTime` and `G_i = hairerKernelTorusGrad N i`:

* `hairerGradIncrementKernel N i x y w = G_i (y - w) - G_i (x - w)`;
* `hairerTaylorKernel N x t a w = K(x + (t, proj a) - w) - K(x - w) - ∑ᵢ G_i (x - w) aᵢ`.

Both are measurable and integrable, and satisfy the majorant hypothesis `gammaMajorant` of
`GammaMomentMajorant` with decay `p = 4 + γ`, gain `γ ∈ [0, 1]` (gradient increment) and
`p = 4 + θ`, gain `1 + θ` with `θ ∈ [0, 1]` (Taylor remainder, in terms of the size `‖(t, a)‖` of
the lift).
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

open RegularityStructures

/-- The increment of the gradient kernel, `G_i (y - w) - G_i (x - w)`. -/
def hairerGradIncrementKernel (N : ℕ) (i : Fin 3) (x y w : SpaceTime) : ℝ :=
  hairerKernelTorusGrad N i (y - w) - hairerKernelTorusGrad N i (x - w)

/-- The kernel of the Taylor remainder `K(x + h - w) - K(x - w) - ∑ᵢ ∂ᵢK(x - w) aᵢ`,
`h = (t, proj a)`. -/
def hairerTaylorKernel (N : ℕ) (x : SpaceTime) (t : ℝ) (a : Fin 3 → ℝ) (w : SpaceTime) : ℝ :=
  hairerKernelTorus N (x + (t, torusProj a) - w) - hairerKernelTorus N (x - w) -
    ∑ i : Fin 3, hairerKernelTorusGrad N i (x - w) * a i

end RegularityStructures.Phi43

end

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

theorem hairerKernelGrad_measurable (N : ℕ) (i : Fin 3) : Measurable (hairerKernelGrad N i) := by
  unfold hairerKernelGrad
  apply Measurable.tsum
  intro n
  exact (contDiff_lineIter (contDiff_annShellC N n) _).continuous.measurable

theorem measurable_hairerKernelTorusGrad (N : ℕ) (i : Fin 3) :
    Measurable (hairerKernelTorusGrad N i) := by
  unfold hairerKernelTorusGrad
  apply Measurable.tsum
  intro k
  apply (hairerKernelGrad_measurable N i).comp
  exact measurable_fst.prodMk ((measurable_torusRep.comp measurable_snd).add measurable_const)

theorem hairerKernelTorusGrad_eq_zero_of_one_lt (N : ℕ) (i : Fin 3) {z : SpaceTime}
    (hz : 1 < torusParabolicSize z) : hairerKernelTorusGrad N i z = 0 := by
  unfold hairerKernelTorusGrad
  have hk : ∀ k : Fin 3 → ℤ,
      hairerKernelGrad N i (z.1, torusRep z.2 + fun j => (k j : ℝ)) = 0 := fun k =>
    hairerKernelGrad_eq_zero_of_one_lt N i (lt_of_lt_of_le hz (torusParabolicSize_le_periodicLift z k))
  simp only [hk]
  exact tsum_zero

theorem hairerKernelTorusGrad_eq_zero_of_one_lt_time (N : ℕ) (i : Fin 3) {z : SpaceTime}
    (hz : 1 < |z.1|) : hairerKernelTorusGrad N i z = 0 := by
  refine hairerKernelTorusGrad_eq_zero_of_one_lt N i ?_
  have h1 : 1 < √|z.1| := by
    rw [Real.lt_sqrt zero_le_one]
    simpa using hz
  unfold torusParabolicSize
  linarith [torusSpatialNorm_nonneg z.2]

theorem integrable_hairerKernelTorusGrad (N : ℕ) (i : Fin 3) :
    Integrable (hairerKernelTorusGrad N i) := by
  obtain ⟨C, hC, hG⟩ := hairerKernelTorusGrad_abs_le N
  have hweight := integrable_constantsComparisonSingularWeight (q := (4 : ℝ)) (by norm_num)
    (by norm_num)
  refine Integrable.mono' (hweight.const_mul C) (measurable_hairerKernelTorusGrad N i).aestronglyMeasurable ?_
  filter_upwards [@Measure.ae_ne SpaceTime _ volume
    (Measure.IsAddHaarMeasure.nullSingletonClass volume) (0 : SpaceTime)] with z hz
  have hpos := torusParabolicSize_pos_of_ne_zero hz
  by_cases hsmall : torusParabolicSize z ≤ 1
  · simpa [constantsComparisonSingularWeight, hpos, hsmall] using hG i hpos
  · rw [hairerKernelTorusGrad_eq_zero_of_one_lt N i (lt_of_not_ge hsmall)]
    simp [constantsComparisonSingularWeight, hpos, hsmall]

theorem integrable_hairerGradIncrementKernel (N : ℕ) (i : Fin 3) (x y : SpaceTime) :
    Integrable (hairerGradIncrementKernel N i x y) :=
  (integrable_comp_sub_left_spaceTime (integrable_hairerKernelTorusGrad N i) y).sub
    (integrable_comp_sub_left_spaceTime (integrable_hairerKernelTorusGrad N i) x)

theorem measurable_hairerGradIncrementKernel (N : ℕ) (i : Fin 3) (x y : SpaceTime) :
    Measurable (hairerGradIncrementKernel N i x y) :=
  ((measurable_hairerKernelTorusGrad N i).comp (measurable_const.sub measurable_id)).sub
    ((measurable_hairerKernelTorusGrad N i).comp (measurable_const.sub measurable_id))

theorem measurable_hairerTaylorKernel (N : ℕ) (x : SpaceTime) (t : ℝ) (a : Fin 3 → ℝ) :
    Measurable (hairerTaylorKernel N x t a) := by
  unfold hairerTaylorKernel
  refine (((measurable_constantsComparison_hairerKernelTorus N).comp
    (measurable_const.sub measurable_id)).sub
    ((measurable_constantsComparison_hairerKernelTorus N).comp
    (measurable_const.sub measurable_id))).sub ?_
  refine Finset.measurable_sum _ fun i _ => ?_
  exact ((measurable_hairerKernelTorusGrad N i).comp (measurable_const.sub measurable_id)).mul
    measurable_const

theorem integrable_hairerTaylorKernel (N : ℕ) (x : SpaceTime) (t : ℝ) (a : Fin 3 → ℝ) :
    Integrable (hairerTaylorKernel N x t a) := by
  unfold hairerTaylorKernel
  refine ((integrable_hairerKernelTorus_sub N (x + (t, torusProj a))).sub
    (integrable_hairerKernelTorus_sub N x)).sub ?_
  refine integrable_finsetSum _ fun i _ => ?_
  exact (integrable_comp_sub_left_spaceTime (integrable_hairerKernelTorusGrad N i) x).mul_const _

private theorem gk_interp {r s γ : ℝ} (hr : 0 ≤ r) (hs : 0 < s) (hrs : r ≤ s) (_hγ0 : 0 ≤ γ)
    (hγ1 : γ ≤ 1) : r * s ^ (-(5 : ℝ)) ≤ r ^ γ * s ^ (-(4 + γ)) := by
  rcases hr.eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul]
    exact mul_nonneg (Real.rpow_nonneg le_rfl _) (Real.rpow_nonneg hs.le _)
  · have e1 : r = r ^ γ * r ^ (1 - γ) := by
      rw [← Real.rpow_add hpos]; simp
    have e2 : s ^ (1 - γ) * s ^ (-(5 : ℝ)) = s ^ (-(4 + γ)) := by
      rw [← Real.rpow_add hs]; congr 1; ring
    have h3 : r ^ (1 - γ) ≤ s ^ (1 - γ) := Real.rpow_le_rpow hr hrs (by linarith)
    have h4 : 0 ≤ r ^ γ := Real.rpow_nonneg hr _
    have h5 : 0 ≤ s ^ (-(5 : ℝ)) := Real.rpow_nonneg hs.le _
    calc r * s ^ (-(5 : ℝ)) = r ^ γ * (r ^ (1 - γ) * s ^ (-(5 : ℝ))) := by
          conv_lhs => rw [e1]
          ring
      _ ≤ r ^ γ * (s ^ (1 - γ) * s ^ (-(5 : ℝ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 h5) h4
      _ = _ := by rw [e2]

theorem gammaMajorant_rpow_near {s r c m : ℝ} (hs : 0 < s) (hr : 0 ≤ r) (hsL : s ≤ 5 * r) (hc : 0 ≤ c)
    (hc2 : c ≤ 2) : s ^ (-m) ≤ 25 * r ^ c * s ^ (-(m + c)) := by
  have e : s ^ (-m) = s ^ c * s ^ (-(m + c)) := by
    rw [← Real.rpow_add hs]; congr 1; ring
  have h1 : s ^ c ≤ (5 * r) ^ c := Real.rpow_le_rpow hs.le hsL hc
  have h2 : (5 : ℝ) ^ c ≤ 5 ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hc2
  have h3 : (5 : ℝ) ^ (2 : ℝ) = 25 := by norm_num
  rw [Real.mul_rpow (by norm_num) hr] at h1
  have h4 : 0 ≤ r ^ c := Real.rpow_nonneg hr _
  rw [e]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hs.le _)
  calc s ^ c ≤ 5 ^ c * r ^ c := h1
    _ ≤ 25 * r ^ c := mul_le_mul_of_nonneg_right (h3 ▸ h2) h4
    _ = _ := rfl

theorem gammaMajorant_alg_le {F A C P Sv Su : ℝ} (hC : 0 ≤ C) (hP : 0 ≤ P) (hSv : 0 ≤ Sv)
    (hSu : 0 ≤ Su) (hF : F ≤ A * (P * Su)) (hA : A ≤ C) : F ≤ C * P * (Sv + Su) := by
  have h1 : 0 ≤ P * Su := mul_nonneg hP hSu
  have h2 : 0 ≤ P * Sv := mul_nonneg hP hSv
  nlinarith [mul_le_mul_of_nonneg_right hA h1]

private theorem gk_sub_zero {N : ℕ} {i : Fin 3} {x y w : SpaceTime} (hxy : |y.1 - x.1| ≤ 1)
    (hs : ¬ |w.1 - x.1| ≤ 2) : hairerGradIncrementKernel N i x y w = 0 := by
  unfold hairerGradIncrementKernel
  have h1 : 1 < |(y - w).1| := by
    simp only [Prod.fst_sub]
    have : |w.1 - x.1| ≤ |(y.1 - x.1)| + |y.1 - w.1| := by
      calc |w.1 - x.1| = |(y.1 - x.1) - (y.1 - w.1)| := by congr 1; ring
        _ ≤ _ := abs_sub _ _
    linarith [not_le.1 hs]
  have h2 : 1 < |(x - w).1| := by
    simp only [Prod.fst_sub]
    rw [abs_sub_comm]
    linarith [not_le.1 hs]
  rw [hairerKernelTorusGrad_eq_zero_of_one_lt_time N i h1,
    hairerKernelTorusGrad_eq_zero_of_one_lt_time N i h2, sub_zero]

/-- **Majorant of the gradient increment kernel**: decay `4 + γ`, gain `γ ∈ [0, 1]`. -/
theorem gammaMajorant_hairerGradIncrement (N : ℕ) (i : Fin 3) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ ≤ 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ {x y : SpaceTime}, |y.1 - x.1| ≤ 1 →
      gammaMajorant (hairerGradIncrementKernel N i x y) x y (torusParabolicSize (y - x)) M γ
        (4 + γ) := by
  obtain ⟨C1, hC1, hG⟩ := hairerKernelTorusGrad_abs_le N
  obtain ⟨C2, hC2, hI⟩ := hairerKernelTorusGrad_sub_abs_le N
  refine ⟨25 * C1 + 2 * C2, by positivity, fun {x y} hxy => ⟨torusParabolicSize_nonneg _,
    by positivity, measurable_hairerGradIncrementKernel N i x y, ?_⟩⟩
  intro w hy hx
  by_cases hs : |w.1 - x.1| ≤ 2
  · rw [i2Psi2Slab_of_le hs, one_mul]
    set r := torusParabolicSize (y - x) with hr
    have hr0 : 0 ≤ r := torusParabolicSize_nonneg _
    have hv : y - w = (x - w) + (y - x) := by abel
    have hP : 0 ≤ r ^ γ := Real.rpow_nonneg hr0 _
    have hSv : 0 ≤ torusParabolicSize (y - w) ^ (-(4 + γ)) := Real.rpow_nonneg (torusParabolicSize_nonneg _) _
    have hSu : 0 ≤ torusParabolicSize (x - w) ^ (-(4 + γ)) := Real.rpow_nonneg (torusParabolicSize_nonneg _) _
    unfold hairerGradIncrementKernel
    by_cases hfar : 4 * r ≤ torusParabolicSize (x - w)
    · obtain ⟨a, ha, hpa, hnorm⟩ := exists_torusLift_norm_le (y - x)
      have hh : ((y - x).1, torusProj a) = y - x := Prod.ext rfl hpa
      have hn : parabolicNorm ((y - x).1, a) ≤ torusParabolicSize (x - w) / 2 := by linarith
      have h1 := hI i hx ha hn
      rw [hh, ← hv] at h1
      have h2 : parabolicNorm ((y - x).1, a) * torusParabolicSize (x - w) ^ (-(5 : ℝ)) ≤
          2 * r * torusParabolicSize (x - w) ^ (-(5 : ℝ)) :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
      have h3 := gk_interp hr0 hx (by linarith) hγ0 hγ1
      refine gammaMajorant_alg_le (A := 2 * C2) (by positivity) hP hSv hSu ?_ (by linarith)
      calc _ ≤ C2 * parabolicNorm ((y - x).1, a) * torusParabolicSize (x - w) ^ (-(5 : ℝ)) := h1
        _ ≤ C2 * (2 * r) * torusParabolicSize (x - w) ^ (-(5 : ℝ)) := by
            rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_left h2 hC2
        _ = 2 * C2 * (r * torusParabolicSize (x - w) ^ (-(5 : ℝ))) := by ring
        _ ≤ 2 * C2 * (r ^ γ * torusParabolicSize (x - w) ^ (-(4 + γ))) :=
            mul_le_mul_of_nonneg_left h3 (by positivity)
    · have hlt : torusParabolicSize (x - w) < 4 * r := lt_of_not_ge hfar
      have hsv : torusParabolicSize (y - w) ≤ 5 * r := by
        have := torusParabolicSize_add_le_add (x - w) (y - x)
        rw [← hv] at this
        linarith
      have b1 := gammaMajorant_rpow_near hy hr0 hsv hγ0 (by linarith) (m := 4)
      have b2 := gammaMajorant_rpow_near hx hr0 (by linarith) hγ0 (by linarith) (m := 4)
      have g1 := hG i hy
      have g2 := hG i hx
      have hq : (-(4 : ℝ)) = -(4:ℝ) := rfl
      have s1 : |hairerKernelTorusGrad N i (y - w)| ≤ C1 * (25 * r ^ γ *
          torusParabolicSize (y - w) ^ (-(4 + γ))) := g1.trans (mul_le_mul_of_nonneg_left b1 hC1)
      have s2 : |hairerKernelTorusGrad N i (x - w)| ≤ C1 * (25 * r ^ γ *
          torusParabolicSize (x - w) ^ (-(4 + γ))) := g2.trans (mul_le_mul_of_nonneg_left b2 hC1)
      have hab := abs_sub (hairerKernelTorusGrad N i (y - w)) (hairerKernelTorusGrad N i (x - w))
      have key : |hairerKernelTorusGrad N i (y - w) - hairerKernelTorusGrad N i (x - w)| ≤
          (25 * C1 + 2 * C2) * r ^ γ * (torusParabolicSize (y - w) ^ (-(4 + γ)) +
            torusParabolicSize (x - w) ^ (-(4 + γ))) := by
        generalize torusParabolicSize (y - w) ^ (-(4 + γ)) = Sv at *
        generalize torusParabolicSize (x - w) ^ (-(4 + γ)) = Su at *
        generalize r ^ γ = P at *
        nlinarith [mul_nonneg hP hSv, mul_nonneg hP hSu, mul_nonneg hC2 (mul_nonneg hP hSv),
          mul_nonneg hC2 (mul_nonneg hP hSu)]
      exact key
  · rw [gk_sub_zero hxy hs]
    have : i2Psi2Slab x.1 w = 0 := by unfold i2Psi2Slab; simp [hs]
    rw [this]
    simp

end RegularityStructures.Phi43

end
