/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Kernel.Moments
public import RegularityStructures.Analysis.Semigroup.Basic

/-!
# The auxiliary regularising semigroup on `ℝ⁴`

`parabolicSemigroup` is the `RegularisingSemigroup ParabolicSpace volume` with kernel
`Q_t(x, y) = q_t(x - y)`, `q_t = parabolicKernel t`, scaling order `ℓ = 4` and size
`d(y, x) = ‖y - x‖_𝔰`. It is used *only* to measure regularity; it is not the causal heat kernel
of the PDE. This is the setting of [Hos25, Definition 2.6 (i), (iii), Example 2.7]
(arXiv:2310.07396v2).

* the semigroup property follows from the 1D ones by Fubini
  (`integral_quarticKernel_mul_quarticKernel`, `integral_heatKernel1D_mul_heatKernel1D`);
* the moment bounds from `RegularityStructures.Analysis.Kernel.Moments`.
-/

public section

open MeasureTheory

namespace RegularityStructures

theorem integral_parabolicKernel_mul_parabolicKernel {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (x y : ParabolicSpace) :
    ∫ z, parabolicKernel s (x - z) * parabolicKernel t (z - y) = parabolicKernel (s + t) (x - y) := by
  have h : ∀ z : ParabolicSpace, parabolicKernel s (x - z) * parabolicKernel t (z - y) =
      (heatKernel1D s (x.1 - z.1) * heatKernel1D t (z.1 - y.1)) *
        ∏ i, (quarticKernel s (x.2 i - z.2 i) * quarticKernel t (z.2 i - y.2 i)) := by
    intro z
    simp only [parabolicKernel, Prod.fst_sub, Prod.snd_sub, Pi.sub_apply, Finset.prod_mul_distrib]
    ring
  simp_rw [h]
  have h2 : ∫ z : ParabolicSpace, (heatKernel1D s (x.1 - z.1) * heatKernel1D t (z.1 - y.1)) *
        ∏ i, (quarticKernel s (x.2 i - z.2 i) * quarticKernel t (z.2 i - y.2 i)) =
      (∫ a, heatKernel1D s (x.1 - a) * heatKernel1D t (a - y.1)) *
        ∫ w : Fin 3 → ℝ, ∏ i, (quarticKernel s (x.2 i - w i) * quarticKernel t (w i - y.2 i)) := by
    rw [Measure.volume_eq_prod]
    exact integral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure (Fin 3 → ℝ)))
      (fun a => heatKernel1D s (x.1 - a) * heatKernel1D t (a - y.1))
      (fun w : Fin 3 → ℝ => ∏ i, (quarticKernel s (x.2 i - w i) * quarticKernel t (w i - y.2 i)))
  rw [h2, integral_heatKernel1D_mul_heatKernel1D hs ht, volume_pi,
    integral_fintype_prod_eq_prod
      (f := fun i b => quarticKernel s (x.2 i - b) * quarticKernel t (b - y.2 i))]
  simp only [integral_quarticKernel_mul_quarticKernel hs ht]
  simp [parabolicKernel]

theorem integrable_abs_parabolicKernel_mul_norm {t : ℝ} (ht : 0 < t) {r : ℝ} (hr : 0 ≤ r) :
    Integrable (fun w => |parabolicKernel t w| * parabolicNorm w ^ r) := by
  refine (integrable_parabolicMomentBound ht hr).mono' ?_
    (Filter.Eventually.of_forall fun w => ?_)
  · exact ((continuous_abs.measurable.comp (measurable_parabolicKernel t)).mul
      (continuous_parabolicNorm.measurable.pow_const r)).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (parabolicNorm_nonneg _) r))]
    exact abs_parabolicKernel_mul_le t hr w

/-- The auxiliary regularising semigroup `Q_t(x, y) = q_t(x - y)` on `ℝ⁴ = ℝ × ℝ³`
with order `4`, where `q_t(s, x) = g_t(s) ∏ᵢ k_t(xᵢ)` is the tensor product of the 1D heat kernel
and three 1D quartic kernels. The moment constant is `parabolicMomentConst`. -/
@[expose] noncomputable def parabolicSemigroup : RegularisingSemigroup ParabolicSpace volume where
  kernel t x y := parabolicKernel t (x - y)
  order := 4
  order_pos := by norm_num
  scaleDist x y := parabolicNorm (x - y)
  scaleDist_nonneg x y := parabolicNorm_nonneg _
  momentConst := parabolicMomentConst
  momentConst_nonneg := parabolicMomentConst_nonneg
  measurable_kernel t :=
    (measurable_parabolicKernel t).comp (measurable_fst.sub measurable_snd)
  integrable_moment t ht r hr x := by
    have h : Integrable (fun y : ParabolicSpace => |parabolicKernel t (y - x)| *
        parabolicNorm (y - x) ^ r) volume := by
      have h0 := integrable_abs_parabolicKernel_mul_norm ht hr
      rw [Measure.volume_eq_prod] at h0 ⊢
      exact h0.comp_sub_right x
    refine h.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [← parabolicKernel_neg t (y - x), neg_sub]
  moment_le t ht r hr x := by
    have e : ∀ y : ParabolicSpace, |parabolicKernel t (x - y)| * parabolicNorm (y - x) ^ r =
        |parabolicKernel t (y - x)| * parabolicNorm (y - x) ^ r := fun y => by
      rw [← parabolicKernel_neg t (y - x), neg_sub]
    simp only [e]
    have hshift : ∫ y : ParabolicSpace, |parabolicKernel t (y - x)| * parabolicNorm (y - x) ^ r =
        ∫ w : ParabolicSpace, |parabolicKernel t w| * parabolicNorm w ^ r := by
      rw [Measure.volume_eq_prod]
      exact integral_sub_right_eq_self (fun w : ParabolicSpace =>
        |parabolicKernel t w| * parabolicNorm w ^ r) x
    rw [hshift]
    calc ∫ w, |parabolicKernel t w| * parabolicNorm w ^ r
        ≤ ∫ w, parabolicMomentBound t r w :=
          integral_mono (integrable_abs_parabolicKernel_mul_norm ht hr)
            (integrable_parabolicMomentBound ht hr) (fun w => abs_parabolicKernel_mul_le t hr w)
      _ = parabolicMomentConst r * t ^ (r / 4) := integral_parabolicMomentBound ht hr
      _ = _ := by norm_num
  semigroup s t hs ht x y := integral_parabolicKernel_mul_parabolicKernel hs ht x y

end RegularityStructures

end
