/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Kernel.Quartic
public import RegularityStructures.Analysis.Kernel.Gaussian
public import RegularityStructures.Analysis.Parabolic.Basic
import Mathlib.MeasureTheory.Integral.Pi

/-!
# The parabolic kernel on `ℝ × ℝ³`

`parabolicKernel t (s, x) = heatKernel1D t s * ∏ᵢ quarticKernel t (xᵢ)`: the tensor product of the
1D heat kernel in time and three 1D quartic kernels in space. It is the fundamental solution of
`∂_t - ∂₀² + ∑ᵢ ∂ᵢ⁴` ([Hos25, Example 2.7] (arXiv:2310.07396v2), with the spatial bi-Laplacian
replaced by `∑ᵢ ∂ᵢ⁴`), and is *only* used as the auxiliary kernel measuring regularity.

We prove joint measurability, exact parabolic scaling
`q_t(z) = t^{-5/4} q_1(S^{t^{-1/4}} z)`, `∫ q_t = 1`, and integrability and the value of the weighted
integrals `∫ |g_t(z₀)| |z₀|^a ∏ᵢ |k_t(zᵢ)| |zᵢ|^{eᵢ} dz`, from which the moment bounds follow
(`RegularityStructures.Analysis.Kernel.Moments`).
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The parabolic kernel `q_t(s, x) = g_t(s) ∏ᵢ k_t(xᵢ)`. -/
def parabolicKernel (t : ℝ) (z : ParabolicSpace) : ℝ :=
  heatKernel1D t z.1 * ∏ i, quarticKernel t (z.2 i)

/-- The weight `|g_t(z₀)| |z₀|^a ∏ᵢ |k_t(zᵢ)| |zᵢ|^{eᵢ}`. -/
def parabolicKernelWeight (t a : ℝ) (e : Fin 3 → ℝ) (z : ParabolicSpace) : ℝ :=
  (|heatKernel1D t z.1| * |z.1| ^ a) * ∏ i, (|quarticKernel t (z.2 i)| * |z.2 i| ^ e i)

end RegularityStructures

end

public section

open MeasureTheory

namespace RegularityStructures

theorem parabolicKernel_neg (t : ℝ) (z : ParabolicSpace) :
    parabolicKernel t (-z) = parabolicKernel t z := by
  simp [parabolicKernel, heatKernel1D_neg, quarticKernel_neg]

theorem measurable_parabolicKernel (t : ℝ) : Measurable (parabolicKernel t) := by
  unfold parabolicKernel
  have h1 : Measurable fun z : ParabolicSpace => heatKernel1D t z.1 :=
    (measurable_heatKernel1D t).comp measurable_fst
  have h2 : ∀ i : Fin 3, Measurable fun z : ParabolicSpace => quarticKernel t (z.2 i) :=
    fun i => (measurable_quarticKernel t).comp ((measurable_pi_apply i).comp measurable_snd)
  exact h1.mul (Finset.measurable_prod _ fun i _ => h2 i)

/-- Exact parabolic scaling of the kernel. -/
theorem parabolicKernel_eq_scale {t : ℝ} (ht : 0 < t) (z : ParabolicSpace) :
    parabolicKernel t z =
      t ^ (-(5 / 4 : ℝ)) * parabolicKernel 1 (parabolicDilate (t ^ (-(1 / 4 : ℝ))) z) := by
  have hl : 0 < t ^ (-(1 / 4 : ℝ)) := Real.rpow_pos_of_pos ht _
  have hsq : (t ^ (-(1 / 4 : ℝ))) ^ 2 = t ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    norm_num
  have hprod : t ^ (-(5 / 4 : ℝ)) =
      t ^ (-(1 / 2 : ℝ)) * (t ^ (-(1 / 4 : ℝ))) ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le, ← Real.rpow_add ht]
    norm_num
  unfold parabolicKernel parabolicDilate
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [heatKernel1D_eq_scale ht, hsq, Finset.prod_congr rfl fun i _ => quarticKernel_eq_scale ht _,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hprod]
  ring

theorem integral_parabolicKernel {t : ℝ} (ht : 0 < t) : ∫ z, parabolicKernel t z = 1 := by
  have h : ∫ z : ParabolicSpace, parabolicKernel t z =
      (∫ a, heatKernel1D t a) * ∫ y : Fin 3 → ℝ, ∏ i, quarticKernel t (y i) := by
    rw [Measure.volume_eq_prod]
    exact integral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure (Fin 3 → ℝ))) (fun a => heatKernel1D t a)
      (fun y : Fin 3 → ℝ => ∏ i, quarticKernel t (y i))
  rw [h, integral_heatKernel1D ht, volume_pi,
    integral_fintype_prod_eq_prod (f := fun _ b => quarticKernel t b)]
  simp [integral_quarticKernel ht]

theorem integrable_parabolicKernelWeight {t : ℝ} (ht : 0 < t) {a : ℝ} (ha : 0 ≤ a) {e : Fin 3 → ℝ}
    (he : ∀ i, 0 ≤ e i) : Integrable (parabolicKernelWeight t a e) := by
  have h1 : Integrable (fun x : ℝ => |heatKernel1D t x| * |x| ^ a) :=
    integrable_abs_heatKernel1D_mul_rpow ht ha
  have h2 : Integrable (fun y : Fin 3 → ℝ => ∏ i, (|quarticKernel t (y i)| * |y i| ^ e i)) := by
    rw [volume_pi]
    exact Integrable.fintype_prod (f := fun i b => |quarticKernel t b| * |b| ^ e i)
      fun i => integrable_abs_quarticKernel_mul_rpow ht (he i)
  rw [Measure.volume_eq_prod]
  exact h1.mul_prod h2

theorem integral_parabolicWeight {t : ℝ} (ht : 0 < t) (a : ℝ) (e : Fin 3 → ℝ) :
    ∫ z, parabolicKernelWeight t a e z =
      (t ^ (a / 2) * heatMoment a) * ∏ i, (t ^ (e i / 4) * quarticMoment (e i)) := by
  have h : ∫ z : ParabolicSpace, parabolicKernelWeight t a e z =
      (∫ x, |heatKernel1D t x| * |x| ^ a) *
        ∫ y : Fin 3 → ℝ, ∏ i, (|quarticKernel t (y i)| * |y i| ^ e i) := by
    rw [Measure.volume_eq_prod]
    exact integral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure (Fin 3 → ℝ))) (fun x => |heatKernel1D t x| * |x| ^ a)
      (fun y : Fin 3 → ℝ => ∏ i, (|quarticKernel t (y i)| * |y i| ^ e i))
  rw [h, volume_pi, integral_fintype_prod_eq_prod (f := fun i b => |quarticKernel t b| * |b| ^ e i)]
  rw [integral_abs_heatKernel1D_mul_rpow ht]
  simp only [integral_abs_quarticKernel_mul_rpow ht]

end RegularityStructures

end
