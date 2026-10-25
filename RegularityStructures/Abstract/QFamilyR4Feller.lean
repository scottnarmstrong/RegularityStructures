/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.QFamilyKernelPairing
public import RegularityStructures.Analysis.KernelAll
public import RegularityStructures.Analysis.Kernel.Conservative
public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import RegularityStructures.Analysis.Parabolic.TestFunctionExists
public import RegularityStructures.Analysis.Semigroup.Pairing.FubiniBound

/-!
# The auxiliary semigroup on `ℝ⁴` is strong Feller

For `t > 0` and a bounded measurable `g`, `x ↦ ∫ q_t(x − y) g(y) dy` is continuous
(`continuous_apply_parabolicSemigroup`): approximate the integrable kernel `q_t` in `L¹` by
continuous compactly supported functions `ψ`, for which `x ↦ ∫ ψ(x − y) g(y) dy` is continuous
(a convolution), and note that the error is uniform in `x`. Hence `parabolicSemigroup` is strong
Feller (`parabolicSemigroup_isStrongFeller`), and the abstract results of
`RegularityStructures.Abstract.QFamilyKernelPairing` apply on `ℝ⁴`:

* `parabolicSemigroup_pairing_kernel`: `⟨Λ, q_t(x − ·)⟩ = Λ_t(x)`;
* `parabolicSemigroup_eq_of_pairing_kernel_eq`: a `Q`-family on `ℝ⁴` with measurable bounded
  regularisations is determined by its pairings with the kernel functions.
-/

public section

open MeasureTheory Filter Set
open scoped Topology Convolution

namespace RegularityStructures

theorem isAddHaarMeasure_volume_parabolicSpace :
    (volume : Measure ParabolicSpace).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod]
  infer_instance

attribute [local instance] isAddHaarMeasure_volume_parabolicSpace

/-- `x ↦ ∫ ψ(x − y) g(y) dy` is continuous for a continuous compactly supported `ψ` and a locally
integrable `g`. -/
theorem continuous_integral_comp_sub_mul {ψ g : ParabolicSpace → ℝ} (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) (hg : LocallyIntegrable g) :
    Continuous fun x => ∫ y, ψ (x - y) * g y := by
  have := hc.continuous_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hg hψ (μ := volume)
  refine this.congr fun x => ?_
  simp only [convolution, ContinuousLinearMap.mul_apply', mul_comm]

/-- **Strong Feller property on `ℝ⁴`**: for `t > 0` and bounded measurable `g`, `Q_t g` is
continuous. -/
theorem continuous_apply_parabolicSemigroup {t : ℝ} (ht : 0 < t) {g : ParabolicSpace → ℝ}
    (hg : Measurable g) {B : ℝ} (hB : ∀ y, |g y| ≤ B) :
    Continuous (parabolicSemigroup.apply t g) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hq : Integrable (parabolicKernel t) := integrable_parabolicKernel ht
  have hloc : LocallyIntegrable g :=
    (memLp_top_of_bound hg.aestronglyMeasurable B
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hB y)).locallyIntegrable
      le_top
  have key : ∀ ε > (0 : ℝ), ∃ F : ParabolicSpace → ℝ, Continuous F ∧
      ∀ x, dist (parabolicSemigroup.apply t g x) (F x) ≤ ε := by
    intro ε hε
    obtain ⟨ψ, hψc, hψε, hψcont, hψi⟩ :=
      hq.exists_hasCompactSupport_integral_sub_le (show 0 < ε / (B + 1) by positivity)
    refine ⟨fun x => ∫ y, ψ (x - y) * g y, continuous_integral_comp_sub_mul hψcont hψc hloc,
      fun x => ?_⟩
    have hi1 : Integrable (fun y => parabolicKernel t (x - y) * g y) :=
      (hq.comp_sub_left x).mul_bdd hg.aestronglyMeasurable
        (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hB y)
    have hi2 : Integrable (fun y => ψ (x - y) * g y) :=
      (hψi.comp_sub_left x).mul_bdd hg.aestronglyMeasurable
        (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hB y)
    have hd : Integrable (fun y => ‖parabolicKernel t (x - y) - ψ (x - y)‖) :=
      ((hq.sub hψi).comp_sub_left x).norm
    rw [Real.dist_eq, show parabolicSemigroup.apply t g x =
      ∫ y, parabolicKernel t (x - y) * g y from rfl, ← integral_sub hi1 hi2, ← Real.norm_eq_abs]
    calc ‖∫ y, (parabolicKernel t (x - y) * g y - ψ (x - y) * g y)‖
        ≤ ∫ y, ‖parabolicKernel t (x - y) - ψ (x - y)‖ * B := by
          refine norm_integral_le_of_norm_le (hd.mul_const B) (Eventually.of_forall fun y => ?_)
          rw [← sub_mul, norm_mul, Real.norm_eq_abs (g y)]
          exact mul_le_mul_of_nonneg_left (hB y) (norm_nonneg _)
      _ = (∫ y, ‖parabolicKernel t y - ψ y‖) * B := by
          rw [integral_mul_const,
            integral_sub_left_eq_self (fun y => ‖parabolicKernel t y - ψ y‖) volume x]
      _ ≤ ε / (B + 1) * B := mul_le_mul_of_nonneg_right hψε hB0
      _ ≤ ε := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith
  refine continuous_of_uniform_approx_of_continuous fun u hu => ?_
  obtain ⟨ε, hε, hεu⟩ := Metric.mem_uniformity_dist.1 hu
  obtain ⟨F, hFc, hF⟩ := key (ε / 2) (half_pos hε)
  exact ⟨F, hFc, fun y => hεu ((hF y).trans_lt (half_lt_self hε))⟩

/-- The auxiliary semigroup on `ℝ⁴` is strong Feller. -/
theorem parabolicSemigroup_isStrongFeller : parabolicSemigroup.IsStrongFeller :=
  fun _ ht _ hg _ hB x =>
    parabolicSemigroup_continuity (continuous_apply_parabolicSemigroup ht hg hB) x

/-- **`Λ_t(x) = ⟨Λ, q_t(x − ·)⟩` on `ℝ⁴`** for a `Q`-family with measurable bounded
regularisations. -/
theorem parabolicSemigroup_pairing_kernel {Λ : ℝ → ParabolicSpace → ℝ}
    (hΛ : Λ ∈ parabolicSemigroup.distributions) (hΛm : ∀ u, 0 < u → Measurable (Λ u))
    (hΛb : ∀ u, 0 < u → ∃ B, ∀ y, |Λ u y| ≤ B) {t : ℝ} (ht : 0 < t) (x : ParabolicSpace) :
    parabolicSemigroup.pairing Λ (parabolicSemigroup.kernel t x) = Λ t x :=
  RegularisingSemigroup.pairing_kernel parabolicSemigroup_isConservative
    parabolicSemigroup_isStrongFeller hΛ hΛm hΛb ht x

/-- **A `Q`-family on `ℝ⁴` is determined by its pairings with the kernel functions
`q_t(x − ·)`.** -/
theorem parabolicSemigroup_eq_of_pairing_kernel_eq {Λ Λ' : ℝ → ParabolicSpace → ℝ}
    (hΛ : Λ ∈ parabolicSemigroup.distributions) (hΛ' : Λ' ∈ parabolicSemigroup.distributions)
    (hΛm : ∀ u, 0 < u → Measurable (Λ u)) (hΛ'm : ∀ u, 0 < u → Measurable (Λ' u))
    (hΛb : ∀ u, 0 < u → ∃ B, ∀ y, |Λ u y| ≤ B) (hΛ'b : ∀ u, 0 < u → ∃ B, ∀ y, |Λ' u y| ≤ B)
    (h : ∀ t, 0 < t → ∀ x, parabolicSemigroup.pairing Λ (parabolicSemigroup.kernel t x) =
      parabolicSemigroup.pairing Λ' (parabolicSemigroup.kernel t x)) :
    Λ = Λ' :=
  RegularisingSemigroup.eq_of_pairing_kernel_eq parabolicSemigroup_isConservative
    parabolicSemigroup_isStrongFeller hΛ hΛ' hΛm hΛ'm hΛb hΛ'b h

end RegularityStructures

end
