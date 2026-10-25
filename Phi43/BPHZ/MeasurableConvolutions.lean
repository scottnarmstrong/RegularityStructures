/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.CanonicalSmoothCharacters
public import Phi43.Structure.CanonicalSmoothConvolution
public import Phi43.Stochastic.ConstantsComparisonKernelLp
public import Phi43.Structure.CanonicalSmoothBasis
import Mathlib.Tactic

/-!
# Measurability in `ω` of convolutions and of spatial gradients

For a family of fields `Y ω` on `ℝ⁴` jointly measurable in `(ω, w)`:

* `measurable_hairerConvolution_apply`: `ω ↦ (K_N * Y ω)(z)` is measurable (Fubini);
* `measurable_hairerConvolution_uncurry`: `(ω, z) ↦ (K_N * Y ω)(z)` is jointly measurable when each
  `K_N * Y ω` is continuous;
* `measurable_fderiv_apply_of_family`: the derivative of a measurable family of differentiable
  functions is measurable (difference quotients);
* `measurable_hairerSpatialGradient_apply`: `ω ↦ ∂_i (K_N * Y ω)(z)` is measurable for smooth `Y ω`.
-/

public section

open MeasureTheory Filter Topology

namespace RegularityStructures.Phi43

open RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω]

theorem measurable_hairerConvolution_apply (N : ℕ) {Y : Ω → ParabolicSpace → ℝ}
    (hY : Measurable fun q : Ω × ParabolicSpace => Y q.1 q.2) (w : ParabolicSpace) :
    Measurable fun ω => hairerConvolution N (Y ω) w := by
  have hK : Measurable fun q : Ω × ParabolicSpace => hairerKernel N (w - q.2) :=
    (measurable_constantsComparison_hairerKernel N).comp (measurable_const.sub measurable_snd)
  exact ((hK.mul hY).stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure ParabolicSpace))).measurable

theorem measurable_swap_of_continuous_of_measurable {α : Type*} [MeasurableSpace α]
    (u : ParabolicSpace → α → ℝ) (h1 : ∀ a, Continuous fun w => u w a)
    (h2 : ∀ w, Measurable (u w)) : Measurable fun q : α × ParabolicSpace => u q.2 q.1 :=
  (measurable_uncurry_of_continuous_of_measurable (u := u) h1 h2).comp measurable_swap

theorem measurable_hairerConvolution_uncurry (N : ℕ) {Y : Ω → ParabolicSpace → ℝ}
    (hY : Measurable fun q : Ω × ParabolicSpace => Y q.1 q.2)
    (hc : ∀ ω, Continuous (hairerConvolution N (Y ω))) :
    Measurable fun q : Ω × ParabolicSpace => hairerConvolution N (Y q.1) q.2 :=
  measurable_swap_of_continuous_of_measurable (fun w ω => hairerConvolution N (Y ω) w) hc
    (fun w => measurable_hairerConvolution_apply N hY w)

/-- The derivative of a measurable family of differentiable functions is measurable. -/
theorem measurable_fderiv_apply_of_family {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Ω → E → ℝ) (hm : ∀ x, Measurable fun ω => F ω x) (hd : ∀ ω, Differentiable ℝ (F ω))
    (x₀ v : E) : Measurable fun ω => fderiv ℝ (F ω) x₀ v := by
  have hlim : ∀ ω, Tendsto (fun n : ℕ => ((n : ℝ) + 1) * (F ω (x₀ + (1 / ((n : ℝ) + 1)) • v) -
      F ω x₀)) atTop (𝓝 (fderiv ℝ (F ω) x₀ v)) := by
    intro ω
    have hF : HasFDerivAt (F ω) (fderiv ℝ (F ω) x₀) (x₀ + (0 : ℝ) • v) := by
      rw [zero_smul, add_zero]; exact (hd ω x₀).hasFDerivAt
    have hl : HasDerivAt (fun s : ℝ => x₀ + s • v) v 0 := by
      have := ((hasDerivAt_id' (0 : ℝ)).smul_const v).const_add x₀
      rwa [one_smul] at this
    have h1 : HasDerivAt (F ω ∘ fun s : ℝ => x₀ + s • v) (fderiv ℝ (F ω) x₀ v) 0 :=
      hF.comp_hasDerivAt (0 : ℝ) hl
    have h2 := (hasDerivAt_iff_tendsto_slope_zero.1 h1)
    have h3 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
        Filter.Eventually.of_forall fun n => ?_⟩
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      positivity
    refine (h2.comp h3).congr fun n => ?_
    simp only [Function.comp, zero_add, smul_eq_mul]
    simp [one_div]
  refine measurable_of_tendsto_metrizable (fun n => ?_) (tendsto_pi_nhds.2 hlim)
  exact measurable_const.mul ((hm _).sub (hm _))

theorem measurable_hairerSpatialGradient_apply (N : ℕ) {Y : Ω → ParabolicSpace → ℝ}
    (hY : Measurable fun q : Ω × ParabolicSpace => Y q.1 q.2)
    (hs : ∀ ω, ContDiff ℝ (↑(⊤ : ℕ∞)) (Y ω)) (i : Fin 3) (z : ParabolicSpace) :
    Measurable fun ω => hairerSpatialGradient N (Y ω) i z := by
  unfold hairerSpatialGradient
  refine measurable_fderiv_apply_of_family (fun ω x => hairerSpatialSection N (Y ω) z x)
    (fun x => measurable_hairerConvolution_apply N hY (z.1, x)) (fun ω => ?_) z.2 _
  have h := (contDiff_hairerConvolution N (hs ω)).differentiable (by simp)
  exact h.comp ((differentiable_const _).prodMk differentiable_id)

end RegularityStructures.Phi43

end
