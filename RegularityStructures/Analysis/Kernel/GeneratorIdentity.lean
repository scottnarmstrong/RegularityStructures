/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Kernel.GeneratorMoment
public import RegularityStructures.Analysis.Semigroup.Pairing.Fubini
public import RegularityStructures.Analysis.Parabolic.GeneratorScaling.Algebra

/-!
# The generator identity for the auxiliary semigroup

For `φ : ℝ⁴ → ℝ` smooth with compact support,
`Q_h φ(z) - φ(z) = ∫_0^h Q_v (L φ)(z) dv`, with
`L = (4π²)⁻¹ ∂₀² - (16π⁴)⁻¹ ∑ᵢ ∂ᵢ⁴` (`parabolicGenerator`), i.e.
`parabolicSemigroup.IsGeneratorPair φ (parabolicGenerator φ)`.

Route: `F(v) = Q_v φ(z)` is differentiable on `(0, ∞)` with
`F'(v) = ∫ (∂_v q_v)(z - y) φ(y) dy` (`hasDerivAt_apply_parabolicSemigroup`), which equals
`Q_v(Lφ)(z)` by the pointwise heat equation and integration by parts
(`integral_parabolicTimeDeriv_mul`); `F(v) → φ(z)` as `v ↓ 0` (`abs_apply_sub_le`); and `F'` is
bounded and measurable (`abs_apply_le`, joint measurability), so the fundamental theorem of
calculus applies on `[0, h]`.
-/

public section

open MeasureTheory Filter Topology Real Set
open scoped ContDiff

namespace RegularityStructures

theorem hasCompactSupport_parabolicGenerator {φ : ParabolicSpace → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) : HasCompactSupport (parabolicGenerator φ) := by
  have h0 := hasCompactSupport_iterate_dirDeriv hc timeDir 2
  have h1 := fun i : Fin 3 => hasCompactSupport_iterate_dirDeriv hc (spaceDir i) 4
  have e : parabolicGenerator φ =
      (fun x => generatorTimeCoeff * x) ∘ ((dirDeriv timeDir)^[2] φ) +
        (fun x => -(generatorSpaceCoeff * x)) ∘
          ((dirDeriv (spaceDir 0))^[4] φ + (dirDeriv (spaceDir 1))^[4] φ +
            (dirDeriv (spaceDir 2))^[4] φ) := by
    funext y
    rw [parabolicGenerator_eq hφ, Fin.sum_univ_three]
    simp only [Function.comp, Pi.add_apply]
    ring
  rw [e]
  have h3 : HasCompactSupport ((dirDeriv (spaceDir 0))^[4] φ + (dirDeriv (spaceDir 1))^[4] φ +
      (dirDeriv (spaceDir 2))^[4] φ) := ((h1 0).add (h1 1)).add (h1 2)
  exact (h0.comp_left (g := fun x => generatorTimeCoeff * x) (by simp)).add
    (h3.comp_left (g := fun x => -(generatorSpaceCoeff * x)) (by simp))

/-- **The generator identity**: for `φ` smooth with compact support,
`Q_h φ - φ = ∫_0^h Q_v (L φ) dv`. -/
theorem parabolicSemigroup_isGeneratorPair {φ : ParabolicSpace → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) : parabolicSemigroup.IsGeneratorPair φ (parabolicGenerator φ) := by
  intro h hh z
  set ψ := parabolicGenerator φ with hψdef
  have hψc := continuous_parabolicGenerator hφ
  obtain ⟨Bψ, hBψ⟩ := hψc.bounded_above_of_compact_support (hasCompactSupport_parabolicGenerator hφ hc)
  obtain ⟨C, hC⟩ := abs_apply_sub_le hφ hc
  -- the primitive `G`, with the value `φ z` at `0`
  set G : ℝ → ℝ := fun v => if v = 0 then φ z else parabolicSemigroup.apply v φ z with hG
  have hGpos : ∀ v, 0 < v → G v = parabolicSemigroup.apply v φ z := fun v hv => by
    simp [hG, hv.ne']
  have hderiv : ∀ v, 0 < v → HasDerivAt G (parabolicSemigroup.apply v ψ z) v := by
    intro v hv
    have h1 := hasDerivAt_apply_parabolicSemigroup hv hφ.continuous hc z
    rw [integral_parabolicTimeDeriv_mul hv hφ hc z] at h1
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hv] with x hx
    exact hGpos x hx
  have hG0 : G 0 = φ z := by simp [hG]
  have hcont : ContinuousOn G (Icc 0 h) := by
    intro v hv
    rcases eq_or_lt_of_le hv.1 with h0 | hpos
    · subst h0
      have hb : ∀ x ∈ Icc (0 : ℝ) h, |G x - φ z| ≤ C * x ^ (1 / 4 : ℝ) := by
        intro x hx
        rcases eq_or_lt_of_le hx.1 with hx0 | hxp
        · subst hx0
          simp [hG0]
        · rw [hGpos x hxp]
          exact hC x hxp z
      have hlim : Tendsto (fun x => |G x - φ z|) (𝓝[Icc 0 h] 0) (𝓝 0) := by
        refine squeeze_zero' (Filter.Eventually.of_forall fun x => abs_nonneg _)
          (eventually_nhdsWithin_of_forall hb) ?_
        have hc0 : Continuous fun x : ℝ => C * x ^ (1 / 4 : ℝ) :=
          continuous_const.mul (Real.continuous_rpow_const (by norm_num))
        have := (hc0.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Icc 0 h))
        simpa [Real.zero_rpow (by norm_num : (1 / 4 : ℝ) ≠ 0)] using this
      show Tendsto G (𝓝[Icc 0 h] 0) (𝓝 (G 0))
      rw [hG0, tendsto_iff_dist_tendsto_zero]
      simpa [Real.dist_eq] using hlim
    · exact (hderiv v hpos).continuousAt.continuousWithinAt
  have hint : IntervalIntegrable (fun v => parabolicSemigroup.apply v ψ z) volume 0 h := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hh.le]
    have hmeas : Measurable fun v : ℝ => parabolicSemigroup.apply v ψ z :=
      (RegularisingSemigroup.measurable_apply_uncurry parabolicSemigroup_isJointMeasurable hψc.measurable).comp
        (measurable_id.prodMk measurable_const)
    refine Measure.integrableOn_of_bounded (M := parabolicMomentConst 0 * Bψ) (by simp)
      hmeas.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun v hv => ?_)
    rw [Real.norm_eq_abs]
    exact abs_apply_le (fun y => by simpa using hBψ y) hv.1 z
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hh.le hcont
    (fun v hv => hderiv v hv.1) hint
  rw [this, hGpos h hh, hG0]

end RegularityStructures

end
