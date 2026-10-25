/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.StochasticHeatConvergenceCrossMollifierFacts
public import Phi43.Stochastic.StochasticHeatConvergenceBareMollification
public import Phi43.Stochastic.StochasticHeatConvergenceMollifierMass
public import Phi43.Stochastic.StochasticHeatConvergenceMoments

/-!
# Cross-mollifier cancellation of the heat probe

Both periodised profiles have unit mass. Subtracting the common bare kernel therefore centres their
difference without identifying the profiles. This is the cancellation step of [Hai14, Proposition
9.5, (9.17)], for the convergence of the noise potentials (`phi43Noise_cauchy`).
-/

public noncomputable section

open MeasureTheory Real

namespace RegularityStructures.Phi43

private theorem memLp_two_of_integrable_bound {p : SpaceTime → ℝ}
    (hp : Measurable p) (hp1 : Integrable p) {B : ℝ} (hpB : ∀ v, |p v| ≤ B) : MemLp p 2 := by
  apply (memLp_two_iff_integrable_sq hp.aestronglyMeasurable).mpr
  have hi := hp1.mul_bdd hp.aestronglyMeasurable
    (Filter.Eventually.of_forall fun v => by simpa only [Real.norm_eq_abs] using hpB v)
  simpa only [pow_two] using hi

theorem stochasticHeatKernel_cross_difference_eq_centered
    (ρ ρ' : ParabolicSpace → ℝ) (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ')
    {ε ε' s : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hε' : 0 < ε') (hε'1 : ε' ≤ 1)
    (hs : 0 < s) (z w : SpaceTime) :
    stochasticHeatKernel ρ ε s z w - stochasticHeatKernel ρ' ε' s z w =
      ∫ v : SpaceTime, (bareHeatRegularisedKernel s (z - w - v) -
        bareHeatRegularisedKernel s (z - w)) * (periodise ρ ε v - periodise ρ' ε' v) := by
  obtain ⟨B, hB⟩ := bounded_periodise ρ hρ hε
  obtain ⟨B', hB'⟩ := bounded_periodise ρ' hρ' hε'
  have hp2 := memLp_two_of_integrable_bound (measurable_periodise ρ hρ)
    (integrable_periodise ρ hρ hε) hB
  have hp2' := memLp_two_of_integrable_bound (measurable_periodise ρ' hρ')
    (integrable_periodise ρ' hρ' hε') hB'
  have hm := memLp_comp_sub_left_spaceTime (memLp_bareHeatRegularisedKernel hs) (z - w)
  have hi := hm.integrable_mul hp2
  have hi' := hm.integrable_mul hp2'
  let p : SpaceTime → ℝ := fun v => periodise ρ ε v - periodise ρ' ε' v
  have hp1 : Integrable p := (integrable_periodise ρ hρ hε).sub (integrable_periodise ρ' hρ' hε')
  have hmass : ∫ v : SpaceTime, p v = 0 := by
    rw [integral_sub (integrable_periodise ρ hρ hε)
      (integrable_periodise ρ' hρ' hε'),
      stochasticHeat_integral_periodise_eq_one ρ hρ hε hε1,
      stochasticHeat_integral_periodise_eq_one ρ' hρ' hε' hε'1, sub_self]
  have hip : Integrable (fun v : SpaceTime => bareHeatRegularisedKernel s (z - w - v) * p v) := by
    apply (hi.sub hi').congr
    filter_upwards [] with v
    simp only [Pi.sub_apply, Pi.mul_apply]
    dsimp [p]
    ring
  rw [stochasticHeatKernel_eq_bare_convolution ρ hρ hε hs,
    stochasticHeatKernel_eq_bare_convolution ρ' hρ' hε' hs,
    ← integral_sub (f := fun v => bareHeatRegularisedKernel s (z - w - v) * periodise ρ ε v)
      (g := fun v => bareHeatRegularisedKernel s (z - w - v) * periodise ρ' ε' v) hi hi']
  calc
    _ = ∫ v : SpaceTime, bareHeatRegularisedKernel s (z - w - v) * p v := by
      apply integral_congr_ae
      filter_upwards [] with v
      dsimp [p]
      ring
    _ = ∫ v : SpaceTime, (bareHeatRegularisedKernel s (z - w - v) -
        bareHeatRegularisedKernel s (z - w)) * p v := by
      have heq : (fun v : SpaceTime => (bareHeatRegularisedKernel s (z - w - v) -
          bareHeatRegularisedKernel s (z - w)) * p v) =
          (fun v => bareHeatRegularisedKernel s (z - w - v) * p v -
            bareHeatRegularisedKernel s (z - w) * p v) := by funext v; ring
      rw [heq, integral_sub hip (hp1.const_mul _), integral_const_mul, hmass, mul_zero, sub_zero]

end RegularityStructures.Phi43

end

