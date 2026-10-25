/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.StochasticHeatConvergencePolynomialPast
public import Phi43.RegularisedNoise.Properties

/-!
# Existence of massive potentials for smooth polynomial-growth forcings

The zeroth-order consequence of the derivative-growth premise `HasPhi43NoiseGrowth` gives a
polynomial time envelope on the compact torus. Exponential integrability of the
past and local continuity then construct the literal massive heat potential.
This is precisely part (a) of the convergence of the noise potentials (`phi43Noise_cauchy`),
with its predicates unfolded. The kernel is that of equation (2.2) of the statement;
no integrability assumption is added.
-/

public noncomputable section

open MeasureTheory Real

namespace RegularityStructures.Phi43

theorem massivePotential_exists_of_polynomialLift_growth
    (f : SpaceTime → ℝ) (hf : IsSmoothOnSpaceTime f)
    (hg : ∃ (Cg : ℝ) (q : ℕ), ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k (fun w : ParabolicSpace => f (w.1, torusProj w.2)) z‖ ≤
        Cg * (1 + parabolicNorm z) ^ q) :
    ∃ ψ : ℝ → C(Torus3, ℝ), ∀ (t : ℝ) (x : Torus3),
      ψ t x = ∫ w : SpaceTime, massiveHeatKernel ((t, x) - w) * f w := by
  obtain ⟨Cg, q, hg⟩ := hg
  have hzero (z : ParabolicSpace) : |f (z.1, torusProj z.2)| ≤
      Cg * (1 + parabolicNorm z) ^ q := by
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hg 0 (by norm_num) z
  obtain ⟨C, hC, hbound⟩ := polynomial_time_bound_of_polynomialLift_growth hzero
  have hfc : Continuous f := Continuous.continuous_of_isSmoothOnSpaceTime hf
  have hc := continuous_massiveHeatKernel_convolution_of_weighted_past hfc
    (fun a => weighted_past_integrable_of_polynomial_time_bound hfc.measurable hC q hbound a)
  refine ⟨fun t => ⟨fun x => ∫ w : SpaceTime, massiveHeatKernel ((t, x) - w) * f w,
    hc.comp (continuous_const.prodMk continuous_id)⟩, ?_⟩
  intro t x
  rfl

end RegularityStructures.Phi43

end

