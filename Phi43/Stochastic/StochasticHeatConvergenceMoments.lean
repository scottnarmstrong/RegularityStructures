/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.StationaryField
public import Phi43.Stochastic.AnnealedNoiseTorus
public import Phi43.Torus.KernelBoundsFacts

/-!
# Gaussian moment inputs for the spatially heat-smoothed stationary field

This module isolates the Gaussian part of the linear stochastic heat estimate.  The spatially
smoothed deterministic kernel is

`h_{ε,s,z}(w) = ∫_{T³} p_s(y) G_ε((t,x-y)-w) dy`,

so the corresponding random variable is the white-noise pairing `W h_{ε,s,z}`.  The remaining
analytic input is an `L²` estimate on `h_{ε,s,z}`; the lemmas below turn that estimate into the
second and all even moment bounds, uniformly in the later random parameters.

The pointwise stationary-field estimate at the end records the direct consequence of K3.  It is
not a substitute for the spatial convolution estimate: K3 alone controls `Ψ_ε(z)`, whereas the
heat-smoothed bounds require the additional deterministic convolution calculation.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace RegularityStructures.Phi43

variable {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ}

/-- The deterministic space-smoothed kernel representing `P_s Ψ_ε(t,x)`. -/
def stochasticHeatKernel (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε s : ℝ) (z : SpaceTime) :
    SpaceTime → ℝ := fun w =>
  ∫ y : Torus3, heatKernel s y *
    mollifiedKernel ρ ε ((z.1, z.2 - y) - w)

/-- The white-noise pairing with the spatially heat-smoothed stationary kernel. -/
def stochasticHeatField {Ω : Type*} (W : (SpaceTime → ℝ) → Ω → ℝ)
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε s : ℝ) (z : SpaceTime) : Ω → ℝ :=
  W (stochasticHeatKernel ρ ε s z)

end RegularityStructures.Phi43

end

public section

open MeasureTheory ProbabilityTheory

namespace RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : (SpaceTime → ℝ) → Ω → ℝ}

/-- The white-noise pairing has the variance of its deterministic kernel. -/
theorem stochasticHeat_pairing_second_moment_eq
    (hW : IsWhiteNoise P W) {h : SpaceTime → ℝ} (hh : MemLp h 2) :
    ∫ ω, |W h ω| ^ 2 ∂P = ∫ z, h z ^ 2 := by
  exact whiteNoise_pairing_abs_sq_integral hW hh

/-- Even Gaussian moments are controlled by a uniform second-moment bound. -/
theorem stochasticHeat_pairing_even_abs_moment_le
    (hW : IsWhiteNoise P W) {h : SpaceTime → ℝ} (hh : MemLp h 2)
    {V : ℝ} (hsecond : ∫ z, h z ^ 2 ≤ V) (m : ℕ) :
    ∫ ω, |W h ω| ^ (2 * m) ∂P ≤
      (∫ x, |x| ^ (2 * m) ∂gaussianReal 0 1) * V ^ m := by
  have hY : HasGaussianLaw (W h) P := whiteNoise_pairing_hasGaussianLaw hW hh
  have h0 : ∫ ω, W h ω ∂P = 0 := whiteNoise_pairing_integral_eq_zero hW hh
  have hvar : Var[W h; P] ≤ V := by
    calc
      Var[W h; P] = ∫ ω, |W h ω| ^ 2 ∂P := by
        rw [variance_of_integral_eq_zero (hW.1 h hh).aemeasurable h0]
        apply integral_congr_ae
        filter_upwards [] with ω
        simp [sq_abs]
      _ = ∫ z, h z ^ 2 := stochasticHeat_pairing_second_moment_eq hW hh
      _ ≤ V := hsecond
  have hvar_nonneg : 0 ≤ Var[W h; P] := variance_nonneg _ _
  have hmoment := gaussian_even_abs_moment_eq hY h0 m
  have hpow : (Var[W h; P]) ^ m ≤ V ^ m := pow_le_pow_left₀ hvar_nonneg hvar m
  have hgauss_nonneg : 0 ≤ ∫ x, |x| ^ (2 * m) ∂gaussianReal 0 1 :=
    integral_nonneg fun x => by positivity
  change ∫ ω, |W h ω| ^ (2 * m) ∂P ≤ _
  rw [hmoment]
  exact mul_le_mul_of_nonneg_left hpow hgauss_nonneg

end RegularityStructures

end

