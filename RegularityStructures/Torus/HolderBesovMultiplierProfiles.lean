/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.HolderBesovLittlewoodPaley
public import RegularityStructures.Torus.HolderBesovTensorMultiplier
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Fixed Schwartz profiles for the heat/Besov comparison

The tensor cutoff and the localized inverse heat multiplier are smooth compactly supported
profiles. In scaled frequency coordinates the latter is `cutoff(u) exp(4 π² τ u²)`;
the parameters needed for consecutive dyadic levels are fixed (`τ = 1` and `τ = 1/4`).
Consequently the preceding Poisson multiplier bound is uniform in the dyadic level.

These are the actual cutoff profiles, not multiplier hypotheses.
-/

@[expose] public noncomputable section

open scoped ENNReal SchwartzMap

namespace RegularityStructures

open scoped ContDiff in
/-- The fixed one-dimensional complexified frequency cutoff, as a Schwartz function. -/
def torusLPCutoffProfile : 𝓢(ℝ, ℂ) :=
  (torusLPBump.hasCompactSupport.comp_left (g := Complex.ofRealCLM) rfl).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp torusLPBump.contDiff)

theorem torusLPCutoffProfile_apply (u : ℝ) :
    torusLPCutoffProfile u = (torusLPBump u : ℂ) := rfl

open scoped ContDiff in
/-- The fixed compactly supported inverse-heat frequency multiplier profile. -/
def torusLPInverseHeatProfile (τ : ℝ) : 𝓢(ℝ, ℂ) :=
  (show HasCompactSupport (fun u : ℝ => (torusLPBump u : ℂ) *
      Complex.exp ((4 * Real.pi ^ 2 * τ * u ^ 2 : ℝ) : ℂ)) from
    (torusLPBump.hasCompactSupport.comp_left (g := Complex.ofRealCLM) rfl).mul_right).toSchwartzMap
      ((Complex.ofRealCLM.contDiff.comp torusLPBump.contDiff).mul
        (Complex.contDiff_exp.comp (Complex.ofRealCLM.contDiff.comp
          (contDiff_const.mul (contDiff_id.pow 2)))))

theorem torusLPInverseHeatProfile_apply (τ u : ℝ) :
    torusLPInverseHeatProfile τ u = (torusLPBump u : ℂ) *
      Complex.exp ((4 * Real.pi ^ 2 * τ * u ^ 2 : ℝ) : ℂ) := rfl

theorem torusLPCutoffProfile_eq_zero {u : ℝ} (hu : 2 ≤ |u|) :
    torusLPCutoffProfile u = 0 := by
  rw [torusLPCutoffProfile_apply]
  have hz : torusLPBump u = 0 := torusLPBump.zero_of_le_dist (by
    simpa only [torusLPBump, Real.dist_eq, sub_zero] using hu)
  rw [hz, Complex.ofReal_zero]

theorem torusLPInverseHeatProfile_eq_zero (τ : ℝ) {u : ℝ} (hu : 2 ≤ |u|) :
    torusLPInverseHeatProfile τ u = 0 := by
  rw [torusLPInverseHeatProfile_apply]
  have hz : (torusLPBump u : ℂ) = 0 := torusLPCutoffProfile_eq_zero hu
  rw [hz, zero_mul]

end RegularityStructures

end
