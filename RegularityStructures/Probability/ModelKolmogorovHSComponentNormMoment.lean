/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovNorm

/-!
# Component norm moments imply model norm moments

These are the final finite-sector algebraic closure lemmas used after the
`Π`- and `Γ`-sector estimates in Hairer--Steele, arXiv:2301.10081v3,
Theorem B.1.  The premises are moments of the actual component norms; no
random pathwise bound or conclusion-shaped certificate is assumed.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace RegularityStructures

private theorem component_nat_add_pow_le (p : ℕ) (hp : 1 ≤ p) (a b : ℝ≥0∞) :
    (a + b) ^ p ≤ (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) * (a ^ p + b ^ p) := by
  calc
    (a + b) ^ p = (a + b) ^ (p : ℝ) := by rw [ENNReal.rpow_natCast]
    _ ≤ (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) * (a ^ (p : ℝ) + b ^ (p : ℝ)) :=
      ENNReal.rpow_add_le_mul_rpow_add_rpow a b (by exact_mod_cast hp)
    _ = (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) * (a ^ p + b ^ p) := by
      rw [ENNReal.rpow_natCast, ENNReal.rpow_natCast]

theorem randomModel_normOn_moment_le_of_component_norm_moments
    {ι E Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace E]
    [MeasurableSpace Ω] {μ : Measure E} {P : Measure Ω}
    {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ}
    {M : Ω → Model 𝒯 K} {γ : ℝ} {S : Set E} {p : ℕ}
    (hp : 1 ≤ p)
    (hPiMeas : AEMeasurable (fun ω => (M ω).piNormOn γ S) P)
    (hGammaMeas : AEMeasurable (fun ω => (M ω).gammaNormOn γ S) P)
    {A B : ℝ≥0∞}
    (hPi : ∫⁻ ω, (M ω).piNormOn γ S ^ p ∂P ≤ A)
    (hGamma : ∫⁻ ω, (M ω).gammaNormOn γ S ^ p ∂P ≤ B) :
    AEMeasurable (fun ω => (M ω).normOn γ S) P ∧
      ∫⁻ ω, (M ω).normOn γ S ^ p ∂P ≤
        (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) * (A + B) := by
  have hnorm : AEMeasurable (fun ω => (M ω).normOn γ S) P := by
    change AEMeasurable
      ((fun ω => (M ω).piNormOn γ S) + (fun ω => (M ω).gammaNormOn γ S)) P
    exact hPiMeas.add hGammaMeas
  have hpoint : ∀ ω, (M ω).normOn γ S ^ p ≤
      (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) *
        (((M ω).piNormOn γ S) ^ p + ((M ω).gammaNormOn γ S) ^ p) := by
    intro ω
    simpa only [Model.normOn] using
      component_nat_add_pow_le p hp ((M ω).piNormOn γ S) ((M ω).gammaNormOn γ S)
  refine ⟨hnorm, ?_⟩
  have hsumMeas : AEMeasurable
      (fun ω => ((M ω).piNormOn γ S) ^ p + ((M ω).gammaNormOn γ S) ^ p) P := by
    change AEMeasurable
      ((fun ω => ((M ω).piNormOn γ S) ^ p) +
        (fun ω => ((M ω).gammaNormOn γ S) ^ p)) P
    exact (hPiMeas.pow_const p).add (hGammaMeas.pow_const p)
  have hsumIntegral :
      (∫⁻ ω, ((M ω).piNormOn γ S) ^ p + ((M ω).gammaNormOn γ S) ^ p ∂P) =
        ∫⁻ ω, ((M ω).piNormOn γ S) ^ p ∂P +
          ∫⁻ ω, ((M ω).gammaNormOn γ S) ^ p ∂P := by
    exact lintegral_add_left' (hPiMeas.pow_const p)
      (fun ω => ((M ω).gammaNormOn γ S) ^ p)
  calc
    ∫⁻ ω, ((M ω).normOn γ S) ^ p ∂P ≤
        ∫⁻ ω, (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) *
          (((M ω).piNormOn γ S) ^ p + ((M ω).gammaNormOn γ S) ^ p) ∂P :=
      lintegral_mono hpoint
    _ = (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) *
        (∫⁻ ω, ((M ω).piNormOn γ S) ^ p ∂P +
          ∫⁻ ω, ((M ω).gammaNormOn γ S) ^ p ∂P) := by
      rw [lintegral_const_mul'' _ hsumMeas, hsumIntegral]
    _ ≤ (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) * (A + B) := by
      gcongr

theorem randomModel_diffNormOn_moment_le_of_component_norm_moments
    {ι E Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace E]
    [MeasurableSpace Ω] {μ : Measure E} {P : Measure Ω}
    {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ}
    {M₁ M₂ : Ω → Model 𝒯 K} {γ : ℝ} {S : Set E} {p : ℕ}
    (hp : 1 ≤ p)
    (hPiMeas : AEMeasurable (fun ω => (M₁ ω).piDiffNormOn (M₂ ω) γ S) P)
    (hGammaMeas : AEMeasurable
      (fun ω => (M₁ ω).gammaDiffNormOn (M₂ ω) γ S) P)
    {A B : ℝ≥0∞}
    (hPi : ∫⁻ ω, (M₁ ω).piDiffNormOn (M₂ ω) γ S ^ p ∂P ≤ A)
    (hGamma : ∫⁻ ω, (M₁ ω).gammaDiffNormOn (M₂ ω) γ S ^ p ∂P ≤ B) :
    AEMeasurable (fun ω => (M₁ ω).diffNormOn (M₂ ω) γ S) P ∧
      ∫⁻ ω, (M₁ ω).diffNormOn (M₂ ω) γ S ^ p ∂P ≤
        (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) * (A + B) := by
  have hnorm : AEMeasurable (fun ω => (M₁ ω).diffNormOn (M₂ ω) γ S) P := by
    change AEMeasurable
      ((fun ω => (M₁ ω).piDiffNormOn (M₂ ω) γ S) +
        (fun ω => (M₁ ω).gammaDiffNormOn (M₂ ω) γ S)) P
    exact hPiMeas.add hGammaMeas
  have hpoint : ∀ ω, (M₁ ω).diffNormOn (M₂ ω) γ S ^ p ≤
      (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) *
        (((M₁ ω).piDiffNormOn (M₂ ω) γ S) ^ p +
          ((M₁ ω).gammaDiffNormOn (M₂ ω) γ S) ^ p) := by
    intro ω
    simpa only [Model.diffNormOn] using
      component_nat_add_pow_le p hp
        ((M₁ ω).piDiffNormOn (M₂ ω) γ S)
        ((M₁ ω).gammaDiffNormOn (M₂ ω) γ S)
  refine ⟨hnorm, ?_⟩
  have hsumMeas : AEMeasurable
      (fun ω => ((M₁ ω).piDiffNormOn (M₂ ω) γ S) ^ p +
        ((M₁ ω).gammaDiffNormOn (M₂ ω) γ S) ^ p) P := by
    change AEMeasurable
      ((fun ω => ((M₁ ω).piDiffNormOn (M₂ ω) γ S) ^ p) +
        (fun ω => ((M₁ ω).gammaDiffNormOn (M₂ ω) γ S) ^ p)) P
    exact (hPiMeas.pow_const p).add (hGammaMeas.pow_const p)
  have hsumIntegral :
      (∫⁻ ω, ((M₁ ω).piDiffNormOn (M₂ ω) γ S) ^ p +
        ((M₁ ω).gammaDiffNormOn (M₂ ω) γ S) ^ p ∂P) =
          ∫⁻ ω, ((M₁ ω).piDiffNormOn (M₂ ω) γ S) ^ p ∂P +
            ∫⁻ ω, ((M₁ ω).gammaDiffNormOn (M₂ ω) γ S) ^ p ∂P := by
    exact lintegral_add_left' (hPiMeas.pow_const p)
      (fun ω => ((M₁ ω).gammaDiffNormOn (M₂ ω) γ S) ^ p)
  calc
    ∫⁻ ω, ((M₁ ω).diffNormOn (M₂ ω) γ S) ^ p ∂P ≤
        ∫⁻ ω, (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) *
          (((M₁ ω).piDiffNormOn (M₂ ω) γ S) ^ p +
            ((M₁ ω).gammaDiffNormOn (M₂ ω) γ S) ^ p) ∂P :=
      lintegral_mono hpoint
    _ = (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) *
        (∫⁻ ω, ((M₁ ω).piDiffNormOn (M₂ ω) γ S) ^ p ∂P +
          ∫⁻ ω, ((M₁ ω).gammaDiffNormOn (M₂ ω) γ S) ^ p ∂P) := by
      rw [lintegral_const_mul'' _ hsumMeas, hsumIntegral]
    _ ≤ (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) * (A + B) := by
      gcongr

end RegularityStructures

end
