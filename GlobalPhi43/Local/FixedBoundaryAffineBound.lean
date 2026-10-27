/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.HeatBoundaryFamily

/-! Quantitative boundary-potential affine error with ALL choices before h.
The exact PDE representation attachment remains a separate proof step. -/
@[expose] public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MeasureTheory Set Metric Filter Topology
open scoped ContDiff ENNReal

 def heatBoundaryPotential (k χ : ParabolicSpace → ℝ) (μ : Measure ParabolicSpace)
    (g : ParabolicSpace → ℝ) (p : ParabolicSpace) : ℝ :=
  ∑ i : Option (Fin 3), ∫ q, heatBoundaryKernel k i (p - q) *
    (heatBoundaryCoefficient χ i q * g q) ∂μ

/-- One fixed cutoff, one actual annular kernel extension, and one constant
before every field, measure and radius. The bound costs only H times volume. -/
theorem exists_fixed_heat_boundary_affine_bound :
    ∃ (χ k : ParabolicSpace → ℝ) (C : ℝ),
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ range χ ⊆ Icc 0 1 ∧
      tsupport χ ⊆ closedBall 0 (3 / 4 : ℝ) ∧
      (∀ p ∈ closedBall 0 (1 / 2 : ℝ), χ p = 1) ∧
      ContDiff ℝ ∞ k ∧ HasCompactSupport k ∧
      (∀ p ∈ fixedHeatAnnulus, k =ᶠ[𝓝 p] heatKernelR4) ∧ C > 0 ∧
      ∀ (μ : Measure ParabolicSpace), IsFiniteMeasure μ →
        ∀ (g : ParabolicSpace → ℝ) (H : ℝ), AEStronglyMeasurable g μ → 0 ≤ H →
        (∀ᵐ q ∂μ, |g q| ≤ H) → ∀ (x : ParabolicSpace) (R : ℝ), 0 ≤ R →
        pastAffineError (heatBoundaryPotential k χ μ g) x R ≤
          ENNReal.ofReal (C * H * μ.real univ * R ^ 2) := by
  obtain ⟨χ, hχ, hcχ, hrange, hs, hone⟩ := exists_fixed_heat_cutoff
  obtain ⟨k, hk, hck, he, _⟩ := exists_fixed_annular_heat_kernel
  obtain ⟨C, hC, hbound⟩ := finite_boundary_kernel_affine_bound
    (heatBoundaryKernel k) (heatBoundaryCoefficient χ)
    (heatBoundaryKernel_contDiff hk) (heatBoundaryKernel_hasCompactSupport hck)
    (fun i => (heatBoundaryCoefficient_contDiff hχ i).continuous)
    (heatBoundaryCoefficient_hasCompactSupport hcχ)
  exact ⟨χ, k, C, hχ, hcχ, hrange, hs, hone, hk, hck, he, hC, hbound⟩

end GlobalPhi43.Local
