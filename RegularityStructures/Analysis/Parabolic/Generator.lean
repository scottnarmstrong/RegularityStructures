/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Parabolic.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The generator of the auxiliary parabolic semigroup

The auxiliary semigroup `Q_t` on `ℝ⁴` (`RegularityStructures.Analysis.Kernel.ParabolicSemigroup`)
has kernel `q_t(z) = g_t(z₀) ∏ᵢ k_t(zᵢ)` with `g_t = ∫ e^{-tξ²} cos(2πξ·) dξ` and
`k_t = ∫ e^{-tξ⁴} cos(2πξ·) dξ`, so `∂_t g_t = (4π²)⁻¹ ∂² g_t` and `∂_t k_t = -(16π⁴)⁻¹ ∂⁴ k_t`. Its
generator is

  `L φ = (4π²)⁻¹ ∂₀² φ − (16π⁴)⁻¹ ∑ᵢ ∂ᵢ⁴ φ`,

an operator of parabolic order `ℓ = 4` (Hoshino arXiv:2310.07396v2, Example 2.7, with the
anisotropic `∑ᵢ ∂ᵢ⁴` in place of `Δ²`). Partial derivatives are taken as iterated Fréchet
derivatives along the coordinate directions `timeDir = (1, 0)` and `spaceDir i = (0, eᵢ)`.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The time direction `(1, 0)` of `ℝ⁴`. -/
def timeDir : ParabolicSpace := (1, 0)

/-- The space direction `(0, eᵢ)` of `ℝ⁴`. -/
def spaceDir (i : Fin 3) : ParabolicSpace := (0, Pi.single i 1)

/-- The coefficient `(4π²)⁻¹` of `∂₀²` in the generator. -/
def generatorTimeCoeff : ℝ := (4 * Real.pi ^ 2)⁻¹

/-- The coefficient `(16π⁴)⁻¹` of `∂ᵢ⁴` in the generator. -/
def generatorSpaceCoeff : ℝ := (16 * Real.pi ^ 4)⁻¹

/-- The generator `L φ = (4π²)⁻¹ ∂₀² φ − (16π⁴)⁻¹ ∑ᵢ ∂ᵢ⁴ φ` of the auxiliary semigroup. -/
def parabolicGenerator (φ : ParabolicSpace → ℝ) (w : ParabolicSpace) : ℝ :=
  generatorTimeCoeff * iteratedFDeriv ℝ 2 φ w (fun _ => timeDir) -
    generatorSpaceCoeff * ∑ i, iteratedFDeriv ℝ 4 φ w (fun _ => spaceDir i)

end RegularityStructures

end

public section

namespace RegularityStructures

theorem generatorTimeCoeff_pos : 0 < generatorTimeCoeff := by
  unfold generatorTimeCoeff
  have := Real.pi_pos
  positivity

theorem generatorSpaceCoeff_pos : 0 < generatorSpaceCoeff := by
  unfold generatorSpaceCoeff
  have := Real.pi_pos
  positivity

theorem norm_timeDir : ‖timeDir‖ = 1 := by
  simp [timeDir, Prod.norm_def]

theorem norm_spaceDir (i : Fin 3) : ‖spaceDir i‖ = 1 := by
  simp [spaceDir, Prod.norm_def, Pi.norm_single]

end RegularityStructures

end
