/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestAllMomentsSetup
public import Phi43.BPHZ.TreeWickCube

/-!
# The regularised noise as a white-noise pairing

Two inputs of the moment equivalence for the regularised noise `ξ` tested against the periodised
semigroup kernel `q^♯_t(z, ·)`:

* `integral_regularisedNoise_sq_le`: the variance of `ξ` at a point is `∫ ρ_ε^♯ ²`;
* `exists_regularisedNoise_pairing`: for every `y`, `ξ(y)` is almost surely the white-noise
  pairing `W (ρ_ε^♯(y - ·))` of a square-integrable function.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- The variance of the regularised noise at a point is `∫ ρ_ε^♯ ²`. -/
theorem integral_regularisedNoise_sq_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : (SpaceTime → ℝ) → Ω → ℝ} {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ}
    (hρ : IsMollifier ρ) (hε : 0 < ε) (hW : IsWhiteNoise P W)
    (hξ : IsRegularisedNoise P W ρ ε ξ) (y : SpaceTime) :
    ∫ ω, ξ ω y ^ 2 ∂P ≤ ∫ w, periodise ρ ε w ^ 2 := by
  have hm := memLp_mollifierAt ρ hρ hε y
  calc ∫ ω, ξ ω y ^ 2 ∂P = ∫ ω, W (mollifierAt ρ ε y) ω * W (mollifierAt ρ ε y) ω ∂P := by
        refine integral_congr_ae ?_
        filter_upwards [(hξ.2 y).2] with ω hω
        rw [hω, sq]
    _ = ∫ w, mollifierAt ρ ε y w * mollifierAt ρ ε y w := whiteNoise_pairing_mul_integral hW hm hm
    _ = ∫ w, periodise ρ ε (y - w) ^ 2 := by
        simp only [mollifierAt, sq]
    _ ≤ ∫ w, periodise ρ ε w ^ 2 :=
        (integral_comp_sub_left_spaceTime (fun w => periodise ρ ε w ^ 2) y).le

/-- The regularised noise is a white-noise pairing. -/
theorem exists_regularisedNoise_pairing {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : (SpaceTime → ℝ) → Ω → ℝ} {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ}
    (hρ : IsMollifier ρ) (hε : 0 < ε) (hξ : IsRegularisedNoise P W ρ ε ξ) (y : SpaceTime) :
    ∃ h : SpaceTime → ℝ, MemLp h 2 ∧ (fun ω => ξ ω y) =ᵐ[P] W h :=
  ⟨mollifierAt ρ ε y, memLp_mollifierAt ρ hρ hε y, (hξ.2 y).2⟩

end RegularityStructures.Phi43

end
