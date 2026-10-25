/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.StochasticHeatConvergenceGrowth
public import Phi43.Stochastic.WickPowerEstimatesMollifierMass
import Mathlib.Tactic

/-!
# Almost sure polynomial growth of the regularised noise at every scale `ε > 0`

`regularisedNoise_ae_hasPhi43NoiseGrowth` is stated for `ε ∈ (0, 1]`.  Since
`ρ_ε = rescale ρ ε` is again a mollifier and `rescale (rescale ρ ε) 1 = rescale ρ ε`, a regularised
noise at scale `ε` for `ρ` is a regularised noise at scale `1` for `ρ_ε`; this gives the almost sure
growth for every `ε > 0` (`regularisedNoise_ae_hasPhi43NoiseGrowth_of_pos`).
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

theorem rescale_one (ρ : ℝ × (Fin 3 → ℝ) → ℝ) : rescale ρ 1 = ρ := by
  funext z
  simp [rescale]

theorem rescale_rescale_one (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ) :
    rescale (rescale ρ ε) 1 = rescale ρ ε :=
  rescale_one _

/-- The parabolic rescaling of a mollifier is a mollifier. -/
theorem isMollifier_rescale {ρ : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε) :
    IsMollifier (rescale ρ ε) := by
  have hc1 : ε ^ (-2 : ℤ) ≠ 0 := zpow_ne_zero _ hε.ne'
  have hc2 : ε⁻¹ ≠ 0 := inv_ne_zero hε.ne'
  have hφ : (fun z : ℝ × (Fin 3 → ℝ) => (ε ^ (-2 : ℤ) * z.1, ε⁻¹ • z.2)) =
      ⇑((Homeomorph.smulOfNeZero (ε ^ (-2 : ℤ)) hc1).prodCongr
        (Homeomorph.smulOfNeZero (ε⁻¹) hc2)) := rfl
  refine ⟨?_, ?_, wick_integral_rescale_eq_one hρ hε⟩
  · unfold rescale
    refine contDiff_const.mul (hρ.contDiff.comp ?_)
    exact (contDiff_const.mul contDiff_fst).prodMk (contDiff_snd.const_smul _)
  · have h := hρ.hasCompactSupport.comp_homeomorph
      ((Homeomorph.smulOfNeZero (ε ^ (-2 : ℤ)) hc1).prodCongr (Homeomorph.smulOfNeZero (ε⁻¹) hc2))
    have h2 := h.mul_left (f := fun _ : ℝ × (Fin 3 → ℝ) => ε ^ (-5 : ℤ))
    exact h2

/-- A regularised noise at scale `ε` for `ρ` is one at scale `1` for `ρ_ε`. -/
theorem isRegularisedNoise_rescale {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : (SpaceTime → ℝ) → Ω → ℝ} {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ}
    (hξ : IsRegularisedNoise P W ρ ε ξ) : IsRegularisedNoise P W (rescale ρ ε) 1 ξ := by
  refine ⟨hξ.1, fun z => ?_⟩
  have e : mollifierAt (rescale ρ ε) 1 z = mollifierAt ρ ε z := by
    funext w
    simp only [mollifierAt, periodise, rescale_rescale_one]
  rw [e]
  exact hξ.2 z

/-- **Almost sure polynomial growth for every scale `ε > 0`.** -/
theorem regularisedNoise_ae_hasPhi43NoiseGrowth_of_pos {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {W : (SpaceTime → ℝ) → Ω → ℝ}
    (hW : IsWhiteNoise P W) {ρ : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ) {ε : ℝ}
    (hε : 0 < ε) {ξ : Ω → SpaceTime → ℝ} (hξ : IsRegularisedNoise P W ρ ε ξ) :
    ∀ᵐ ω ∂P, Statements.HasPhi43NoiseGrowth (ξ ω) :=
  regularisedNoise_ae_hasPhi43NoiseGrowth P W hW (rescale ρ ε) (isMollifier_rescale hρ hε)
    (ε := 1) ⟨one_pos, le_rfl⟩ ξ (isRegularisedNoise_rescale hξ)

end RegularityStructures.Phi43

end
