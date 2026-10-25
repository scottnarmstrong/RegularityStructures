/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.RegularisedNoise.Properties
public import Phi43.Constants.Finite
public import Phi43.Stochastic.AnnealedNoiseTorus
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Uniform pointwise moments of an arbitrary regularised noise

The hypotheses are exactly `IsWhiteNoise` and `IsRegularisedNoise`. Translation invariance
identifies the second moment at every space-time point with the L² mass of the periodised mollifier.
The uniform first moment is used to control the weighted remote past in the pathwise construction of
the stationary linear field.
-/

public noncomputable section

open MeasureTheory Real ProbabilityTheory

namespace RegularityStructures.Phi43

theorem regularisedNoise_memLp_two
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : (SpaceTime → ℝ) → Ω → ℝ} (hW : IsWhiteNoise P W)
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε)
    (ξ : Ω → SpaceTime → ℝ) (hξ : IsRegularisedNoise P W ρ ε ξ) (z : SpaceTime) :
    MemLp (fun ω => ξ ω z) 2 P := by
  have hgauss := whiteNoise_pairing_hasGaussianLaw hW (memLp_mollifierAt ρ hρ hε z)
  exact (memLp_congr_ae (hξ.2 z).2).mpr hgauss.memLp_two

theorem regularisedNoise_second_moment_eq_periodise_sq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : (SpaceTime → ℝ) → Ω → ℝ} (hW : IsWhiteNoise P W)
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε)
    (ξ : Ω → SpaceTime → ℝ) (hξ : IsRegularisedNoise P W ρ ε ξ) (z : SpaceTime) :
    (∫ ω, ξ ω z ^ 2 ∂P) = ∫ v : SpaceTime, periodise ρ ε v ^ 2 := by
  calc
    _ = ∫ ω, W (mollifierAt ρ ε z) ω ^ 2 ∂P := by
      apply integral_congr_ae
      filter_upwards [(hξ.2 z).2] with ω hω
      rw [hω]
    _ = ∫ v : SpaceTime, mollifierAt ρ ε z v ^ 2 :=
      whiteNoise_pairing_sq_integral hW (memLp_mollifierAt ρ hρ hε z)
    _ = ∫ v : SpaceTime, periodise ρ ε v ^ 2 :=
      integral_comp_sub_left_spaceTime (fun v => periodise ρ ε v ^ 2) z

private theorem abs_le_square_add_one (a : ℝ) : |a| ≤ a ^ 2 + 1 := by
  nlinarith only [sq_nonneg (|a| - 1), sq_abs a]

theorem regularisedNoise_first_moment_bound_uniform
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ}, IsWhiteNoise P W →
      ∀ ξ : Ω → SpaceTime → ℝ, IsRegularisedNoise P W ρ ε ξ → ∀ z : SpaceTime,
      (∫ ω, |ξ ω z| ∂P) ≤ C := by
  let V : ℝ := ∫ v : SpaceTime, periodise ρ ε v ^ 2
  have hV : 0 ≤ V := integral_nonneg fun v => sq_nonneg _
  refine ⟨V + 1, add_nonneg hV zero_le_one, ?_⟩
  intro Ω _ P W hW ξ hξ z
  let : IsProbabilityMeasure P := hW.isProbabilityMeasure
  have hm := regularisedNoise_memLp_two hW ρ hρ hε ξ hξ z
  have hi := hm.integrable (by norm_num)
  have hisq := hm.integrable_sq
  calc
    _ ≤ ∫ ω, ξ ω z ^ 2 + 1 ∂P :=
      integral_mono hi.norm (hisq.add (integrable_const (1 : ℝ)))
        (fun ω => abs_le_square_add_one _)
    _ = V + 1 := by
      rw [integral_add hisq (integrable_const (1 : ℝ)),
        regularisedNoise_second_moment_eq_periodise_sq hW ρ hρ hε ξ hξ z]
      simp only [integral_const, probReal_univ, one_smul, V]

end RegularityStructures.Phi43

end
