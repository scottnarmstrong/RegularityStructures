/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.StochasticHeatConvergenceHeatPairing
public import Phi43.Stochastic.StochasticHeatConvergenceUniformGaussianMoments
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Phi43.Stochastic.StochasticHeatConvergenceMoments

/-!
# Uniform heat moments for arbitrary stationary continuous versions

The canonical Gaussian size, time-increment and space-time increment bounds transfer to every
measurable continuous spatial modification by the proved heat-pairing identity. Constants precede
the noise, scale, time, heat scale, and version binders. No moment or covariance bound is assumed.

Source: the linear stationary field following Definition 2.5 of the statement.
-/

public noncomputable section

open MeasureTheory Real

namespace RegularityStructures.Phi43

theorem stationaryField_version_heat_even_moment_bound_uniform
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ}, IsWhiteNoise P W →
      ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → ∀ t : ℝ, ∀ X : Ω → C(Torus3, ℝ), Measurable X →
      (∀ y, (fun ω => X ω y) =ᵐ[P] stationaryField W ρ ε (t, y)) →
      ∀ {s : ℝ}, 0 < s → s ≤ 1 → ∀ x : Torus3,
      (∫ ω, |heatSemigroup s (X ω) x| ^ (2 * m) ∂P) ≤ C * s ^ (-((m : ℝ) / 2)) := by
  obtain ⟨C, hC, hbound⟩ := stochasticHeatField_even_moment_bound_uniform ρ hρ m
  refine ⟨C, hC, ?_⟩
  intro Ω _ P W hW ε hε hε1 t X hXm hX s hs hs1 x
  calc
    _ = ∫ ω, |stochasticHeatField W ρ ε s (t, x) ω| ^ (2 * m) ∂P := by
      apply integral_congr_ae
      exact (heatSemigroup_stationaryField_version_ae hW ρ hρ hε hXm hX hs x).fun_comp
        (fun a : ℝ => |a| ^ (2 * m))
    _ ≤ _ := hbound hW hε hε1 hs hs1 (t, x)

theorem stationaryField_version_heat_time_even_moment_bound_uniform
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ}, IsWhiteNoise P W →
      ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → ∀ t t' : ℝ,
      ∀ X Y : Ω → C(Torus3, ℝ), Measurable X → Measurable Y →
      (∀ y, (fun ω => X ω y) =ᵐ[P] stationaryField W ρ ε (t, y)) →
      (∀ y, (fun ω => Y ω y) =ᵐ[P] stationaryField W ρ ε (t', y)) →
      ∀ {s : ℝ}, 0 < s → s ≤ 1 → ∀ x : Torus3,
      (∫ ω, |heatSemigroup s (X ω - Y ω) x| ^ (2 * m) ∂P) ≤
        C * |t - t'| ^ ((m : ℝ) * θ) * s ^ (-((m : ℝ) / 2 + (m : ℝ) * θ)) := by
  obtain ⟨C, hC, hbound⟩ := stochasticHeatField_time_increment_even_moment_bound_uniform ρ hρ hθ hθ1 m
  refine ⟨C, hC, ?_⟩
  intro Ω _ P W hW ε hε hε1 t t' X Y hXm hYm hX hY s hs hs1 x
  calc
    _ = ∫ ω, |stochasticHeatField W ρ ε s (t, x) ω -
        stochasticHeatField W ρ ε s (t', x) ω| ^ (2 * m) ∂P := by
      apply integral_congr_ae
      filter_upwards [heatSemigroup_stationaryField_version_ae hW ρ hρ hε hXm hX hs x,
        heatSemigroup_stationaryField_version_ae hW ρ hρ hε hYm hY hs x] with ω hω hω'
      rw [sub_eq_add_neg, heatSemigroup_add hs, heatSemigroup_neg, hω, hω']
      rfl
    _ ≤ _ := hbound hW hε hε1 hs hs1 t t' x

end RegularityStructures.Phi43

end
