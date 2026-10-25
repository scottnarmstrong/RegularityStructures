/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.ClassicalSolution.MeasurableStability

/-!
# Measurability of classical solutions driven by a regularised noise

This is the measurability half of item (W5) of Lemma 4.1 of the statement.  A regularised noise is measurable as a continuous path on every compact
time interval.  The maximum-principle stability estimate factors the classical solution through
that path, and the negative-order Holder--Besov map is continuous.
-/

public section

open MeasureTheory Set Function
open scoped NNReal ENNReal Topology

namespace RegularityStructures.Phi43

/-- **(W5), measurability.** Solutions driven by a regularised noise are measurable in `ω`. -/
theorem classicalSolution_measurable (η : NegExponent) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : (SpaceTime → ℝ) → Ω → ℝ)
    (hW : IsWhiteNoise P W) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) {ε : ℝ}
    (hε : ε ∈ Ioc (0 : ℝ) 1) (ξ : Ω → SpaceTime → ℝ) (hξ : IsRegularisedNoise P W ρ ε ξ)
    (c : ℝ) (u₀ : C(Torus3, ℝ)) (hu₀ : IsSmoothOnTorus u₀) (u : Ω → ℝ → C(Torus3, ℝ))
    (hu : ∀ ω, IsClassicalSolution c (ξ ω) u₀ (u ω)) {t : ℝ} (ht : 0 ≤ t) :
    Measurable fun ω => toHolderBesov η (u ω t) := by
  have _hW := hW
  have _hρ := hρ
  have _hε := hε
  have _hu₀ := hu₀
  let F : Ω → C(Set.Icc (0 : ℝ) t × Torus3, ℝ) := fun ω =>
    ContinuousMap.mk (fun z : Set.Icc (0 : ℝ) t × Torus3 => ξ ω (z.1.1, z.2)) <| by
      exact (Continuous.continuous_of_isSmoothOnSpaceTime (hξ.1 ω)).comp
        ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hF : Measurable F := by
    simpa [F] using
      (regularisedNoise_restriction_measurable P W ρ ε t ξ hξ)
  let G : Ω → HolderBesov η := fun ω => toHolderBesov η (u ω t)
  have hG : Measurable G := by
    let L : ℝ≥0 := ⟨t * Real.exp (|c| * t),
      mul_nonneg ht (Real.exp_nonneg _)⟩
    refine measurable_of_lipschitz_range F G hF (K := L) ?_
    intro ω ω'
    have hforce : ∀ s ∈ Icc (0 : ℝ) t, ∀ x : Torus3,
        |ξ ω (s, x) - ξ ω' (s, x)| ≤ ‖F ω - F ω'‖ := by
      intro s hs x
      let z : Set.Icc (0 : ℝ) t × Torus3 := (⟨s, hs⟩, x)
      have hz := ContinuousMap.norm_coe_le_norm (F ω - F ω') z
      simpa [F, z, Real.norm_eq_abs] using hz
    have hstab := classicalSolution_sup_stability c (hu ω) (hu ω') ht
      ‖F ω - F ω'‖ (norm_nonneg _) hforce
    have hholder : dist (G ω) (G ω') ≤
        (L : ℝ) * dist (F ω) (F ω') := by
      dsimp [G]
      rw [dist_eq_norm]
      have hnorm : ‖toHolderBesov η (u ω t) - toHolderBesov η (u ω' t)‖ ≤
          ‖u ω t - u ω' t‖ := by
        rw [← toHolderBesov_sub η, norm_toHolderBesov]
        rw [← ENNReal.toReal_ofReal (norm_nonneg (u ω t - u ω' t)), ofReal_norm]
        exact ENNReal.toReal_mono enorm_ne_top
          (holderBesovENorm_le η.2.le (u ω t - u ω' t))
      calc
        ‖toHolderBesov η (u ω t) - toHolderBesov η (u ω' t)‖ ≤
            ‖u ω t - u ω' t‖ := hnorm
        _ ≤ ‖F ω - F ω'‖ * t * Real.exp (|c| * t) := hstab t ⟨ht, le_rfl⟩
        _ = (L : ℝ) * dist (F ω) (F ω') := by
          rw [dist_eq_norm]
          change ‖F ω - F ω'‖ * t * Real.exp (|c| * t) =
            (t * Real.exp (|c| * t)) * ‖F ω - F ω'‖
          ring
    rw [edist_dist]
    rw [edist_dist]
    rw [ENNReal.coe_nnreal_eq, ← ENNReal.ofReal_mul (show 0 ≤ (L : ℝ) from L.2)]
    exact ENNReal.ofReal_le_ofReal hholder
  simpa [G] using hG

end RegularityStructures.Phi43

end
