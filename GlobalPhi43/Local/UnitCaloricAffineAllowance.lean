/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.UnitCaloricBasic
public import GlobalPhi43.Local.SpatialAffineHeat
public import GlobalPhi43.Local.PastBoxAffineGerms

/-! The unit caloric estimate from the actual affine infimum; positive
near-minimizer allowances are removed by a limit. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20 Set Metric Filter Topology
open scoped ContDiff ENNReal

 theorem exists_unit_caloric_affine_allowance : ∃ C > 0,
    ∀ (h : ParabolicSpace → ℝ) (O : Set ParabolicSpace), IsOpen O →
      unitHeatPastCarrier ⊆ O → ContDiffOn ℝ ∞ h O →
      ∀ (H F : ℝ), 0 ≤ H → 0 ≤ F → pastAffineError h 0 1 ≤ ENNReal.ofReal H →
      (∀ p ∈ pastBall (0 : ParabolicSpace) 1, |sourceHeat h p| ≤ F) →
      ∀ R : ℝ, 0 ≤ R → R ≤ 1 / 4 →
        pastAffineError h 0 R ≤ ENNReal.ofReal (C * (H * R ^ 2 + F)) := by
  obtain ⟨C, hC, hbasic⟩ := exists_unit_caloric_basic
  refine ⟨C, hC, ?_⟩
  intro h O hO hKO hh H F hH hF hE hPDE R hR hRsmall
  obtain ⟨g, hg, _, he⟩ := exists_compact_smooth_extension unitHeatPastCarrier_isCompact hO hKO hh
  have heR : pastAffineError g 0 R = pastAffineError h 0 R := by
    apply pastAffineError_congr
    intro y hy
    have hy1 : y ∈ pastBall (0 : ParabolicSpace) 1 := ⟨hy.1.trans_le (by linarith), hy.2⟩
    exact (he y (unit_pastBall_subset_carrier hy1)).self_of_nhds
  have hδ (δ : ℝ) (hδ : 0 < δ) :
      pastAffineError h 0 R ≤ ENNReal.ofReal (C * ((H + δ) * R ^ 2 + F)) := by
    obtain ⟨c, ν, hnear⟩ := exists_past_affine_approximation h 0
      (R := 1) (H := H) (γ := 0) (δ := δ) (by norm_num) hH hδ
      (by simpa only [Real.rpow_zero, mul_one] using hE)
    have hresC := hg.sub (spatialAffine_contDiff 0 c ν)
    have hresB : ∀ p ∈ pastBall (0 : ParabolicSpace) 1, |g p - spatialAffine 0 c ν p| ≤ H + δ := by
      intro p hp
      rw [(he p (unit_pastBall_subset_carrier hp)).self_of_nhds]
      simpa only [Real.rpow_zero, mul_one] using hnear p hp
    have hresPDE : ∀ p ∈ pastBall (0 : ParabolicSpace) 1,
        |sourceHeat (fun q => g q - spatialAffine 0 c ν q) p| ≤ F := by
      intro p hp
      rw [sourceHeat_sub_spatialAffine hg,
        sourceHeat_eq_of_eventuallyEq (he p (unit_pastBall_subset_carrier hp))]
      exact hPDE p hp
    have hmain := hbasic (fun q => g q - spatialAffine 0 c ν q) univ isOpen_univ (subset_univ _)
      hresC.contDiffOn (H + δ) F (by linarith) hF hresB hresPDE R hR hRsmall
    rwa [pastAffineError_sub_affine, heR] at hmain
  have hlim : Tendsto (fun δ : ℝ => ENNReal.ofReal (C * ((H + δ) * R ^ 2 + F)))
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal (C * (H * R ^ 2 + F)))) := by
    have hc : ContinuousAt (fun δ : ℝ => ENNReal.ofReal (C * ((H + δ) * R ^ 2 + F))) 0 := by
      exact ENNReal.continuous_ofReal.continuousAt.comp (by fun_prop)
    simpa only [add_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  filter_upwards [self_mem_nhdsWithin] with δ hpos
  exact hδ δ hpos

end GlobalPhi43.Local
