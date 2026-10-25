/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductDiagramKernel

/-!
# Merging a propagator into the gain majorant of a kernel

For a gain kernel `a` at `z` and a centre `c`, `|a w| s(c - w)^(-1)` is dominated by the weighted sum
`c₁ s(z)^θ ∑ s(·- w)^(-(4+θ))` over the centres `z, 0, c` (weights `1, 1, 2`)
(`IsGainKernel.ae_abs_mul_singularPow_le`), with and without the slab indicator.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

/-- `|a w| s(c - w)^(-1) ≤ c₁ s(z)^θ ∑ ...` with the slab indicator. -/
theorem IsGainKernel.ae_abs_mul_singularPow_le_indicator {Θ c T : ℝ} {z : SpaceTime}
    {a : SpaceTime → ℝ} (h : IsGainKernel Θ c T z a) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθΘ : θ ≤ Θ)
    (hc : 0 ≤ c) (c' : SpaceTime) :
    ∀ᵐ w : SpaceTime ∂volume, |a w| * singularPow 1 c' w ≤ c * torusParabolicSize z ^ θ *
      Set.indicator {w : SpaceTime | |w.1 - 0| ≤ T}
        (spSum (3 + θ + 1) [(1, z), (1, 0), (2, c')]) w := by
  filter_upwards [h.ae_abs_le_indicator hθ0 hθΘ, ae_torusParabolicSize_sub_pos z,
    ae_torusParabolicSize_sub_pos 0, ae_torusParabolicSize_sub_pos c'] with w h1 hz h0 hc'
  have hs : 0 ≤ c * torusParabolicSize z ^ θ :=
    mul_nonneg hc (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
  have hn := singularPow_nonneg 1 c' w
  by_cases hw : w ∈ {w : SpaceTime | |w.1 - 0| ≤ T}
  · rw [Set.indicator_of_mem hw] at h1 ⊢
    have hm := spSum_mul_singularPow_le (a := 3 + θ) (e := 1) (by linarith) (by norm_num)
      (ps := [(1, z), (1, 0)]) (fun p hp => by
        simp at hp
        rcases hp with rfl | rfl <;> norm_num) c' (w := w) (by
        intro p hp
        simp at hp
        rcases hp with rfl | rfl
        · exact hz
        · exact h0) hc'
    have e : spSum (3 + θ + 1) [(1, z), (1, 0), (2, c')] w =
        spSum (3 + θ + 1) [(1, z), (1, 0)] w + 2 * singularPow (3 + θ + 1) c' w := by
      simp [spSum]; ring
    have e2 : spWeight [((1 : ℝ), z), (1, 0)] = 2 := by simp [spWeight]; norm_num
    rw [e]
    rw [e2] at hm
    calc |a w| * singularPow 1 c' w
        ≤ (c * torusParabolicSize z ^ θ * spSum (3 + θ) [(1, z), (1, 0)] w) *
          singularPow 1 c' w := mul_le_mul_of_nonneg_right h1 hn
      _ = c * torusParabolicSize z ^ θ * (spSum (3 + θ) [(1, z), (1, 0)] w *
          singularPow 1 c' w) := by ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hs
        have : (3 + θ + 1) = (3 + θ) + 1 := rfl
        rw [this]; exact hm
  · rw [Set.indicator_of_notMem hw] at h1 ⊢
    have h2 : |a w| ≤ 0 := by simpa using h1
    have : a w = 0 := abs_nonpos_iff.1 h2
    rw [this]; simp

/-- `|a w| s(c - w)^(-1) ≤ c₁ s(z)^θ ∑ ...` without the slab indicator. -/
theorem IsGainKernel.ae_abs_mul_singularPow_le {Θ c T : ℝ} {z : SpaceTime}
    {a : SpaceTime → ℝ} (h : IsGainKernel Θ c T z a) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθΘ : θ ≤ Θ)
    (hc : 0 ≤ c) (c' : SpaceTime) :
    ∀ᵐ w : SpaceTime ∂volume, |a w| * singularPow 1 c' w ≤ c * torusParabolicSize z ^ θ *
      spSum (3 + θ + 1) [(1, z), (1, 0), (2, c')] w := by
  filter_upwards [h.ae_abs_mul_singularPow_le_indicator hθ0 hθΘ hc c',
    ae_torusParabolicSize_sub_pos z, ae_torusParabolicSize_sub_pos 0] with w h1 hz h0
  refine h1.trans ?_
  have hs : 0 ≤ c * torusParabolicSize z ^ θ :=
    mul_nonneg hc (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
  refine mul_le_mul_of_nonneg_left ?_ hs
  exact Set.indicator_le_self' (fun w _ => spSum_nonneg (fun p hp => by
    simp at hp
    rcases hp with rfl | rfl | rfl <;> norm_num) w) w

end RegularityStructures

end
