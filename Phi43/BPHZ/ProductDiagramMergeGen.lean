/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductDiagramMerge

/-!
# Merging a power of arbitrary order into the gain majorant

The generalisation of `IsGainKernel.ae_abs_mul_singularPow_le` to a centred power `s(c - w)^(-e)`
with any `e ≥ 0`, and the comparison `s(w - c)^(-e) ≤ 2^e s(c - w)^(-e)` that reverses the orientation
of a propagator argument.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

/-- `|a w| s(c - w)^(-e) ≤ c₁ s(z)^θ ∑ ...` with the slab indicator, any `e ≥ 0`. -/
theorem IsGainKernel.ae_abs_mul_singularPow_le_indicator_gen {Θ c T : ℝ} {z : SpaceTime}
    {a : SpaceTime → ℝ} (h : IsGainKernel Θ c T z a) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθΘ : θ ≤ Θ)
    (hc : 0 ≤ c) {e : ℝ} (he : 0 ≤ e) (c' : SpaceTime) :
    ∀ᵐ w : SpaceTime ∂volume, |a w| * singularPow e c' w ≤ c * torusParabolicSize z ^ θ *
      Set.indicator {w : SpaceTime | |w.1 - 0| ≤ T}
        (spSum (3 + θ + e) [(1, z), (1, 0), (2, c')]) w := by
  filter_upwards [h.ae_abs_le_indicator hθ0 hθΘ, ae_torusParabolicSize_sub_pos z,
    ae_torusParabolicSize_sub_pos 0, ae_torusParabolicSize_sub_pos c'] with w h1 hz h0 hc'
  have hs : 0 ≤ c * torusParabolicSize z ^ θ :=
    mul_nonneg hc (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
  have hn := singularPow_nonneg e c' w
  by_cases hw : w ∈ {w : SpaceTime | |w.1 - 0| ≤ T}
  · rw [Set.indicator_of_mem hw] at h1 ⊢
    have hm := spSum_mul_singularPow_le (a := 3 + θ) (e := e) (by linarith) he
      (ps := [(1, z), (1, 0)]) (fun p hp => by
        simp at hp
        rcases hp with rfl | rfl <;> norm_num) c' (w := w) (by
        intro p hp
        simp at hp
        rcases hp with rfl | rfl
        · exact hz
        · exact h0) hc'
    have e1 : spSum (3 + θ + e) [(1, z), (1, 0), (2, c')] w =
        spSum (3 + θ + e) [(1, z), (1, 0)] w + 2 * singularPow (3 + θ + e) c' w := by
      simp [spSum]; ring
    have e2 : spWeight [((1 : ℝ), z), (1, 0)] = 2 := by simp [spWeight]; norm_num
    rw [e1]
    rw [e2] at hm
    calc |a w| * singularPow e c' w
        ≤ (c * torusParabolicSize z ^ θ * spSum (3 + θ) [(1, z), (1, 0)] w) *
          singularPow e c' w := mul_le_mul_of_nonneg_right h1 hn
      _ = c * torusParabolicSize z ^ θ * (spSum (3 + θ) [(1, z), (1, 0)] w *
          singularPow e c' w) := by ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hs
        have : (3 + θ + e) = (3 + θ) + e := rfl
        rw [this]; exact hm
  · rw [Set.indicator_of_notMem hw] at h1 ⊢
    have h2 : |a w| ≤ 0 := by simpa using h1
    have : a w = 0 := abs_nonpos_iff.1 h2
    rw [this]; simp

/-- `|a w| s(c - w)^(-e) ≤ c₁ s(z)^θ ∑ ...` without the slab indicator, any `e ≥ 0`. -/
theorem IsGainKernel.ae_abs_mul_singularPow_le_gen {Θ c T : ℝ} {z : SpaceTime}
    {a : SpaceTime → ℝ} (h : IsGainKernel Θ c T z a) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθΘ : θ ≤ Θ)
    (hc : 0 ≤ c) {e : ℝ} (he : 0 ≤ e) (c' : SpaceTime) :
    ∀ᵐ w : SpaceTime ∂volume, |a w| * singularPow e c' w ≤ c * torusParabolicSize z ^ θ *
      spSum (3 + θ + e) [(1, z), (1, 0), (2, c')] w := by
  filter_upwards [h.ae_abs_mul_singularPow_le_indicator_gen hθ0 hθΘ hc he c'] with w h1
  refine h1.trans ?_
  have hs : 0 ≤ c * torusParabolicSize z ^ θ :=
    mul_nonneg hc (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
  refine mul_le_mul_of_nonneg_left ?_ hs
  exact Set.indicator_le_self' (fun w _ => spSum_nonneg (fun p hp => by
    simp at hp
    rcases hp with rfl | rfl | rfl <;> norm_num) w) w

/-- Orientation flip: `s(w - c)^(-e) ≤ 2^e s(c - w)^(-e)` for `e ≥ 0`. -/
theorem rpow_neg_sub_flip_le {c w : SpaceTime} {e : ℝ} (he : 0 ≤ e)
    (hc : 0 < torusParabolicSize (c - w)) :
    torusParabolicSize (w - c) ^ (-e) ≤ 2 ^ e * singularPow e c w := by
  have hneg := torusParabolicSize_neg_le_two_mul (w - c)
  rw [neg_sub] at hneg
  have hx : 0 < torusParabolicSize (w - c) := by linarith
  have h2 : torusParabolicSize (c - w) / 2 ≤ torusParabolicSize (w - c) := by linarith
  have h4 : torusParabolicSize (w - c) ^ (-e) ≤ (torusParabolicSize (c - w) / 2) ^ (-e) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) h2 (by linarith)
  rw [Real.div_rpow hc.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
    div_inv_eq_mul] at h4
  simp only [singularPow]
  linarith

end RegularityStructures

end
