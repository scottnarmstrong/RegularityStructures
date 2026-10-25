/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductDiagramMerge

/-!
# The three Wick diagrams of `I(Ψ²)Ψ`

For gain kernels `a` (at `z`), `b` (at `z'`) and a propagator kernel `Q`, the integrands

* `a(w) b(v) Q(w - v)²` (link),
* `a(w) b(v) Q(w - v) Q(w - z') Q(z - v)` (cross),
* `a(w) b(v) Q(w - z) Q(w - v) Q(v - z')` (chain)

are integrable on `SpaceTime × SpaceTime` and their iterated integrals are bounded by
`C c₁ c₂ B^k (1 + T) s(z)^θ s(z')^θ`, with `θ < 1` for the link and `θ < 1/2` for the other two.
All use `productChain_bound`.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

theorem mul_abs_le_of_merge {A q k u X : ℝ} (hq : |q| ≤ k * u) (hk : 0 ≤ k)
    (h : |A| * u ≤ X) : |A| * |q| ≤ k * X := by
  calc |A| * |q| ≤ |A| * (k * u) := mul_le_mul_of_nonneg_left hq (abs_nonneg _)
    _ = k * (|A| * u) := by ring
    _ ≤ k * X := mul_le_mul_of_nonneg_left h hk

theorem IsPropKernel.abs_sq_le {B : ℝ} {Q : SpaceTime → ℝ} (h : IsPropKernel B Q)
    {c w : SpaceTime} (hc : 0 < torusParabolicSize (c - w)) :
    |Q (c - w)| ^ 2 ≤ B ^ 2 * singularPow 2 c w := by
  have h1 := h.2.2 _ hc
  have hsq : |Q (c - w)| ^ 2 ≤ (B * torusParabolicSize (c - w) ^ (-(1 : ℝ))) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) h1 2
  have e : (B * torusParabolicSize (c - w) ^ (-(1 : ℝ))) ^ 2 =
      B ^ 2 * singularPow 2 c w := by
    rw [mul_pow, ← Real.rpow_natCast (torusParabolicSize (c - w) ^ (-(1 : ℝ))) 2,
      ← Real.rpow_mul hc.le]
    simp [singularPow]
  exact hsq.trans e.le

/-- **Link diagram** `a(w) b(v) Q(w - v)²`. -/
theorem productLinkSq_bound {Θ θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hθΘ : θ ≤ Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {c₁ c₂ T T' B : ℝ} {z z' : SpaceTime} {a b Q : SpaceTime → ℝ},
      0 ≤ c₁ → 0 ≤ c₂ → IsGainKernel Θ c₁ T z a → IsGainKernel Θ c₂ T' z' b →
      IsPropKernel B Q → 0 ≤ T →
      Integrable (Function.uncurry fun w v => a w * b v * Q (w - v) ^ 2)
          (volume.prod volume) ∧
        |∫ w, ∫ v, a w * b v * Q (w - v) ^ 2| ≤
          C * (c₁ * c₂ * B ^ 2) * (torusParabolicSize z ^ θ * torusParabolicSize z' ^ θ) *
            (1 + T) := by
  obtain ⟨C, hC, h⟩ := productChain_bound (α := 3 + θ) (β := 3 + θ) (γ := 2) (by linarith)
    (by linarith) (by norm_num) (by linarith) (by norm_num) (by linarith) (by linarith)
  refine ⟨C * 4, by positivity, ?_⟩
  intro c₁ c₂ T T' B z z' a b Q hc₁ hc₂ ha hb hQ hT
  have hB := hQ.2.1
  have hs : 0 ≤ torusParabolicSize z ^ θ := Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have hs' : 0 ≤ torusParabolicSize z' ^ θ := Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have hmeas : Measurable (Function.uncurry fun w v => a w * b v * Q (w - v) ^ 2) := by
    have := ((ha.1.comp measurable_fst).mul (hb.1.comp measurable_snd)).mul
      ((hQ.1.comp (measurable_fst.sub measurable_snd)).pow_const 2)
    exact this
  have := @h (fun w v => a w * b v * Q (w - v) ^ 2)
    (c₁ * c₂ * B ^ 2 * (torusParabolicSize z ^ θ * torusParabolicSize z' ^ θ)) T 0
    [(1, z), (1, 0)] [(1, z'), (1, 0)] (by positivity) hT
    (fun p hp => by simp at hp; rcases hp with rfl | rfl <;> norm_num)
    (fun p hp => by simp at hp; rcases hp with rfl | rfl <;> norm_num)
    hmeas.aestronglyMeasurable (by
      filter_upwards [ha.ae_abs_le_indicator hθ0.le hθΘ] with w hw
      filter_upwards [hb.ae_abs_le hθ0.le hθΘ, ae_torusParabolicSize_sub_pos w] with v hv hpos
      have hq := hQ.abs_sq_le hpos
      have e : |a w * b v * Q (w - v) ^ 2| = |a w| * |b v| * |Q (w - v)| ^ 2 := by
        simp [abs_mul]
      rw [e]
      have n1 := singularPow_nonneg 2 w v
      have n2 : 0 ≤ c₂ * torusParabolicSize z' ^ θ * spSum (3 + θ) [(1, z'), (1, 0)] v :=
        mul_nonneg (mul_nonneg hc₂ hs') (spSum_nonneg (fun p hp => by
          simp at hp; rcases hp with rfl | rfl <;> norm_num) v)
      calc |a w| * |b v| * |Q (w - v)| ^ 2
          ≤ (c₁ * torusParabolicSize z ^ θ * Set.indicator {w : SpaceTime | |w.1 - 0| ≤ T}
              (spSum (3 + θ) [(1, z), (1, 0)]) w) *
            (c₂ * torusParabolicSize z' ^ θ * spSum (3 + θ) [(1, z'), (1, 0)] v) *
            (B ^ 2 * singularPow 2 w v) :=
            mul_le_mul (mul_le_mul hw hv (abs_nonneg _) (abs_nonneg _ |>.trans hw)) hq
              (sq_nonneg _) (mul_nonneg (abs_nonneg _ |>.trans hw) n2)
        _ = _ := by ring)
  refine ⟨this.1, this.2.trans (le_of_eq ?_)⟩
  have e : spWeight [((1 : ℝ), z), (1, 0)] * spWeight [((1 : ℝ), z'), (1, 0)] = 4 := by
    norm_num [spWeight]
  rw [e]
  ring

end RegularityStructures

end
