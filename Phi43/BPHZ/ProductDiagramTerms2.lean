/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductDiagramTerms

/-!
# The cross and chain diagrams of `I(Ψ²)Ψ`

`a(w) b(v) Q(w - v) Q(w - z') Q(z - v)` and `a(w) b(v) Q(w - z) Q(w - v) Q(v - z')`, bounded by
`C c₁ c₂ B³ (1 + T) s(z)^θ s(z')^θ` for `0 < θ < 1/2`.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

/-- **Cross diagram** `a(w) b(v) Q(w - v) Q(w - z') Q(z - v)`. -/
theorem productCross_bound {Θ θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1 / 2) (hθΘ : θ ≤ Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {c₁ c₂ T T' B : ℝ} {z z' : SpaceTime} {a b Q : SpaceTime → ℝ},
      0 ≤ c₁ → 0 ≤ c₂ → IsGainKernel Θ c₁ T z a → IsGainKernel Θ c₂ T' z' b →
      IsPropKernel B Q → 0 ≤ T →
      Integrable (Function.uncurry fun w v => a w * b v * (Q (w - v) * Q (w - z') * Q (z - v)))
          (volume.prod volume) ∧
        |∫ w, ∫ v, a w * b v * (Q (w - v) * Q (w - z') * Q (z - v))| ≤
          C * (c₁ * c₂ * B ^ 3) * (torusParabolicSize z ^ θ * torusParabolicSize z' ^ θ) *
            (1 + T) := by
  obtain ⟨C, hC, h⟩ := productChain_bound (α := 3 + θ + 1) (β := 3 + θ + 1) (γ := 1)
    (by linarith) (by linarith) (by norm_num) (by linarith) (by norm_num) (by linarith)
    (by linarith)
  refine ⟨C * 32, by positivity, ?_⟩
  intro c₁ c₂ T T' B z z' a b Q hc₁ hc₂ ha hb hQ hT
  have hB := hQ.2.1
  have hs : 0 ≤ torusParabolicSize z ^ θ := Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have hs' : 0 ≤ torusParabolicSize z' ^ θ := Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have hmeas : Measurable (Function.uncurry fun w v =>
      a w * b v * (Q (w - v) * Q (w - z') * Q (z - v))) := by
    have h1 := ha.1
    have h2 := hb.1
    have h3 := hQ.1
    change Measurable (fun p : SpaceTime × SpaceTime =>
      a p.1 * b p.2 * (Q (p.1 - p.2) * Q (p.1 - z') * Q (z - p.2)))
    fun_prop
  have hnn1 : SpNonneg [((1 : ℝ), z), (1, 0), (2, z')] :=
    fun p hp => by simp at hp; rcases hp with rfl | rfl | rfl <;> norm_num
  have hnn2 : SpNonneg [((1 : ℝ), z'), (1, 0), (2, z)] :=
    fun p hp => by simp at hp; rcases hp with rfl | rfl | rfl <;> norm_num
  have := @h (fun w v => a w * b v * (Q (w - v) * Q (w - z') * Q (z - v)))
    (2 * (c₁ * c₂ * B ^ 3 * (torusParabolicSize z ^ θ * torusParabolicSize z' ^ θ))) T 0
    [(1, z), (1, 0), (2, z')] [(1, z'), (1, 0), (2, z)] (by positivity) hT hnn1 hnn2
    hmeas.aestronglyMeasurable (by
      filter_upwards [ha.ae_abs_mul_singularPow_le_indicator hθ0.le hθΘ hc₁ z',
        ae_torusParabolicSize_sub_pos z'] with w hw hzw
      filter_upwards [hb.ae_abs_mul_singularPow_le hθ0.le hθΘ hc₂ z,
        ae_torusParabolicSize_sub_pos z, ae_torusParabolicSize_sub_pos w] with v hv hzv hwv
      have q1 := hQ.abs_direct_le hwv
      have q2 := hQ.abs_flip_le (w := w) hzw
      have q3 := hQ.abs_direct_le hzv
      have e : |a w * b v * (Q (w - v) * Q (w - z') * Q (z - v))| =
          (|a w| * |Q (w - z')|) * (|b v| * |Q (z - v)|) * |Q (w - v)| := by
        simp only [abs_mul]; ring
      rw [e]
      have m1 := mul_abs_le_of_merge q2 (by positivity) hw
      have m2 := mul_abs_le_of_merge q3 hB hv
      have n1 : 0 ≤ 2 * B * (c₁ * torusParabolicSize z ^ θ * Set.indicator
          {w : SpaceTime | |w.1 - 0| ≤ T} (spSum (3 + θ + 1) [(1, z), (1, 0), (2, z')]) w) :=
        (mul_nonneg (abs_nonneg _) (abs_nonneg _)).trans m1
      have n2 : 0 ≤ B * (c₂ * torusParabolicSize z' ^ θ *
          spSum (3 + θ + 1) [(1, z'), (1, 0), (2, z)] v) :=
        (mul_nonneg (abs_nonneg _) (abs_nonneg _)).trans m2
      calc _ ≤ (2 * B * (c₁ * torusParabolicSize z ^ θ * Set.indicator
              {w : SpaceTime | |w.1 - 0| ≤ T} (spSum (3 + θ + 1) [(1, z), (1, 0), (2, z')]) w)) *
            (B * (c₂ * torusParabolicSize z' ^ θ *
              spSum (3 + θ + 1) [(1, z'), (1, 0), (2, z)] v)) *
            (B * singularPow 1 w v) :=
            mul_le_mul (mul_le_mul m1 m2 (mul_nonneg (abs_nonneg _) (abs_nonneg _)) n1) q1
              (abs_nonneg _) (mul_nonneg n1 n2)
        _ = _ := by ring)
  refine ⟨this.1, this.2.trans (le_of_eq ?_)⟩
  have e : spWeight [((1 : ℝ), z), (1, 0), (2, z')] *
      spWeight [((1 : ℝ), z'), (1, 0), (2, z)] = 16 := by
    norm_num [spWeight]
  rw [e]
  ring

/-- **Chain diagram** `a(w) b(v) Q(w - z) Q(w - v) Q(v - z')`. -/
theorem productChain3_bound {Θ θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1 / 2) (hθΘ : θ ≤ Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {c₁ c₂ T T' B : ℝ} {z z' : SpaceTime} {a b Q : SpaceTime → ℝ},
      0 ≤ c₁ → 0 ≤ c₂ → IsGainKernel Θ c₁ T z a → IsGainKernel Θ c₂ T' z' b →
      IsPropKernel B Q → 0 ≤ T →
      Integrable (Function.uncurry fun w v => a w * b v * (Q (w - z) * Q (w - v) * Q (v - z')))
          (volume.prod volume) ∧
        |∫ w, ∫ v, a w * b v * (Q (w - z) * Q (w - v) * Q (v - z'))| ≤
          C * (c₁ * c₂ * B ^ 3) * (torusParabolicSize z ^ θ * torusParabolicSize z' ^ θ) *
            (1 + T) := by
  obtain ⟨C, hC, h⟩ := productChain_bound (α := 3 + θ + 1) (β := 3 + θ + 1) (γ := 1)
    (by linarith) (by linarith) (by norm_num) (by linarith) (by norm_num) (by linarith)
    (by linarith)
  refine ⟨C * 64, by positivity, ?_⟩
  intro c₁ c₂ T T' B z z' a b Q hc₁ hc₂ ha hb hQ hT
  have hB := hQ.2.1
  have hs : 0 ≤ torusParabolicSize z ^ θ := Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have hs' : 0 ≤ torusParabolicSize z' ^ θ := Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have hmeas : Measurable (Function.uncurry fun w v =>
      a w * b v * (Q (w - z) * Q (w - v) * Q (v - z'))) := by
    have h1 := ha.1
    have h2 := hb.1
    have h3 := hQ.1
    change Measurable (fun p : SpaceTime × SpaceTime =>
      a p.1 * b p.2 * (Q (p.1 - z) * Q (p.1 - p.2) * Q (p.2 - z')))
    fun_prop
  have hnn1 : SpNonneg [((1 : ℝ), z), (1, 0), (2, z)] :=
    fun p hp => by simp at hp; rcases hp with rfl | rfl | rfl <;> norm_num
  have hnn2 : SpNonneg [((1 : ℝ), z'), (1, 0), (2, z')] :=
    fun p hp => by simp at hp; rcases hp with rfl | rfl | rfl <;> norm_num
  have := @h (fun w v => a w * b v * (Q (w - z) * Q (w - v) * Q (v - z')))
    (4 * (c₁ * c₂ * B ^ 3 * (torusParabolicSize z ^ θ * torusParabolicSize z' ^ θ))) T 0
    [(1, z), (1, 0), (2, z)] [(1, z'), (1, 0), (2, z')] (by positivity) hT hnn1 hnn2
    hmeas.aestronglyMeasurable (by
      filter_upwards [ha.ae_abs_mul_singularPow_le_indicator hθ0.le hθΘ hc₁ z,
        ae_torusParabolicSize_sub_pos z] with w hw hzw
      filter_upwards [hb.ae_abs_mul_singularPow_le hθ0.le hθΘ hc₂ z',
        ae_torusParabolicSize_sub_pos z', ae_torusParabolicSize_sub_pos w] with v hv hzv hwv
      have q1 := hQ.abs_flip_le (w := w) hzw
      have q2 := hQ.abs_direct_le hwv
      have q3 := hQ.abs_flip_le (w := v) hzv
      have e : |a w * b v * (Q (w - z) * Q (w - v) * Q (v - z'))| =
          (|a w| * |Q (w - z)|) * (|b v| * |Q (v - z')|) * |Q (w - v)| := by
        simp only [abs_mul]; ring
      rw [e]
      have m1 := mul_abs_le_of_merge q1 (by positivity) hw
      have m2 := mul_abs_le_of_merge q3 (by positivity) hv
      have n1 : 0 ≤ 2 * B * (c₁ * torusParabolicSize z ^ θ * Set.indicator
          {w : SpaceTime | |w.1 - 0| ≤ T} (spSum (3 + θ + 1) [(1, z), (1, 0), (2, z)]) w) :=
        (mul_nonneg (abs_nonneg _) (abs_nonneg _)).trans m1
      have n2 : 0 ≤ 2 * B * (c₂ * torusParabolicSize z' ^ θ *
          spSum (3 + θ + 1) [(1, z'), (1, 0), (2, z')] v) :=
        (mul_nonneg (abs_nonneg _) (abs_nonneg _)).trans m2
      calc _ ≤ (2 * B * (c₁ * torusParabolicSize z ^ θ * Set.indicator
              {w : SpaceTime | |w.1 - 0| ≤ T} (spSum (3 + θ + 1) [(1, z), (1, 0), (2, z)]) w)) *
            (2 * B * (c₂ * torusParabolicSize z' ^ θ *
              spSum (3 + θ + 1) [(1, z'), (1, 0), (2, z')] v)) *
            (B * singularPow 1 w v) :=
            mul_le_mul (mul_le_mul m1 m2 (mul_nonneg (abs_nonneg _) (abs_nonneg _)) n1) q2
              (abs_nonneg _) (mul_nonneg n1 n2)
        _ = _ := by ring)
  refine ⟨this.1, this.2.trans (le_of_eq ?_)⟩
  have e : spWeight [((1 : ℝ), z), (1, 0), (2, z)] *
      spWeight [((1 : ℝ), z'), (1, 0), (2, z')] = 16 := by
    norm_num [spWeight]
  rw [e]
  ring

end RegularityStructures

end
