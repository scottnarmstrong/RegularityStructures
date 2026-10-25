/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductDiagramMergeGen

/-!
# The link, cross and chain diagrams with arbitrary slot exponents

If `|F(w, v)| ≤ |a(w)| |b(v)| M s(w - v)^(-γ)` (link), `≤ |a| |b| M s(w - v)^(-g₁) s(z' - w)^(-g₂)
s(z - v)^(-g₃)` (cross) or `≤ |a| |b| M s(z - w)^(-g₁) s(w - v)^(-g₂) s(z' - v)^(-g₃)` (chain) for
gain kernels `a` (at `z`), `b` (at `z'`), then `F` is integrable on `SpaceTime × SpaceTime` and
`|∫∫ F| ≤ C c₁ c₂ M (1 + T) s(z)^θ₁ s(z')^θ₂`, provided the exponents satisfy the conditions of
`productChain_bound`.  The constant depends only on the exponents.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

private theorem sp_nonneg_pair {z : SpaceTime} : SpNonneg [((1 : ℝ), z), (1, 0)] :=
  fun p hp => by simp at hp; rcases hp with rfl | rfl <;> norm_num

private theorem sp_nonneg_trip (z c' : SpaceTime) : SpNonneg [((1 : ℝ), z), (1, 0), (2, c')] :=
  fun p hp => by simp at hp; rcases hp with rfl | rfl | rfl <;> norm_num

/-- **Link diagram** `|F| ≤ |a| |b| M s(w - v)^(-γ)`. -/
theorem productLinkGen_bound {Θ θ₁ θ₂ γ : ℝ} (hθ₁ : 0 ≤ θ₁) (hθ₁Θ : θ₁ ≤ Θ) (hθ₂ : 0 ≤ θ₂)
    (hθ₂Θ : θ₂ ≤ Θ) (hγ : 0 < γ) (hγ5 : γ < 5) (hβ5 : 3 + θ₂ < 5) (hβγ : 5 < 3 + θ₂ + γ)
    (hout : 3 + θ₁ + (3 + θ₂ + γ - 5) < 5) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {c₁ c₂ T T' M : ℝ} {z z' : SpaceTime} {a b : SpaceTime → ℝ}
      {F : SpaceTime → SpaceTime → ℝ}, 0 ≤ c₁ → 0 ≤ c₂ → 0 ≤ M → 0 ≤ T →
      IsGainKernel Θ c₁ T z a → IsGainKernel Θ c₂ T' z' b →
      AEStronglyMeasurable (Function.uncurry F) (volume.prod volume) →
      (∀ᵐ w : SpaceTime ∂volume, ∀ᵐ v : SpaceTime ∂volume,
        |F w v| ≤ |a w| * |b v| * (M * singularPow γ w v)) →
      Integrable (Function.uncurry F) (volume.prod volume) ∧
        |∫ w, ∫ v, F w v| ≤ C * (c₁ * c₂ * M) *
          (torusParabolicSize z ^ θ₁ * torusParabolicSize z' ^ θ₂) * (1 + T) := by
  obtain ⟨C, hC, h⟩ := productChain_bound (α := 3 + θ₁) (β := 3 + θ₂) (γ := γ) (by linarith)
    (by linarith) hγ hβ5 hγ5 hβγ hout
  refine ⟨C * 4, by positivity, ?_⟩
  intro c₁ c₂ T T' M z z' a b F hc₁ hc₂ hM hT ha hb hmeas hF
  have hs : 0 ≤ torusParabolicSize z ^ θ₁ := Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have hs' : 0 ≤ torusParabolicSize z' ^ θ₂ := Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have := @h F (c₁ * c₂ * M * (torusParabolicSize z ^ θ₁ * torusParabolicSize z' ^ θ₂)) T 0
    [(1, z), (1, 0)] [(1, z'), (1, 0)] (by positivity) hT sp_nonneg_pair sp_nonneg_pair
    hmeas (by
      filter_upwards [ha.ae_abs_le_indicator hθ₁ hθ₁Θ, hF] with w hw hFw
      filter_upwards [hb.ae_abs_le hθ₂ hθ₂Θ, hFw] with v hv hFv
      refine hFv.trans ?_
      have n1 := singularPow_nonneg γ w v
      have n2 : 0 ≤ c₂ * torusParabolicSize z' ^ θ₂ * spSum (3 + θ₂) [(1, z'), (1, 0)] v :=
        mul_nonneg (mul_nonneg hc₂ hs') (spSum_nonneg (sp_nonneg_pair (z := z')) v)
      calc |a w| * |b v| * (M * singularPow γ w v)
          ≤ (c₁ * torusParabolicSize z ^ θ₁ * Set.indicator {w : SpaceTime | |w.1 - 0| ≤ T}
              (spSum (3 + θ₁) [(1, z), (1, 0)]) w) *
            (c₂ * torusParabolicSize z' ^ θ₂ * spSum (3 + θ₂) [(1, z'), (1, 0)] v) *
            (M * singularPow γ w v) :=
            mul_le_mul (mul_le_mul hw hv (abs_nonneg _) ((abs_nonneg _).trans hw))
              le_rfl (mul_nonneg hM n1) (mul_nonneg ((abs_nonneg _).trans hw) n2)
        _ = _ := by ring)
  refine ⟨this.1, this.2.trans (le_of_eq ?_)⟩
  have e : spWeight [((1 : ℝ), z), (1, 0)] * spWeight [((1 : ℝ), z'), (1, 0)] = 4 := by
    norm_num [spWeight]
  rw [e]
  ring

/-- **Cross diagram** `|F| ≤ |a| |b| M s(w - v)^(-g₁) s(z' - w)^(-g₂) s(z - v)^(-g₃)`. -/
theorem productCrossGen_bound {Θ θ₁ θ₂ g₁ g₂ g₃ : ℝ} (hθ₁ : 0 ≤ θ₁) (hθ₁Θ : θ₁ ≤ Θ)
    (hθ₂ : 0 ≤ θ₂) (hθ₂Θ : θ₂ ≤ Θ) (hg₁ : 0 < g₁) (hg₂ : 0 ≤ g₂) (hg₃ : 0 ≤ g₃)
    (hg₁5 : g₁ < 5) (hβ5 : 3 + θ₂ + g₃ < 5)
    (hβγ : 5 < 3 + θ₂ + g₃ + g₁)
    (hout : 3 + θ₁ + g₂ + (3 + θ₂ + g₃ + g₁ - 5) < 5) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {c₁ c₂ T T' M : ℝ} {z z' : SpaceTime} {a b : SpaceTime → ℝ}
      {F : SpaceTime → SpaceTime → ℝ}, 0 ≤ c₁ → 0 ≤ c₂ → 0 ≤ M → 0 ≤ T →
      IsGainKernel Θ c₁ T z a → IsGainKernel Θ c₂ T' z' b →
      AEStronglyMeasurable (Function.uncurry F) (volume.prod volume) →
      (∀ᵐ w : SpaceTime ∂volume, ∀ᵐ v : SpaceTime ∂volume,
        |F w v| ≤ |a w| * |b v| * (M * (singularPow g₁ w v * singularPow g₂ z' w *
          singularPow g₃ z v))) →
      Integrable (Function.uncurry F) (volume.prod volume) ∧
        |∫ w, ∫ v, F w v| ≤ C * (c₁ * c₂ * M) *
          (torusParabolicSize z ^ θ₁ * torusParabolicSize z' ^ θ₂) * (1 + T) := by
  obtain ⟨C, hC, h⟩ := productChain_bound (α := 3 + θ₁ + g₂) (β := 3 + θ₂ + g₃) (γ := g₁)
    (by linarith) (by linarith) hg₁ hβ5 hg₁5 hβγ hout
  refine ⟨C * 16, by positivity, ?_⟩
  intro c₁ c₂ T T' M z z' a b F hc₁ hc₂ hM hT ha hb hmeas hF
  have hs : 0 ≤ torusParabolicSize z ^ θ₁ := Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have hs' : 0 ≤ torusParabolicSize z' ^ θ₂ := Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have := @h F (c₁ * c₂ * M * (torusParabolicSize z ^ θ₁ * torusParabolicSize z' ^ θ₂)) T 0
    [(1, z), (1, 0), (2, z')] [(1, z'), (1, 0), (2, z)] (by positivity) hT (sp_nonneg_trip z z')
    (sp_nonneg_trip z' z) hmeas (by
      filter_upwards [ha.ae_abs_mul_singularPow_le_indicator_gen hθ₁ hθ₁Θ hc₁ hg₂ z', hF] with
        w hw hFw
      filter_upwards [hb.ae_abs_mul_singularPow_le_gen hθ₂ hθ₂Θ hc₂ hg₃ z, hFw] with v hv hFv
      refine hFv.trans ?_
      have n1 := singularPow_nonneg g₁ w v
      have n2 := singularPow_nonneg g₂ z' w
      have n3 := singularPow_nonneg g₃ z v
      have e : |a w| * |b v| * (M * (singularPow g₁ w v * singularPow g₂ z' w *
          singularPow g₃ z v)) = M * ((|a w| * singularPow g₂ z' w) *
          (|b v| * singularPow g₃ z v) * singularPow g₁ w v) := by ring
      rw [e]
      have p1 : 0 ≤ |a w| * singularPow g₂ z' w := mul_nonneg (abs_nonneg _) n2
      have p2 : 0 ≤ |b v| * singularPow g₃ z v := mul_nonneg (abs_nonneg _) n3
      have q1 := p1.trans hw
      calc M * ((|a w| * singularPow g₂ z' w) * (|b v| * singularPow g₃ z v) *
            singularPow g₁ w v)
          ≤ M * ((c₁ * torusParabolicSize z ^ θ₁ * Set.indicator {w : SpaceTime | |w.1 - 0| ≤ T}
              (spSum (3 + θ₁ + g₂) [(1, z), (1, 0), (2, z')]) w) *
            (c₂ * torusParabolicSize z' ^ θ₂ *
              spSum (3 + θ₂ + g₃) [(1, z'), (1, 0), (2, z)] v) * singularPow g₁ w v) :=
            mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_mul hw hv p2 q1) le_rfl n1
              (mul_nonneg q1 (p2.trans hv))) hM
        _ = _ := by ring)
  refine ⟨this.1, this.2.trans (le_of_eq ?_)⟩
  have e : spWeight [((1 : ℝ), z), (1, 0), (2, z')] *
      spWeight [((1 : ℝ), z'), (1, 0), (2, z)] = 16 := by norm_num [spWeight]
  rw [e]
  ring

/-- **Chain diagram** `|F| ≤ |a| |b| M s(z - w)^(-g₁) s(w - v)^(-g₂) s(z' - v)^(-g₃)`. -/
theorem productChainGen_bound {Θ θ₁ θ₂ g₁ g₂ g₃ : ℝ} (hθ₁ : 0 ≤ θ₁) (hθ₁Θ : θ₁ ≤ Θ)
    (hθ₂ : 0 ≤ θ₂) (hθ₂Θ : θ₂ ≤ Θ) (hg₁ : 0 ≤ g₁) (hg₂ : 0 < g₂) (hg₃ : 0 ≤ g₃)
    (hg₂5 : g₂ < 5) (hβ5 : 3 + θ₂ + g₃ < 5)
    (hβγ : 5 < 3 + θ₂ + g₃ + g₂)
    (hout : 3 + θ₁ + g₁ + (3 + θ₂ + g₃ + g₂ - 5) < 5) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {c₁ c₂ T T' M : ℝ} {z z' : SpaceTime} {a b : SpaceTime → ℝ}
      {F : SpaceTime → SpaceTime → ℝ}, 0 ≤ c₁ → 0 ≤ c₂ → 0 ≤ M → 0 ≤ T →
      IsGainKernel Θ c₁ T z a → IsGainKernel Θ c₂ T' z' b →
      AEStronglyMeasurable (Function.uncurry F) (volume.prod volume) →
      (∀ᵐ w : SpaceTime ∂volume, ∀ᵐ v : SpaceTime ∂volume,
        |F w v| ≤ |a w| * |b v| * (M * (singularPow g₁ z w * singularPow g₂ w v *
          singularPow g₃ z' v))) →
      Integrable (Function.uncurry F) (volume.prod volume) ∧
        |∫ w, ∫ v, F w v| ≤ C * (c₁ * c₂ * M) *
          (torusParabolicSize z ^ θ₁ * torusParabolicSize z' ^ θ₂) * (1 + T) := by
  obtain ⟨C, hC, h⟩ := productChain_bound (α := 3 + θ₁ + g₁) (β := 3 + θ₂ + g₃) (γ := g₂)
    (by linarith) (by linarith) hg₂ hβ5 hg₂5 hβγ hout
  refine ⟨C * 16, by positivity, ?_⟩
  intro c₁ c₂ T T' M z z' a b F hc₁ hc₂ hM hT ha hb hmeas hF
  have hs : 0 ≤ torusParabolicSize z ^ θ₁ := Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have hs' : 0 ≤ torusParabolicSize z' ^ θ₂ := Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have := @h F (c₁ * c₂ * M * (torusParabolicSize z ^ θ₁ * torusParabolicSize z' ^ θ₂)) T 0
    [(1, z), (1, 0), (2, z)] [(1, z'), (1, 0), (2, z')] (by positivity) hT (sp_nonneg_trip z z)
    (sp_nonneg_trip z' z') hmeas (by
      filter_upwards [ha.ae_abs_mul_singularPow_le_indicator_gen hθ₁ hθ₁Θ hc₁ hg₁ z, hF] with
        w hw hFw
      filter_upwards [hb.ae_abs_mul_singularPow_le_gen hθ₂ hθ₂Θ hc₂ hg₃ z', hFw] with v hv hFv
      refine hFv.trans ?_
      have n1 := singularPow_nonneg g₁ z w
      have n2 := singularPow_nonneg g₂ w v
      have n3 := singularPow_nonneg g₃ z' v
      have e : |a w| * |b v| * (M * (singularPow g₁ z w * singularPow g₂ w v *
          singularPow g₃ z' v)) = M * ((|a w| * singularPow g₁ z w) *
          (|b v| * singularPow g₃ z' v) * singularPow g₂ w v) := by ring
      rw [e]
      have p1 : 0 ≤ |a w| * singularPow g₁ z w := mul_nonneg (abs_nonneg _) n1
      have p2 : 0 ≤ |b v| * singularPow g₃ z' v := mul_nonneg (abs_nonneg _) n3
      have q1 := p1.trans hw
      calc M * ((|a w| * singularPow g₁ z w) * (|b v| * singularPow g₃ z' v) *
            singularPow g₂ w v)
          ≤ M * ((c₁ * torusParabolicSize z ^ θ₁ * Set.indicator {w : SpaceTime | |w.1 - 0| ≤ T}
              (spSum (3 + θ₁ + g₁) [(1, z), (1, 0), (2, z)]) w) *
            (c₂ * torusParabolicSize z' ^ θ₂ *
              spSum (3 + θ₂ + g₃) [(1, z'), (1, 0), (2, z')] v) * singularPow g₂ w v) :=
            mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_mul hw hv p2 q1) le_rfl n2
              (mul_nonneg q1 (p2.trans hv))) hM
        _ = _ := by ring)
  refine ⟨this.1, this.2.trans (le_of_eq ?_)⟩
  have e : spWeight [((1 : ℝ), z), (1, 0), (2, z)] *
      spWeight [((1 : ℝ), z'), (1, 0), (2, z')] = 16 := by norm_num [spWeight]
  rw [e]
  ring

end RegularityStructures

end
