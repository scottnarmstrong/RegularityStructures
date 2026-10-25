/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductDiagramDiff3

/-!
# The difference chain piece of `I(Ψ²)Ψ`

`productDiffPiece3_bound`: the integrand `a(w) b(v) E(w - z, w - v, v - z')` is integrable with
iterated integral bounded by `C c₁ c₂ K μ (1 + T) s(z)^η s(z')^η`, `2 η + σ < 1`, for `E` as in
`productDiffPiece2_bound`.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

private theorem measurable_abq {a b : SpaceTime → ℝ} (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun p : SpaceTime × SpaceTime => |a p.1| * |b p.2|) :=
  ((continuous_abs.measurable.comp ha).comp measurable_fst).mul
    ((continuous_abs.measurable.comp hb).comp measurable_snd)

/-- **Difference chain piece** `a(w) b(v) E(w - z, w - v, v - z')`. -/
theorem productDiffPiece3_bound {Θ σ η : ℝ} (hσ : 0 < σ) (hη : 0 < η) (hηΘ : η ≤ Θ)
    (hout : 2 * η + σ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {c₁ c₂ T T' K μ : ℝ} {z z' : SpaceTime} {a b : SpaceTime → ℝ}
      {E : SpaceTime → SpaceTime → SpaceTime → ℝ}, 0 ≤ c₁ → 0 ≤ c₂ → 0 ≤ K → 0 ≤ μ → 0 ≤ T →
      IsGainKernel Θ c₁ T z a → IsGainKernel Θ c₂ T' z' b →
      Measurable (fun q : SpaceTime × SpaceTime × SpaceTime => E q.1 q.2.1 q.2.2) →
      (∀ x₁ x₂ x₃ : SpaceTime, 0 < torusParabolicSize x₁ → 0 < torusParabolicSize x₂ →
        0 < torusParabolicSize x₃ →
        |E x₁ x₂ x₃| ≤ K * μ * (torusParabolicSize x₁ ^ (-(1 + σ)) *
              torusParabolicSize x₂ ^ (-(1 : ℝ)) * torusParabolicSize x₃ ^ (-(1 : ℝ)) +
            torusParabolicSize x₁ ^ (-(1 : ℝ)) * torusParabolicSize x₂ ^ (-(1 + σ)) *
              torusParabolicSize x₃ ^ (-(1 : ℝ)) +
            torusParabolicSize x₁ ^ (-(1 : ℝ)) * torusParabolicSize x₂ ^ (-(1 : ℝ)) *
              torusParabolicSize x₃ ^ (-(1 + σ)))) →
      Integrable (Function.uncurry fun w v => a w * b v * E (w - z) (w - v) (v - z'))
          (volume.prod volume) ∧
        |∫ w, ∫ v, a w * b v * E (w - z) (w - v) (v - z')| ≤
          C * (c₁ * c₂ * K * μ) * (1 + T) *
            (torusParabolicSize z ^ η * torusParabolicSize z' ^ η) := by
  obtain ⟨C1, hC1, h1⟩ := productChain_majorant_integral (Θ := Θ) (θ₁ := η) (θ₂ := η)
    hη.le hηΘ hη.le hηΘ (g₁ := 1 + σ) (g₂ := 1) (g₃ := 1) (by linarith) (by norm_num)
    (by norm_num) (by norm_num) (by linarith) (by linarith) (by linarith)
  obtain ⟨C2, hC2, h2⟩ := productChain_majorant_integral (Θ := Θ) (θ₁ := η) (θ₂ := η)
    hη.le hηΘ hη.le hηΘ (g₁ := 1) (g₂ := 1 + σ) (g₃ := 1) (by norm_num) (by linarith)
    (by norm_num) (by linarith) (by linarith) (by linarith) (by linarith)
  obtain ⟨C3, hC3, h3⟩ := productChain_majorant_integral (Θ := Θ) (θ₁ := η) (θ₂ := η)
    hη.le hηΘ hη.le hηΘ (g₁ := 1) (g₂ := 1) (g₃ := 1 + σ) (by norm_num) (by norm_num)
    (by linarith) (by norm_num) (by linarith) (by linarith) (by linarith)
  have hq : 0 ≤ (2 : ℝ) ^ (1 + σ) := by positivity
  refine ⟨(C1 + C2 + C3) * (2 ^ (1 + σ) * 2 ^ (1 + σ)), by positivity, ?_⟩
  intro c₁ c₂ T T' K μ z z' a b E hc₁ hc₂ hK hμ hT ha hb hEm hE
  set M : ℝ := K * μ * (2 ^ (1 + σ) * 2 ^ (1 + σ)) with hMdef
  have hM : 0 ≤ M := by positivity
  obtain ⟨i1, b1⟩ := h1 hc₁ hc₂ hM hT ha hb
  obtain ⟨i2, b2⟩ := h2 hc₁ hc₂ hM hT ha hb
  obtain ⟨i3, b3⟩ := h3 hc₁ hc₂ hM hT ha hb
  have hFm : Measurable (Function.uncurry fun w v => a w * b v * E (w - z) (w - v) (v - z')) := by
    have h1 := ha.1
    have h2 := hb.1
    change Measurable (fun p : SpaceTime × SpaceTime =>
      a p.1 * b p.2 * E (p.1 - z) (p.1 - p.2) (p.2 - z'))
    exact ((h1.comp measurable_fst).mul (h2.comp measurable_snd)).mul
      (hEm.comp ((measurable_fst.sub measurable_const).prodMk
        ((measurable_fst.sub measurable_snd).prodMk (measurable_snd.sub measurable_const))))
  have mm : ∀ g₁ g₂ g₃ : ℝ, Measurable (Function.uncurry fun w v => |a w| * |b v| *
      (M * (singularPow g₁ z w * singularPow g₂ w v * singularPow g₃ z' v))) := fun g₁ g₂ g₃ =>
    (measurable_abq ha.1 hb.1).mul (measurable_const.mul (((measurable_singularPow_fst g₁ z).mul
      (measurable_singularPow_pair g₂)).mul (measurable_singularPow_snd g₃ z')))
  obtain ⟨hint, hbd⟩ := abs_iterated_le_of_dominated3
    (F := fun w v => a w * b v * E (w - z) (w - v) (v - z')) hFm (mm _ _ _) (mm _ _ _)
    (mm _ _ _) i1 i2 i3 (by
      filter_upwards [ae_torusParabolicSize_sub_pos z] with w hzw
      filter_upwards [ae_torusParabolicSize_sub_pos w, ae_torusParabolicSize_sub_pos z'] with
        v hv hzv
      have hwz : 0 < torusParabolicSize (w - z) := by
        have := torusParabolicSize_neg_le_two_mul (w - z)
        rw [neg_sub] at this
        linarith
      have hvz : 0 < torusParabolicSize (v - z') := by
        have := torusParabolicSize_neg_le_two_mul (v - z')
        rw [neg_sub] at this
        linarith
      have hEb := hE (w - z) (w - v) (v - z') hwz hv hvz
      have e : |a w * b v * E (w - z) (w - v) (v - z')| =
          |a w| * |b v| * |E (w - z) (w - v) (v - z')| := by simp [abs_mul]
      rw [e]
      have hab : 0 ≤ |a w| * |b v| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
      have key : ∀ g₁ g₂ g₃ : ℝ, 0 ≤ g₁ → g₁ ≤ 1 + σ → 0 ≤ g₃ → g₃ ≤ 1 + σ →
          torusParabolicSize (w - z) ^ (-g₁) * torusParabolicSize (w - v) ^ (-g₂) *
            torusParabolicSize (v - z') ^ (-g₃) ≤
          (2 ^ (1 + σ) * 2 ^ (1 + σ)) *
            (singularPow g₁ z w * singularPow g₂ w v * singularPow g₃ z' v) := by
        intro g₁ g₂ g₃ h1 h1' h3 h3'
        have f1 := rpow_neg_sub_flip_le' h1 h1' hzw
        have f3 := rpow_neg_sub_flip_le' h3 h3' hzv
        have n2 : 0 ≤ torusParabolicSize (w - v) ^ (-g₂) :=
          Real.rpow_nonneg (torusParabolicSize_nonneg _) _
        have n1 : 0 ≤ torusParabolicSize (w - z) ^ (-g₁) :=
          Real.rpow_nonneg (torusParabolicSize_nonneg _) _
        calc _ ≤ (2 ^ (1 + σ) * singularPow g₁ z w) * torusParabolicSize (w - v) ^ (-g₂) *
              (2 ^ (1 + σ) * singularPow g₃ z' v) :=
              mul_le_mul (mul_le_mul_of_nonneg_right f1 n2) f3
                (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
                (mul_nonneg (mul_nonneg hq (singularPow_nonneg _ _ _)) n2)
          _ = _ := by simp only [singularPow]; ring
      have k1 := key (1 + σ) 1 1 (by linarith) le_rfl (by norm_num) (by linarith)
      have k2 := key 1 (1 + σ) 1 (by norm_num) (by linarith) (by norm_num) (by linarith)
      have k3 := key 1 1 (1 + σ) (by norm_num) (by linarith) (by linarith) le_rfl
      calc |a w| * |b v| * |E (w - z) (w - v) (v - z')|
          ≤ |a w| * |b v| * (K * μ * (torusParabolicSize (w - z) ^ (-(1 + σ)) *
              torusParabolicSize (w - v) ^ (-(1 : ℝ)) * torusParabolicSize (v - z') ^ (-(1 : ℝ)) +
            torusParabolicSize (w - z) ^ (-(1 : ℝ)) * torusParabolicSize (w - v) ^ (-(1 + σ)) *
              torusParabolicSize (v - z') ^ (-(1 : ℝ)) +
            torusParabolicSize (w - z) ^ (-(1 : ℝ)) * torusParabolicSize (w - v) ^ (-(1 : ℝ)) *
              torusParabolicSize (v - z') ^ (-(1 + σ)))) := mul_le_mul_of_nonneg_left hEb hab
        _ ≤ |a w| * |b v| * (K * μ * ((2 ^ (1 + σ) * 2 ^ (1 + σ)) * (singularPow (1 + σ) z w *
              singularPow 1 w v * singularPow 1 z' v) +
            (2 ^ (1 + σ) * 2 ^ (1 + σ)) * (singularPow 1 z w * singularPow (1 + σ) w v *
              singularPow 1 z' v) +
            (2 ^ (1 + σ) * 2 ^ (1 + σ)) * (singularPow 1 z w * singularPow 1 w v *
              singularPow (1 + σ) z' v))) := by
            refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (mul_nonneg hK hμ)) hab
            linarith
        _ = _ := by simp only [hMdef]; ring)
  refine ⟨hint, hbd.trans ?_⟩
  have s0 := Real.rpow_nonneg (torusParabolicSize_nonneg z) η
  have s0' := Real.rpow_nonneg (torusParabolicSize_nonneg z') η
  have T0 : 0 ≤ 1 + T := by linarith
  have P0 : 0 ≤ (c₁ * c₂ * K * μ) * (1 + T) * (torusParabolicSize z ^ η * torusParabolicSize z' ^ η) := by
    positivity
  have e1 : C1 * (c₁ * c₂ * M) * (torusParabolicSize z ^ η * torusParabolicSize z' ^ η) * (1 + T) =
      C1 * (2 ^ (1 + σ) * 2 ^ (1 + σ)) * ((c₁ * c₂ * K * μ) * (1 + T) *
        (torusParabolicSize z ^ η * torusParabolicSize z' ^ η)) := by simp only [hMdef]; ring
  have e2 : C2 * (c₁ * c₂ * M) * (torusParabolicSize z ^ η * torusParabolicSize z' ^ η) * (1 + T) =
      C2 * (2 ^ (1 + σ) * 2 ^ (1 + σ)) * ((c₁ * c₂ * K * μ) * (1 + T) *
        (torusParabolicSize z ^ η * torusParabolicSize z' ^ η)) := by simp only [hMdef]; ring
  have e3 : C3 * (c₁ * c₂ * M) * (torusParabolicSize z ^ η * torusParabolicSize z' ^ η) * (1 + T) =
      C3 * (2 ^ (1 + σ) * 2 ^ (1 + σ)) * ((c₁ * c₂ * K * μ) * (1 + T) *
        (torusParabolicSize z ^ η * torusParabolicSize z' ^ η)) := by simp only [hMdef]; ring
  rw [e1] at b1
  rw [e2] at b2
  rw [e3] at b3
  nlinarith [b1, b2, b3]

end RegularityStructures

end
