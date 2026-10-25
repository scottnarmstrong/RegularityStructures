/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2ChaosOneCross
public import Phi43.BPHZ.TreeI3Psi2ChaosOnePotPair

/-!
# Convolution estimates for potentials with general kernel exponents

Generalisations of `power_mul_abs_J_le`, `abs_J_mul_J_le` and `integral_pot_mul_pot_le` of the
chaos-`1` part of `I(Ψ³)Ψ²` to kernels `J` with `|J| ≤ B s^(-j)` of possibly different orders
`j` (the kernel `J_a` of order `3` and the kernel difference `ΔJ` of order `3 + θ`), and to two
different kernels in the pairing of two potentials.
-/

public section

open MeasureTheory

namespace RegularityStructures

/-- `∫ s(c - y)^(-a) |J(w - y)| dy ≤ C B s(c - w)^(5-a-j)` for `|J| ≤ B s^(-j)`. -/
theorem power_mul_abs_J_le_gen {a j : ℝ} (ha : 0 < a) (ha5 : a < 5) (hj : 0 < j)
    (hj5 : j < 5) (haj : 5 < a + j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {J : SpaceTime → ℝ} {B : ℝ}, 0 ≤ B → Measurable J →
      (∀ x, 0 < torusParabolicSize x → |J x| ≤ B * torusParabolicSize x ^ (-j)) →
      ∀ c w : SpaceTime, 0 < torusParabolicSize (c - w) →
        Integrable (fun y => singularPow a c y * |J (w - y)|) ∧
          ∫ y, singularPow a c y * |J (w - y)| ≤ C * B * torusParabolicSize (c - w) ^ (5 - a - j) := by
  obtain ⟨C, hC, h⟩ := integrable_and_integral_singularPow_mul_le (a := a) (b := j)
    ha ha5 hj hj5 haj
  refine ⟨C, hC, fun {J B} hB hJm hJ c w hcw => ?_⟩
  obtain ⟨i, b⟩ := h c w hcw
  have hmaj : Integrable (fun y => B * (singularPow a c y * singularPow j w y)) := i.const_mul _
  have hm : Measurable (fun y => singularPow a c y * |J (w - y)|) :=
    (measurable_singularPow a c).mul
      (continuous_abs.measurable.comp (hJm.comp (measurable_const.sub measurable_id)))
  have hle : ∀ᵐ y : SpaceTime ∂volume, singularPow a c y * |J (w - y)| ≤
      B * (singularPow a c y * singularPow j w y) := by
    filter_upwards [ae_torusParabolicSize_sub_pos w] with y a'
    have := mul_le_mul_of_nonneg_left (hJ _ a') (singularPow_nonneg a c y)
    refine this.trans (le_of_eq ?_)
    unfold singularPow
    ring
  refine ⟨Integrable.mono' hmaj hm.aestronglyMeasurable ?_, ?_⟩
  · filter_upwards [hle] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (singularPow_nonneg _ _ _) (abs_nonneg _))]
    exact hy
  · calc ∫ y, singularPow a c y * |J (w - y)| ≤ ∫ y, B * (singularPow a c y * singularPow j w y) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun y =>
            mul_nonneg (singularPow_nonneg _ _ _) (abs_nonneg _)) hmaj hle
      _ = B * ∫ y, singularPow a c y * singularPow j w y := by rw [integral_const_mul]
      _ ≤ B * (C * torusParabolicSize (c - w) ^ (5 - a - j)) :=
          mul_le_mul_of_nonneg_left b hB
      _ = _ := by ring

/-- `∫ |J₁(w - y)| |J₂(w' - y)| dy ≤ C B₁ B₂ s(w - w')^(5-j₁-j₂)`. -/
theorem abs_J_mul_J_le_gen {j₁ j₂ : ℝ} (hj₁ : 0 < j₁)
    (hj₁5 : j₁ < 5) (hj₂ : 0 < j₂) (hj₂5 : j₂ < 5) (hj : 5 < j₁ + j₂) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {J₁ J₂ : SpaceTime → ℝ} {B₁ B₂ : ℝ}, 0 ≤ B₁ → 0 ≤ B₂ →
      Measurable J₁ → Measurable J₂ →
      (∀ x, 0 < torusParabolicSize x → |J₁ x| ≤ B₁ * torusParabolicSize x ^ (-j₁)) →
      (∀ x, 0 < torusParabolicSize x → |J₂ x| ≤ B₂ * torusParabolicSize x ^ (-j₂)) →
      ∀ w w' : SpaceTime, 0 < torusParabolicSize (w - w') →
        Integrable (fun y => |J₁ (w - y)| * |J₂ (w' - y)|) ∧
          ∫ y, |J₁ (w - y)| * |J₂ (w' - y)| ≤
            C * B₁ * B₂ * torusParabolicSize (w - w') ^ (5 - j₁ - j₂) := by
  obtain ⟨C, hC, h⟩ := integrable_and_integral_singularPow_mul_le (a := j₁) (b := j₂)
    hj₁ hj₁5 hj₂ hj₂5 hj
  refine ⟨C, hC, fun {J₁ J₂ B₁ B₂} hB₁ hB₂ hJ₁m hJ₂m hJ₁ hJ₂ w w' hww => ?_⟩
  obtain ⟨i, b⟩ := h w w' hww
  have hmaj : Integrable (fun y => B₁ * B₂ * (singularPow j₁ w y * singularPow j₂ w' y)) :=
    i.const_mul _
  have hm : Measurable (fun y => |J₁ (w - y)| * |J₂ (w' - y)|) :=
    (continuous_abs.measurable.comp (hJ₁m.comp (measurable_const.sub measurable_id))).mul
      (continuous_abs.measurable.comp (hJ₂m.comp (measurable_const.sub measurable_id)))
  have hle : ∀ᵐ y : SpaceTime ∂volume, |J₁ (w - y)| * |J₂ (w' - y)| ≤
      B₁ * B₂ * (singularPow j₁ w y * singularPow j₂ w' y) := by
    filter_upwards [ae_torusParabolicSize_sub_pos w, ae_torusParabolicSize_sub_pos w'] with y a' b'
    have := mul_le_mul (hJ₁ _ a') (hJ₂ _ b') (abs_nonneg _) (mul_nonneg hB₁
      (singularPow_nonneg j₁ w y))
    refine this.trans (le_of_eq ?_)
    unfold singularPow
    ring
  refine ⟨Integrable.mono' hmaj hm.aestronglyMeasurable ?_, ?_⟩
  · filter_upwards [hle] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))]
    exact hy
  · calc ∫ y, |J₁ (w - y)| * |J₂ (w' - y)| ≤
          ∫ y, B₁ * B₂ * (singularPow j₁ w y * singularPow j₂ w' y) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun y =>
            mul_nonneg (abs_nonneg _) (abs_nonneg _)) hmaj hle
      _ = B₁ * B₂ * ∫ y, singularPow j₁ w y * singularPow j₂ w' y := by rw [integral_const_mul]
      _ ≤ B₁ * B₂ * (C * torusParabolicSize (w - w') ^ (5 - j₁ - j₂)) :=
          mul_le_mul_of_nonneg_left b (mul_nonneg hB₁ hB₂)
      _ = _ := by ring

/-- `∫ Pot_{J₁} h₁ · Pot_{J₂} h₂ ≤ X`, for two different kernels. -/
theorem integral_pot_mul_pot_le_pair {J₁ J₂ h₁ h₂ H₁ H₂ R : SpaceTime → ℝ}
    {Λ : SpaceTime → SpaceTime → ℝ} {X : ℝ} (hJ₁m : Measurable J₁) (hJ₂m : Measurable J₂)
    (hh₁0 : ∀ w, 0 ≤ h₁ w) (hh₁m : Measurable h₁) (hh₂0 : ∀ w, 0 ≤ h₂ w)
    (hh₂m : Measurable h₂) (hh₁H : ∀ᵐ w : SpaceTime ∂volume, h₁ w ≤ H₁ w)
    (hh₂H : ∀ᵐ w : SpaceTime ∂volume, h₂ w ≤ H₂ w)
    (hκ : ∀ w w' : SpaceTime, 0 < torusParabolicSize (w - w') →
      Integrable (fun y => |J₁ (w - y)| * |J₂ (w' - y)|) ∧
        ∫ y, |J₁ (w - y)| * |J₂ (w' - y)| ≤ Λ w w')
    (hR : ∀ᵐ w' : SpaceTime ∂volume, SingularIntLe (fun w => H₁ w * Λ w w') (R w'))
    (hX : SingularIntLe (fun w' => H₂ w' * R w') X) :
    Integrable (fun y => i3Psi2Pot J₁ h₁ y * i3Psi2Pot J₂ h₂ y) ∧
      ∫ y, i3Psi2Pot J₁ h₁ y * i3Psi2Pot J₂ h₂ y ≤ X := by
  have hmeasJ : ∀ w' : SpaceTime, Measurable (fun y => |J₂ (w' - y)|) := fun w' =>
    continuous_abs.measurable.comp (hJ₂m.comp (measurable_const.sub measurable_id))
  have step1 : ∀ᵐ w' : SpaceTime ∂volume,
      Integrable (fun y => |J₂ (w' - y)| * i3Psi2Pot J₁ h₁ y) ∧
      ∫ y, |J₂ (w' - y)| * i3Psi2Pot J₁ h₁ y ≤ R w' := by
    filter_upwards [hR] with w' hw'
    refine integral_mul_pot_le (J := J₁) (U := fun w => Λ w w') hJ₁m (fun y => abs_nonneg _)
      (hmeasJ w') hh₁0 hh₁m hh₁H ?_ hw'
    filter_upwards [ae_torusParabolicSize_sub_pos w'] with w hw
    have := hκ w w' (torusParabolicSize_sub_pos_symm hw)
    exact ⟨by simpa [mul_comm] using this.1, by simpa [mul_comm] using this.2⟩
  have step2 : ∀ᵐ w' : SpaceTime ∂volume,
      Integrable (fun y => i3Psi2Pot J₁ h₁ y * |J₂ (w' - y)|) ∧
      ∫ y, i3Psi2Pot J₁ h₁ y * |J₂ (w' - y)| ≤ R w' := by
    filter_upwards [step1] with w' hw'
    exact ⟨by simpa [mul_comm] using hw'.1, by simpa [mul_comm] using hw'.2⟩
  exact integral_mul_pot_le hJ₂m (i3Psi2Pot_nonneg hh₁0) (measurable_i3Psi2Pot hJ₁m hh₁m) hh₂0
    hh₂m hh₂H step2 hX

end RegularityStructures

end
