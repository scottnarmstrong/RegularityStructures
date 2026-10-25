/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestTreesDiffI3Psi2PointN
public import Phi43.BPHZ.TreeI3Psi2DiagramMultiWeighted

/-!
# The weighted chain diagrams of the difference of `I(Ψ³)Ψ²`, for arbitrary `z, z'`

Global versions of `i3Psi2ChainLeftWeighted_twoLevelLe`, `i3Psi2ChainWeighted_twoLevelLe`: the
bound is `Λ C D^δ S_η(z, z')` where `D` bounds `s(w - v)` on the slab
`|w.1| ≤ |z.1| + 1`, `|v.1| ≤ |z'.1| + 1`.
-/

public section

open MeasureTheory

namespace RegularityStructures

private theorem measurable_dK_abs_c {K : SpaceTime → ℝ} (hK : Measurable K) (z' : SpaceTime) :
    Measurable (fun v => |i3Psi2dK K z' v|) := by
  have : Measurable (fun v => i3Psi2dK K z' v) := by unfold i3Psi2dK; fun_prop
  exact continuous_abs.measurable.comp this

private theorem measurable_size_sub_right_c (a : SpaceTime) (e : ℝ) :
    Measurable (fun v => torusParabolicSize (a - v) ^ e) :=
  (Phi43.measurable_torusParabolicSize.comp (measurable_const.sub measurable_id)).pow_const _

private theorem measurable_size_sub_left_c (a : SpaceTime) (e : ℝ) :
    Measurable (fun v => torusParabolicSize (v - a) ^ e) :=
  (Phi43.measurable_torusParabolicSize.comp (measurable_id.sub measurable_const)).pow_const _

/-- **Weighted chain diagram, global**, weights `s(w - u)^(-(1+α)) s(w - v)^(-(2+β₀))
s(u' - v)^(-(1+γ))` with `(u, u') = (z, z')` or `(z', z)`. -/
theorem i3Psi2ChainLeftWeighted_twoLevelLe_global {B δ α β₀ γ η : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ)
    (hα : 0 ≤ α) (hα1 : α < 1) (hγ : 0 ≤ γ) (hγ1 : γ < 1) (hβ₀ : 0 ≤ β₀) (hβ3 : β₀ + δ < 3)
    (he : α + (γ + (β₀ + δ)) = η) (hη1 : η ≤ 1) (hκ1 : γ + (β₀ + δ) < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K : SpaceTime → ℝ} {Λ D : ℝ}, 0 ≤ Λ → 0 ≤ D → Measurable K →
      (∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ))) →
      (∀ x : SpaceTime, 1 < |x.1| → K x = 0) →
      ∀ z z' u u' : SpaceTime,
        (∀ w v : SpaceTime, |w.1| ≤ |z.1| + 1 → |v.1| ≤ |z'.1| + 1 →
          torusParabolicSize (w - v) ≤ D) →
        0 < torusParabolicSize (z - z') → 0 < torusParabolicSize z →
        0 < torusParabolicSize z' → ((u = z ∧ u' = z') ∨ (u = z' ∧ u' = z)) →
        TwoLevelLe (fun w v => Λ * (|i3Psi2dK K z w| * |i3Psi2dK K z' v| *
          (torusParabolicSize (w - u) ^ (-(1 + α)) * torusParabolicSize (w - v) ^ (-(2 + β₀)) *
            torusParabolicSize (u' - v) ^ (-(1 + γ))))) (Λ * C * D ^ δ * i3Psi2S η z z') := by
  have hη : 0 < η := by rw [← he]; linarith
  obtain ⟨Cc, hCc, hC⟩ := twoLevelLe_chainMajorant_of_eq (α := α) (β := β₀ + δ) (γ := γ) (η := η)
    hα1 hγ hγ1 (by linarith) hβ3 he hη hη1 hκ1
  refine ⟨4 * B ^ 2 * Cc, by positivity, ?_⟩
  intro K Λ D hΛ hD0 hKm hK hKs z z' u u' hD hzz hz hz' hu
  have n3 : (0 : ℝ) ≤ D ^ δ := Real.rpow_nonneg hD0 _
  have hnn : 0 ≤ Λ * (4 * B ^ 2 * D ^ δ) := mul_nonneg hΛ (by positivity)
  have hG := ((hC z z' u u' hzz hz hz' hu).const_mul hnn).mono_right
    (le_of_eq (show Λ * (4 * B ^ 2 * D ^ δ) * (Cc * (torusParabolicSize (z - z') ^ (-η) +
        torusParabolicSize z ^ (-η) + torusParabolicSize z' ^ (-η))) =
      Λ * (4 * B ^ 2 * Cc) * D ^ δ * i3Psi2S η z z' by
        unfold i3Psi2S; simp only [sub_zero]; ring))
  refine hG.of_le (fun w => ?_) (fun w v => ?_) ?_
  · exact measurable_const.mul ((measurable_const.mul (measurable_dK_abs_c hKm z')).mul
      (((measurable_const.mul (measurable_size_sub_right_c w _)).mul
        (measurable_size_sub_right_c u' _))))
  · exact mul_nonneg hΛ (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      (mul_nonneg (mul_nonneg (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
        (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
        (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)))
  · filter_upwards [ae_torusParabolicSize_sub_pos z, ae_torusParabolicSize_sub_pos 0,
      ae_torusParabolicSize_sub_pos u] with w a b c
    filter_upwards [ae_torusParabolicSize_sub_pos z', ae_torusParabolicSize_sub_pos 0,
      ae_torusParabolicSize_sub_pos u', ae_torusParabolicSize_sub_pos w] with v a' b' c' d'
    have := abs_dK_dK_chain_flip_left_le_global (K := K) (B := B) (δ := δ) (α := α) (β₀ := β₀)
      (β := β₀ + δ) (γ := γ) (a := 1 + α) (b := 2 + β₀) (c := 1 + γ) hB hδ.le hα hα1.le hγ hD0
      rfl rfl rfl rfl hK hKs hD a b c a' b' c' d'
    have h2 := mul_le_mul_of_nonneg_left this hΛ
    refine h2.trans (le_of_eq ?_)
    ring

/-- **Weighted chain diagram, global**, weights `s(w - u)^(-(1+α)) s(w - v)^(-(2+β₀))
s(v - u')^(-(1+γ))` with `(u, u') = (z, z')` or `(z', z)`. -/
theorem i3Psi2ChainWeighted_twoLevelLe_global {B δ α β₀ γ η : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ)
    (hα : 0 ≤ α) (hα1 : α < 1) (hγ : 0 ≤ γ) (hγ1 : γ < 1) (hβ₀ : 0 ≤ β₀) (hβ3 : β₀ + δ < 3)
    (he : α + (γ + (β₀ + δ)) = η) (hη1 : η ≤ 1) (hκ1 : γ + (β₀ + δ) < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K : SpaceTime → ℝ} {Λ D : ℝ}, 0 ≤ Λ → 0 ≤ D → Measurable K →
      (∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ))) →
      (∀ x : SpaceTime, 1 < |x.1| → K x = 0) →
      ∀ z z' u u' : SpaceTime,
        (∀ w v : SpaceTime, |w.1| ≤ |z.1| + 1 → |v.1| ≤ |z'.1| + 1 →
          torusParabolicSize (w - v) ≤ D) →
        0 < torusParabolicSize (z - z') → 0 < torusParabolicSize z →
        0 < torusParabolicSize z' → ((u = z ∧ u' = z') ∨ (u = z' ∧ u' = z)) →
        TwoLevelLe (fun w v => Λ * (|i3Psi2dK K z w| * |i3Psi2dK K z' v| *
          (torusParabolicSize (w - u) ^ (-(1 + α)) * torusParabolicSize (w - v) ^ (-(2 + β₀)) *
            torusParabolicSize (v - u') ^ (-(1 + γ))))) (Λ * C * D ^ δ * i3Psi2S η z z') := by
  have hη : 0 < η := by rw [← he]; linarith
  obtain ⟨Cc, hCc, hC⟩ := twoLevelLe_chainMajorant_of_eq (α := α) (β := β₀ + δ) (γ := γ) (η := η)
    hα1 hγ hγ1 (by linarith) hβ3 he hη hη1 hκ1
  refine ⟨16 * B ^ 2 * Cc, by positivity, ?_⟩
  intro K Λ D hΛ hD0 hKm hK hKs z z' u u' hD hzz hz hz' hu
  have n3 : (0 : ℝ) ≤ D ^ δ := Real.rpow_nonneg hD0 _
  have hnn : 0 ≤ Λ * (16 * B ^ 2 * D ^ δ) := mul_nonneg hΛ (by positivity)
  have hG := ((hC z z' u u' hzz hz hz' hu).const_mul hnn).mono_right
    (le_of_eq (show Λ * (16 * B ^ 2 * D ^ δ) * (Cc * (torusParabolicSize (z - z') ^ (-η) +
        torusParabolicSize z ^ (-η) + torusParabolicSize z' ^ (-η))) =
      Λ * (16 * B ^ 2 * Cc) * D ^ δ * i3Psi2S η z z' by
        unfold i3Psi2S; simp only [sub_zero]; ring))
  refine hG.of_le (fun w => ?_) (fun w v => ?_) ?_
  · exact measurable_const.mul ((measurable_const.mul (measurable_dK_abs_c hKm z')).mul
      (((measurable_const.mul (measurable_size_sub_right_c w _)).mul
        (measurable_size_sub_left_c u' _))))
  · exact mul_nonneg hΛ (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      (mul_nonneg (mul_nonneg (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
        (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
        (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)))
  · filter_upwards [ae_torusParabolicSize_sub_pos z, ae_torusParabolicSize_sub_pos 0,
      ae_torusParabolicSize_sub_pos u] with w a b c
    filter_upwards [ae_torusParabolicSize_sub_pos z', ae_torusParabolicSize_sub_pos 0,
      ae_torusParabolicSize_sub_pos u', ae_torusParabolicSize_sub_pos w] with v a' b' c' d'
    have := abs_dK_dK_chain_flip_le_global (K := K) (B := B) (δ := δ) (α := α) (β₀ := β₀)
      (β := β₀ + δ) (γ := γ) (a := 1 + α) (b := 2 + β₀) (c := 1 + γ) hB hδ.le hα hα1.le hγ hγ1.le
      hD0 rfl rfl rfl rfl hK hKs hD a b c a' b' c' d'
    have h2 := mul_le_mul_of_nonneg_left this hΛ
    refine h2.trans (le_of_eq ?_)
    ring

end RegularityStructures

end
