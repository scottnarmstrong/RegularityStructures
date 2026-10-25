/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3PsiDiagramMultiPointwise
public import Phi43.BPHZ.TreeI3Psi2DiagramLeaves
public import Phi43.BPHZ.TreeI3Psi2DiagramDefs
public import Phi43.BPHZ.TreeI3Psi2DiagramMultiLevel

/-!
# Weighted principal and chain diagrams

Wrappers around the chain and principal majorants of `I(Ψ³)Ψ` for the weights that occur in
`I(Ψ³)Ψ²`: the weight `Λ |δK(z, w)| |δK(z', v)| ×` (a product of powers of the distances) is a
two-level majorant (`TwoLevelLe`) with bound `Λ C ×` a power combination.  Hence every measurable `F`
dominated by it is integrable on the product with iterated integral bounded by this bound, and
sums of such weights are handled by `TwoLevelLe.add`.  The exponents are general, so that they
accommodate the factor `μ s^(-θ)` gained by one covariance in the difference of two fields.
-/

public section

open MeasureTheory

namespace RegularityStructures

private theorem measurable_dK_abs {K : SpaceTime → ℝ} (hK : Measurable K) (z' : SpaceTime) :
    Measurable (fun v => |i3Psi2dK K z' v|) := by
  have : Measurable (fun v => i3Psi2dK K z' v) := by unfold i3Psi2dK; fun_prop
  exact continuous_abs.measurable.comp this

private theorem measurable_size_sub_right (a : SpaceTime) (e : ℝ) :
    Measurable (fun v => torusParabolicSize (a - v) ^ e) :=
  (Phi43.measurable_torusParabolicSize.comp (measurable_const.sub measurable_id)).pow_const _

private theorem measurable_size_sub_left (a : SpaceTime) (e : ℝ) :
    Measurable (fun v => torusParabolicSize (v - a) ^ e) :=
  (Phi43.measurable_torusParabolicSize.comp (measurable_id.sub measurable_const)).pow_const _

/-- **Weighted principal diagram.** -/
theorem i3Psi2PrincipalWeighted_twoLevelLe {B θ τ : ℝ} (hB : 0 ≤ B) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hτ : 0 ≤ τ) (hθτ : θ + τ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K : SpaceTime → ℝ} {Λ : ℝ}, 0 ≤ Λ → Measurable K →
      (∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ))) →
      (∀ u h : SpaceTime, 0 < torusParabolicSize u → torusParabolicSize h ≤ torusParabolicSize u / 2 →
        |K (u + h) - K u| ≤ B * torusParabolicSize h * torusParabolicSize u ^ (-(4 : ℝ))) →
      (∀ x : SpaceTime, 1 < |x.1| → K x = 0) →
      ∀ z z' : SpaceTime, torusParabolicSize z ≤ 1 → torusParabolicSize z' ≤ 1 →
        TwoLevelLe (fun w v => Λ * (|i3Psi2dK K z w| * |i3Psi2dK K z' v| *
          torusParabolicSize (w - v) ^ (-(3 + τ)))) (Λ * C * torusParabolicSize z' ^ θ) := by
  obtain ⟨Cp, hCp, hP⟩ := twoLevelLe_principalMajorant hθ hτ hθτ
  refine ⟨12 * B ^ 2 * Cp, by positivity, ?_⟩
  intro K Λ hΛ hKm hK hinc hKs z z' hz1 hz1'
  have hnn : 0 ≤ Λ * (12 * B ^ 2 * torusParabolicSize z' ^ θ) :=
    mul_nonneg hΛ (mul_nonneg (by positivity) (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
  have hG := ((hP z z' hz1 hz1').const_mul hnn).mono_right
    (le_of_eq (show Λ * (12 * B ^ 2 * torusParabolicSize z' ^ θ) * Cp =
      Λ * (12 * B ^ 2 * Cp) * torusParabolicSize z' ^ θ by ring))
  refine hG.of_le (fun w => ?_) (fun w v => ?_) ?_
  · exact measurable_const.mul ((measurable_const.mul (measurable_dK_abs hKm z')).mul
      (measurable_size_sub_right w _))
  · exact mul_nonneg hΛ (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
  · filter_upwards [ae_torusParabolicSize_sub_pos z, ae_torusParabolicSize_sub_pos 0] with w a b
    filter_upwards [ae_torusParabolicSize_sub_pos z', ae_torusParabolicSize_sub_pos 0] with v a' b'
    have := abs_dK_dK_principal_le (θ := θ) (τ := τ) hB hθ.le hθ1 hK hinc hKs hz1 a b a' b'
    have h2 := mul_le_mul_of_nonneg_left this hΛ
    refine h2.trans (le_of_eq ?_)
    ring

/-- **Weighted chain diagram**, weights `s(w - u)^(-(1+α)) s(w - v)^(-(2+β₀)) s(u' - v)^(-(1+γ))`
with `(u, u') = (z, z')` or `(z', z)`. -/
theorem i3Psi2ChainLeftWeighted_twoLevelLe {B δ α β₀ γ η : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ)
    (hα : 0 ≤ α) (hα1 : α < 1) (hγ : 0 ≤ γ) (hγ1 : γ < 1) (hβ₀ : 0 ≤ β₀) (hβ3 : β₀ + δ < 3)
    (he : α + (γ + (β₀ + δ)) = η) (hη1 : η ≤ 1) (hκ1 : γ + (β₀ + δ) < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K : SpaceTime → ℝ} {Λ : ℝ}, 0 ≤ Λ → Measurable K →
      (∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ))) →
      (∀ x : SpaceTime, 1 < |x.1| → K x = 0) →
      ∀ z z' u u' : SpaceTime, 0 < torusParabolicSize (z - z') → 0 < torusParabolicSize z →
        0 < torusParabolicSize z' → torusParabolicSize z ≤ 1 → torusParabolicSize z' ≤ 1 →
        ((u = z ∧ u' = z') ∨ (u = z' ∧ u' = z)) →
        TwoLevelLe (fun w v => Λ * (|i3Psi2dK K z w| * |i3Psi2dK K z' v| *
          (torusParabolicSize (w - u) ^ (-(1 + α)) * torusParabolicSize (w - v) ^ (-(2 + β₀)) *
            torusParabolicSize (u' - v) ^ (-(1 + γ))))) (Λ * C * i3Psi2S η z z') := by
  have hη : 0 < η := by rw [← he]; linarith
  obtain ⟨Cc, hCc, hC⟩ := twoLevelLe_chainMajorant_of_eq (α := α) (β := β₀ + δ) (γ := γ) (η := η)
    hα1 hγ hγ1 (by linarith) hβ3 he hη hη1 hκ1
  have n3 : (0 : ℝ) ≤ 3 ^ δ := Real.rpow_nonneg (by norm_num) _
  refine ⟨4 * B ^ 2 * 3 ^ δ * Cc, by positivity, ?_⟩
  intro K Λ hΛ hKm hK hKs z z' u u' hzz hz hz' hz1 hz1' hu
  have hnn : 0 ≤ Λ * (4 * B ^ 2 * 3 ^ δ) := mul_nonneg hΛ (by positivity)
  have hG := ((hC z z' u u' hzz hz hz' hu).const_mul hnn).mono_right
    (le_of_eq (show Λ * (4 * B ^ 2 * 3 ^ δ) * (Cc * (torusParabolicSize (z - z') ^ (-η) +
        torusParabolicSize z ^ (-η) + torusParabolicSize z' ^ (-η))) =
      Λ * (4 * B ^ 2 * 3 ^ δ * Cc) * i3Psi2S η z z' by
        unfold i3Psi2S; simp only [sub_zero]; ring))
  refine hG.of_le (fun w => ?_) (fun w v => ?_) ?_
  · exact measurable_const.mul ((measurable_const.mul (measurable_dK_abs hKm z')).mul
      (((measurable_const.mul (measurable_size_sub_right w _)).mul
        (measurable_size_sub_right u' _))))
  · exact mul_nonneg hΛ (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      (mul_nonneg (mul_nonneg (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
        (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
        (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)))
  · filter_upwards [ae_torusParabolicSize_sub_pos z, ae_torusParabolicSize_sub_pos 0,
      ae_torusParabolicSize_sub_pos u] with w a b c
    filter_upwards [ae_torusParabolicSize_sub_pos z', ae_torusParabolicSize_sub_pos 0,
      ae_torusParabolicSize_sub_pos u', ae_torusParabolicSize_sub_pos w] with v a' b' c' d'
    have := abs_dK_dK_chain_flip_left_le (K := K) (B := B) (δ := δ) (α := α) (β₀ := β₀)
      (β := β₀ + δ) (γ := γ) (a := 1 + α) (b := 2 + β₀) (c := 1 + γ) hB hδ.le hα hα1.le hγ rfl
      rfl rfl rfl hK hKs hz1 hz1' a b c a' b' c' d'
    have h2 := mul_le_mul_of_nonneg_left this hΛ
    refine h2.trans (le_of_eq ?_)
    ring

/-- **Weighted chain diagram**, weights `s(w - u)^(-(1+α)) s(w - v)^(-(2+β₀)) s(v - u')^(-(1+γ))`
with `(u, u') = (z, z')` or `(z', z)`. -/
theorem i3Psi2ChainWeighted_twoLevelLe {B δ α β₀ γ η : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ) (hα : 0 ≤ α)
    (hα1 : α < 1) (hγ : 0 ≤ γ) (hγ1 : γ < 1) (hβ₀ : 0 ≤ β₀) (hβ3 : β₀ + δ < 3)
    (he : α + (γ + (β₀ + δ)) = η) (hη1 : η ≤ 1) (hκ1 : γ + (β₀ + δ) < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K : SpaceTime → ℝ} {Λ : ℝ}, 0 ≤ Λ → Measurable K →
      (∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ))) →
      (∀ x : SpaceTime, 1 < |x.1| → K x = 0) →
      ∀ z z' u u' : SpaceTime, 0 < torusParabolicSize (z - z') → 0 < torusParabolicSize z →
        0 < torusParabolicSize z' → torusParabolicSize z ≤ 1 → torusParabolicSize z' ≤ 1 →
        ((u = z ∧ u' = z') ∨ (u = z' ∧ u' = z)) →
        TwoLevelLe (fun w v => Λ * (|i3Psi2dK K z w| * |i3Psi2dK K z' v| *
          (torusParabolicSize (w - u) ^ (-(1 + α)) * torusParabolicSize (w - v) ^ (-(2 + β₀)) *
            torusParabolicSize (v - u') ^ (-(1 + γ))))) (Λ * C * i3Psi2S η z z') := by
  have hη : 0 < η := by rw [← he]; linarith
  obtain ⟨Cc, hCc, hC⟩ := twoLevelLe_chainMajorant_of_eq (α := α) (β := β₀ + δ) (γ := γ) (η := η)
    hα1 hγ hγ1 (by linarith) hβ3 he hη hη1 hκ1
  have n3 : (0 : ℝ) ≤ 3 ^ δ := Real.rpow_nonneg (by norm_num) _
  refine ⟨16 * B ^ 2 * 3 ^ δ * Cc, by positivity, ?_⟩
  intro K Λ hΛ hKm hK hKs z z' u u' hzz hz hz' hz1 hz1' hu
  have hnn : 0 ≤ Λ * (16 * B ^ 2 * 3 ^ δ) := mul_nonneg hΛ (by positivity)
  have hG := ((hC z z' u u' hzz hz hz' hu).const_mul hnn).mono_right
    (le_of_eq (show Λ * (16 * B ^ 2 * 3 ^ δ) * (Cc * (torusParabolicSize (z - z') ^ (-η) +
        torusParabolicSize z ^ (-η) + torusParabolicSize z' ^ (-η))) =
      Λ * (16 * B ^ 2 * 3 ^ δ * Cc) * i3Psi2S η z z' by
        unfold i3Psi2S; simp only [sub_zero]; ring))
  refine hG.of_le (fun w => ?_) (fun w v => ?_) ?_
  · exact measurable_const.mul ((measurable_const.mul (measurable_dK_abs hKm z')).mul
      (((measurable_const.mul (measurable_size_sub_right w _)).mul
        (measurable_size_sub_left u' _))))
  · exact mul_nonneg hΛ (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      (mul_nonneg (mul_nonneg (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
        (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
        (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)))
  · filter_upwards [ae_torusParabolicSize_sub_pos z, ae_torusParabolicSize_sub_pos 0,
      ae_torusParabolicSize_sub_pos u] with w a b c
    filter_upwards [ae_torusParabolicSize_sub_pos z', ae_torusParabolicSize_sub_pos 0,
      ae_torusParabolicSize_sub_pos u', ae_torusParabolicSize_sub_pos w] with v a' b' c' d'
    have := abs_dK_dK_chain_flip_le (K := K) (B := B) (δ := δ) (α := α) (β₀ := β₀)
      (β := β₀ + δ) (γ := γ) (a := 1 + α) (b := 2 + β₀) (c := 1 + γ) hB hδ.le hα hα1.le hγ hγ1.le
      rfl rfl rfl rfl hK hKs hz1 hz1' a b c a' b' c' d'
    have h2 := mul_le_mul_of_nonneg_left this hΛ
    refine h2.trans (le_of_eq ?_)
    ring

end RegularityStructures

end
